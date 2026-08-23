//! The rename scan and its capture guard.
//!
//! `scan_for_renames` walks the tree deciding which binder gets which
//! new display name. The `name_shared_with_other_id*` family is the
//! guard that keeps it honest: a target name already carried by a
//! DIFFERENT `VarId` anywhere the binder is visible would make two
//! distinct bindings read alike, so the rename is dropped instead.

use super::*;

/// Scan the AST for function bindings and determine better names.
pub(super) fn scan_for_renames(
    expr: &PseudoExpr,
    rename_map: &mut HashMap<String, String>,
    fallback_rename_map: &mut HashMap<String, String>,
    let_rename_map: &mut HashMap<VarId, String>,
    binder_rename_map: &mut HashMap<VarId, String>,
    used_names: &mut HashSet<String>,
    _phase: NamingPhase,
) {
    let consistent_ref_ids = collect_consistent_ref_ids(expr);
    let fold_rec_candidates = collect_fold_rec_candidates(expr);

    struct RenameScanVisitor<'a> {
        rename_map: &'a mut HashMap<String, String>,
        fallback_rename_map: &'a mut HashMap<String, String>,
        let_rename_map: &'a mut HashMap<VarId, String>,
        binder_rename_map: &'a mut HashMap<VarId, String>,
        used_names: &'a mut HashSet<String>,
        skip_let_bound_recfns: HashSet<VarId>,
        consistent_ref_ids: &'a HashSet<VarId>,
        fold_rec_candidates: &'a HashSet<FoldRecCandidateKey>,
        root_expr: &'a PseudoExpr,
    }

    impl RenameScanVisitor<'_> {
        fn maybe_rename_param_binders<'a>(
            &mut self,
            hints: impl IntoIterator<Item = (&'a Binder, &'a str)>,
            scope_expr: &PseudoExpr,
        ) {
            let mut used_param_names = HashSet::new();
            for (binder, hint) in hints {
                if !is_param_hint_candidate_name(binder.as_str()) {
                    continue;
                }
                let new_name = if expr_references_other_var_named(scope_expr, hint, binder.var_id())
                {
                    unique_name(hint, self.used_names)
                } else {
                    let new_name = unique_param_name(hint, &mut used_param_names);
                    self.used_names.insert(new_name.clone());
                    new_name
                };
                if binder.as_str() != new_name {
                    self.binder_rename_map.insert(binder.id, new_name.clone());
                    self.rename_map.insert(binder.to_string(), new_name.clone());
                    if !name_shared_with_other_id_outside_expr(
                        self.root_expr,
                        scope_expr,
                        binder.as_str(),
                        binder.id,
                    ) {
                        self.fallback_rename_map
                            .insert(binder.to_string(), new_name);
                    }
                }
            }
        }

        fn record_let_rename(
            &mut self,
            name: &str,
            id: VarId,
            allowed_other_ids: &[VarId],
            new_name: String,
        ) {
            self.let_rename_map.insert(id, new_name.clone());
            self.binder_rename_map.insert(id, new_name.clone());
            self.rename_map.insert(name.to_string(), new_name.clone());
            if !name_shared_with_other_id_except(self.root_expr, name, id, allowed_other_ids) {
                self.fallback_rename_map.insert(name.to_string(), new_name);
            }
        }
    }

    impl ExprVisitor for RenameScanVisitor<'_> {
        fn visit_let(
            &mut self,
            name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            body: &PseudoExpr,
        ) {
            if let Some(let_vid) = *id
                && let Some(hint) = analyze_function_binding_with_fold_rec_candidates(
                    name,
                    value,
                    self.fold_rec_candidates,
                )
                .or_else(|| {
                    analyze_temporary_value_binding_with_consistency_impl(
                        name,
                        value,
                        Some(self.consistent_ref_ids),
                    )
                })
                .or_else(|| analyze_value_binding_with_known_renames(name, value, self.rename_map))
            {
                let new_name = unique_name(&hint, self.used_names);
                if new_name != name {
                    let allowed_other_ids = linked_let_rename_ids(name, let_vid, value, body);
                    self.record_let_rename(name, let_vid, &allowed_other_ids, new_name);
                }
            }

            if let PseudoExpr::RecFn {
                name: rec_name,
                params,
                body: rec_body,
            } = value
            {
                if !self.rename_map.contains_key(name)
                    && let Some(hint) = analyze_rec_function_body(
                        rec_name.as_str(),
                        Some(rec_name.var_id()),
                        params,
                        rec_body,
                    )
                {
                    // Feed dependent result-name inference without renaming
                    // this let: the fold rewrites from the id-keyed maps, so
                    // this name-keyed map is analysis input only.
                    self.rename_map.insert(name.to_string(), hint);
                }
                if let Some(let_vid) = *id
                    && let Some(new_name) = self.let_rename_map.get(&let_vid).cloned()
                    && rec_name.as_str() != new_name
                {
                    self.binder_rename_map.insert(rec_name.id, new_name);
                }
                self.skip_let_bound_recfns.insert(rec_name.id);
                self.maybe_rename_param_binders(
                    analyze_rec_function_param_hints(
                        rec_name.as_str(),
                        Some(rec_name.var_id()),
                        params,
                        rec_body,
                    ),
                    rec_body,
                );
            }

            if let PseudoExpr::Lambda {
                params,
                body: lambda_body,
            } = value
            {
                self.maybe_rename_param_binders(
                    analyze_lambda_param_hints(params, lambda_body),
                    lambda_body,
                );
            }
        }

        fn visit_recfn(&mut self, name: &Binder, params: &[Binder], body: &PseudoExpr) {
            if self.skip_let_bound_recfns.remove(&name.id) {
                return;
            }
            if let Some(hint) =
                analyze_rec_function_body(name.as_str(), Some(name.var_id()), params, body)
            {
                let new_name = unique_name(&hint, self.used_names);
                if name.as_str() != new_name {
                    self.binder_rename_map.insert(name.id, new_name.clone());
                    self.rename_map.insert(name.to_string(), new_name.clone());
                    if !name_shared_with_other_id(self.root_expr, name.as_str(), name.id) {
                        self.fallback_rename_map.insert(name.to_string(), new_name);
                    }
                }
            }
            self.maybe_rename_param_binders(
                analyze_rec_function_param_hints(name.as_str(), Some(name.var_id()), params, body),
                body,
            );
        }
    }

    RenameScanVisitor {
        rename_map,
        fallback_rename_map,
        let_rename_map,
        binder_rename_map,
        used_names,
        skip_let_bound_recfns: HashSet::new(),
        consistent_ref_ids: &consistent_ref_ids,
        fold_rec_candidates: &fold_rec_candidates,
        root_expr: expr,
    }
    .walk(expr);
}

/// True if `name` names at least two distinct binders (different
/// `VarId`s) in `expr`. Guards name-keyed rename insertion: with a
/// shared old name, `rename_map[old_name] = new_name` would also
/// rename the unrelated binders and strand their refs.
pub(super) fn name_shared_with_other_id(expr: &PseudoExpr, name: &str, own_id: VarId) -> bool {
    name_shared_with_other_id_except(expr, name, own_id, &[])
}

pub(super) fn name_shared_with_other_id_outside_expr(
    expr: &PseudoExpr,
    skipped_expr: &PseudoExpr,
    name: &str,
    own_id: VarId,
) -> bool {
    name_shared_with_other_id_except_skipping(
        expr,
        name,
        own_id,
        &[],
        Some(skipped_expr as *const PseudoExpr),
    )
}

pub(super) fn linked_let_rename_ids(
    let_name: &str,
    let_id: VarId,
    value: &PseudoExpr,
    body: &PseudoExpr,
) -> Vec<VarId> {
    let mut ids = Vec::new();
    if let PseudoExpr::RecFn { name, .. } = value
        && name.as_str() == let_name
    {
        ids.push(name.id);
    }
    if let Some(id) = linked_let_when_subject_name_id(let_name, let_id, body) {
        ids.push(id);
    }
    ids
}

pub(super) fn linked_let_when_subject_name_id(
    let_name: &str,
    let_id: VarId,
    body: &PseudoExpr,
) -> Option<VarId> {
    let PseudoExpr::When {
        subject,
        subject_name: Some(subject_name),
        ..
    } = body
    else {
        return None;
    };
    let PseudoExpr::Var {
        name: subject_var,
        id: subject_id,
    } = subject.as_ref()
    else {
        return None;
    };
    if subject_name.as_str() != let_name || subject_var != let_name {
        return None;
    }
    if subject_id.get().is_some() && *subject_id != Some(let_id) {
        return None;
    }
    Some(subject_name.id)
}

pub(super) fn name_shared_with_other_id_except(
    expr: &PseudoExpr,
    name: &str,
    own_id: VarId,
    allowed_other_ids: &[VarId],
) -> bool {
    name_shared_with_other_id_except_skipping(expr, name, own_id, allowed_other_ids, None)
}

pub(super) fn name_shared_with_other_id_except_skipping(
    expr: &PseudoExpr,
    name: &str,
    own_id: VarId,
    allowed_other_ids: &[VarId],
    skipped_expr: Option<*const PseudoExpr>,
) -> bool {
    fn walk(
        expr: &PseudoExpr,
        name: &str,
        own_id: VarId,
        allowed_other_ids: &[VarId],
        skipped_expr: Option<*const PseudoExpr>,
        found: &mut bool,
    ) {
        if *found {
            return;
        }
        if skipped_expr.is_some_and(|skipped| std::ptr::addr_eq(expr, skipped)) {
            return;
        }
        let check_binder = |b_name: &str, b_id: VarId, found: &mut bool| {
            if b_name == name && b_id != own_id && !allowed_other_ids.contains(&b_id) {
                *found = true;
            }
        };
        match expr {
            PseudoExpr::Var { .. } => {}
            PseudoExpr::Lambda { params, body } => {
                for p in params {
                    check_binder(p.as_str(), p.var_id(), found);
                }
                walk(body, name, own_id, allowed_other_ids, skipped_expr, found);
            }
            PseudoExpr::RecFn {
                name: rn,
                params,
                body,
            } => {
                check_binder(rn.as_str(), rn.var_id(), found);
                for p in params {
                    check_binder(p.as_str(), p.var_id(), found);
                }
                walk(body, name, own_id, allowed_other_ids, skipped_expr, found);
            }
            PseudoExpr::Let {
                name: ln,
                id,
                value,
                body,
            } => {
                // Use the stored id, compat placeholders included, so a
                // Let's own id equals itself in the `b_id != own_id`
                // check. `.get()` maps compat ids to `None`, so
                // `.get().unwrap_or_else(...)` would mint a fresh one per
                // call and trip the shared-name check on the Let itself.
                check_binder(
                    ln.as_str(),
                    id.unwrap_or_else(VarId::fresh_compat_placeholder),
                    found,
                );
                walk(value, name, own_id, allowed_other_ids, skipped_expr, found);
                walk(body, name, own_id, allowed_other_ids, skipped_expr, found);
            }
            PseudoExpr::Apply { function, args } => {
                walk(
                    function,
                    name,
                    own_id,
                    allowed_other_ids,
                    skipped_expr,
                    found,
                );
                for a in args {
                    walk(a, name, own_id, allowed_other_ids, skipped_expr, found);
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                walk(
                    condition,
                    name,
                    own_id,
                    allowed_other_ids,
                    skipped_expr,
                    found,
                );
                walk(
                    then_branch,
                    name,
                    own_id,
                    allowed_other_ids,
                    skipped_expr,
                    found,
                );
                walk(
                    else_branch,
                    name,
                    own_id,
                    allowed_other_ids,
                    skipped_expr,
                    found,
                );
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                walk(
                    subject,
                    name,
                    own_id,
                    allowed_other_ids,
                    skipped_expr,
                    found,
                );
                if let Some(sn) = subject_name {
                    check_binder(sn.as_str(), sn.var_id(), found);
                }
                for c in clauses {
                    match &c.pattern {
                        WhenPattern::Var(b) => check_binder(b.as_str(), b.var_id(), found),
                        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                            for b in fields {
                                check_binder(b.as_str(), b.var_id(), found);
                            }
                        }
                        WhenPattern::List { elements, tail } => {
                            for b in elements {
                                check_binder(b.as_str(), b.var_id(), found);
                            }
                            if let Some(t) = tail {
                                check_binder(t.as_str(), t.var_id(), found);
                            }
                        }
                        WhenPattern::Pair(a, b) => {
                            check_binder(a.as_str(), a.var_id(), found);
                            check_binder(b.as_str(), b.var_id(), found);
                        }
                        _ => {}
                    }
                    if let Some(g) = &c.guard {
                        walk(g, name, own_id, allowed_other_ids, skipped_expr, found);
                    }
                    walk(
                        &c.body,
                        name,
                        own_id,
                        allowed_other_ids,
                        skipped_expr,
                        found,
                    );
                }
            }
            PseudoExpr::BinOp { left, right, .. } => {
                walk(left, name, own_id, allowed_other_ids, skipped_expr, found);
                walk(right, name, own_id, allowed_other_ids, skipped_expr, found);
            }
            PseudoExpr::UnOp { operand, .. } => walk(
                operand,
                name,
                own_id,
                allowed_other_ids,
                skipped_expr,
                found,
            ),
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => {
                walk(inner, name, own_id, allowed_other_ids, skipped_expr, found)
            }
            PseudoExpr::Trace { message, value } => {
                walk(
                    message,
                    name,
                    own_id,
                    allowed_other_ids,
                    skipped_expr,
                    found,
                );
                walk(value, name, own_id, allowed_other_ids, skipped_expr, found);
            }
            PseudoExpr::List { elements, tail } => {
                for e in elements {
                    walk(e, name, own_id, allowed_other_ids, skipped_expr, found);
                }
                if let Some(t) = tail {
                    walk(t, name, own_id, allowed_other_ids, skipped_expr, found);
                }
            }
            PseudoExpr::Tuple(items) => {
                for i in items {
                    walk(i, name, own_id, allowed_other_ids, skipped_expr, found);
                }
            }
            PseudoExpr::Pair(a, b) => {
                walk(a, name, own_id, allowed_other_ids, skipped_expr, found);
                walk(b, name, own_id, allowed_other_ids, skipped_expr, found);
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields {
                    walk(f, name, own_id, allowed_other_ids, skipped_expr, found);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => {
                walk(record, name, own_id, allowed_other_ids, skipped_expr, found)
            }
            PseudoExpr::IndexAccess { collection, .. } => walk(
                collection,
                name,
                own_id,
                allowed_other_ids,
                skipped_expr,
                found,
            ),
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args {
                    walk(a, name, own_id, allowed_other_ids, skipped_expr, found);
                }
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }

    let mut found = false;
    walk(
        expr,
        name,
        own_id,
        allowed_other_ids,
        skipped_expr,
        &mut found,
    );
    found
}
