//! Gathering the raw material a rename decides on: which ids are
//! consistently referenced, which names are already taken, and the
//! per-shape display-name HINTS (`check_temp`, `arithmetic_temp`,
//! `option_wrapper_temp`, `extractor_temp`, `field_payload_temp`,
//! `when`-pattern binders, `data_list_temp`).
//!
//! Collect only — nothing here rewrites a tree.

use super::*;

/// Record the id of every Var reference whose nearest in-scope
/// binder by name carries that same id — the refs that are
/// "properly bound" by name, and the only ones the name-keyed
/// fallback in `MapRenamer` may touch.
pub(super) fn collect_consistent_ref_ids(expr: &PseudoExpr) -> HashSet<VarId> {
    /// One pending step of the scoped, read-only walk below.
    enum Step<'a> {
        Visit(&'a PseudoExpr),
        /// A `let`'s bound name comes into scope BETWEEN its value (walked
        /// already, outside any new frame) and its body.
        EnterLetBody {
            name: &'a str,
            id: Option<VarId>,
            body: &'a PseudoExpr,
        },
        EnterLambdaBody {
            params: &'a [Binder],
            body: &'a PseudoExpr,
        },
        EnterRecFnBody {
            name: &'a Binder,
            params: &'a [Binder],
            body: &'a PseudoExpr,
        },
        /// The `when` subject name's scope wraps every clause; opened once
        /// subject is fully walked.
        PushSubjectScope(&'a Binder),
        /// One clause's own (nested) pattern scope, closed by the `PopScope`
        /// pushed right after it.
        EnterClause(&'a WhenClause),
        PopScope,
    }

    fn bind(scopes: &mut [HashMap<String, VarId>], name: &str, id: VarId) {
        if let Some(top) = scopes.last_mut() {
            top.insert(name.to_string(), id);
        }
    }
    fn lookup(scopes: &[HashMap<String, VarId>], name: &str) -> Option<VarId> {
        for frame in scopes.iter().rev() {
            if let Some(&id) = frame.get(name) {
                return Some(id);
            }
        }
        None
    }

    let mut scopes: Vec<HashMap<String, VarId>> = vec![HashMap::new()];
    let mut consistent: HashSet<VarId> = HashSet::new();
    let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];

    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(expr) => match expr {
                PseudoExpr::Var { name, id } => {
                    if let Some(vid) = *id
                        && lookup(&scopes, name) == Some(vid)
                    {
                        consistent.insert(vid);
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(Step::EnterLambdaBody { params, body });
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(Step::EnterRecFnBody { name, params, body });
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(Step::EnterLetBody {
                        name,
                        id: *id,
                        body,
                    });
                    steps.push(Step::Visit(value));
                }
                PseudoExpr::Apply { function, args } => {
                    for a in args.iter().rev() {
                        steps.push(Step::Visit(a));
                    }
                    steps.push(Step::Visit(function));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(Step::Visit(else_branch));
                    steps.push(Step::Visit(then_branch));
                    steps.push(Step::Visit(condition));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let pushed_subject = subject_name.is_some();
                    if pushed_subject {
                        steps.push(Step::PopScope);
                    }
                    for c in clauses.iter().rev() {
                        steps.push(Step::PopScope);
                        steps.push(Step::EnterClause(c));
                    }
                    if let Some(subject_name) = subject_name.as_ref() {
                        steps.push(Step::PushSubjectScope(subject_name));
                    }
                    steps.push(Step::Visit(subject));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail.as_deref() {
                        steps.push(Step::Visit(t));
                    }
                    for e in elements.iter().rev() {
                        steps.push(Step::Visit(e));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for i in items.iter().rev() {
                        steps.push(Step::Visit(i));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    steps.push(Step::Visit(b));
                    steps.push(Step::Visit(a));
                }
                PseudoExpr::Constr { fields, .. } => {
                    for f in fields.iter().rev() {
                        steps.push(Step::Visit(f));
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => steps.push(Step::Visit(record)),
                PseudoExpr::IndexAccess { collection, .. } => steps.push(Step::Visit(collection)),
                PseudoExpr::BinOp { left, right, .. } => {
                    steps.push(Step::Visit(right));
                    steps.push(Step::Visit(left));
                }
                PseudoExpr::UnOp { operand, .. } => steps.push(Step::Visit(operand)),
                PseudoExpr::BuiltinCall { args, .. } => {
                    for a in args.iter().rev() {
                        steps.push(Step::Visit(a));
                    }
                }
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                    steps.push(Step::Visit(inner))
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(Step::Visit(value));
                    steps.push(Step::Visit(message));
                }
                _ => {}
            },
            Step::EnterLetBody { name, id, body } => {
                scopes.push(HashMap::new());
                if let Some(vid) = id {
                    bind(&mut scopes, name, vid);
                }
                steps.push(Step::PopScope);
                steps.push(Step::Visit(body));
            }
            Step::EnterLambdaBody { params, body } => {
                scopes.push(HashMap::new());
                for p in params {
                    bind(&mut scopes, p.as_str(), p.var_id());
                }
                steps.push(Step::PopScope);
                steps.push(Step::Visit(body));
            }
            Step::EnterRecFnBody { name, params, body } => {
                scopes.push(HashMap::new());
                bind(&mut scopes, name.as_str(), name.var_id());
                for p in params {
                    bind(&mut scopes, p.as_str(), p.var_id());
                }
                steps.push(Step::PopScope);
                steps.push(Step::Visit(body));
            }
            Step::PushSubjectScope(subject_name) => {
                scopes.push(HashMap::new());
                bind(&mut scopes, subject_name.as_str(), subject_name.var_id());
            }
            Step::EnterClause(c) => {
                scopes.push(HashMap::new());
                match &c.pattern {
                    WhenPattern::Var(b) => bind(&mut scopes, b.as_str(), b.var_id()),
                    WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                        for b in fields {
                            bind(&mut scopes, b.as_str(), b.var_id());
                        }
                    }
                    WhenPattern::List { elements, tail } => {
                        for b in elements {
                            bind(&mut scopes, b.as_str(), b.var_id());
                        }
                        if let Some(t) = tail {
                            bind(&mut scopes, t.as_str(), t.var_id());
                        }
                    }
                    WhenPattern::Pair(a, b) => {
                        bind(&mut scopes, a.as_str(), a.var_id());
                        bind(&mut scopes, b.as_str(), b.var_id());
                    }
                    _ => {}
                }
                steps.push(Step::Visit(&c.body));
                if let Some(g) = &c.guard {
                    steps.push(Step::Visit(g));
                }
            }
            Step::PopScope => {
                scopes.pop();
            }
        }
    }

    consistent
}

/// Collect all variable/binding names in the AST to avoid collisions.
pub(super) fn collect_all_names(expr: &PseudoExpr, names: &mut HashSet<String>) {
    struct CollectAllNamesVisitor<'a> {
        names: &'a mut HashSet<String>,
    }

    impl ExprVisitor for CollectAllNamesVisitor<'_> {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            self.names.insert(name.to_string());
        }

        fn visit_let_pre(&mut self, name: &str) {
            self.names.insert(name.to_string());
        }

        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for param in params {
                self.names.insert(param.to_string());
            }
        }

        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            self.names.insert(name.to_string());
            for param in params {
                self.names.insert(param.to_string());
            }
        }
    }

    CollectAllNamesVisitor { names }.walk(expr);
}

#[cfg(test)]
pub(super) fn collect_all_names_sorted(expr: &PseudoExpr) -> Vec<String> {
    let mut names = HashSet::new();
    collect_all_names(expr, &mut names);
    let mut names: Vec<String> = names.into_iter().collect();
    names.sort();
    names
}

/// Generate a unique name from a hint, avoiding collisions with existing names.
pub(super) fn unique_name(hint: &str, used: &mut HashSet<String>) -> String {
    if !used.contains(hint) {
        used.insert(hint.to_string());
        return hint.to_string();
    }
    let mut suffix = 2;
    loop {
        let candidate = format!("{}_{}", hint, suffix);
        if !used.contains(&candidate) {
            used.insert(candidate.clone());
            return candidate;
        }
        suffix += 1;
    }
}

pub(super) fn unique_param_name(hint: &str, used_in_signature: &mut HashSet<String>) -> String {
    if used_in_signature.insert(hint.to_string()) {
        return hint.to_string();
    }

    let mut suffix = 2;
    loop {
        let candidate = format!("{}_{}", hint, suffix);
        if used_in_signature.insert(candidate.clone()) {
            return candidate;
        }
        suffix += 1;
    }
}

pub(crate) fn collect_check_temp_display_name_hints(expr: &PseudoExpr) -> HashMap<VarId, String> {
    let consistent_ref_ids = collect_consistent_ref_ids(expr);
    let mut used_names = HashSet::new();
    collect_all_names(expr, &mut used_names);

    struct CheckTempHintVisitor<'a> {
        consistent_ref_ids: &'a HashSet<VarId>,
        hints: HashMap<VarId, String>,
        used_names: &'a mut HashSet<String>,
    }

    impl ExprVisitor for CheckTempHintVisitor<'_> {
        fn visit_let(
            &mut self,
            name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            body: &PseudoExpr,
        ) {
            let Some(vid) = *id else { return };
            if !(is_temporary_helper_name(name) || name == "check" || name.starts_with("check_"))
                || var_is_referenced_id_aware(body, vid, name)
            {
                return;
            }

            let check_hint = analyze_unit_check_temp_binding_with_consistency(
                value,
                Some(self.consistent_ref_ids),
            );
            if check_hint.is_none() && name != "check" && !name.starts_with("check_") {
                return;
            }

            let hint = check_hint.unwrap_or_else(|| "check".to_string());
            let unique = unique_name(&hint, self.used_names);
            self.hints.insert(vid, unique);
        }
    }

    let mut visitor = CheckTempHintVisitor {
        consistent_ref_ids: &consistent_ref_ids,
        hints: HashMap::new(),
        used_names: &mut used_names,
    };
    visitor.walk(expr);
    visitor.hints
}

pub(crate) fn collect_arithmetic_temp_display_name_hints(
    expr: &PseudoExpr,
) -> HashMap<VarId, String> {
    let mut used_names = HashSet::new();
    collect_all_names(expr, &mut used_names);

    struct ArithmeticTempHintVisitor<'a> {
        hints: HashMap<VarId, String>,
        used_names: &'a mut HashSet<String>,
    }

    impl ExprVisitor for ArithmeticTempHintVisitor<'_> {
        fn visit_let(
            &mut self,
            name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            if !is_temporary_helper_name(name) {
                return;
            }
            let Some(hint) = analyze_arithmetic_temp_binding(value) else {
                return;
            };
            let Some(vid) = *id else { return };

            let unique = unique_name(&hint, self.used_names);
            self.hints.insert(vid, unique);
        }
    }

    let mut visitor = ArithmeticTempHintVisitor {
        hints: HashMap::new(),
        used_names: &mut used_names,
    };
    visitor.walk(expr);
    visitor.hints
}

pub(crate) fn collect_option_wrapper_temp_display_name_hints(
    expr: &PseudoExpr,
) -> HashMap<VarId, String> {
    let mut used_names = HashSet::new();
    collect_all_names(expr, &mut used_names);

    struct OptionWrapperTempHintVisitor<'a> {
        hints: HashMap<VarId, String>,
        used_names: &'a mut HashSet<String>,
    }

    impl ExprVisitor for OptionWrapperTempHintVisitor<'_> {
        fn visit_let(
            &mut self,
            name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            if !is_temporary_helper_name(name) {
                return;
            }
            let Some(hint) = analyze_option_wrapper_temp_binding(value) else {
                return;
            };
            let Some(vid) = *id else { return };

            let unique = unique_name(&hint, self.used_names);
            self.hints.insert(vid, unique);
        }
    }

    let mut visitor = OptionWrapperTempHintVisitor {
        hints: HashMap::new(),
        used_names: &mut used_names,
    };
    visitor.walk(expr);
    visitor.hints
}

pub(crate) fn collect_extractor_temp_display_name_hints(
    expr: &PseudoExpr,
) -> HashMap<VarId, String> {
    let mut used_names = HashSet::new();
    collect_all_names(expr, &mut used_names);

    struct ExtractorTempHintVisitor<'a> {
        hints: HashMap<VarId, String>,
        used_names: &'a mut HashSet<String>,
    }

    impl ExprVisitor for ExtractorTempHintVisitor<'_> {
        fn visit_let(
            &mut self,
            name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            if !is_temporary_helper_name(name) {
                return;
            }
            let Some(hint) = analyze_extractor_temp_binding(value) else {
                return;
            };
            let Some(vid) = *id else { return };

            let unique = unique_name(&hint, self.used_names);
            self.hints.insert(vid, unique);
        }
    }

    let mut visitor = ExtractorTempHintVisitor {
        hints: HashMap::new(),
        used_names: &mut used_names,
    };
    visitor.walk(expr);
    visitor.hints
}

pub(crate) fn collect_field_payload_temp_display_name_hints(
    expr: &PseudoExpr,
) -> HashMap<VarId, String> {
    let consistent_ref_ids = collect_consistent_ref_ids(expr);
    let mut used_names = HashSet::new();
    collect_all_names(expr, &mut used_names);

    struct FieldPayloadTempHintVisitor<'a> {
        consistent_ref_ids: &'a HashSet<VarId>,
        hints: HashMap<VarId, String>,
        used_names: &'a mut HashSet<String>,
    }

    impl ExprVisitor for FieldPayloadTempHintVisitor<'_> {
        fn visit_let(
            &mut self,
            name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            if !is_temporary_helper_name(name) {
                return;
            }
            let Some(hint) = analyze_field_alias_temp_binding(value, Some(self.consistent_ref_ids))
                .or_else(|| analyze_constructor_payload_alias_temp_binding(value))
            else {
                return;
            };
            let Some(vid) = *id else { return };

            let unique = unique_name(&hint, self.used_names);
            self.hints.insert(vid, unique);
        }
    }

    let mut visitor = FieldPayloadTempHintVisitor {
        consistent_ref_ids: &consistent_ref_ids,
        hints: HashMap::new(),
        used_names: &mut used_names,
    };
    visitor.walk(expr);
    visitor.hints
}

pub(crate) fn collect_when_pattern_binder_display_name_hints(
    expr: &PseudoExpr,
) -> HashMap<VarId, String> {
    let mut used_names = HashSet::new();
    collect_all_names(expr, &mut used_names);

    struct WhenPatternHintVisitor<'a> {
        hints: HashMap<VarId, String>,
        used_names: &'a mut HashSet<String>,
    }

    impl ExprVisitor for WhenPatternHintVisitor<'_> {
        fn visit_when(
            &mut self,
            subject: &PseudoExpr,
            _subject_name: Option<&Binder>,
            clauses: &[WhenClause],
        ) {
            for clause in clauses {
                for (binder, hint) in analyze_when_clause_pattern_hints(subject, clause) {
                    if !is_pattern_hint_candidate_name(binder.as_str()) {
                        continue;
                    }
                    let new_name = if let Some(base) = scoped_reusable_hint(&hint) {
                        if clause.guard.as_ref().is_none_or(|guard| {
                            !expr_references_other_var_named(guard, &base, binder.id)
                        }) && !expr_references_other_var_named(&clause.body, &base, binder.id)
                        {
                            base
                        } else {
                            unique_name(&hint, self.used_names)
                        }
                    } else {
                        unique_name(&hint, self.used_names)
                    };
                    if binder.as_str() != new_name {
                        self.hints.insert(binder.id, new_name);
                    }
                }
            }
        }
    }

    let mut visitor = WhenPatternHintVisitor {
        hints: HashMap::new(),
        used_names: &mut used_names,
    };
    visitor.walk(expr);
    visitor.hints
}

pub(crate) fn collect_data_list_temp_display_name_hints(
    expr: &PseudoExpr,
) -> HashMap<VarId, String> {
    let mut used_names = HashSet::new();
    collect_all_names(expr, &mut used_names);

    struct DataListTempHintVisitor<'a> {
        hints: HashMap<VarId, String>,
        used_names: &'a mut HashSet<String>,
    }

    impl ExprVisitor for DataListTempHintVisitor<'_> {
        fn visit_let(
            &mut self,
            name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            if !is_temporary_helper_name(name) {
                return;
            }
            let Some(hint) = analyze_data_list_temp_binding(value) else {
                return;
            };
            let Some(vid) = *id else { return };

            let unique = unique_name(&hint, self.used_names);
            self.hints.insert(vid, unique);
        }
    }

    let mut visitor = DataListTempHintVisitor {
        hints: HashMap::new(),
        used_names: &mut used_names,
    };
    visitor.walk(expr);
    visitor.hints
}
