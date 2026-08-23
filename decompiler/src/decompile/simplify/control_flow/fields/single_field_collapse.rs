use std::collections::{BTreeSet, HashMap, HashSet};

use crate::decompile::simplify::Simplifier;
use crate::decompile::simplify::postprocess::{
    ContextType, SumTypeId, context_field_at, sum_type_constructor_fields,
};
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

impl Simplifier {
    pub(super) fn collapse_exact_single_field_subject_fields_clause(
        &mut self,
        clause: &WhenClause,
        subject_name: &str,
        subject_id: Option<VarId>,
    ) -> Option<WhenClause> {
        let WhenPattern::Constructor {
            type_hint,
            tag,
            fields,
            shape,
        } = &clause.pattern
        else {
            return None;
        };
        let existing_field_binder = match fields.as_slice() {
            [] => None,
            [field] => Some(field.clone()),
            _ => return None,
        };
        if clause.guard.is_some() {
            return None;
        }

        let PseudoExpr::When {
            subject: outer_subject,
            clauses: outer_clauses,
            ..
        } = &clause.body
        else {
            return None;
        };
        if !Self::direct_subject_fields_matches(outer_subject, subject_name, subject_id) {
            return None;
        }
        if outer_clauses.len() != 2 {
            return None;
        }

        let mut fallback = None;
        let mut head_binder = None;
        let mut tail_binder = None;
        let mut nonempty_body = None;

        for outer_clause in outer_clauses {
            if outer_clause.guard.is_some() {
                return None;
            }
            match &outer_clause.pattern {
                WhenPattern::List { elements, tail } if elements.is_empty() && tail.is_none() => {
                    fallback = Some(outer_clause.body.clone());
                }
                WhenPattern::List { elements, tail } if elements.len() == 1 => {
                    head_binder = Some(elements[0].clone());
                    tail_binder = tail.clone();
                    nonempty_body = Some(outer_clause.body.clone());
                }
                _ => return None,
            }
        }

        let fallback = fallback?;
        let nonempty_body = nonempty_body?;
        let outer_head_binder = head_binder?;

        let PseudoExpr::When {
            subject: inner_subject,
            clauses: inner_clauses,
            ..
        } = nonempty_body
        else {
            return None;
        };
        let lifted_inner_subject_binder = match inner_subject.as_ref() {
            PseudoExpr::Var { name, id, .. }
                if name != outer_head_binder.as_str()
                    && tail_binder
                        .as_ref()
                        .is_none_or(|tail| name != tail.as_str()) =>
            {
                let binder = match id.get() {
                    Some(id) => Binder::new(name.clone(), id),
                    None => self.fresh_synthetic_binder(name),
                };
                Some(binder)
            }
            _ => None,
        };
        let mut used_names = HashSet::new();
        Self::collect_var_names(&clause.body, &mut used_names);
        used_names.insert(subject_name.to_string());
        // Schema field name (`out_ref`, `address`, …) for the single
        // field when the outer subject's type resolves to a known
        // sum/record; `field_0` otherwise.
        let cardano_field_name = self
            .single_field_cardano_name(subject_name, subject_id, *tag)
            .filter(|s| !used_names.contains(s));
        let cardano_is_some = cardano_field_name.is_some();
        let pick_field_name =
            |used_names: &mut HashSet<String>, cardano: Option<String>| match cardano {
                Some(n) => {
                    used_names.insert(n.clone());
                    n
                }
                None => "field_0".to_string(),
            };
        let mut field_binder = existing_field_binder
            .or(lifted_inner_subject_binder)
            .unwrap_or_else(|| {
                if outer_head_binder == "_" {
                    let base = pick_field_name(&mut used_names, cardano_field_name.clone());
                    let field_name = self.fresh_name_for_scope(&mut used_names, base);
                    let binder = self.fresh_synthetic_binder(&field_name);
                    if cardano_is_some {
                        self.var_kinds.kind_annotations.insert(
                            binder.id,
                            VarKind::CardanoContext {
                                context_type: field_name.clone(),
                            },
                        );
                    }
                    binder
                } else {
                    outer_head_binder.clone()
                }
            });
        if field_binder == "_" {
            let base = pick_field_name(&mut used_names, cardano_field_name);
            let field_name = self.fresh_name_for_scope(&mut used_names, base);
            field_binder = self.fresh_synthetic_binder(&field_name);
            if cardano_is_some {
                self.var_kinds.kind_annotations.insert(
                    field_binder.id,
                    VarKind::CardanoContext {
                        context_type: field_name.clone(),
                    },
                );
            }
        }
        let inner_subject_matches = matches!(
            inner_subject.as_ref(),
            PseudoExpr::IndexAccess { index: 0, .. }
                if Self::direct_subject_fields_index_access_matches(
                    inner_subject.as_ref(),
                    subject_name,
                    subject_id,
                )
        ) || matches!(
            inner_subject.as_ref(),
            PseudoExpr::Var { name, id, .. }
                if Self::ref_matches_var_id(
                    name,
                    *id,
                    field_binder.as_str(),
                    field_binder.id.get(),
                ) || Self::ref_matches_var_id(
                    name,
                    *id,
                    outer_head_binder.as_str(),
                    outer_head_binder.id.get(),
                )
        );
        if !inner_subject_matches {
            return None;
        }

        let transformed_inner_clauses =
            inner_clauses
                .into_iter()
                .map(|inner_clause| {
                    if inner_clause.guard.is_some() {
                        return None;
                    }

                    let body = if inner_clause.body.structural_eq(&fallback) {
                        inner_clause.body
                    } else if let Some(tail_binder) = &tail_binder {
                        Self::collapse_tail_empty_fallback_gate(
                            inner_clause.body,
                            tail_binder,
                            &fallback,
                        )?
                    } else {
                        inner_clause.body
                    };

                    let replacement_names = std::slice::from_ref(&field_binder.name);
                    if outer_head_binder != field_binder
                        && (inner_clause.guard.as_ref().is_some_and(|guard| {
                            Self::has_binding_for_any(guard, replacement_names)
                        }) || Self::has_binding_for_any(&body, replacement_names))
                    {
                        return None;
                    }

                    let guard = if outer_head_binder != field_binder {
                        inner_clause.guard.map(|guard| {
                            Self::substitute_var_for_var(
                                &guard,
                                outer_head_binder.as_str(),
                                outer_head_binder.var_id().get(),
                                field_binder.as_str(),
                                field_binder.var_id(),
                            )
                        })
                    } else {
                        inner_clause.guard
                    };

                    let body = if outer_head_binder != field_binder {
                        Self::substitute_var_for_var(
                            &body,
                            outer_head_binder.as_str(),
                            outer_head_binder.var_id().get(),
                            field_binder.as_str(),
                            field_binder.var_id(),
                        )
                    } else {
                        body
                    };

                    Some(WhenClause {
                        pattern: inner_clause.pattern,
                        guard,
                        body,
                    })
                })
                .collect::<Option<Vec<_>>>()?;

        let type_hint = type_hint.clone();
        let fields = vec![field_binder.clone()];
        let shape = ConstructorShape::from_name_and_tag(shape.pretty_name(), *tag, fields.len());
        let collapsed_body = self.simplify_when(
            PseudoExpr::Var {
                name: field_binder.to_string(),
                id: Some(field_binder.id),
            },
            Some(field_binder),
            transformed_inner_clauses,
        );
        if Self::contains_free_generated_payload_alias(
            &collapsed_body,
            &self.var_kinds.kind_annotations,
            self.use_varkind_recovery,
        ) {
            return None;
        }

        Some(WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint,
                tag: *tag,
                fields,
                shape,
            },
            guard: None,
            body: collapsed_body,
        })
    }

    /// Resolve the schema field name for the single field of a
    /// `Constr<tag>(field_0)` clause whose outer subject has a known
    /// record/sum type. `None` otherwise, so callers use `field_0`.
    fn single_field_cardano_name(
        &self,
        subject_name: &str,
        subject_id: Option<VarId>,
        tag: usize,
    ) -> Option<String> {
        let version = self.script_version?;
        let ctx_name: &str = subject_id
            .get()
            .and_then(|id| self.context.context_field_names_by_id.get(&id))
            .map(String::as_str)
            .or_else(|| {
                self.context
                    .context_field_names
                    .get(subject_name)
                    .map(String::as_str)
            })
            .unwrap_or(subject_name);
        // Sum-type case: `tag` picks the constructor; only a
        // single-field constructor qualifies, e.g.
        // `Purpose::Spending(out_ref)`.
        if let Some(sum_id) = SumTypeId::from_display_name(ctx_name)
            && let Some(fields) = sum_type_constructor_fields(sum_id, tag, version)
            && let Some((field, _)) = fields.first()
            && fields.len() == 1
        {
            return Some(field.display_name().to_string());
        }
        // Record case: records are tag-0 / arity-N, so accept only a
        // schema arity of 1 — index 0 of a multi-field record would
        // mis-tag its first slot.
        if tag == 0
            && let Some(ctx_type) = ContextType::from_display_name(ctx_name)
        {
            // Arity 1 iff index 1 is `None` and index 0 is `Some`.
            if context_field_at(ctx_type, 1, version).is_none()
                && let Some(field) = context_field_at(ctx_type, 0, version)
            {
                return Some(field.display_name().to_string());
            }
        }
        None
    }

    fn contains_free_generated_payload_alias(
        expr: &PseudoExpr,
        kind_annotations: &HashMap<VarId, VarKind>,
        use_varkind_recovery: bool,
    ) -> bool {
        fn is_generated_payload_alias(name: &str) -> bool {
            name.starts_with("item_") || name.starts_with("fields_")
        }

        // Authoritative payload-shape kinds (`ConstrPayload |
        // FieldIndexAlias | Synthetic`) match immediately; everything
        // else falls back to the legacy name predicate, so the result
        // is a strict superset of that predicate.
        fn is_orphan_payload_ref(
            name: &str,
            id: Option<VarId>,
            kind_annotations: &HashMap<VarId, VarKind>,
            use_varkind_recovery: bool,
        ) -> bool {
            let id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
            if use_varkind_recovery {
                let typed_match = kind_annotations.get(&id).is_some_and(|kind| {
                    matches!(
                        kind,
                        VarKind::ConstrPayload { .. }
                            | VarKind::FieldIndexAlias { .. }
                            | VarKind::Synthetic
                    )
                });
                let legacy_match = is_generated_payload_alias(name);

                if typed_match && !legacy_match && crate::debug_env::varkind_recovery() {
                    let kind = kind_annotations
                        .get(&id)
                        .map(|k| format!("{:?}", k))
                        .unwrap_or_else(|| "<missing>".to_string());
                    eprintln!(
                        "[varkind-recovery delta single-field-collapse] typed-only orphan: id={} name={:?} kind={}",
                        id, name, kind,
                    );
                }

                return typed_match || legacy_match;
            }
            is_generated_payload_alias(name)
        }

        // One pending step of the scoped free-variable walk below. `bound` is
        // a `Vec`, not a set, so a scope's binders are undone by truncating
        // back to the length recorded before they were pushed — duplicates
        // (shadowing) are harmless, unlike the add/remove tracking a
        // `HashSet`-backed scope would need.
        enum Step<'a> {
            Visit(&'a PseudoExpr),
            /// A `let`'s VALUE is walked outside the binding; only once it's
            /// done does the name come into scope for the body.
            OpenLetBody {
                name: &'a str,
                body: &'a PseudoExpr,
            },
            /// A `when` clause: subject_name + pattern binders are in scope
            /// for its guard and body only.
            OpenClause {
                subject_name: Option<&'a str>,
                pattern: &'a WhenPattern,
                guard: Option<&'a PseudoExpr>,
                body: &'a PseudoExpr,
            },
            /// Drop everything a scope pushed, back to this length.
            Truncate(usize),
        }

        fn go(
            expr: &PseudoExpr,
            bound: &mut Vec<String>,
            free: &mut BTreeSet<String>,
            kind_annotations: &HashMap<VarId, VarKind>,
            use_varkind_recovery: bool,
        ) {
            let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];
            while let Some(step) = steps.pop() {
                match step {
                    Step::Visit(expr) => match expr {
                        PseudoExpr::Var { name, id, .. } => {
                            if is_orphan_payload_ref(
                                name,
                                *id,
                                kind_annotations,
                                use_varkind_recovery,
                            ) && !bound.iter().rev().any(|bound_name| bound_name == name)
                            {
                                free.insert(name.clone());
                            }
                        }
                        PseudoExpr::Lambda { params, body } => {
                            let base = bound.len();
                            bound.extend(params.iter().map(|param| param.name.clone()));
                            steps.push(Step::Truncate(base));
                            steps.push(Step::Visit(body));
                        }
                        PseudoExpr::RecFn { name, params, body } => {
                            let base = bound.len();
                            bound.push(name.name.clone());
                            bound.extend(params.iter().map(|param| param.name.clone()));
                            steps.push(Step::Truncate(base));
                            steps.push(Step::Visit(body));
                        }
                        PseudoExpr::Let {
                            name, value, body, ..
                        } => {
                            steps.push(Step::OpenLetBody { name, body });
                            steps.push(Step::Visit(value));
                        }
                        PseudoExpr::Apply { function, args } => {
                            for arg in args.iter().rev() {
                                steps.push(Step::Visit(arg));
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
                            for clause in clauses.iter().rev() {
                                steps.push(Step::OpenClause {
                                    subject_name: subject_name.as_ref().map(|b| b.name.as_str()),
                                    pattern: &clause.pattern,
                                    guard: clause.guard.as_ref(),
                                    body: &clause.body,
                                });
                            }
                            steps.push(Step::Visit(subject));
                        }
                        PseudoExpr::List { elements, tail } => {
                            if let Some(tail) = tail {
                                steps.push(Step::Visit(tail));
                            }
                            for element in elements.iter().rev() {
                                steps.push(Step::Visit(element));
                            }
                        }
                        PseudoExpr::Tuple(elements) => {
                            for element in elements.iter().rev() {
                                steps.push(Step::Visit(element));
                            }
                        }
                        PseudoExpr::Pair(left, right) | PseudoExpr::BinOp { left, right, .. } => {
                            steps.push(Step::Visit(right));
                            steps.push(Step::Visit(left));
                        }
                        PseudoExpr::UnOp { operand, .. }
                        | PseudoExpr::Delay(operand)
                        | PseudoExpr::Force(operand)
                        | PseudoExpr::FieldAccess {
                            record: operand, ..
                        }
                        | PseudoExpr::IndexAccess {
                            collection: operand,
                            ..
                        } => steps.push(Step::Visit(operand)),
                        PseudoExpr::BuiltinCall { args, .. }
                        | PseudoExpr::Constr { fields: args, .. } => {
                            for arg in args.iter().rev() {
                                steps.push(Step::Visit(arg));
                            }
                        }
                        PseudoExpr::Trace { message, value } => {
                            steps.push(Step::Visit(value));
                            steps.push(Step::Visit(message));
                        }
                        PseudoExpr::Int(_)
                        | PseudoExpr::ByteArray(_)
                        | PseudoExpr::String(_)
                        | PseudoExpr::Bool(_)
                        | PseudoExpr::Unit
                        | PseudoExpr::Data(_)
                        | PseudoExpr::Error { .. }
                        | PseudoExpr::Raw { .. }
                        | PseudoExpr::HelperSymbol(_) => {}
                    },
                    Step::OpenLetBody { name, body } => {
                        let base = bound.len();
                        bound.push(name.to_string());
                        steps.push(Step::Truncate(base));
                        steps.push(Step::Visit(body));
                    }
                    Step::OpenClause {
                        subject_name,
                        pattern,
                        guard,
                        body,
                    } => {
                        let base = bound.len();
                        if let Some(subject_name) = subject_name {
                            bound.push(subject_name.to_string());
                        }
                        bound.extend(
                            Simplifier::pattern_bound_vars(pattern)
                                .into_iter()
                                .filter(|name| name != "_"),
                        );
                        steps.push(Step::Truncate(base));
                        steps.push(Step::Visit(body));
                        if let Some(guard) = guard {
                            steps.push(Step::Visit(guard));
                        }
                    }
                    Step::Truncate(base) => bound.truncate(base),
                }
            }
        }

        let mut free = BTreeSet::new();
        go(
            expr,
            &mut Vec::new(),
            &mut free,
            kind_annotations,
            use_varkind_recovery,
        );
        !free.is_empty()
    }

    fn collapse_tail_empty_fallback_gate(
        expr: PseudoExpr,
        tail_binder: &Binder,
        fallback: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        if matches!(fallback, PseudoExpr::Bool(false))
            && matches!(
                &expr,
                PseudoExpr::Apply { function, args }
                    if args.len() == 1
                        && matches!(
                            function.as_ref(),
                            PseudoExpr::Var { name, .. } if name == "List.is_empty"
                        )
                        && matches!(
                            args.first(),
                            Some(PseudoExpr::Var { name, .. }) if name == tail_binder.as_str()
                        )
            )
        {
            return Some(expr);
        }

        let PseudoExpr::When {
            subject, clauses, ..
        } = expr
        else {
            return None;
        };
        if !matches!(
            subject.as_ref(),
            PseudoExpr::Var { name, .. } if name == tail_binder.as_str()
        ) {
            return None;
        }
        if clauses.len() != 2 {
            return None;
        }

        let mut success = None;
        let mut wildcard_fallback = false;
        for clause in clauses {
            if clause.guard.is_some() {
                return None;
            }
            match clause.pattern {
                WhenPattern::List { elements, tail } if elements.is_empty() && tail.is_none() => {
                    success = Some(clause.body);
                }
                WhenPattern::Wildcard if clause.body.structural_eq(fallback) => {
                    wildcard_fallback = true;
                }
                _ => return None,
            }
        }

        if wildcard_fallback { success } else { None }
    }
}

#[cfg(test)]
mod tests;
