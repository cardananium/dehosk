//! Control flow (if/when) simplification methods for Simplifier.

use crate::pseudo::ast::PBox;
mod clauses;
mod constant_constructor;
mod eta_pair;
mod expect;
mod fields;
mod list_destructure;
mod naming;
mod scott;
mod summary;
mod tag_dispatch;
mod tag_literal;
mod two_clause;

use std::collections::HashSet;

use super::Simplifier;
use super::postprocess::{SumTypeId, sum_type_constructor_fields};
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
#[cfg(test)]
use crate::pseudo::constructor::ConstructorShape;
#[cfg(test)]
use crate::pseudo::var_id::VarId;
use summary::{LateWhenClauseSummary, ScottClauseSummary, WhenClauseShapeSummary};

#[cfg(test)]
mod tests;

impl Simplifier {
    fn cached_can_short_circuit_with_boolean(cache: &mut Option<bool>, expr: &PseudoExpr) -> bool {
        *cache.get_or_insert_with(|| Self::can_short_circuit_with_boolean(expr))
    }

    fn expect_void(cond: PseudoExpr) -> PseudoExpr {
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::expect_helper()),
            args: vec![cond, PseudoExpr::Unit].into(),
        }
    }

    /// Negate a condition, preferring to invert comparison operators
    /// rather than wrapping in `!`.
    fn negate_condition(&self, cond: PseudoExpr) -> PseudoExpr {
        if let PseudoExpr::BinOp { op, left, right } = &cond {
            let inverted = match op {
                BinaryOp::Eq => Some(BinaryOp::Neq),
                BinaryOp::Neq => Some(BinaryOp::Eq),
                BinaryOp::Lt => Some(BinaryOp::Gte),
                BinaryOp::Lte => Some(BinaryOp::Gt),
                BinaryOp::Gt => Some(BinaryOp::Lte),
                BinaryOp::Gte => Some(BinaryOp::Lt),
                _ => None,
            };
            if let Some(new_op) = inverted {
                return PseudoExpr::BinOp {
                    op: new_op,
                    left: left.clone(),
                    right: right.clone(),
                };
            }
        }
        // If already negated, double-negate cancels
        if let PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand,
        } = &cond
        {
            return (**operand).clone();
        }
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand: PBox::new(cond),
        }
    }

    pub(super) fn simplify_if(
        &mut self,
        condition: PseudoExpr,
        then_branch: PseudoExpr,
        else_branch: PseudoExpr,
    ) -> PseudoExpr {
        let cond = self.simplify(condition);
        let mut then_br = self.simplify(then_branch);
        let mut else_br = self.simplify(else_branch);
        let mut cond_can_short_circuit = None;
        let mut then_can_short_circuit = None;
        let mut else_can_short_circuit = None;
        let eq_tag_comparison = match &cond {
            PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left,
                right,
            } => self.extract_tag_comparison(left, right),
            _ => None,
        };

        if let Some((rewritten_then, rewritten_else)) =
            Self::rewrite_scott_constructor_if_branches(&then_br, &else_br)
        {
            then_br = rewritten_then;
            else_br = rewritten_else;
        }

        // Constant condition folding: if True { A } else { B } -> A
        if self.is_true(&cond) {
            return then_br;
        }
        // Constant condition folding: if False { A } else { B } -> B
        if self.is_false(&cond) {
            return else_br;
        }

        // if cond { A } else { A } -> A, when cond is side-effect free
        if then_br == else_br && Self::is_side_effect_free_if_condition(&cond) {
            return then_br;
        }

        // if cond { False } else { True } -> !cond (with simplification)
        if self.is_false(&then_br)
            && self.is_true(&else_br)
            && Self::cached_can_short_circuit_with_boolean(&mut cond_can_short_circuit, &cond)
        {
            // Try to simplify !(comparison) to inverted comparison
            if let PseudoExpr::BinOp { op, left, right } = &cond {
                let inverted = match op {
                    BinaryOp::Eq => Some(BinaryOp::Neq),
                    BinaryOp::Neq => Some(BinaryOp::Eq),
                    BinaryOp::Lt => Some(BinaryOp::Gte),
                    BinaryOp::Lte => Some(BinaryOp::Gt),
                    BinaryOp::Gt => Some(BinaryOp::Lte),
                    BinaryOp::Gte => Some(BinaryOp::Lt),
                    _ => None,
                };
                if let Some(new_op) = inverted {
                    return PseudoExpr::BinOp {
                        op: new_op,
                        left: left.clone(),
                        right: right.clone(),
                    };
                }
            }
            return PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand: PBox::new(cond),
            };
        }

        // if cond { True } else { False } -> cond
        if self.is_true(&then_br)
            && self.is_false(&else_br)
            && Self::cached_can_short_circuit_with_boolean(&mut cond_can_short_circuit, &cond)
        {
            return cond;
        }

        // No Scott boolean collapse (`if cond { choose_fst } else { choose_snd }`
        // → cond) here: the result may be over-applied as a selector, as in
        // `fn_3(x, y)(delay(a), delay(b))`, and a Bool is not callable. Proving
        // the result is only used as a Bool needs call-graph analysis.

        if let Some(expr) =
            self.try_simplify_expect_tag_comparison_if(&eq_tag_comparison, &then_br, &else_br)
        {
            return expr;
        }

        // If-when merge: if (when subject is { P1 -> True; P2 -> False; ... }) { A } else { B }
        // becomes: when subject is { P1 -> A; P2 -> B; ... }
        // Must be BEFORE ||/&& conversion so `if (when P -> True; _ -> fail) { rest } else { False }`
        // becomes `when P -> rest; _ -> fail` instead of `(when ...) && rest`.
        if let PseudoExpr::When {
            subject: ref when_subject,
            ref subject_name,
            ref clauses,
        } = cond
        {
            let all_bool_or_fail = !clauses.is_empty()
                && clauses.iter().all(|c| {
                    self.is_true(&c.body) || self.is_false(&c.body) || Self::is_fail(&c.body)
                });
            if all_bool_or_fail {
                let mut true_uses = clauses.iter().filter(|c| self.is_true(&c.body)).count();
                let mut false_uses = clauses.iter().filter(|c| self.is_false(&c.body)).count();
                let new_clauses: Vec<_> = clauses
                    .iter()
                    .map(|c| {
                        let new_body = if self.is_true(&c.body) {
                            let body = if true_uses == 1 {
                                then_br.clone()
                            } else {
                                self.clone_with_fresh_ids(&then_br)
                            };
                            true_uses = true_uses.saturating_sub(1);
                            body
                        } else if self.is_false(&c.body) {
                            let body = if false_uses == 1 {
                                else_br.clone()
                            } else {
                                self.clone_with_fresh_ids(&else_br)
                            };
                            false_uses = false_uses.saturating_sub(1);
                            body
                        } else {
                            // fail stays as fail
                            c.body.clone()
                        };
                        WhenClause {
                            pattern: c.pattern.clone(),
                            guard: c.guard.clone(),
                            body: new_body,
                        }
                    })
                    .collect();
                return self.simplify_when(
                    (**when_subject).clone(),
                    subject_name.clone(),
                    new_clauses,
                );
            }
        }

        if let Some(expr) = self.try_reconstruct_list_subject_if(&cond, &then_br, &else_br) {
            return expr;
        }

        if let Some(expr) =
            self.try_simplify_tag_comparison_if(&eq_tag_comparison, &then_br, &else_br)
        {
            return expr;
        }

        // Build the integer when-chain BEFORE boolean collapse, or
        // `if z == 0 { T } else { if z == 1 { ... } }` collapses into
        // `z == 0 || (if z == 1 ...)` first.
        if Self::may_build_when_from_if_chain(&cond, &else_br)
            && let Some(when_expr) = Self::try_build_when_from_if_chain(&cond, &then_br, &else_br)
        {
            if let PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } = when_expr
            {
                return self.simplify_when(subject.into_inner(), subject_name, clauses);
            }
            return when_expr;
        }

        // Merge nested ifs with a shared False fallback:
        // if a { if b { x } else { False } } else { False }
        //   > if a && b { x } else { False }
        //
        // Keeps the final branch type while collapsing one layer, even
        // when `x` is too conservatively typed to become `a && b && x`.
        if self.is_false(&else_br)
            && Self::cached_can_short_circuit_with_boolean(&mut cond_can_short_circuit, &cond)
            && let PseudoExpr::If {
                condition: inner_cond,
                then_branch: inner_then,
                else_branch: inner_else,
            } = &then_br
            && self.is_false(inner_else)
            && Self::can_short_circuit_with_boolean(inner_cond)
        {
            return self.simplify_if(
                PseudoExpr::BinOp {
                    op: BinaryOp::And,
                    left: PBox::new(Self::unwrap_delay(&cond)),
                    right: PBox::new(Self::unwrap_delay(inner_cond)),
                },
                (**inner_then).clone(),
                PseudoExpr::Bool(false),
            );
        }

        // if cond { True } else { expr } -> cond || expr
        // Placed after tag-check so `if z.tag == 0 { True } else { expr }` becomes
        // `when z is { Constr<0> -> True; _ -> expr }` first.
        if self.is_true(&then_br)
            && Self::cached_can_short_circuit_with_boolean(&mut cond_can_short_circuit, &cond)
            && Self::cached_can_short_circuit_with_boolean(&mut else_can_short_circuit, &else_br)
        {
            return PseudoExpr::BinOp {
                op: BinaryOp::Or,
                left: PBox::new(Self::unwrap_delay(&cond)),
                right: PBox::new(Self::unwrap_delay(&else_br)),
            };
        }

        // if cond { False } else { expr } -> !cond && expr
        // Common in Plinth-compiled code where `a && b` becomes `if a then b else False`
        // but with inverted condition: `if (not a) then False else b`.
        if self.is_false(&then_br)
            && !self.is_true(&else_br)
            && !Self::is_fail(&else_br)
            && Self::cached_can_short_circuit_with_boolean(&mut cond_can_short_circuit, &cond)
            && Self::cached_can_short_circuit_with_boolean(&mut else_can_short_circuit, &else_br)
        {
            let negated_cond = self.negate_condition(cond);
            return PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(negated_cond),
                right: PBox::new(Self::unwrap_delay(&else_br)),
            };
        }

        // if cond { expr } else { True } -> !cond || expr
        // Mirror of the `cond || expr` rule above, for inverted conditions;
        // common in Plinth-compiled `a || b`.
        if self.is_true(&else_br)
            && !self.is_false(&then_br)
            && !Self::is_fail(&then_br)
            && Self::cached_can_short_circuit_with_boolean(&mut cond_can_short_circuit, &cond)
            && Self::cached_can_short_circuit_with_boolean(&mut then_can_short_circuit, &then_br)
        {
            let negated_cond = self.negate_condition(cond);
            return PseudoExpr::BinOp {
                op: BinaryOp::Or,
                left: PBox::new(negated_cond),
                right: PBox::new(Self::unwrap_delay(&then_br)),
            };
        }

        // if cond { expr } else { False } -> cond && expr
        if self.is_false(&else_br)
            && Self::cached_can_short_circuit_with_boolean(&mut cond_can_short_circuit, &cond)
            && Self::cached_can_short_circuit_with_boolean(&mut then_can_short_circuit, &then_br)
        {
            return PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(Self::unwrap_delay(&cond)),
                right: PBox::new(Self::unwrap_delay(&then_br)),
            };
        }

        if let Some(expr) = Self::try_simplify_if_expect(&cond, &then_br, &else_br) {
            return expr;
        }

        // Readability: avoid inline `if (when ...)` and similar control-flow-heavy
        // conditions by extracting condition into a named let first.
        if !self.safe_mode && Self::contains_control_flow_expr(&cond) {
            let mut used_names = std::collections::HashSet::new();
            Self::collect_var_names(&cond, &mut used_names);
            Self::collect_var_names(&then_br, &mut used_names);
            Self::collect_var_names(&else_br, &mut used_names);
            let base = Self::suggest_boolish_name_from_expr(&cond)
                .unwrap_or_else(|| "condition_ok".to_string());
            let cond_name = self.fresh_name_for_scope(&mut used_names, base);
            let binder = self.fresh_synthetic_binder(&cond_name);
            return self.make_let_for_binder(
                binder.clone(),
                cond,
                PseudoExpr::If {
                    condition: PBox::new(self.make_var_for_binder(&binder)),
                    then_branch: PBox::new(then_br),
                    else_branch: PBox::new(else_br),
                },
            );
        }

        if let Some(expr) = self.try_simplify_data_like_condition_if(&cond, &then_br, &else_br) {
            return expr;
        }

        PseudoExpr::If {
            condition: PBox::new(cond),
            then_branch: PBox::new(then_br),
            else_branch: PBox::new(else_br),
        }
    }

    pub(super) fn simplify_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let simplified_subject = self.simplify(subject);

        // Remove arity checks: `expect [] = expr` (single empty-list clause +
        // error fallback), compiler-generated assertions that a list/fields is
        // exhausted. Skip a subject containing an explicit Error — the rewrite
        // would silently discard an intentional failure.
        if !Self::contains_explicit_error(&simplified_subject) {
            let mut non_error_clause = None;
            let mut multiple_non_error_clauses = false;
            for clause in &clauses {
                if matches!(clause.body, PseudoExpr::Error { .. }) {
                    continue;
                }
                if non_error_clause.is_some() {
                    multiple_non_error_clauses = true;
                    break;
                }
                non_error_clause = Some(clause);
            }
            if !multiple_non_error_clauses
                && let Some(clause) = non_error_clause
                && let WhenPattern::List {
                    elements,
                    tail: None,
                } = &clause.pattern
                && elements.is_empty()
                && clause.guard.is_none()
            {
                return self.simplify(clause.body.clone());
            }
        }

        // Sum-type context subject (`purpose`/`script_info`) enables
        // constructor-specific field overrides per clause.
        let subject_sum_type = if self.script_version.is_some() {
            match &simplified_subject {
                PseudoExpr::Var { name, .. } => {
                    match self
                        .context
                        .context_field_names
                        .get(name)
                        .map(|s| s.as_str())
                    {
                        Some("purpose") => Some("purpose".to_string()),
                        Some("script_info") => Some("script_info".to_string()),
                        _ => {
                            if name == "purpose" || name == "script_info" {
                                Some(name.clone())
                            } else {
                                None
                            }
                        }
                    }
                }
                PseudoExpr::FieldAccess { selector, .. } => {
                    let name = selector.as_pretty_name();
                    if name == "purpose" || name == "script_info" {
                        Some(name.to_string())
                    } else {
                        None
                    }
                }
                _ => None,
            }
        } else {
            None
        };

        let mut simplified_clauses = Vec::with_capacity(clauses.len());
        let mut scott_clause_summary = ScottClauseSummary::default();
        if let Some(ctx_name) = subject_sum_type.as_deref() {
            for clause in clauses {
                let override_entry = if let WhenPattern::Constructor { tag, .. } = &clause.pattern {
                    if let Some(script_version) = self.script_version {
                        if let Some(fields) = SumTypeId::from_display_name(ctx_name)
                            .and_then(|id| sum_type_constructor_fields(id, *tag, script_version))
                        {
                            let override_data: Vec<(String, Option<String>)> = fields
                                .iter()
                                .map(|(n, t)| {
                                    (
                                        n.display_name().to_string(),
                                        t.map(|ft| ft.display_name().to_string()),
                                    )
                                })
                                .collect();
                            // Register type info for constructor fields
                            for (name, maybe_type) in &override_data {
                                self.context
                                    .context_field_names
                                    .insert(name.clone(), name.clone());
                                // Dual-write by VarId (use name_to_id bridge for constructor fields)
                                if let Some(&vid) = self.naming.name_to_id.get(name) {
                                    self.context
                                        .context_field_names_by_id
                                        .insert(vid, name.clone());
                                }
                                if let Some(type_name) = maybe_type {
                                    self.context
                                        .context_var_types
                                        .insert(name.clone(), type_name.clone());
                                    if let Some(&vid) = self.naming.name_to_id.get(name) {
                                        self.context
                                            .context_var_types_by_id
                                            .insert(vid, type_name.clone());
                                    }
                                }
                            }
                            let prev = self
                                .context
                                .sum_type_field_overrides
                                .insert(ctx_name.to_string(), override_data);
                            Some((ctx_name.to_string(), prev))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };

                let result = WhenClause {
                    pattern: clause.pattern,
                    guard: clause.guard.map(|guard| self.simplify(guard)),
                    body: self.simplify(clause.body),
                };
                scott_clause_summary.add_assign(ScottClauseSummary::observe(&result.body));

                if let Some((ctx_name, prev)) = override_entry {
                    match prev {
                        Some(old) => {
                            self.context.sum_type_field_overrides.insert(ctx_name, old);
                        }
                        None => {
                            self.context.sum_type_field_overrides.remove(&ctx_name);
                        }
                    }
                }

                simplified_clauses.push(result);
            }
        } else {
            for clause in clauses {
                let result = WhenClause {
                    pattern: clause.pattern,
                    guard: clause.guard.map(|guard| self.simplify(guard)),
                    body: self.simplify(clause.body),
                };
                scott_clause_summary.add_assign(ScottClauseSummary::observe(&result.body));
                simplified_clauses.push(result);
            }
        }

        if scott_clause_summary.may_rewrite()
            && let Some(rewritten_clauses) =
                Self::rewrite_scott_constructor_when_clauses(&simplified_clauses)
        {
            simplified_clauses = rewritten_clauses;
        }

        if let Some(expr) = self.collapse_eta_pair_selector_when(
            &simplified_subject,
            &subject_name,
            &simplified_clauses,
        ) {
            return expr;
        }

        if let Some((subject, clauses)) =
            self.rewrite_tag_literal_when_subject(&simplified_subject, &simplified_clauses)
        {
            return self.simplify_when(subject, subject_name, clauses);
        }

        if let Some(expr) = self.collapse_constant_constructor_subject(
            &simplified_subject,
            &subject_name,
            &simplified_clauses,
        ) {
            return expr;
        }

        if let Some(expr) = self.try_simplify_two_clause_wildcard_when(
            &simplified_subject,
            &subject_name,
            &simplified_clauses,
        ) {
            return expr;
        }

        let initial_shape_summary = WhenClauseShapeSummary::analyze(&simplified_clauses);

        // Flatten nested when on the same subject:
        // When x is { A -> ...; _ -> when x is { B -> ...; _ -> fail } }
        // becomes: when x is { A -> ...; B -> ...; _ -> fail }
        let (simplified_clauses, shape_summary) =
            if initial_shape_summary.has_guardless_nested_when_body {
                let simplified_clauses =
                    Self::flatten_nested_when(&simplified_subject, simplified_clauses);
                let shape_summary = WhenClauseShapeSummary::analyze(&simplified_clauses);
                (simplified_clauses, shape_summary)
            } else {
                (simplified_clauses, initial_shape_summary)
            };

        // When-clause field destructuring:
        // Convert `when x is { Constr<N> -> ... fv[0] ... fv[1] ... }` where fv = x.fields
        // into `when x is { Constr<N>(field_0, field_1) -> ... field_0 ... field_1 ... }`
        let simplified_clauses = if shape_summary.has_constructor_clause {
            self.destructure_when_fields(&simplified_subject, &subject_name, simplified_clauses)
        } else {
            simplified_clauses
        };

        // List head/tail destructuring:
        // Convert wildcard clause `_ -> let h = subj[0]; let t = List.tail(subj); body`
        // into `[h, ..t] -> body`
        let simplified_clauses = if shape_summary.has_guardless_wildcard_let_body {
            Self::destructure_list_head_tail(&simplified_subject, &subject_name, simplified_clauses)
        } else {
            simplified_clauses
        };

        // Inline list head/tail destructuring (not let-bound):
        // Convert wildcard clause `_ -> ... subj[0] ... List.tail(subj) ...`
        // into `[subj_h, ..subj_t] -> ... subj_h ... subj_t ...`
        let simplified_clauses = if shape_summary.has_guardless_wildcard_clause {
            self.destructure_inline_list_head_tail(
                &simplified_subject,
                &subject_name,
                simplified_clauses,
            )
        } else {
            simplified_clauses
        };

        // Name ScriptPurpose/ScriptInfo constructors from context tracking.
        // Must run BEFORE generic Bool/Option naming, or `ScriptInfo
        // {Minting(x), Spending}` matches `Option {Some(x), None}`. Covers the
        // other known context sum types too.
        let (simplified_clauses, has_unnamed_constructors) =
            if shape_summary.has_unnamed_constructor_pattern {
                if self
                    .subject_constructor_names(&simplified_subject)
                    .is_some()
                {
                    let result =
                        self.name_subject_constructors(&simplified_subject, simplified_clauses);
                    (result.clauses, result.has_unnamed_constructors)
                } else {
                    (simplified_clauses, true)
                }
            } else {
                (simplified_clauses, false)
            };

        let subject_fields_accessed_in_clauses = subject_name
            .as_ref()
            .map(|binder| (binder.as_ref(), Some(binder.id)))
            .or(match &simplified_subject {
                PseudoExpr::Var { name, id } => Some((name.as_str(), *id)),
                _ => None,
            })
            // compat refs carry `id: None`. Synthesize a
            // fresh compat placeholder so `expr_accesses_fields_of` (which keys
            // off `id.get()`) still falls back to name-based comparison.
            .map(|(name, id_opt)| {
                (
                    name,
                    id_opt.unwrap_or_else(crate::pseudo::var_id::VarId::fresh_compat_placeholder),
                )
            })
            .is_some_and(|(subject_var_name, subject_var_id)| {
                simplified_clauses.iter().any(|clause| {
                    clause.guard.as_ref().is_some_and(|guard| {
                        Self::expr_accesses_fields_of(guard, subject_var_name, subject_var_id)
                    }) || Self::expr_accesses_fields_of(
                        &clause.body,
                        subject_var_name,
                        subject_var_id,
                    )
                })
            });

        let should_try_known_constructor_naming = has_unnamed_constructors
            && simplified_clauses.len() <= 3
            && !subject_fields_accessed_in_clauses;

        // Don't rename `Constr<0>/Constr<1>` → `False/True` when the subject is
        // known non-Bool or the clauses carry an explicit `_ -> fail` wildcard —
        // that wildcard signals sum-type dispatch, so `when script_info is {
        // Constr<0>; Constr<1>; _ -> fail }` must not become `{ False; True; _ ->
        // fail }`: `script_info` is not a Bool.
        let has_wildcard_fail_clause_early = simplified_clauses
            .iter()
            .any(|c| matches!(c.pattern, WhenPattern::Wildcard) && Self::is_fail(&c.body));
        let allow_bool_like_naming = !has_wildcard_fail_clause_early
            && !Self::has_known_non_boolean_type(&simplified_subject);

        // Name well-known constructor patterns (Bool, Option) in when clauses.
        // Runs after context naming so already-named constructors are skipped.
        let simplified_clauses = if should_try_known_constructor_naming && allow_bool_like_naming {
            Self::name_known_constructors(simplified_clauses)
        } else {
            simplified_clauses
        };

        if simplified_clauses.len() <= 1 && !shape_summary.has_guardless_wildcard_if_body {
            return PseudoExpr::When {
                subject: PBox::new(simplified_subject),
                subject_name,
                clauses: simplified_clauses,
            };
        }

        let late_summary = LateWhenClauseSummary::analyze(&simplified_clauses);
        let has_late_guardless_wildcard_clause = late_summary.shape.has_guardless_wildcard_clause;
        let has_late_guardless_wildcard_if_body = late_summary.shape.has_guardless_wildcard_if_body;

        if simplified_clauses.len() <= 1 {
            let simplified_clauses = if has_late_guardless_wildcard_if_body {
                Self::expand_wildcard_if_to_clauses(
                    simplified_clauses,
                    &simplified_subject,
                    &subject_name,
                )
            } else {
                simplified_clauses
            };

            return PseudoExpr::When {
                subject: PBox::new(simplified_subject),
                subject_name,
                clauses: simplified_clauses,
            };
        }
        let outcome_summary = late_summary.outcome;

        // Boolean when → if/else conversion
        // when x is { True -> A; False -> B } → if x { A } else { B }
        // Also handles: True + False + _ -> fail (in any order)
        //
        // Refuse to collapse when (1) the subject is *known*
        // non-Bool, (2) `subject_constructor_names` recognizes it as
        // a sum-type carrier (V3 `script_info`, V1/V2 `purpose`,
        // `credential`, …), or (3) an explicit `_ -> fail` wildcard
        // clause is present: Bool dispatch is True/False exhaustive,
        // so a wildcard-fail clause marks constructor-tag dispatch on
        // a sum-type (or `Data`) value, whose shape `if script_info
        // { … }` would lose.
        let subject_is_sum_type = self
            .subject_constructor_names(&simplified_subject)
            .is_some();
        let has_wildcard_fail_clause = simplified_clauses
            .iter()
            .any(|c| matches!(c.pattern, WhenPattern::Wildcard) && Self::is_fail(&c.body));
        if outcome_summary.all_bool_or_fail
            && !Self::has_known_non_boolean_type(&simplified_subject)
            && !subject_is_sum_type
            && !has_wildcard_fail_clause
            && let (Some(then_branch), Some(else_branch)) =
                (outcome_summary.true_body, outcome_summary.false_body)
        {
            // A bool→bool MAP `when B is { <arm_a> -> boolConstr_p; <arm_b> ->
            // boolConstr_q }` whose arm bodies are *nullary bool constructors*
            // is convention-INDEPENDENT: identity (`B`) or negation (`!B`)
            // follows purely from whether the body tags are in the SAME order
            // as the scrutinee pattern tags or SWAPPED — the True/False
            // meaning of either tag never enters. Routing it through the
            // value-convention `simplify_if` below is UNSOUND when the
            // pattern-labelling convention (`name_known_constructors`:
            // tag0=False, tag1=True) disagrees with the program's church-bool
            // value convention (InverseCip: tag0=True): the two cancel and a
            // genuine `!B` collapses to identity `B`.
            //
            // `true_body` is therefore the tag-1 arm's body and `false_body`
            // the tag-0 arm's:
            // - identity  : true_body has tag 1 AND false_body has tag 0.
            // - negation  : true_body has tag 0 AND false_body has tag 1.
            if let (Some(true_body_tag), Some(false_body_tag)) = (
                Self::nullary_bool_constr_tag(then_branch),
                Self::nullary_bool_constr_tag(else_branch),
            ) {
                let subject_expr = if let Some(name) = &subject_name {
                    self.make_var_for_binder(name)
                } else {
                    simplified_subject.clone()
                };
                // Same order (True-arm→tag1, False-arm→tag0) → identity.
                if true_body_tag == 1 && false_body_tag == 0 {
                    return self.simplify(subject_expr);
                }
                // Swapped order (True-arm→tag0, False-arm→tag1) → negation.
                if true_body_tag == 0 && false_body_tag == 1 {
                    let simplified = self.simplify(subject_expr);
                    return PseudoExpr::UnOp {
                        op: UnaryOp::Not,
                        operand: PBox::new(simplified),
                    };
                }
            }
            // Per-bool church-bool collapse orientation.
            //
            // A WITNESSED data-tag church bool (arm patterns carry a
            // `church_true` tag, stamped at lowering from the data-tag
            // convention) already had its `true_body`/`false_body` oriented
            // by its OWN convention in `summary.rs`, so the collapse needs no
            // program-flag swap and must not double-correct.
            //
            // An UNWITNESSED church bool (no `church_true` on the arm
            // patterns) in an inverse-CIP program reaches here with CIP
            // `recognize_two_branch_adt` labels (church_true = Constr<0> was
            // labelled `False`), so swap to restore the real order. Gated to
            // an `Apply` subject — a church-bool-returning call the data-tag
            // dataflow can't cross; native whens (comparisons / builtins /
            // `Bool` literals) keep CIP.
            let witnessed_church_bool = simplified_clauses.iter().any(|c| {
                matches!(
                    &c.pattern,
                    WhenPattern::Constructor { shape, .. } if shape.church_true().is_some()
                )
            });
            let swap_church = !witnessed_church_bool
                && self.church_polarity
                    == crate::decompile::church_polarity::ChurchPolarity::InverseCip
                && matches!(&simplified_subject, PseudoExpr::Apply { .. });
            let subject_expr = if let Some(name) = &subject_name {
                self.make_var_for_binder(name)
            } else {
                simplified_subject
            };
            let (then_b, else_b) = if swap_church {
                (else_branch, then_branch)
            } else {
                (then_branch, else_branch)
            };
            return self.simplify_if(subject_expr, then_b.clone(), else_b.clone());
        }

        // Collapse when all non-error clauses have identical bodies and none
        // reference pattern-bound variables, e.g.
        // `when x is { True -> expr; False -> expr; _ -> error } → expr`.
        // Skip if the subject has an explicit Error — that failure is intentional.
        if !Self::contains_explicit_error(&simplified_subject)
            && outcome_summary.non_fail_count >= 2
            && outcome_summary.all_non_fail_same
        {
            let first_body = outcome_summary
                .first_non_fail_body
                .expect("non_fail_count >= 2 implies a non-fail body");
            let mut used_names = HashSet::new();
            Self::collect_var_names(first_body, &mut used_names);
            let safe = simplified_clauses
                .iter()
                .filter(|clause| !Self::is_fail(&clause.body))
                .all(|clause| !Self::pattern_binds_any_used_name(&clause.pattern, &used_names));
            if safe {
                return first_body.clone();
            }
        }

        // Deduplicate when clauses: drop clauses whose body matches the
        // wildcard's (already covered); with no wildcard, a majority sharing
        // one body becomes a single wildcard clause.
        let simplified_clauses = if has_late_guardless_wildcard_clause {
            Self::deduplicate_when_clauses(simplified_clauses)
        } else {
            simplified_clauses
        };

        // Expand a wildcard whose body is `if subject { A } else { B }`
        // into two explicit constructor clauses, so constructor dispatch
        // is not printed as a boolean `if`.
        let simplified_clauses = if has_late_guardless_wildcard_if_body {
            Self::expand_wildcard_if_to_clauses(
                simplified_clauses,
                &simplified_subject,
                &subject_name,
            )
        } else {
            simplified_clauses
        };

        PseudoExpr::When {
            subject: PBox::new(simplified_subject),
            subject_name,
            clauses: simplified_clauses,
        }
    }
}
