use crate::decompile::list_traversal::list_tail_argument;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

use super::Simplifier;

mod index;
mod legacy;

#[derive(Clone, Copy, Default)]
struct ListAccessUsage {
    has_head: bool,
    has_tail: bool,
}

#[derive(Clone, Copy, Default)]
struct AccessShadow {
    exact_blocked: bool,
    fallback_blocked: bool,
}

fn access_ref_matches(
    name: &str,
    id: Option<VarId>,
    target_name: &str,
    target_id: Option<VarId>,
    shadow: AccessShadow,
) -> bool {
    match (target_id, id.get()) {
        (Some(target), Some(candidate)) => !shadow.exact_blocked && target == candidate,
        _ => !shadow.fallback_blocked && name == target_name,
    }
}

fn shadow_access_binding(
    shadow: AccessShadow,
    binder_name: &str,
    binder_id: Option<VarId>,
    target_name: &str,
    target_id: Option<VarId>,
) -> AccessShadow {
    AccessShadow {
        exact_blocked: shadow.exact_blocked
            || crate::decompile::var_match::ids_match_strict(target_id, binder_id.get()),
        fallback_blocked: shadow.fallback_blocked || binder_name == target_name,
    }
}

fn shadow_access_binder(
    shadow: AccessShadow,
    binder: &Binder,
    target_name: &str,
    target_id: Option<VarId>,
) -> AccessShadow {
    shadow_access_binding(
        shadow,
        binder.as_str(),
        Some(binder.id),
        target_name,
        target_id,
    )
}

fn shadow_access_pattern(
    mut shadow: AccessShadow,
    pattern: &WhenPattern,
    target_name: &str,
    target_id: Option<VarId>,
) -> AccessShadow {
    match pattern {
        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
            for binder in fields {
                shadow = shadow_access_binder(shadow, binder, target_name, target_id);
            }
        }
        WhenPattern::List { elements, tail } => {
            for binder in elements {
                shadow = shadow_access_binder(shadow, binder, target_name, target_id);
            }
            if let Some(tail) = tail {
                shadow = shadow_access_binder(shadow, tail, target_name, target_id);
            }
        }
        WhenPattern::Pair(left, right) => {
            shadow = shadow_access_binder(shadow, left, target_name, target_id);
            shadow = shadow_access_binder(shadow, right, target_name, target_id);
        }
        WhenPattern::Var(binder) => {
            shadow = shadow_access_binder(shadow, binder, target_name, target_id);
        }
        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
    }
    shadow
}

fn is_head_access_of_target(
    expr: &PseudoExpr,
    subj_var_name: &str,
    subj_id: Option<VarId>,
    shadow: AccessShadow,
) -> bool {
    match expr {
        PseudoExpr::IndexAccess { collection, index } if *index == 0 => {
            if let PseudoExpr::Var { name, id, .. } = collection.as_ref() {
                access_ref_matches(name, *id, subj_var_name, subj_id, shadow)
            } else {
                false
            }
        }
        PseudoExpr::FieldAccess {
            record, selector, ..
        } if selector.is_list_head() => {
            if let PseudoExpr::Var { name, id, .. } = record.as_ref() {
                access_ref_matches(name, *id, subj_var_name, subj_id, shadow)
            } else {
                false
            }
        }
        _ => false,
    }
}

fn is_tail_access_of_target(
    expr: &PseudoExpr,
    subj_var_name: &str,
    subj_id: Option<VarId>,
    shadow: AccessShadow,
) -> bool {
    match list_tail_argument(expr) {
        Some(PseudoExpr::Var { name, id, .. }) => {
            access_ref_matches(name, *id, subj_var_name, subj_id, shadow)
        }
        _ => false,
    }
}

fn replace_list_access_by_id(
    expr: PseudoExpr,
    subj_var_name: &str,
    subj_id: Option<VarId>,
    replacement_name: &str,
    replacement_id: VarId,
    access_matches: fn(&PseudoExpr, &str, Option<VarId>, AccessShadow) -> bool,
) -> PseudoExpr {
    use crate::pseudo::fold::{ExprFolder, FoldAction};

    struct AccessReplacer<'a> {
        subj_var_name: &'a str,
        subj_id: Option<VarId>,
        replacement_name: &'a str,
        replacement_id: VarId,
        access_matches: fn(&PseudoExpr, &str, Option<VarId>, AccessShadow) -> bool,
        shadow: AccessShadow,
        // Saved shadow to restore in the matching `exit_*`/post-clause step.
        saved: Vec<AccessShadow>,
    }

    impl<'a> ExprFolder for AccessReplacer<'a> {
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            if (self.access_matches)(expr, self.subj_var_name, self.subj_id, self.shadow) {
                FoldAction::Replace(PseudoExpr::Var {
                    name: self.replacement_name.to_string(),
                    id: Some(self.replacement_id),
                })
            } else {
                FoldAction::Walk
            }
        }

        fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
            self.saved.push(self.shadow);
            for param in params {
                self.shadow =
                    shadow_access_binder(self.shadow, param, self.subj_var_name, self.subj_id);
            }
            params.to_vec()
        }

        fn exit_lambda(&mut self, _params: &[Binder]) {
            self.shadow = self.saved.pop().expect("lambda shadow");
        }

        fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
            self.saved.push(self.shadow);
            self.shadow = shadow_access_binder(self.shadow, name, self.subj_var_name, self.subj_id);
            for param in params {
                self.shadow =
                    shadow_access_binder(self.shadow, param, self.subj_var_name, self.subj_id);
            }
            (name.clone(), params.to_vec())
        }

        fn exit_recfn(&mut self, _name: &Binder, _params: &[Binder]) {
            self.shadow = self.saved.pop().expect("recfn shadow");
        }

        fn enter_let(&mut self, name: &str, id: &Option<VarId>, _value: &PseudoExpr) -> String {
            self.saved.push(self.shadow);
            self.shadow =
                shadow_access_binding(self.shadow, name, *id, self.subj_var_name, self.subj_id);
            name.to_string()
        }

        fn exit_let(&mut self, _name: &str) {
            self.shadow = self.saved.pop().expect("let shadow");
        }

        // Not on the generic step machine (its clauses need pattern-binder
        // shadowing), so overridden directly rather than via `fold_clause` —
        // which would also fold `Literal` patterns.
        fn fold_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            let subject = self.fold(subject);
            let outer_shadow = self.shadow;
            let clauses = clauses
                .into_iter()
                .map(|c| {
                    self.shadow = outer_shadow;
                    if let Some(sn) = &subject_name {
                        self.shadow =
                            shadow_access_binder(self.shadow, sn, self.subj_var_name, self.subj_id);
                    }
                    self.shadow = shadow_access_pattern(
                        self.shadow,
                        &c.pattern,
                        self.subj_var_name,
                        self.subj_id,
                    );
                    let guard = c.guard.map(|g| self.fold(g));
                    let body = self.fold(c.body);
                    WhenClause {
                        pattern: c.pattern,
                        guard,
                        body,
                    }
                })
                .collect();
            self.shadow = outer_shadow;
            self.post_when(subject, subject_name, clauses)
        }
    }

    AccessReplacer {
        subj_var_name,
        subj_id,
        replacement_name,
        replacement_id,
        access_matches,
        shadow: AccessShadow::default(),
        saved: Vec::new(),
    }
    .fold(expr)
}

impl Simplifier {
    #[cfg(test)]
    pub(crate) fn list_access_usage(expr: &PseudoExpr, subj_var_name: &str) -> (bool, bool) {
        Self::list_access_usage_by_id(expr, subj_var_name, None)
    }

    pub(crate) fn list_access_usage_by_id(
        expr: &PseudoExpr,
        subj_var_name: &str,
        subj_id: Option<VarId>,
    ) -> (bool, bool) {
        fn go(
            expr: &PseudoExpr,
            subj_var_name: &str,
            subj_id: Option<VarId>,
            shadow: AccessShadow,
        ) -> ListAccessUsage {
            let usage = ListAccessUsage {
                has_head: is_head_access_of_target(expr, subj_var_name, subj_id, shadow),
                has_tail: is_tail_access_of_target(expr, subj_var_name, subj_id, shadow),
            };
            if usage.has_head && usage.has_tail {
                return usage;
            }

            let merge = |mut usage: ListAccessUsage, other: ListAccessUsage| {
                usage.has_head |= other.has_head;
                usage.has_tail |= other.has_tail;
                usage
            };

            match expr {
                PseudoExpr::Lambda { params, body } => {
                    let mut next_shadow = shadow;
                    for param in params {
                        next_shadow =
                            shadow_access_binder(next_shadow, param, subj_var_name, subj_id);
                    }
                    merge(usage, go(body, subj_var_name, subj_id, next_shadow))
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let mut next_shadow =
                        shadow_access_binder(shadow, name, subj_var_name, subj_id);
                    for param in params {
                        next_shadow =
                            shadow_access_binder(next_shadow, param, subj_var_name, subj_id);
                    }
                    merge(usage, go(body, subj_var_name, subj_id, next_shadow))
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    let usage = merge(usage, go(value, subj_var_name, subj_id, shadow));
                    if usage.has_head && usage.has_tail {
                        return usage;
                    }
                    let next_shadow =
                        shadow_access_binding(shadow, name, *id, subj_var_name, subj_id);
                    merge(usage, go(body, subj_var_name, subj_id, next_shadow))
                }
                PseudoExpr::Apply { function, args } => {
                    let mut usage = merge(usage, go(function, subj_var_name, subj_id, shadow));
                    if usage.has_head && usage.has_tail {
                        return usage;
                    }
                    for arg in args {
                        usage = merge(usage, go(arg, subj_var_name, subj_id, shadow));
                        if usage.has_head && usage.has_tail {
                            break;
                        }
                    }
                    usage
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    let usage = merge(usage, go(condition, subj_var_name, subj_id, shadow));
                    if usage.has_head && usage.has_tail {
                        return usage;
                    }
                    let usage = merge(usage, go(then_branch, subj_var_name, subj_id, shadow));
                    if usage.has_head && usage.has_tail {
                        return usage;
                    }
                    merge(usage, go(else_branch, subj_var_name, subj_id, shadow))
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut usage = merge(usage, go(subject, subj_var_name, subj_id, shadow));
                    if usage.has_head && usage.has_tail {
                        return usage;
                    }
                    for clause in clauses {
                        let mut clause_shadow = shadow;
                        if let Some(subject_name) = subject_name {
                            clause_shadow = shadow_access_binder(
                                clause_shadow,
                                subject_name,
                                subj_var_name,
                                subj_id,
                            );
                        }
                        clause_shadow = shadow_access_pattern(
                            clause_shadow,
                            &clause.pattern,
                            subj_var_name,
                            subj_id,
                        );
                        if let Some(guard) = &clause.guard {
                            usage = merge(usage, go(guard, subj_var_name, subj_id, clause_shadow));
                            if usage.has_head && usage.has_tail {
                                return usage;
                            }
                        }
                        usage = merge(
                            usage,
                            go(&clause.body, subj_var_name, subj_id, clause_shadow),
                        );
                        if usage.has_head && usage.has_tail {
                            break;
                        }
                    }
                    usage
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    let usage = merge(usage, go(left, subj_var_name, subj_id, shadow));
                    if usage.has_head && usage.has_tail {
                        return usage;
                    }
                    merge(usage, go(right, subj_var_name, subj_id, shadow))
                }
                PseudoExpr::UnOp { operand, .. }
                | PseudoExpr::Force(operand)
                | PseudoExpr::Delay(operand)
                | PseudoExpr::FieldAccess {
                    record: operand, ..
                }
                | PseudoExpr::IndexAccess {
                    collection: operand,
                    ..
                } => merge(usage, go(operand, subj_var_name, subj_id, shadow)),
                PseudoExpr::Trace { message, value } => {
                    let usage = merge(usage, go(message, subj_var_name, subj_id, shadow));
                    if usage.has_head && usage.has_tail {
                        return usage;
                    }
                    merge(usage, go(value, subj_var_name, subj_id, shadow))
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    let mut usage = usage;
                    for arg in args {
                        usage = merge(usage, go(arg, subj_var_name, subj_id, shadow));
                        if usage.has_head && usage.has_tail {
                            break;
                        }
                    }
                    usage
                }
                PseudoExpr::Constr { fields, .. } => {
                    let mut usage = usage;
                    for field in fields {
                        usage = merge(usage, go(field, subj_var_name, subj_id, shadow));
                        if usage.has_head && usage.has_tail {
                            break;
                        }
                    }
                    usage
                }
                PseudoExpr::List { elements, tail } => {
                    let mut usage = usage;
                    for element in elements {
                        usage = merge(usage, go(element, subj_var_name, subj_id, shadow));
                        if usage.has_head && usage.has_tail {
                            return usage;
                        }
                    }
                    if let Some(tail) = tail {
                        usage = merge(usage, go(tail, subj_var_name, subj_id, shadow));
                    }
                    usage
                }
                PseudoExpr::Pair(a, b) => {
                    let usage = merge(usage, go(a, subj_var_name, subj_id, shadow));
                    if usage.has_head && usage.has_tail {
                        return usage;
                    }
                    merge(usage, go(b, subj_var_name, subj_id, shadow))
                }
                PseudoExpr::Tuple(elements) => {
                    let mut usage = usage;
                    for element in elements {
                        usage = merge(usage, go(element, subj_var_name, subj_id, shadow));
                        if usage.has_head && usage.has_tail {
                            break;
                        }
                    }
                    usage
                }
                _ => usage,
            }
        }
        let usage = go(expr, subj_var_name, subj_id, AccessShadow::default());
        (usage.has_head, usage.has_tail)
    }

    /// Check if an expression contains `subj[0]` (IndexAccess with index 0 on a Var matching subj_var_name).
    /// Respects variable shadowing.
    #[cfg(test)]
    pub(crate) fn contains_head_access(expr: &PseudoExpr, subj_var_name: &str) -> bool {
        Self::list_access_usage(expr, subj_var_name).0
    }

    pub(crate) fn contains_head_access_by_id(
        expr: &PseudoExpr,
        subj_var_name: &str,
        subj_id: Option<VarId>,
    ) -> bool {
        Self::list_access_usage_by_id(expr, subj_var_name, subj_id).0
    }

    pub(crate) fn replace_head_access_by_id(
        expr: PseudoExpr,
        subj_var_name: &str,
        subj_id: Option<VarId>,
        replacement_name: &str,
        replacement_id: VarId,
    ) -> PseudoExpr {
        replace_list_access_by_id(
            expr,
            subj_var_name,
            subj_id,
            replacement_name,
            replacement_id,
            is_head_access_of_target,
        )
    }

    pub(crate) fn replace_tail_access_by_id(
        expr: PseudoExpr,
        subj_var_name: &str,
        subj_id: Option<VarId>,
        replacement_name: &str,
        replacement_id: VarId,
    ) -> PseudoExpr {
        replace_list_access_by_id(
            expr,
            subj_var_name,
            subj_id,
            replacement_name,
            replacement_id,
            is_tail_access_of_target,
        )
    }
}

#[cfg(test)]
mod tests;
