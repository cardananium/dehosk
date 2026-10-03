//! Spell the empty-list arm of a destructure as the fall-through:
//!   `when xs is { [] -> fail   [h, ..t] -> B }`
//!     →  `when xs is { [h, ..t] -> B   _ -> fail }`
//! A list is `[]` or a cons, so the rewrite is exact. It puts a head-peeled
//! destructure in the same shape as `expect [h, ..t] = xs`, which the
//! renderer prints as a single `expect` line and which the other peeled
//! copies of the same loop already use.

use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};

use super::fold_unrolled_list_helper::{cons_binders, is_nil_pattern};
use super::scope_recurse::rewrite_bottom_up;

pub(super) fn list_fail_arm_to_wildcard(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, |node| match node {
        PseudoExpr::When {
            subject,
            subject_name,
            mut clauses,
        } if is_nil_fail_then_cons(&clauses) || is_cons_then_nil_fail(&clauses) => {
            let (nil, cons) = if is_nil_pattern(&clauses[0].pattern) {
                (clauses.remove(0), clauses.remove(0))
            } else {
                let cons = clauses.remove(0);
                (clauses.remove(0), cons)
            };
            PseudoExpr::When {
                subject,
                subject_name,
                clauses: vec![
                    cons,
                    WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: nil.body,
                    },
                ],
            }
        }
        other => other,
    })
}

fn is_nil_fail_then_cons(clauses: &[WhenClause]) -> bool {
    matches!(clauses, [nil, cons]
        if nil.guard.is_none() && cons.guard.is_none()
            && is_nil_pattern(&nil.pattern)
            && matches!(nil.body, PseudoExpr::Error { .. })
            && cons_binders(&cons.pattern).is_some())
}

fn is_cons_then_nil_fail(clauses: &[WhenClause]) -> bool {
    matches!(clauses, [cons, nil]
        if nil.guard.is_none() && cons.guard.is_none()
            && is_nil_pattern(&nil.pattern)
            && matches!(nil.body, PseudoExpr::Error { .. })
            && cons_binders(&cons.pattern).is_some())
}

#[cfg(test)]
mod tests;
