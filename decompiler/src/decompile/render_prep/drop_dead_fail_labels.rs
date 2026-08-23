//! Drop `let X = fail @"L<line>;<col>"` bindings whose binder is unused.
//!
//! MIR lowering can hoist source-map error labels out of position, leaving
//! `let X = fail @"L155;3"` chains at the top of a validator body that
//! shadow every short single-letter binder below. When the binder is never
//! referenced, the `let` is pure noise.
//!
//! Criteria:
//! 1. RHS is *exactly* `PseudoExpr::Error { message: Some(msg) }` (no
//!    wrapping/composition).
//! 2. `msg` matches the source-label pattern `L<digits>;<digits>`.
//! 3. The binder is **not** referenced anywhere in the surviving body
//!    (scope-aware free-variable check).
//!
//! On match the `Let` collapses to its body; nothing references the binder,
//! so the `fail` was unreachable.

use super::let_disambiguation::pattern_binds_name;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::{ExprFolder, ExprVisitor};
use crate::pseudo::var_id::VarId;

pub(super) fn drop_dead_fail_labels(expr: PseudoExpr) -> PseudoExpr {
    walk(expr)
}

fn walk(expr: PseudoExpr) -> PseudoExpr {
    struct DropDeadFailLabels;

    impl ExprFolder for DropDeadFailLabels {
        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            pattern
        }

        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            // A `fail` RHS holds no nested labels; other RHS shapes can.
            if is_source_label_fail(&value) && !expr_contains_name(&body, &name) {
                body
            } else {
                PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                }
            }
        }
    }

    DropDeadFailLabels.fold(expr)
}

fn is_source_label_fail(value: &PseudoExpr) -> bool {
    matches!(value, PseudoExpr::Error { message: Some(msg) } if is_source_label(msg))
}

/// Match `L<digits>;<digits>` — the MIR source-map error label format.
fn is_source_label(msg: &str) -> bool {
    let Some(rest) = msg.strip_prefix('L') else {
        return false;
    };
    let Some((line, col)) = rest.split_once(';') else {
        return false;
    };
    !line.is_empty()
        && line.chars().all(|c| c.is_ascii_digit())
        && !col.is_empty()
        && col.chars().all(|c| c.is_ascii_digit())
}

/// Scope-aware free-variable check: `true` if `target` appears as a `Var`
/// reference in `expr` not shadowed by an intervening Let / Lambda /
/// RecFn / when-clause pattern binding the same name.
fn expr_contains_name(expr: &PseudoExpr, target: &str) -> bool {
    struct ContainsVarVisitor<'a> {
        target: &'a str,
        blocked_depth: usize,
        found: bool,
    }

    impl ExprVisitor for ContainsVarVisitor<'_> {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            if self.blocked_depth == 0 && name == self.target {
                self.found = true;
            }
        }

        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            if params.iter().any(|p| p == self.target) {
                self.blocked_depth += 1;
            }
        }
        fn visit_lambda_post(&mut self, params: &[Binder]) {
            if params.iter().any(|p| p == self.target) {
                self.blocked_depth -= 1;
            }
        }

        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            if name == self.target || params.iter().any(|p| p == self.target) {
                self.blocked_depth += 1;
            }
        }
        fn visit_recfn_post(&mut self, name: &Binder, params: &[Binder]) {
            if name == self.target || params.iter().any(|p| p == self.target) {
                self.blocked_depth -= 1;
            }
        }

        fn visit_let_value_post(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) {
            if name == self.target {
                self.blocked_depth += 1;
            }
        }
        fn visit_let_post(&mut self, name: &str) {
            if name == self.target {
                self.blocked_depth -= 1;
            }
        }

        fn visit_when_clause_pre(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            let subject_binds_target = subject_name.is_some_and(|n| n == self.target);
            let pattern_binds_target = pattern_binds_name(&clause.pattern, self.target);
            if subject_binds_target || pattern_binds_target {
                self.blocked_depth += 1;
            }
        }
        fn visit_when_clause_post(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            let subject_binds_target = subject_name.is_some_and(|n| n == self.target);
            let pattern_binds_target = pattern_binds_name(&clause.pattern, self.target);
            if subject_binds_target || pattern_binds_target {
                self.blocked_depth -= 1;
            }
        }
    }

    let mut visitor = ContainsVarVisitor {
        target,
        blocked_depth: 0,
        found: false,
    };
    visitor.walk(expr);
    visitor.found
}

#[cfg(test)]
mod tests;
