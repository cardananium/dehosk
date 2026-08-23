use super::Simplifier;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, UnaryOp};

impl Simplifier {
    pub(super) fn try_simplify_if_expect(
        cond: &PseudoExpr,
        then_branch: &PseudoExpr,
        else_branch: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        // expect pattern: if cond { value } else { fail }. Fail messages
        // lift into the 3-arg expect! shape so the printer can render
        // `expect! cond, @"msg"`. When cond is already a `when` with a
        // guardless wildcard-fail clause and then_branch is Void, that
        // when encodes the fail semantics itself and is the result.
        if Self::is_fail(else_branch) && !Self::is_fail(then_branch) {
            if Self::when_has_guardless_wildcard_fail(cond) && Self::is_void(then_branch) {
                return Some(cond.clone());
            }
            let mut args = vec![cond.clone(), then_branch.clone()];
            if let Some(msg) = Self::fail_message(else_branch) {
                args.push(PseudoExpr::String(msg.to_string()));
            }
            return Some(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::expect_helper()),
                args: args.into(),
            });
        }

        // if cond { fail } else { value } -> expect !cond; value.
        // Keep the explicit `!cond`; do not invert the comparison, since these
        // expect rewrites mirror the source shape.
        if Self::is_fail(then_branch) && !Self::is_fail(else_branch) {
            let msg = Self::fail_message(then_branch).map(|m| m.to_string());
            let mut args = vec![
                PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand: PBox::new(cond.clone()),
                },
                else_branch.clone(),
            ];
            if let Some(msg) = msg {
                args.push(PseudoExpr::String(msg));
            }
            return Some(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::expect_helper()),
                args: args.into(),
            });
        }

        None
    }
}
