//! Rewrite the 3-arg `expect!` form whose `args[2]` is non-string
//! to `If`.
//!
//! The chain renderer treats `args[2]` of a 3-arg `expect!` as the
//! fail-message (`expect cond, @"msg"; body`), so a non-`String`
//! `args[2]` renders as invalid surface syntax.
//!
//! That shape is a church-Bool eliminator: UPLC encodes
//! `if cond { then } else { else }` as `cond(then)(else)` with
//! `True = λt.λe.t` and `False = λt.λe.e`, and lowering left it as
//! `Apply(Var "expect!", [cond, then, else])` instead of an `If`.
//!
//! All four gates must hold; any other shape is left alone:
//! - Function is `Var{name:"expect!", id:None}` (the simplifier's
//!   synthetic helper).
//! - `args.len() == 3`.
//! - `args[2]` is not `PseudoExpr::String` — that is the fail-message
//!   sugar.
//! - `args[0]` is structurally Bool: `BinOp::{Eq,Neq,Lt,Lte,Gt,
//!   Gte,And,Or}`, `Bool` literal, or `UnOp::Not(<structurally_bool>)`
//!   but not `UnOp::Not(Let{..})`.
//!
//! After `lift_let_through_expect`, which lifts the `Let` out of
//! `Not(Let ...)` in `args[0]`, leaving a `Not(body)` this pass can
//! fire on.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr, UnaryOp};
use crate::pseudo::fold::ExprFolder;

/// Convert 3-arg `expect!(c, t, e)` with non-String `e`
/// to `If { c, t, e }` when `c` is structurally Bool.
pub(super) fn rewrite_expect_three_arg_conditional(expr: PseudoExpr) -> PseudoExpr {
    struct ThreeArgFolder;

    impl ExprFolder for ThreeArgFolder {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
            if args.len() == 3
                && is_bare_expect_helper(&function)
                && !matches!(args[2], PseudoExpr::String(_))
                && is_structurally_bool(&args[0])
            {
                let mut iter = args.into_iter();
                let condition = iter.next().unwrap();
                let then_branch = iter.next().unwrap();
                let else_branch = iter.next().unwrap();
                return PseudoExpr::If {
                    condition: PBox::new(condition),
                    then_branch: PBox::new(then_branch),
                    else_branch: PBox::new(else_branch),
                };
            }
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
    }

    ThreeArgFolder.fold(expr)
}

/// Returns `true` when `expr` is the bare synthetic `expect!`
/// helper (id None) — the same gate as `expect_field_access`.
fn is_bare_expect_helper(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Var { name, id: None } if name.as_str() == "expect!"
    )
}

/// Returns `true` when `expr` is structurally Bool-typed:
/// a comparison (Eq, Neq, Lt, Lte, Gt, Gte), And, Or, a
/// `Bool` literal, or `UnOp::Not(<structurally_bool>)` — but
/// NOT `Not(Let{..})`, which `lift_let_through_expect`
/// handles first.
///
/// Bare `Var` is deliberately excluded: too weak a signal, it
/// would fire on identity references to any-typed bindings.
fn is_structurally_bool(expr: &PseudoExpr) -> bool {
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::BinOp { op, .. } => {
                return matches!(
                    op,
                    BinaryOp::Eq
                        | BinaryOp::Neq
                        | BinaryOp::Lt
                        | BinaryOp::Lte
                        | BinaryOp::Gt
                        | BinaryOp::Gte
                        | BinaryOp::And
                        | BinaryOp::Or
                );
            }
            PseudoExpr::Bool(_) => return true,
            // Narrow inclusion: `Not(x)` is Bool-typed iff `x` is.
            // `Not(Let{..})` belongs to `lift_let_through_expect`,
            // which runs first, so any `Not(Let)` is already lifted.
            PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand,
            } => {
                if matches!(operand.as_ref(), PseudoExpr::Let { .. }) {
                    return false;
                }
                current = operand;
            }
            _ => return false,
        }
    }
}

#[cfg(test)]
mod tests;
