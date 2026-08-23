//! Reverse the pathological `If { condition: <Lambda/RecFn>, then,
//! else }` that an over-eager church/Scott conditional recognizer
//! leaves behind.
//!
//! A native `if` requires a `Bool` condition. The recognizer
//! consumed an `Apply(<eliminator>, [then, else])` and took the
//! eliminator for the condition, so the surface is invalid: a
//! function is not a `Bool`, and the lambda's body brace abuts the
//! then-block brace.
//!
//! Restore the church-application form `Apply(<eliminator>, [then,
//! else])` — not the pre-recognition MIR
//! `Builtin(IfThenElse, [cond, then, else])`, but its church/Scott
//! equivalent: an encoded conditional computes `b then else` by
//! applying the encoded value to its branches. Downstream
//! `beta_reduce_lambda_apply` folds the immediately-applied lambda
//! into a `let`-chain when arity allows.
//!
//! Fires only when the condition (after stripping `Force` wrappers)
//! is a `Lambda` or `RecFn` — never a `Bool`, so the `If` was
//! definitionally malformed. Both branches must be `is_pure_value`:
//! the native `if` evaluates one branch lazily, the restored
//! `Apply` passes both eagerly. For pure branches that is
//! unobservable; otherwise the malformed `If` is left alone.

use crate::pseudo::ast::PseudoExpr;

use super::purity::is_pure_value;
use super::scope_recurse::rewrite_bottom_up;

pub(super) fn undo_if_on_function_condition(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_undo)
}

fn try_undo(expr: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = expr
    else {
        return expr;
    };
    if condition_is_function(&condition)
        && is_pure_value(&then_branch)
        && is_pure_value(&else_branch)
    {
        return PseudoExpr::Apply {
            function: condition,
            args: vec![then_branch.into_inner(), else_branch.into_inner()].into(),
        };
    }
    PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    }
}

/// True when `expr` (after peeling `Force` wrappers) is a `Lambda`
/// or `RecFn` — a value that is never a valid `Bool` condition.
fn condition_is_function(expr: &PseudoExpr) -> bool {
    let mut cur = expr;
    while let PseudoExpr::Force(inner) = cur {
        cur = inner.as_ref();
    }
    matches!(cur, PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. })
}

#[cfg(test)]
mod tests;
