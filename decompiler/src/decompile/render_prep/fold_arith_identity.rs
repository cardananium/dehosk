//! Fold arithmetic/boolean identities that survive lowering:
//!   `x + 0` / `0 + x` / `x - 0`  →  `x`
//!   `x * 1` / `1 * x`            →  `x`
//!   `a && a` (identical pure Var) →  `a`
//!
//! Always-on and semantics-preserving: the kept operand is still evaluated, so
//! no identity drops an effect, e.g. the UPLC error in `un_i_data(bad) + 0`.
//! The `&&` fold needs both sides to be the same pure `Var` (by VarId, not
//! display name), so it never drops a distinct operand's effect or `trace`.
//! `x * 0` is not folded: that would drop the other operand's evaluation.

use crate::pseudo::ast::PBox;
use num_bigint::BigInt;

use crate::pseudo::ast::{BinaryOp, PseudoExpr};

use super::scope_recurse::rewrite_bottom_up;

/// Bottom-up: fold children first, then re-examine this node.
pub(super) fn fold_arith_identity(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_fold)
}

fn try_fold(expr: PseudoExpr) -> PseudoExpr {
    match expr {
        PseudoExpr::BinOp { op, left, right } => fold_binop(op, left, right),
        other => other,
    }
}

fn is_int(e: &PseudoExpr, n: i64) -> bool {
    matches!(e, PseudoExpr::Int(v) if *v == BigInt::from(n))
}

/// Both expressions are the SAME variable, identified by VarId (never by the
/// display name — disambiguation can give distinct vars the same name).
fn same_pure_var(a: &PseudoExpr, b: &PseudoExpr) -> bool {
    matches!(
        (a, b),
        (
            PseudoExpr::Var { id: Some(x), .. },
            PseudoExpr::Var { id: Some(y), .. },
        ) if x == y
    )
}

fn fold_binop(op: BinaryOp, left: PBox, right: PBox) -> PseudoExpr {
    match op {
        // Additive identity (kept operand still evaluated; +0 / -0 is a no-op).
        BinaryOp::Add if is_int(&right, 0) => left.into_inner(),
        BinaryOp::Add if is_int(&left, 0) => right.into_inner(),
        BinaryOp::Sub if is_int(&right, 0) => left.into_inner(),
        // Multiplicative identity.
        BinaryOp::Mul if is_int(&right, 1) => left.into_inner(),
        BinaryOp::Mul if is_int(&left, 1) => right.into_inner(),
        BinaryOp::And => fold_and(left, right),
        _ => PseudoExpr::BinOp { op, left, right },
    }
}

/// Idempotent `&&` on identical PURE Var refs: the direct `a && a → a`
/// and the right-associated chain `a && (a && rest) → a && rest`. Sound
/// because `&&` short-circuits and `a` is a pure Var, so re-evaluating it
/// yields the same value — no effect or `trace` is dropped.
fn fold_and(left: PBox, right: PBox) -> PseudoExpr {
    if same_pure_var(&left, &right) {
        return left.into_inner();
    }
    // `a && (a && rest)` → `a && rest`: the chain's head duplicates `left`.
    let chain_dup = matches!(
        right.as_ref(),
        PseudoExpr::BinOp { op: BinaryOp::And, left: inner_left, .. }
            if same_pure_var(&left, inner_left)
    );
    if chain_dup {
        let inner = right.into_inner();
        if let PseudoExpr::BinOp {
            right: inner_right, ..
        } = inner
        {
            return PseudoExpr::BinOp {
                op: BinaryOp::And,
                left,
                right: inner_right,
            };
        }
        return PseudoExpr::BinOp {
            op: BinaryOp::And,
            left,
            right: PBox::new(inner),
        };
    }
    PseudoExpr::BinOp {
        op: BinaryOp::And,
        left,
        right,
    }
}

#[cfg(test)]
mod tests;
