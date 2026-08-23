use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::var_id::VarId;

fn int(n: i64) -> PseudoExpr {
    PseudoExpr::Int(BigInt::from(n))
}
fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}
fn binop(op: BinaryOp, l: PseudoExpr, r: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BinOp {
        op,
        left: PBox::new(l),
        right: PBox::new(r),
    }
}

#[test]
fn add_zero_folds_either_side() {
    assert_eq!(
        fold_arith_identity(binop(BinaryOp::Add, var("x", 1), int(0))),
        var("x", 1)
    );
    assert_eq!(
        fold_arith_identity(binop(BinaryOp::Add, int(0), var("x", 1))),
        var("x", 1)
    );
}

#[test]
fn sub_zero_folds_right_only() {
    assert_eq!(
        fold_arith_identity(binop(BinaryOp::Sub, var("x", 1), int(0))),
        var("x", 1)
    );
    // `0 - x` is negation, NOT an identity — left unchanged.
    let neg = binop(BinaryOp::Sub, int(0), var("x", 1));
    assert_eq!(fold_arith_identity(neg.clone()), neg);
}

#[test]
fn mul_one_folds_either_side() {
    assert_eq!(
        fold_arith_identity(binop(BinaryOp::Mul, var("x", 1), int(1))),
        var("x", 1)
    );
    assert_eq!(
        fold_arith_identity(binop(BinaryOp::Mul, int(1), var("x", 1))),
        var("x", 1)
    );
}

#[test]
fn mul_zero_not_folded() {
    // Folding would drop the other operand's evaluation — keep as-is.
    let e = binop(BinaryOp::Mul, var("x", 1), int(0));
    assert_eq!(fold_arith_identity(e.clone()), e);
}

#[test]
fn idempotent_and_same_var_folds() {
    assert_eq!(
        fold_arith_identity(binop(BinaryOp::And, var("a", 7), var("a", 7))),
        var("a", 7)
    );
}

#[test]
fn and_different_vars_unchanged() {
    // Same display name, different VarId → NOT folded.
    let e = binop(BinaryOp::And, var("a", 7), var("a", 8));
    assert_eq!(fold_arith_identity(e.clone()), e);
    // Non-Var operands (possible effects) → NOT folded even if equal-looking.
    let calls = binop(
        BinaryOp::And,
        PseudoExpr::var_with_id("f", VarId::new(1)),
        int(5),
    );
    assert_eq!(fold_arith_identity(calls.clone()), calls);
}

#[test]
fn idempotent_and_right_assoc_chain_dedup() {
    // a && (a && rest)  →  a && rest   (right-assoc `a && a && rest`)
    let rest = var("rest", 9);
    let inner = binop(BinaryOp::And, var("a", 7), rest.clone());
    let chain = binop(BinaryOp::And, var("a", 7), inner);
    let expected = binop(BinaryOp::And, var("a", 7), rest);
    assert_eq!(fold_arith_identity(chain), expected);
    // different head var in the chain → unchanged
    let inner2 = binop(BinaryOp::And, var("b", 8), var("rest", 9));
    let chain2 = binop(BinaryOp::And, var("a", 7), inner2);
    assert_eq!(fold_arith_identity(chain2.clone()), chain2);
}

#[test]
fn folds_nested_operands_bottom_up() {
    // (x + 0) + 0  →  x
    let inner = binop(BinaryOp::Add, var("x", 1), int(0));
    let outer = binop(BinaryOp::Add, inner, int(0));
    assert_eq!(fold_arith_identity(outer), var("x", 1));
}
