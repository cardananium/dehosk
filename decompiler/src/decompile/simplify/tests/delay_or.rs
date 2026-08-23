use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_commutative_binop_canonicalization() {
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::int(1)),
        right: PBox::new(PseudoExpr::var("x")),
    };

    let simplified = simplify(expr);
    dbg!(&simplified);
    match simplified {
        PseudoExpr::BinOp { left, right, .. } => {
            assert!(matches!(*left, PseudoExpr::Var { .. }));
            assert!(matches!(*right, PseudoExpr::Int(_)));
        }
        _ => panic!("expected binop"),
    }
}

#[test]
fn test_or_unwraps_delayed_rhs() {
    // a || delay(True) -> True (delay unwrapped, then x || True -> True)
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::var("a")),
        right: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Bool(true)))),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Bool(true)),
        "expected Bool(true), got: {:?}",
        simplified
    );
}

#[test]
fn test_or_unwraps_delayed_rhs_non_constant() {
    // a || delay(b) -> a || b (delay unwrapped, but no constant folding)
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::var("a")),
        right: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("b")))),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::BinOp {
            op: BinaryOp::Or,
            right,
            ..
        } => {
            assert!(matches!(*right, PseudoExpr::Var { ref name, .. } if name == "b"));
        }
        _ => panic!("expected or binop, got: {:?}", simplified),
    }
}

#[test]
fn test_delay_wrapped_or_drops_inner_delay_rhs() {
    let expr = PseudoExpr::Delay(PBox::new(PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::var("a")),
        right: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("b")))),
    }));

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Delay(inner) => match inner.as_ref() {
            PseudoExpr::BinOp {
                op: BinaryOp::Or,
                right,
                ..
            } => {
                assert!(matches!(right.as_ref(), PseudoExpr::Var { name, .. } if name == "b"));
            }
            _ => panic!("expected delayed or binop"),
        },
        _ => panic!("expected outer delay"),
    }
}
