use super::*;
use crate::pseudo::ast::PBox;

// ========== Boolean constant folding tests ==========

#[test]
fn test_if_true_constant_fold() {
    // if True { a } else { b } -> a
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(true)),
        then_branch: PBox::new(PseudoExpr::var("a")),
        else_branch: PBox::new(PseudoExpr::var("b")),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "a"),
        "expected Var(a), got: {:?}",
        simplified
    );
}

#[test]
fn test_if_false_constant_fold() {
    // if False { a } else { b } -> b
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(false)),
        then_branch: PBox::new(PseudoExpr::var("a")),
        else_branch: PBox::new(PseudoExpr::var("b")),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "b"),
        "expected Var(b), got: {:?}",
        simplified
    );
}

#[test]
fn test_if_same_branches_var_condition_fold() {
    // if c { a } else { a } -> a (safe: condition is side-effect free var)
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("c")),
        then_branch: PBox::new(PseudoExpr::var("a")),
        else_branch: PBox::new(PseudoExpr::var("a")),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "a"),
        "expected Var(a), got: {:?}",
        simplified
    );
}

#[test]
fn test_if_same_branches_trace_condition_not_folded() {
    // Keep condition evaluation when it may have effects (trace).
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::string("m")),
            value: PBox::new(PseudoExpr::var("c")),
        }),
        then_branch: PBox::new(PseudoExpr::var("a")),
        else_branch: PBox::new(PseudoExpr::var("a")),
    };
    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::If { condition, .. } => {
            assert!(
                matches!(condition.as_ref(), PseudoExpr::Trace { .. }),
                "expected trace condition to be preserved, got: {:?}",
                condition
            );
        }
        _ => panic!(
            "expected If to preserve effectful condition, got: {:?}",
            simplified
        ),
    }
}

#[test]
fn test_true_and_x() {
    // True && x -> x
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::Bool(true)),
        right: PBox::new(PseudoExpr::var("x")),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "x"),
        "expected Var(x), got: {:?}",
        simplified
    );
}

#[test]
fn test_x_and_true() {
    // x && True -> x
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::var("x")),
        right: PBox::new(PseudoExpr::Bool(true)),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "x"),
        "expected Var(x), got: {:?}",
        simplified
    );
}

#[test]
fn test_false_and_x() {
    // False && x -> False
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::Bool(false)),
        right: PBox::new(PseudoExpr::var("x")),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Bool(false)),
        "expected Bool(false), got: {:?}",
        simplified
    );
}

#[test]
fn test_false_or_x() {
    // False || x -> x
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::Bool(false)),
        right: PBox::new(PseudoExpr::var("x")),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "x"),
        "expected Var(x), got: {:?}",
        simplified
    );
}

#[test]
fn test_true_or_x() {
    // True || x -> True
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::Bool(true)),
        right: PBox::new(PseudoExpr::var("x")),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Bool(true)),
        "expected Bool(true), got: {:?}",
        simplified
    );
}

#[test]
fn test_not_false() {
    // !False -> True
    let expr = PseudoExpr::UnOp {
        op: UnaryOp::Not,
        operand: PBox::new(PseudoExpr::Bool(false)),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Bool(true)),
        "expected Bool(true), got: {:?}",
        simplified
    );
}

#[test]
fn test_not_true() {
    // !True -> False
    let expr = PseudoExpr::UnOp {
        op: UnaryOp::Not,
        operand: PBox::new(PseudoExpr::Bool(true)),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Bool(false)),
        "expected Bool(false), got: {:?}",
        simplified
    );
}

#[test]
fn test_not_comparison_flips_and_non_comparison_keeps_not() {
    let comparison = PseudoExpr::UnOp {
        op: UnaryOp::Not,
        operand: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Lt,
            left: PBox::new(PseudoExpr::var("a")),
            right: PBox::new(PseudoExpr::int(3)),
        }),
    };
    let simplified = simplify(comparison);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::BinOp {
                op: BinaryOp::Gte,
                left,
                right,
            } if matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == "a")
                && matches!(right.as_ref(), PseudoExpr::Int(n) if *n == 3.into())
        ),
        "expected !Lt to flip to Gte, got: {simplified:?}"
    );

    let non_comparison = PseudoExpr::UnOp {
        op: UnaryOp::Not,
        operand: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::int(1)),
            right: PBox::new(PseudoExpr::int(2)),
        }),
    };
    let simplified = simplify(non_comparison);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand,
            } if matches!(operand.as_ref(), PseudoExpr::BinOp { op: BinaryOp::Add, .. })
        ),
        "expected !Add to stay wrapped in Not, got: {simplified:?}"
    );
}
