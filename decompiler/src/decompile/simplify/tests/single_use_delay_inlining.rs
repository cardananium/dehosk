use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_single_force_dethunk_non_closed_capture_safe() {
    // let k = delay(f(x)) in force(k) -> f(x)
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::var("x")].into(),
        }))),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("k")))),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Apply { .. }),
        "expected inlined apply, got: {:?}",
        simplified
    );
}

#[test]
fn test_single_force_dethunk_non_closed_capture_unsafe_not_inlined() {
    // let k = delay(f(x)) in fn(x) { Pair(force(k), x) }
    // Inlining would capture x from lambda scope, so keep the let.
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::var("x")].into(),
        }))),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::Pair(
                PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("k")))),
                PBox::new(PseudoExpr::var("x")),
            )),
        }),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Let { .. }),
        "expected let to remain to avoid capture, got: {:?}",
        simplified
    );
}

#[test]
fn test_single_force_dethunk_delay_when_non_closed() {
    // let d = delay(when y is { Some(x) -> x; None -> z }) in force(d)
    // > when y is { Some(x) -> x; None -> z }
    let expr = PseudoExpr::Let {
        name: "d".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("y")),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::Some, vec!["x".into()]),
                    PseudoExpr::var("x"),
                ),
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                    PseudoExpr::var("z"),
                ),
            ],
        }))),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("d")))),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::When { .. }),
        "expected inlined when expression, got: {:?}",
        simplified
    );
}

#[test]
fn test_single_use_large_delay_bool_expr_inlined() {
    // let y = delay(fn_21(a,b,c,d) == 1) in x && y
    // should inline y even when delayed value is larger than tiny-expression budget.
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("fn_21")),
                args: vec![
                    PseudoExpr::var("a"),
                    PseudoExpr::var("b"),
                    PseudoExpr::var("c"),
                    PseudoExpr::var("d"),
                ]
                .into(),
            }),
            right: PBox::new(PseudoExpr::int(1)),
        }))),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(PseudoExpr::var("x")),
            right: PBox::new(PseudoExpr::var("y")),
        }),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            simplified,
            PseudoExpr::BinOp {
                op: BinaryOp::And,
                ..
            }
        ),
        "expected inlined boolean binop, got: {:?}",
        simplified
    );
}

#[test]
fn test_delay_lambda_not_single_use_inlined() {
    // let k = delay(fn(a) { a }) in body_using_k_once
    // Delay(Lambda) is excluded from single-use inlining to avoid reintroducing an IIFE.
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec!["a".to_string().into()],
            body: PBox::new(PseudoExpr::var("a")),
        }))),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("g")),
            args: vec![PseudoExpr::var("k")].into(),
        }),
    };

    let simplified = simplify(expr);
    // The let should remain because Delay(Lambda) is excluded
    assert!(
        matches!(simplified, PseudoExpr::Let { .. }),
        "expected let to remain for Delay(Lambda), got: {:?}",
        simplified
    );
}
