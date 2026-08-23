use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::var_id::VarId;

/// Simple shape: `expect!(!(let X = v in body), tail)` lifts the
/// let out to `let X = v; expect!(!body, tail)`.
#[test]
fn d2_lifts_simple_expect_not_let() {
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand: PBox::new(PseudoExpr::let_bind_with_id(
                    "X",
                    x_id,
                    PseudoExpr::Int(1.into()),
                    PseudoExpr::Bool(true),
                )),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let result = lift_let_through_expect(expr);
    // Expect: Let { X, 1, Apply(expect!, [Not(true), Unit]) }
    let PseudoExpr::Let {
        name, value, body, ..
    } = result
    else {
        panic!("expected Let at top level")
    };
    assert_eq!(name, "X");
    assert!(matches!(value.as_ref(), PseudoExpr::Int(_)));
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        panic!("expected Apply inside Let body")
    };
    assert!(matches!(function.as_ref(),
        PseudoExpr::Var { name, .. } if name == "expect!"));
    assert_eq!(args.len(), 2);
    let PseudoExpr::UnOp {
        op: UnaryOp::Not,
        operand,
    } = &args[0]
    else {
        panic!("expected Not(body)")
    };
    assert!(matches!(operand.as_ref(), PseudoExpr::Bool(true)));
    assert!(matches!(args[1], PseudoExpr::Unit));
}

/// Shape A: bare `Let` (no `Not`) in cond position lifts to
/// `let X = v; expect <body>; <tail>` — valid surface syntax.
#[test]
fn d2_lifts_bare_let_in_cond_position() {
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::let_bind_with_id(
                "X",
                x_id,
                PseudoExpr::Int(1.into()),
                PseudoExpr::Bool(true),
            ),
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let result = lift_let_through_expect(expr);
    // Expect: Let { X, 1, Apply(expect!, [Bool(true), Unit]) }
    let PseudoExpr::Let {
        name, value, body, ..
    } = result
    else {
        panic!("expected Let at top level");
    };
    assert_eq!(name, "X");
    assert!(matches!(value.as_ref(), PseudoExpr::Int(_)));
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        panic!("expected Apply inside Let body");
    };
    assert!(matches!(function.as_ref(),
        PseudoExpr::Var { name, .. } if name == "expect!"));
    assert_eq!(args.len(), 2);
    // First arg is the let body (Bool(true)) — NOT wrapped
    // in Not (that is Shape B's path).
    assert!(matches!(&args[0], PseudoExpr::Bool(true)));
    assert!(matches!(args[1], PseudoExpr::Unit));
}

/// Shape A safety: bare Let whose binder is referenced in
/// the tail — refuse to lift.
#[test]
fn d2_does_not_lift_bare_let_when_tail_references_binder() {
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::let_bind_with_id(
                "X",
                x_id,
                PseudoExpr::Int(1.into()),
                PseudoExpr::Bool(true),
            ),
            PseudoExpr::var_with_id("X", x_id),
        ]
        .into(),
    };
    let result = lift_let_through_expect(expr.clone());
    assert!(matches!(result, PseudoExpr::Apply { .. }));
}

/// Safety: a let-binder free in the tail (`args[1]`) must NOT be
/// lifted — that would capture it. The renderer then emits the
/// invalid `expect !let ...` rather than miscompiling silently.
#[test]
fn d2_does_not_lift_when_tail_references_let_binder() {
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand: PBox::new(PseudoExpr::let_bind_with_id(
                    "X",
                    x_id,
                    PseudoExpr::Int(1.into()),
                    PseudoExpr::Bool(true),
                )),
            },
            // tail references X — must not lift.
            PseudoExpr::var_with_id("X", x_id),
        ]
        .into(),
    };
    let result = lift_let_through_expect(expr.clone());
    // No lift — top level is still Apply.
    assert!(matches!(result, PseudoExpr::Apply { .. }));
}

/// 3-arg `expect!(cond, body, msg)` also lifts the let; the msg
/// arg (fail-message sugar, `expect cond, @"msg"; body`) rides
/// along unchanged.
#[test]
fn d2_lifts_three_arg_expect_form() {
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand: PBox::new(PseudoExpr::let_bind_with_id(
                    "X",
                    x_id,
                    PseudoExpr::Int(1.into()),
                    PseudoExpr::Bool(true),
                )),
            },
            PseudoExpr::Unit,
            PseudoExpr::String("msg".to_string()),
        ]
        .into(),
    };
    let result = lift_let_through_expect(expr.clone());
    // Top-level should be a Let now.
    let PseudoExpr::Let { name, body, .. } = result else {
        panic!("expected Let at top level after 3-arg lift");
    };
    assert_eq!(name, "X");
    // Body remains a 3-arg Apply with the message preserved.
    let PseudoExpr::Apply { args, .. } = body.as_ref() else {
        panic!("expected Apply inside Let body");
    };
    assert_eq!(args.len(), 3, "msg arg must be preserved");
    assert!(matches!(&args[2], PseudoExpr::String(s) if s == "msg"));
}

#[test]
fn d2_lifts_inside_lambda_body() {
    let x_id = VarId::fresh_binding();
    let param_id = VarId::fresh_binding();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("p", param_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("expect!")),
            args: vec![
                PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand: PBox::new(PseudoExpr::let_bind_with_id(
                        "X",
                        x_id,
                        PseudoExpr::Int(7.into()),
                        PseudoExpr::Bool(false),
                    )),
                },
                PseudoExpr::Unit,
            ]
            .into(),
        }),
    };
    let result = lift_let_through_expect(expr);
    let PseudoExpr::Lambda { body, .. } = result else {
        panic!("expected Lambda");
    };
    assert!(matches!(body.as_ref(), PseudoExpr::Let { name, .. } if name == "X"));
}

/// When `cond` is `Not(<not-Let>)`, no lift — the pass fires
/// only on the `Not(Let(...))` shape.
#[test]
fn d2_does_not_lift_when_not_is_over_non_let_expression() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::UnOp {
                op: UnaryOp::Not,
                // operand is NOT a Let — it's a Bool literal.
                operand: PBox::new(PseudoExpr::Bool(true)),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let result = lift_let_through_expect(expr.clone());
    assert!(matches!(result, PseudoExpr::Apply { .. }));
}
