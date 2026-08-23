use super::*;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::var_id::VarId;

fn expect_apply(args: Vec<PseudoExpr>) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "expect!".to_string(),
            id: None,
        }),
        args: args.into(),
    }
}

fn bool_eq(left: PseudoExpr, right: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(left),
        right: PBox::new(right),
    }
}

/// D3 positive: `expect!(q == 0, then, else)` with else not a
/// String → `if q == 0 { then } else { else }`.
#[test]
fn d3_rewrites_when_cond_is_eq_and_else_is_apply() {
    let input = expect_apply(vec![
        bool_eq(
            PseudoExpr::Var {
                name: "q".to_string(),
                id: Some(VarId::fresh_binding()),
            },
            PseudoExpr::Int(0.into()),
        ),
        PseudoExpr::Var {
            name: "choose_fst".to_string(),
            id: Some(VarId::fresh_binding()),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Var {
                name: "f_33".to_string(),
                id: Some(VarId::fresh_binding()),
            }),
            args: vec![PseudoExpr::Int(1.into())].into(),
        },
    ]);
    let out = rewrite_expect_three_arg_conditional(input);
    match out {
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            assert!(matches!(
                *condition,
                PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    ..
                }
            ));
            assert!(matches!(
                *then_branch,
                PseudoExpr::Var { ref name, .. } if name == "choose_fst"
            ));
            assert!(matches!(*else_branch, PseudoExpr::Apply { .. }));
        }
        other => panic!("expected If, got {other:?}"),
    }
}

/// D3 positive: Bool literal as condition (degenerate but
/// structurally valid).
#[test]
fn d3_rewrites_when_cond_is_bool_literal() {
    let input = expect_apply(vec![
        PseudoExpr::Bool(true),
        PseudoExpr::Int(1.into()),
        PseudoExpr::Int(2.into()),
    ]);
    let out = rewrite_expect_three_arg_conditional(input);
    assert!(matches!(out, PseudoExpr::If { .. }));
}

/// D3 positive: any Bool-typed `BinOp` fires.
#[test]
fn d3_rewrites_when_cond_is_and_or() {
    for op in [
        BinaryOp::And,
        BinaryOp::Or,
        BinaryOp::Neq,
        BinaryOp::Lt,
        BinaryOp::Gte,
    ] {
        let label = format!("{op:?}");
        let input = expect_apply(vec![
            PseudoExpr::BinOp {
                op,
                left: PBox::new(PseudoExpr::Bool(true)),
                right: PBox::new(PseudoExpr::Bool(false)),
            },
            PseudoExpr::Int(1.into()),
            PseudoExpr::Int(2.into()),
        ]);
        let out = rewrite_expect_three_arg_conditional(input);
        assert!(
            matches!(out, PseudoExpr::If { .. }),
            "op {label} should fire"
        );
    }
}

/// D3 refusal: a `String` `args[2]` is fail-message sugar.
#[test]
fn d3_refuses_when_args2_is_string_literal() {
    let input = expect_apply(vec![
        bool_eq(
            PseudoExpr::Var {
                name: "q".to_string(),
                id: Some(VarId::fresh_binding()),
            },
            PseudoExpr::Int(0.into()),
        ),
        PseudoExpr::Int(1.into()),
        PseudoExpr::String("fail message".to_string()),
    ]);
    let out = rewrite_expect_three_arg_conditional(input.clone());
    // Must be unchanged — fail-message sugar.
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

/// D3 refusal: a bare `Var` `args[0]` is too weak a signal.
#[test]
fn d3_refuses_when_args0_is_bare_var() {
    let input = expect_apply(vec![
        PseudoExpr::Var {
            name: "some_var".to_string(),
            id: Some(VarId::fresh_binding()),
        },
        PseudoExpr::Int(1.into()),
        PseudoExpr::Int(2.into()),
    ]);
    let out = rewrite_expect_three_arg_conditional(input);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

/// D3 refusal: `args[0]` is `UnOp::Not(Let{...})` —
/// `lift_let_through_expect` lifts the `Let` out first,
/// leaving a `Not(body)` D3 can fire on.
#[test]
fn d3_refuses_when_args0_is_not_of_let() {
    use crate::pseudo::ast::UnaryOp;
    let input = expect_apply(vec![
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand: PBox::new(PseudoExpr::Let {
                name: "x".to_string(),
                id: None,
                value: PBox::new(PseudoExpr::Bool(true)),
                body: PBox::new(PseudoExpr::Bool(false)),
            }),
        },
        PseudoExpr::Int(1.into()),
        PseudoExpr::Int(2.into()),
    ]);
    let out = rewrite_expect_three_arg_conditional(input);
    // Unchanged — `Not(Let)` belongs to
    // `lift_let_through_expect`.
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

/// D3 positive: `args[0]` is `UnOp::Not(BinOp::Eq(..))` —
/// Bool-typed via narrow inclusion. Fires.
#[test]
fn d3_rewrites_when_args0_is_not_of_eq() {
    use crate::pseudo::ast::UnaryOp;
    let input = expect_apply(vec![
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand: PBox::new(bool_eq(
                PseudoExpr::Var {
                    name: "q".to_string(),
                    id: Some(VarId::fresh_binding()),
                },
                PseudoExpr::Int(0.into()),
            )),
        },
        PseudoExpr::Int(1.into()),
        PseudoExpr::Int(2.into()),
    ]);
    let out = rewrite_expect_three_arg_conditional(input);
    match out {
        PseudoExpr::If { condition, .. } => {
            assert!(matches!(
                *condition,
                PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    ..
                }
            ));
        }
        other => panic!("expected If, got {other:?}"),
    }
}

/// D3 positive: `args[0]` is `UnOp::Not(Bool literal)` —
/// Bool-typed via narrow inclusion. Fires.
#[test]
fn d3_rewrites_when_args0_is_not_of_bool_literal() {
    use crate::pseudo::ast::UnaryOp;
    let input = expect_apply(vec![
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand: PBox::new(PseudoExpr::Bool(true)),
        },
        PseudoExpr::Int(1.into()),
        PseudoExpr::Int(2.into()),
    ]);
    let out = rewrite_expect_three_arg_conditional(input);
    assert!(matches!(out, PseudoExpr::If { .. }));
}

/// D3 refusal: `Not(Apply{..})` — the operand's type is
/// unknown, so D3 refuses rather than guess.
#[test]
fn d3_refuses_when_not_operand_is_not_structurally_bool() {
    use crate::pseudo::ast::UnaryOp;
    let input = expect_apply(vec![
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: "f".to_string(),
                    id: Some(VarId::fresh_binding()),
                }),
                args: vec![].into(),
            }),
        },
        PseudoExpr::Int(1.into()),
        PseudoExpr::Int(2.into()),
    ]);
    let out = rewrite_expect_three_arg_conditional(input);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

/// D3 refusal: the 2-arg form is a standard expect-chain.
#[test]
fn d3_refuses_2_arg_form() {
    let input = expect_apply(vec![
        bool_eq(
            PseudoExpr::Var {
                name: "q".to_string(),
                id: Some(VarId::fresh_binding()),
            },
            PseudoExpr::Int(0.into()),
        ),
        PseudoExpr::Int(1.into()),
    ]);
    let out = rewrite_expect_three_arg_conditional(input);
    match out {
        PseudoExpr::Apply { args, .. } => assert_eq!(args.len(), 2),
        other => panic!("expected Apply, got {other:?}"),
    }
}

/// D3 refusal: function name "expect!" but with `Some(id)`
/// (concrete VarId) — not the synthetic helper.
#[test]
fn d3_refuses_when_expect_has_concrete_var_id() {
    let id = VarId::fresh_binding();
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "expect!".to_string(),
            id: Some(id),
        }),
        args: vec![
            bool_eq(
                PseudoExpr::Var {
                    name: "q".to_string(),
                    id: Some(VarId::fresh_binding()),
                },
                PseudoExpr::Int(0.into()),
            ),
            PseudoExpr::Int(1.into()),
            PseudoExpr::Int(2.into()),
        ]
        .into(),
    };
    let out = rewrite_expect_three_arg_conditional(input);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

#[test]
fn d3_refuses_when_function_is_not_expect_helper() {
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "other".to_string(),
            id: None,
        }),
        args: vec![
            PseudoExpr::Bool(true),
            PseudoExpr::Int(1.into()),
            PseudoExpr::Int(2.into()),
        ]
        .into(),
    };
    let out = rewrite_expect_three_arg_conditional(input);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

/// D3: nested — the pass walks bottom-up via ExprFolder, so a
/// 3-arg expect!() inside a let value still gets rewritten.
#[test]
fn d3_rewrites_inside_let_value() {
    let input = PseudoExpr::Let {
        name: "result".to_string(),
        id: None,
        value: PBox::new(expect_apply(vec![
            PseudoExpr::Bool(true),
            PseudoExpr::Int(1.into()),
            PseudoExpr::Int(2.into()),
        ])),
        body: PBox::new(PseudoExpr::Var {
            name: "result".to_string(),
            id: None,
        }),
    };
    let out = rewrite_expect_three_arg_conditional(input);
    match out {
        PseudoExpr::Let { value, .. } => {
            assert!(matches!(*value, PseudoExpr::If { .. }));
        }
        other => panic!("expected Let preserved, got {other:?}"),
    }
}

/// D3 idempotence: after the first rewrite the AST is `If`,
/// so the second pass finds no 3-arg `expect!` to rewrite.
#[test]
fn d3_is_idempotent() {
    let input = expect_apply(vec![
        PseudoExpr::Bool(true),
        PseudoExpr::Int(1.into()),
        PseudoExpr::Int(2.into()),
    ]);
    let once = rewrite_expect_three_arg_conditional(input);
    let twice = rewrite_expect_three_arg_conditional(once.clone());
    assert_eq!(once, twice);
}
