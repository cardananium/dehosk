use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_multi_use_delayed_call_wrapper_lambda_inlines_through_force_uses() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("g")),
                args: vec![PseudoExpr::var("x"), PseudoExpr::int(1)].into(),
            }))),
        }),
        body: PBox::new(PseudoExpr::Pair(
            PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![PseudoExpr::int(10)].into(),
            }))),
            PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![PseudoExpr::int(20)].into(),
            }))),
        )),
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Pair(left, right) => {
            for (expr, expected) in [(left.into_inner(), 10), (right.into_inner(), 20)] {
                match expr {
                    PseudoExpr::Apply { function, args } => {
                        assert!(
                            matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "g"),
                            "expected call target g, got: {function:?}"
                        );
                        assert_eq!(args.len(), 2, "expected binary g call, got: {args:?}");
                        assert!(
                            matches!(args[0], PseudoExpr::Int(ref n) if *n == expected.into()),
                            "expected first arg {expected}, got: {:?}",
                            args[0]
                        );
                        assert!(
                            matches!(args[1], PseudoExpr::Int(ref n) if *n == 1.into()),
                            "expected second arg 1, got: {:?}",
                            args[1]
                        );
                    }
                    other => panic!("expected inlined g call, got: {other:?}"),
                }
            }
        }
        other => panic!("expected pair after simplification, got: {other:?}"),
    }
}

#[test]
fn test_multi_use_small_boolean_helper_inlines_into_if_condition() {
    let expr = PseudoExpr::Let {
        name: "same_pair".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into(), "y".to_string().into()],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("x")),
                            args: vec![].into(),
                        },
                        "fst".to_string(),
                    )),
                    right: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("y")),
                            args: vec![].into(),
                        },
                        "fst".to_string(),
                    )),
                }),
                right: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("x")),
                            args: vec![].into(),
                        },
                        "snd".to_string(),
                    )),
                    right: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("y")),
                            args: vec![].into(),
                        },
                        "snd".to_string(),
                    )),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("same_pair")),
                args: vec![PseudoExpr::var("a"), PseudoExpr::var("b")].into(),
            }),
            then_branch: PBox::new(PseudoExpr::var("ok")),
            else_branch: PBox::new(PseudoExpr::var("err")),
        }),
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            assert!(
                matches!(
                    condition.as_ref(),
                    PseudoExpr::BinOp {
                        op: BinaryOp::And,
                        ..
                    }
                ),
                "expected inlined boolean helper condition, got: {condition:?}"
            );
            let rendered = format!("{condition:?}");
            assert!(
                rendered.contains("name: \"a\"") && rendered.contains("name: \"b\""),
                "expected inlined condition to reference a/b directly, got: {rendered}"
            );
            assert!(matches!(then_branch.as_ref(), PseudoExpr::Var { name, .. } if name == "ok"));
            assert!(matches!(else_branch.as_ref(), PseudoExpr::Var { name, .. } if name == "err"));
        }
        other => panic!("expected if after simplification, got: {other:?}"),
    }
}
