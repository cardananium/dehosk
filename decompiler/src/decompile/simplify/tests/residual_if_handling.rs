use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_builtin_call_if_3_args_becomes_if_expr() {
    // BuiltinCall("if", [cond, delay(then), delay(else)]) → If { cond, then, else }
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("if_then_else"),
        args: vec![
            PseudoExpr::Bool(true),
            PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::int(2))),
        ]
        .into(),
    };
    let simplified = simplify(expr);
    // if True { 1 } else { 2 } simplifies to just 1
    assert!(
        matches!(simplified, PseudoExpr::Int(_)),
        "expected Int, got: {:?}",
        simplified
    );
}

#[test]
fn test_builtin_call_if_3_args_and_pattern() {
    // BuiltinCall("if", [cond, delay(False), delay(expr)]) → cond && expr
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("if"),
        args: vec![
            PseudoExpr::var("x"),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("y"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::Bool(false))),
        ]
        .into(),
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
        "expected And binop, got: {:?}",
        simplified
    );
}

#[test]
fn test_builtin_call_if_3_args_or_pattern() {
    // BuiltinCall("if", [cond, delay(True), delay(expr)]) → cond || expr
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("if"),
        args: vec![
            PseudoExpr::var("x"),
            PseudoExpr::Delay(PBox::new(PseudoExpr::Bool(true))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("y"))),
        ]
        .into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(
            simplified,
            PseudoExpr::BinOp {
                op: BinaryOp::Or,
                ..
            }
        ),
        "expected Or binop, got: {:?}",
        simplified
    );
}

#[test]
fn test_when_void_fail_pattern_becomes_expect_guard() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("redeemer")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::Unit,
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
        ],
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Apply { function, args } => {
            assert_expect_helper_head(function.as_ref());
            assert_eq!(args.len(), 2, "expected expect!(cond, Void), got: {args:?}");
            assert!(matches!(args[1], PseudoExpr::Unit));
            assert!(
                matches!(&args[0], PseudoExpr::When { clauses, .. }
                    if matches!(&clauses[0].body, PseudoExpr::Bool(true))
                        && matches!(&clauses[1].body, PseudoExpr::Bool(false))),
                "expected booleanized when guard inside expect!, got: {:?}",
                args[0]
            );
        }
        other => panic!("expected expect! guard from when Void/fail pattern, got: {other:?}"),
    }
}

#[test]
fn test_when_fail_void_pattern_becomes_inverted_expect_guard() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("redeemer")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::Error { message: None },
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Unit),
        ],
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Apply { function, args } => {
            assert_expect_helper_head(function.as_ref());
            assert_eq!(args.len(), 2, "expected expect!(cond, Void), got: {args:?}");
            assert!(matches!(args[1], PseudoExpr::Unit));
            assert!(
                matches!(&args[0], PseudoExpr::When { clauses, .. }
                    if matches!(&clauses[0].body, PseudoExpr::Bool(false))
                        && matches!(&clauses[1].body, PseudoExpr::Bool(true))),
                "expected inverted booleanized when guard inside expect!, got: {:?}",
                args[0]
            );
        }
        other => {
            panic!("expected inverted expect! guard from when fail/Void pattern, got: {other:?}")
        }
    }
}

#[test]
fn test_nested_if_with_shared_false_merges_conditions() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("a")),
        then_branch: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("b")),
            then_branch: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("fn_2")),
                args: vec![PseudoExpr::var("x")].into(),
            }),
            else_branch: PBox::new(PseudoExpr::Bool(false)),
        }),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
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
                "expected merged boolean condition, got: {condition:?}"
            );
            assert!(
                matches!(then_branch.as_ref(), PseudoExpr::Apply { function, args }
                    if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "fn_2")
                        && args.len() == 1),
                "expected original then branch payload to survive, got: {then_branch:?}"
            );
            assert!(matches!(else_branch.as_ref(), PseudoExpr::Bool(false)));
        }
        other => panic!("expected flattened shared-false if, got: {other:?}"),
    }
}

#[test]
fn test_apply_if_1_builtin_arg_plus_2_apply_args() {
    // Apply(BuiltinCall("if", [cond]), [delay(then), delay(else)])
    // → If { cond, then, else }
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![PseudoExpr::var("x")].into(),
        }),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::int(10))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::int(20))),
        ]
        .into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::If { .. }),
        "expected If, got: {:?}",
        simplified
    );
}

#[test]
fn test_apply_direct_if_3_args_moves_and_unwraps_delayed_branches_preserving_ids() {
    let cond_id = VarId::new(9271);
    let value_id = VarId::new(9272);
    let fallback_id = VarId::new(9273);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![].into(),
        }),
        args: vec![
            PseudoExpr::var_with_id("cond", cond_id),
            PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("value", value_id)],
                body: PBox::new(PseudoExpr::var_with_id("value", value_id)),
            })),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("fallback", fallback_id))),
        ]
        .into(),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } if matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id))
                && matches!(
                    then_branch.as_ref(),
                    PseudoExpr::Lambda { params, body }
                        if matches!(params.as_slice(), [binder] if binder.as_str() == "value" && binder.id == value_id)
                            && matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "value" && *id == Some(value_id))
                )
                && matches!(else_branch.as_ref(), PseudoExpr::Var { name, id } if name == "fallback" && *id == Some(fallback_id))
        ),
        "expected direct Apply-form if to move cond and unwrap branches with ids intact, got: {simplified:?}"
    );
}

#[test]
fn test_apply_if_2_builtin_args_plus_1_apply_arg() {
    // Apply(BuiltinCall("if", [cond, delay(then)]), [delay(else)])
    // → If { cond, then, else }
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![
                PseudoExpr::var("x"),
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(10))),
            ]
            .into(),
        }),
        args: vec![PseudoExpr::Delay(PBox::new(PseudoExpr::int(20)))].into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::If { .. }),
        "expected If, got: {:?}",
        simplified
    );
}

#[test]
fn test_apply_if_1_builtin_arg_plus_2_apply_args_and_pattern() {
    // Apply(BuiltinCall("if", [cond]), [delay(expr), delay(False)])
    // → cond && expr
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if_then_else"),
            args: vec![PseudoExpr::var("a")].into(),
        }),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::Bool(false))),
        ]
        .into(),
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
        "expected And binop, got: {:?}",
        simplified
    );
}

#[test]
fn test_apply_if_1_builtin_arg_plus_3_apply_args_cps() {
    // Apply(BuiltinCall("if", [cond]), [fn(_){then}, fn(_){else}, Unit])
    // → CPS 4-arg if → If { cond, then, else }
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![PseudoExpr::var("x")].into(),
        }),
        args: vec![
            PseudoExpr::Lambda {
                params: vec!["_".to_string().into()],
                body: PBox::new(PseudoExpr::int(10)),
            },
            PseudoExpr::Lambda {
                params: vec!["_".to_string().into()],
                body: PBox::new(PseudoExpr::int(20)),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::If { .. }),
        "expected If, got: {:?}",
        simplified
    );
}

#[test]
fn test_apply_if_1_builtin_arg_plus_3_apply_args_cps_not_rewritten_in_safe_mode() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![PseudoExpr::var("x")].into(),
        }),
        args: vec![
            PseudoExpr::Lambda {
                params: vec!["_".to_string().into()],
                body: PBox::new(PseudoExpr::int(10)),
            },
            PseudoExpr::Lambda {
                params: vec!["_".to_string().into()],
                body: PBox::new(PseudoExpr::int(20)),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };

    let simplified = simplify_with_options(expr, true);
    assert!(
        matches!(
            simplified,
            PseudoExpr::BuiltinCall { ref name, ref args }
                if name == "if" && args.len() == 4
        ),
        "expected unresolved 4-arg if builtin in safe mode, got: {:?}",
        simplified
    );
}

#[test]
fn test_force_applied_if_with_noncheap_args_avoids_partial_if_output() {
    // force((if cond_outer { if(cond_inner) } else { if(cond_fallback) })(delay(expensive(z)), k))
    // should not leave residual partial if(...) nodes.
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond_outer")),
            then_branch: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("if"),
                args: vec![PseudoExpr::var("cond_inner")].into(),
            }),
            else_branch: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("if"),
                args: vec![PseudoExpr::var("cond_fallback")].into(),
            }),
        }),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("expensive")),
                args: vec![PseudoExpr::var("z")].into(),
            })),
            PseudoExpr::var("k"),
        ]
        .into(),
    }));

    let simplified = simplify(expr);
    let output = simplified.to_pretty();
    assert!(
        !output.contains("if("),
        "expected no residual partial if(...) in output, got:\n{}",
        output
    );
}

#[test]
fn test_builtin_call_if_5_args_not_rewritten_in_safe_mode() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("if"),
        args: vec![
            PseudoExpr::var("c"),
            PseudoExpr::Lambda {
                params: vec!["x".to_string().into(), "_".to_string().into()],
                body: PBox::new(PseudoExpr::var("x")),
            },
            PseudoExpr::Lambda {
                params: vec!["_".to_string().into(), "y".to_string().into()],
                body: PBox::new(PseudoExpr::var("y")),
            },
            PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::int(2))),
        ]
        .into(),
    };

    let simplified = simplify_with_options(expr, true);
    assert!(
        matches!(
            simplified,
            PseudoExpr::BuiltinCall { ref name, ref args }
                if name == "if" && args.len() == 5
        ),
        "expected unresolved 5-arg if builtin in safe mode, got: {:?}",
        simplified
    );
}

#[test]
fn test_builtin_call_if_3_args_no_delay() {
    // BuiltinCall("if", [cond, then, else]) without delay wrapping
    // → If { cond, then, else }
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("if"),
        args: vec![PseudoExpr::var("x"), PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::If { .. }),
        "expected If, got: {:?}",
        simplified
    );
}
