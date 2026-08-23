use super::*;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;

#[test]
fn test_selector_lambda_cse() {
    // let y = delay(fn(_, b) { b }) in ... fn(_, err) { err } ...
    // The inline fn(_, err) { err } should be replaced with y
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec!["_".to_string().into(), "b".to_string().into()],
            body: PBox::new(PseudoExpr::var("b")),
        }))),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::Lambda {
                params: vec!["_".to_string().into(), "err".to_string().into()],
                body: PBox::new(PseudoExpr::var("err")),
            }]
            .into(),
        }),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::FieldAccess { record, selector, .. }
                if selector.is_pair_snd()
                    && matches!(record.as_ref(), PseudoExpr::Var { name, .. } if name == "f")
        ),
        "expected selector CSE to collapse all the way to f.snd, got: {simplified:?}"
    );
}

#[test]
fn test_nested_when_wildcard_flattening_still_works() {
    // When x is {
    //   Constr<0> -> A
    //   _ -> when x is { Constr<1> -> B; Constr<2> -> C }
    // }
    // Should flatten to:
    // When x is { Constr<0> -> A; Constr<1> -> B; Constr<2> -> C }
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::int(1),
            ),
            WhenClause::new(
                WhenPattern::Wildcard,
                PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("x")),
                    subject_name: None,
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                            PseudoExpr::int(2),
                        ),
                        WhenClause::new(
                            WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
                            PseudoExpr::int(3),
                        ),
                    ],
                },
            ),
        ],
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(
                clauses.len(),
                3,
                "expected 3 clauses after wildcard flattening, got: {:?}",
                clauses
            );
        }
        _ => panic!("expected When, got: {:?}", simplified),
    }
}

#[test]
fn test_eta_pair_selector_when_inlines_first_field_without_second_binder() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Lambda {
            params: vec!["sel".to_string().into(), "rest".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("sel")),
                args: vec![PseudoExpr::var("rec_fn_16"), PseudoExpr::var("rest")].into(),
            }),
        }),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Pair("left".into(), "_".into()),
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("use_left")),
                args: vec![PseudoExpr::var("left")].into(),
            },
        )],
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "use_left")
                    && matches!(args.as_slice(), [PseudoExpr::Var { name, .. }] if name == "rec_fn_16")
        ),
        "expected one-clause pair selector wrapper to inline left field, got: {simplified:?}"
    );
}

#[test]
fn test_eta_pair_selector_when_keeps_second_binder_as_lambda_param() {
    let left_id = VarId::fresh_binding();
    let k_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Lambda {
            params: vec!["sel".to_string().into(), "rest".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("sel")),
                args: vec![PseudoExpr::var("rec_fn_18"), PseudoExpr::var("rest")].into(),
            }),
        }),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Pair(Binder::new("left", left_id), Binder::new("k", k_id)),
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
                args: vec![PseudoExpr::var_with_id("left", left_id)].into(),
            },
        )],
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "k");
            assert_eq!(params[0].id, k_id);
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, args }
                        if matches!(function.as_ref(), PseudoExpr::Var { name, id, .. } if name == "k" && *id == Some(k_id))
                            && matches!(args.as_slice(), [PseudoExpr::Var { name, .. }] if name == "rec_fn_18")
                ),
                "expected selector wrapper to become lambda over the second binder, got: {body:?}"
            );
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn test_eta_pair_selector_when_ignores_same_name_foreign_second_ref() {
    let left_id = VarId::new(9_881);
    let k_id = VarId::new(9_882);
    let foreign_k_id = VarId::new(9_883);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Lambda {
            params: vec!["sel".to_string().into(), "rest".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("sel")),
                args: vec![PseudoExpr::var("rec_fn_22"), PseudoExpr::var("rest")].into(),
            }),
        }),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Pair(Binder::new("left", left_id), Binder::new("k", k_id)),
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("use_outer")),
                args: vec![
                    PseudoExpr::var_with_id("k", foreign_k_id),
                    PseudoExpr::var_with_id("left", left_id),
                ]
                .into(),
            },
        )],
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "use_outer")
                    && matches!(
                        args.as_slice(),
                        [
                            PseudoExpr::Var { name: k_name, id: k_id_seen },
                            PseudoExpr::Var { name: left_name, .. },
                        ] if k_name == "k" && *k_id_seen == Some(foreign_k_id) && left_name == "rec_fn_22"
                    )
        ),
        "same-name foreign `k` ref must not make the pair collapse introduce a lambda over k: {simplified:?}"
    );
}

#[test]
fn test_eta_pair_selector_when_preserves_hidden_subject_name_usage() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Lambda {
            params: vec!["sel".to_string().into(), "rest".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("sel")),
                args: vec![PseudoExpr::var("rec_fn_21"), PseudoExpr::var("rest")].into(),
            }),
        }),
        subject_name: Some("pair_value".to_string().into()),
        clauses: vec![WhenClause::new(
            WhenPattern::Pair("left".into(), "_".into()),
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("use_pair")),
                args: vec![PseudoExpr::var("pair_value"), PseudoExpr::var("left")].into(),
            },
        )],
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "use_pair")
                    && matches!(args.as_slice(),
                        [PseudoExpr::Lambda { .. }, PseudoExpr::Var { name, .. }]
                        if name == "rec_fn_21")
        ),
        "expected collapse to preserve the hidden subject value semantically while eliminating the wrapper, got: {simplified:?}"
    );
}

#[test]
fn test_constant_constructor_collapse_does_not_bind_same_name_foreign_ref() {
    let foreign_id = VarId::new(9_884);
    let pattern_id = VarId::new(9_885);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(foreign_id),
        value: PBox::new(PseudoExpr::raw("foreign", "test foreign")),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::constr(
                ConstructorShape::unknown_data(0, 1),
                vec![PseudoExpr::int(1)],
            )),
            subject_name: None,
            clauses: vec![WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec![Binder::new("x", pattern_id)],
                ),
                PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("x", foreign_id),
                        PseudoExpr::var_with_id("x", foreign_id),
                    ]
                    .into(),
                ),
            )],
        }),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::Let { name, id, body, .. }
                if name == "x" && *id == Some(foreign_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Tuple(items)
                            if matches!(
                                items.as_slice(),
                                [
                                    PseudoExpr::Var { name: first_name, id: first_id },
                                    PseudoExpr::Var { name: second_name, id: second_id },
                                ] if first_name == "x"
                                    && second_name == "x"
                                    && *first_id == Some(foreign_id)
                                    && *second_id == Some(foreign_id)
                            )
                    )
        ),
        "constructor collapse must not bind the unused pattern x over same-name foreign refs: {simplified:?}"
    );
}

#[test]
fn test_hoist_let_from_builtin_arg() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.to_bytes"),
        args: vec![PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("expensive")),
                args: vec![PseudoExpr::var("v")].into(),
            }),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var("x")),
                right: PBox::new(PseudoExpr::var("x")),
            }),
        }]
        .into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "x");
            assert!(
                matches!(body.as_ref(), PseudoExpr::BuiltinCall { name, .. } if name == "Data.to_bytes"),
                "expected let-hoisted builtin call, got: {:?}",
                body
            );
        }
        _ => panic!("expected Let-wrapped builtin call, got: {:?}", simplified),
    }
}

#[test]
fn test_hoist_let_from_apply_arg_normalizes_compat_placeholder_to_binding_id() {
    let compat_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(compat_id),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("expensive")),
                args: vec![PseudoExpr::var("v")].into(),
            }),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var("x")),
                right: PBox::new(PseudoExpr::var("x")),
            }),
        }]
        .into(),
    };
    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Let { name, id, body, .. } => {
            assert_eq!(name, "x");
            let binding_id = id
                .get()
                .expect("expected named hoisted let to normalize compat placeholder to a VarId");
            match body.as_ref() {
                PseudoExpr::Apply { args, .. } => {
                    assert!(
                        matches!(
                            args.as_slice(),
                            [PseudoExpr::BinOp { left, right, .. }]
                                if matches!(
                                    left.as_ref(),
                                    PseudoExpr::Var { name, id, .. }
                                        if name == "x" && id.get() == Some(binding_id)
                                ) && matches!(
                                    right.as_ref(),
                                    PseudoExpr::Var { name, id, .. }
                                        if name == "x" && id.get() == Some(binding_id)
                                )
                        ),
                        "expected hoisted apply arg to reuse normalized binding id, got: {args:?}"
                    );
                }
                other => panic!("expected apply body, got: {other:?}"),
            }
        }
        other => panic!("expected hoisted let binding, got: {other:?}"),
    }
}

#[test]
fn test_hoist_let_from_apply_arg_underscore_rename_keeps_compat_placeholder_id() {
    let compat_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![PseudoExpr::Let {
            name: "_".to_string(),
            id: Some(compat_id),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("expensive")),
                args: vec![PseudoExpr::var("v")].into(),
            }),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var("_")),
                right: PBox::new(PseudoExpr::var("_")),
            }),
        }]
        .into(),
    };
    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Let {
            name: let_name,
            id,
            body,
            ..
        } => {
            assert_ne!(
                let_name, "_",
                "expected underscore-origin hoist to become a readable binding name"
            );
            let binding_id = id.get().expect(
                "expected underscore-origin hoist to normalize to a concrete VarId after rename",
            );
            match body.as_ref() {
                PseudoExpr::Apply { args, .. } => {
                    assert!(
                        matches!(
                            args.as_slice(),
                            [PseudoExpr::BinOp { left, right, .. }]
                                if matches!(
                                    left.as_ref(),
                                    PseudoExpr::Var { name, id, .. }
                                        if name == &let_name && id.get() == Some(binding_id)
                                ) && matches!(
                                    right.as_ref(),
                                    PseudoExpr::Var { name, id, .. }
                                        if name == &let_name && id.get() == Some(binding_id)
                                )
                        ),
                        "expected renamed underscore hoist to keep normalized refs aligned, got: {args:?}"
                    );
                }
                other => panic!("expected apply body, got: {other:?}"),
            }
        }
        other => panic!("expected hoisted let binding, got: {other:?}"),
    }
}

#[test]
fn test_index_access_pushed_into_when_clauses() {
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("s")),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(
                        ConstructorShape::unknown_data(1, 1),
                        vec!["t".into()],
                    ),
                    PseudoExpr::field_access(PseudoExpr::var("t"), "fields".to_string()),
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::error()),
            ],
        }),
        index: 0,
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When { clauses, .. } => {
            assert!(
                matches!(clauses[0].body, PseudoExpr::IndexAccess { .. }),
                "expected first clause body to become IndexAccess, got: {:?}",
                clauses[0].body
            );
        }
        _ => panic!("expected When, got: {:?}", simplified),
    }
}
