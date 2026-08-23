use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_lookup_nested_map_inner_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "fn_8".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["map_data".to_string().into(), "keys".to_string().into()],
            body: PBox::new(PseudoExpr::Let {
                name: "rec_fn".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::RecFn {
                    name: "rec_fn".to_string().into(),
                    params: vec!["cont".to_string().into(), "pairs".to_string().into()],
                    body: PBox::new(PseudoExpr::When {
                        subject: PBox::new(PseudoExpr::var("pairs")),
                        subject_name: Some("pairs".to_string().into()),
                        clauses: vec![
                            WhenClause::new(
                                WhenPattern::List {
                                    elements: vec![],
                                    tail: None,
                                },
                                PseudoExpr::int(0),
                            ),
                            WhenClause::new(
                                WhenPattern::List {
                                    elements: vec!["entry".into()],
                                    tail: Some("tail".into()),
                                },
                                PseudoExpr::If {
                                    condition: PBox::new(PseudoExpr::BinOp {
                                        op: BinaryOp::Eq,
                                        left: PBox::new(PseudoExpr::field_access(
                                            PseudoExpr::var("entry"),
                                            "fst".to_string(),
                                        )),
                                        right: PBox::new(PseudoExpr::var("needle_1")),
                                    }),
                                    then_branch: PBox::new(PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var("cont")),
                                        args: vec![
                                            PseudoExpr::var("cont"),
                                            PseudoExpr::BuiltinCall {
                                                name: crate::BuiltinId::expect_known("Data.un_map"),
                                                args: vec![PseudoExpr::field_access(
                                                    PseudoExpr::var("entry"),
                                                    "snd".to_string(),
                                                )]
                                                .into(),
                                            },
                                        ]
                                        .into(),
                                    }),
                                    else_branch: PBox::new(PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var("rec_fn")),
                                        args: vec![
                                            PseudoExpr::var("cont"),
                                            PseudoExpr::var_with_id("tail", outer_tail_id),
                                        ]
                                        .into(),
                                    }),
                                },
                            ),
                        ],
                    }),
                }),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("rec_fn")),
                    args: vec![
                        PseudoExpr::Lambda {
                            params: vec!["self".to_string().into(), "pairs_2".to_string().into()],
                            body: PBox::new(PseudoExpr::When {
                                subject: PBox::new(PseudoExpr::var("pairs_2")),
                                subject_name: Some("pairs_2".to_string().into()),
                                clauses: vec![
                                    WhenClause::new(
                                        WhenPattern::List {
                                            elements: vec![],
                                            tail: None,
                                        },
                                        PseudoExpr::int(0),
                                    ),
                                    WhenClause::new(
                                        WhenPattern::List {
                                            elements: vec!["entry_2".into()],
                                            tail: Some("tail_2".into()),
                                        },
                                        PseudoExpr::If {
                                            condition: PBox::new(PseudoExpr::BinOp {
                                                op: BinaryOp::Eq,
                                                left: PBox::new(PseudoExpr::field_access(
                                                    PseudoExpr::var("entry_2"),
                                                    "fst".to_string(),
                                                )),
                                                right: PBox::new(PseudoExpr::var("needle_2")),
                                            }),
                                            then_branch: PBox::new(PseudoExpr::field_access(
                                                PseudoExpr::var("entry_2"),
                                                "snd".to_string(),
                                            )),
                                            else_branch: PBox::new(PseudoExpr::Apply {
                                                function: PBox::new(PseudoExpr::var("self")),
                                                args: vec![
                                                    PseudoExpr::var("self"),
                                                    PseudoExpr::var("tail_2"),
                                                ]
                                                .into(),
                                            }),
                                        },
                                    ),
                                ],
                            }),
                        },
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.un_map"),
                            args: vec![PseudoExpr::var("map_data")].into(),
                        },
                    ]
                    .into(),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("fn_8")),
            args: vec![PseudoExpr::var("map_arg"), PseudoExpr::var("keys_arg")].into(),
        }),
    };

    let improved = improve_variable_names(expr);

    let PseudoExpr::Let { name, body, .. } = improved else {
        panic!("expected outer let");
    };
    assert_eq!(name, "fn_8");
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Apply { function, .. }
                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "fn_8")
        ),
        "expected lookup-nested-map false positive to stay unrenamed, got: {body:?}"
    );
}

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_lookup_then_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "rec_fn_3".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "rec_fn_3".to_string().into(),
            params: vec!["cont".to_string().into(), "pairs".to_string().into()],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("pairs")),
                subject_name: Some("pairs".to_string().into()),
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec![],
                            tail: None,
                        },
                        PseudoExpr::int(0),
                    ),
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec!["entry".into()],
                            tail: Some("tail".into()),
                        },
                        PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::BinOp {
                                op: BinaryOp::Eq,
                                left: PBox::new(PseudoExpr::field_access(
                                    PseudoExpr::var("entry"),
                                    "fst".to_string(),
                                )),
                                right: PBox::new(PseudoExpr::var("needle")),
                            }),
                            then_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("cont")),
                                args: vec![
                                    PseudoExpr::var("cont"),
                                    PseudoExpr::BuiltinCall {
                                        name: crate::BuiltinId::expect_known("Data.un_map"),
                                        args: vec![PseudoExpr::field_access(
                                            PseudoExpr::var("entry"),
                                            "snd".to_string(),
                                        )]
                                        .into(),
                                    },
                                ]
                                .into(),
                            }),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("rec_fn_3")),
                                args: vec![
                                    PseudoExpr::var("cont"),
                                    PseudoExpr::var_with_id("tail", outer_tail_id),
                                ]
                                .into(),
                            }),
                        },
                    ),
                ],
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("rec_fn_3")),
            args: vec![PseudoExpr::var("cont_arg"), PseudoExpr::var("pairs_arg")].into(),
        }),
    };

    let improved = improve_variable_names(expr);

    let PseudoExpr::Let { name, body, .. } = improved else {
        panic!("expected outer let");
    };
    assert_eq!(name, "rec_fn_3");
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Apply { function, .. }
                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "rec_fn_3")
        ),
        "expected lookup-then false positive to stay unrenamed, got: {body:?}"
    );
}

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_lookup_nested_int_bridge_subject() {
    let outer_lookup_result_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "fn_2".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                "x_6".to_string().into(),
                "y_3".to_string().into(),
                "z_2".to_string().into(),
            ],
            body: PBox::new(PseudoExpr::Let {
                name: "lookup_result_2".to_string(),
                id: Some(VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("lookup_2")),
                    args: vec![PseudoExpr::var("x_6"), PseudoExpr::var("y_3")].into(),
                }),
                body: PBox::new(PseudoExpr::Let {
                    name: "lookup_4".to_string(),
                    id: Some(VarId::fresh_compat_placeholder()),
                    value: PBox::new(PseudoExpr::RecFn {
                        name: "lookup_4".to_string().into(),
                        params: vec!["pairs_3".to_string().into()],
                        body: PBox::new(PseudoExpr::When {
                            subject: PBox::new(PseudoExpr::var("pairs_3")),
                            subject_name: Some("pairs_3".to_string().into()),
                            clauses: vec![
                                WhenClause::new(
                                    WhenPattern::List {
                                        elements: vec![],
                                        tail: None,
                                    },
                                    PseudoExpr::bool(false),
                                ),
                                WhenClause::new(
                                    WhenPattern::List {
                                        elements: vec!["entry".into()],
                                        tail: Some("tail".into()),
                                    },
                                    PseudoExpr::If {
                                        condition: PBox::new(PseudoExpr::BinOp {
                                            op: BinaryOp::Lte,
                                            left: PBox::new(PseudoExpr::var("z_2")),
                                            right: PBox::new(PseudoExpr::field_access(
                                                PseudoExpr::var("entry"),
                                                "fst".to_string(),
                                            )),
                                        }),
                                        then_branch: PBox::new(PseudoExpr::If {
                                            condition: PBox::new(PseudoExpr::BinOp {
                                                op: BinaryOp::Eq,
                                                left: PBox::new(PseudoExpr::var("z_2")),
                                                right: PBox::new(PseudoExpr::field_access(
                                                    PseudoExpr::var("entry"),
                                                    "fst".to_string(),
                                                )),
                                            }),
                                            then_branch: PBox::new(PseudoExpr::constr_known(
                                                KnownConstructor::Some,
                                                vec![PseudoExpr::field_access(
                                                    PseudoExpr::var("entry"),
                                                    "snd".to_string(),
                                                )],
                                            )),
                                            else_branch: PBox::new(PseudoExpr::bool(false)),
                                        }),
                                        else_branch: PBox::new(PseudoExpr::Apply {
                                            function: PBox::new(PseudoExpr::var("lookup_4")),
                                            args: vec![PseudoExpr::var("tail")].into(),
                                        }),
                                    },
                                ),
                            ],
                        }),
                    }),
                    body: PBox::new(PseudoExpr::Let {
                        name: "l2".to_string(),
                        id: Some(VarId::fresh_compat_placeholder()),
                        value: PBox::new(PseudoExpr::When {
                            subject: PBox::new(PseudoExpr::var_with_id(
                                "lookup_result_2",
                                outer_lookup_result_id,
                            )),
                            subject_name: Some("lookup_result_2".to_string().into()),
                            clauses: vec![
                                WhenClause::new(
                                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                                    PseudoExpr::bool(false),
                                ),
                                WhenClause::new(
                                    WhenPattern::Wildcard,
                                    PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var("lookup_4")),
                                        args: vec![PseudoExpr::BuiltinCall {
                                            name: crate::BuiltinId::expect_known("Data.un_map"),
                                            args: vec![PseudoExpr::IndexAccess {
                                                collection: PBox::new(PseudoExpr::field_access(
                                                    PseudoExpr::var("lookup_result_2"),
                                                    "fields".to_string(),
                                                )),
                                                index: 0,
                                            }]
                                            .into(),
                                        }]
                                        .into(),
                                    },
                                ),
                            ],
                        }),
                        body: PBox::new(PseudoExpr::When {
                            subject: PBox::new(PseudoExpr::var("l2")),
                            subject_name: Some("l2".to_string().into()),
                            clauses: vec![
                                WhenClause::new(
                                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                                    PseudoExpr::int(0),
                                ),
                                WhenClause::new(
                                    WhenPattern::Wildcard,
                                    PseudoExpr::BuiltinCall {
                                        name: crate::BuiltinId::expect_known("Data.un_int"),
                                        args: vec![PseudoExpr::IndexAccess {
                                            collection: PBox::new(PseudoExpr::field_access(
                                                PseudoExpr::var("l2"),
                                                "fields".to_string(),
                                            )),
                                            index: 0,
                                        }]
                                        .into(),
                                    },
                                ),
                            ],
                        }),
                    }),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("fn_2")),
            args: vec![
                PseudoExpr::var("pairs_arg"),
                PseudoExpr::var("needle_arg"),
                PseudoExpr::var("nested_arg"),
            ]
            .into(),
        }),
    };

    let improved = improve_variable_names(expr);

    let PseudoExpr::Let { name, body, .. } = improved else {
        panic!("expected outer let");
    };
    assert_eq!(name, "fn_2");
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Apply { function, .. }
                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "fn_2")
        ),
        "expected nested-lookup-int false positive to stay unrenamed, got: {body:?}"
    );
}
