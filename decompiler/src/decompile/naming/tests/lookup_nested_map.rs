use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_lookup_nested_map_wrapper() {
    let value = PseudoExpr::Lambda {
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
                                    args: vec![PseudoExpr::var("cont"), PseudoExpr::var("tail")]
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
    };

    assert_eq!(
        analyze_function_binding("fn_8", &value),
        Some("lookup_nested_map".to_string())
    );
}

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_lookup_nested_map_inner_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let value = PseudoExpr::Lambda {
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
    };

    assert_eq!(analyze_function_binding("fn_8", &value), None);
}
