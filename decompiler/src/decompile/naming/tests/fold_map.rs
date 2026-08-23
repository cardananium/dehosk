use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_fold_map_wrapper() {
    let value = PseudoExpr::Lambda {
        params: vec![
            "map_data".to_string().into(),
            "step".to_string().into(),
            "init".to_string().into(),
        ],
        body: PBox::new(PseudoExpr::Let {
            name: "rec_fn".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "rec_fn".to_string().into(),
                params: vec![
                    "list".to_string().into(),
                    "idx".to_string().into(),
                    "acc".to_string().into(),
                ],
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("list")),
                    subject_name: Some("list".to_string().into()),
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            PseudoExpr::var("acc"),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec!["entry".into()],
                                tail: Some("tail".into()),
                            },
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("rec_fn")),
                                args: vec![
                                    PseudoExpr::var("tail"),
                                    PseudoExpr::var("idx"),
                                    PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var("idx")),
                                        args: vec![
                                            PseudoExpr::var("acc"),
                                            PseudoExpr::var("entry"),
                                        ]
                                        .into(),
                                    },
                                ]
                                .into(),
                            },
                        ),
                    ],
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("rec_fn")),
                args: vec![
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_map"),
                        args: vec![PseudoExpr::var("map_data")].into(),
                    },
                    PseudoExpr::var("step"),
                    PseudoExpr::var("init"),
                ]
                .into(),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_5", &value),
        Some("fold_map".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_hoisted_fold_map_adapter() {
    let rec_value = PseudoExpr::RecFn {
        name: "rec_fn_4".to_string().into(),
        params: vec![
            "list".to_string().into(),
            "step".to_string().into(),
            "acc".to_string().into(),
        ],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("list")),
            subject_name: Some("list".to_string().into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::var("acc"),
                ),
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec!["entry".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("rec_fn_4")),
                        args: vec![
                            PseudoExpr::var("tail"),
                            PseudoExpr::var("step"),
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("step")),
                                args: vec![PseudoExpr::var("acc"), PseudoExpr::var("entry")].into(),
                            },
                        ]
                        .into(),
                    },
                ),
            ],
        }),
    };
    let root = PseudoExpr::Let {
        name: "rec_fn_4".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(rec_value),
        body: PBox::new(PseudoExpr::unit()),
    };
    let fold_rec_candidates = collect_fold_rec_candidates(&root);

    let value = PseudoExpr::Lambda {
        params: vec![
            "map_data".to_string().into(),
            "step".to_string().into(),
            "init".to_string().into(),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("rec_fn_4")),
            args: vec![
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_map"),
                    args: vec![PseudoExpr::var("map_data")].into(),
                },
                PseudoExpr::Lambda {
                    params: vec!["acc".to_string().into(), "entry".to_string().into()],
                    body: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("step")),
                        args: vec![
                            PseudoExpr::var("acc"),
                            PseudoExpr::field_access(PseudoExpr::var("entry"), "fst".to_string()),
                            PseudoExpr::field_access(PseudoExpr::var("entry"), "snd".to_string()),
                        ]
                        .into(),
                    }),
                },
                PseudoExpr::var("init"),
            ]
            .into(),
        }),
    };

    assert_eq!(
        analyze_function_binding_with_fold_rec_candidates("rec_fn_5", &value, &fold_rec_candidates),
        Some("fold_map".to_string())
    );
}

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_fold_map_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let value = PseudoExpr::Lambda {
        params: vec![
            "map_data".to_string().into(),
            "step".to_string().into(),
            "init".to_string().into(),
        ],
        body: PBox::new(PseudoExpr::Let {
            name: "rec_fn".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "rec_fn".to_string().into(),
                params: vec![
                    "list".to_string().into(),
                    "idx".to_string().into(),
                    "acc".to_string().into(),
                ],
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("list")),
                    subject_name: Some("list".to_string().into()),
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            PseudoExpr::var("acc"),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec!["entry".into()],
                                tail: Some("tail".into()),
                            },
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("rec_fn")),
                                args: vec![
                                    PseudoExpr::var_with_id("tail", outer_tail_id),
                                    PseudoExpr::var("idx"),
                                    PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var("idx")),
                                        args: vec![
                                            PseudoExpr::var("acc"),
                                            PseudoExpr::var("entry"),
                                        ]
                                        .into(),
                                    },
                                ]
                                .into(),
                            },
                        ),
                    ],
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("rec_fn")),
                args: vec![
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_map"),
                        args: vec![PseudoExpr::var("map_data")].into(),
                    },
                    PseudoExpr::var("step"),
                    PseudoExpr::var("init"),
                ]
                .into(),
            }),
        }),
    };

    assert_eq!(analyze_function_binding("rec_fn_5", &value), None);
}
