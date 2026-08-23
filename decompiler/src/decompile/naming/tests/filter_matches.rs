use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_filter_matches_wrapper() {
    let value = PseudoExpr::Lambda {
        params: vec![
            "xs".to_string().into(),
            "pred".to_string().into(),
            "seed".to_string().into(),
        ],
        body: PBox::new(PseudoExpr::Let {
            name: "rec_fn".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "rec_fn".to_string().into(),
                params: vec!["list".to_string().into(), "predicate".to_string().into()],
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("list")),
                    subject_name: Some("list".to_string().into()),
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            PseudoExpr::var("seed"),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec!["head".into()],
                                tail: Some("tail".into()),
                            },
                            PseudoExpr::If {
                                condition: PBox::new(PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("predicate")),
                                    args: vec![PseudoExpr::var("head")].into(),
                                }),
                                then_branch: PBox::new(PseudoExpr::BuiltinCall {
                                    name: crate::BuiltinId::expect_known("List.cons"),
                                    args: vec![
                                        PseudoExpr::var("head"),
                                        PseudoExpr::Apply {
                                            function: PBox::new(PseudoExpr::var("rec_fn")),
                                            args: vec![
                                                PseudoExpr::var("tail"),
                                                PseudoExpr::var("predicate"),
                                            ]
                                            .into(),
                                        },
                                    ]
                                    .into(),
                                }),
                                else_branch: PBox::new(PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("rec_fn")),
                                    args: vec![
                                        PseudoExpr::var("tail"),
                                        PseudoExpr::var("predicate"),
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
                args: vec![PseudoExpr::var("xs"), PseudoExpr::var("pred")].into(),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_5", &value),
        Some("filter_matches".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_direct_rec_filter_matches_with_capture_param() {
    let value = PseudoExpr::RecFn {
        name: "fn_5".to_string().into(),
        params: vec![
            "xs".to_string().into(),
            "pred".to_string().into(),
            "seed".to_string().into(),
        ],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("xs")),
            subject_name: Some("xs".to_string().into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::var("seed"),
                ),
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec!["head".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("pred")),
                            args: vec![PseudoExpr::var("head")].into(),
                        }),
                        then_branch: PBox::new(PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("List.cons"),
                            args: vec![
                                PseudoExpr::var("head"),
                                PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("fn_5")),
                                    args: vec![
                                        PseudoExpr::var("tail"),
                                        PseudoExpr::var("pred"),
                                        PseudoExpr::var("seed"),
                                    ]
                                    .into(),
                                },
                            ]
                            .into(),
                        }),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("fn_5")),
                            args: vec![
                                PseudoExpr::var("tail"),
                                PseudoExpr::var("pred"),
                                PseudoExpr::var("seed"),
                            ]
                            .into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_5", &value),
        Some("filter_matches".to_string())
    );
}

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_direct_rec_filter_matches_tail_ref()
{
    let outer_tail_id = VarId::fresh_binding();
    let value = PseudoExpr::RecFn {
        name: "fn_5".to_string().into(),
        params: vec![
            "xs".to_string().into(),
            "pred".to_string().into(),
            "seed".to_string().into(),
        ],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("xs")),
            subject_name: Some("xs".to_string().into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::var("seed"),
                ),
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec!["head".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("pred")),
                            args: vec![PseudoExpr::var("head")].into(),
                        }),
                        then_branch: PBox::new(PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("List.cons"),
                            args: vec![
                                PseudoExpr::var("head"),
                                PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("fn_5")),
                                    args: vec![
                                        PseudoExpr::var_with_id("tail", outer_tail_id),
                                        PseudoExpr::var("pred"),
                                        PseudoExpr::var("seed"),
                                    ]
                                    .into(),
                                },
                            ]
                            .into(),
                        }),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("fn_5")),
                            args: vec![
                                PseudoExpr::var_with_id("tail", outer_tail_id),
                                PseudoExpr::var("pred"),
                                PseudoExpr::var("seed"),
                            ]
                            .into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(analyze_function_binding("fn_5", &value), None);
}
