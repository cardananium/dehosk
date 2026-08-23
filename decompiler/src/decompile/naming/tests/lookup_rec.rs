use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_lookup_rec() {
    let value = PseudoExpr::RecFn {
        name: "rec_fn_9".to_string().into(),
        params: vec!["pairs".to_string().into()],
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
                        then_branch: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var("entry"),
                            "snd".to_string(),
                        )),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("rec_fn_9")),
                            args: vec![PseudoExpr::var("tail")].into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_9", &value),
        Some("lookup".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_lookup_rec_with_some_payload() {
    let value = PseudoExpr::RecFn {
        name: "rec_fn_9".to_string().into(),
        params: vec!["pairs".to_string().into(), "needle".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("pairs")),
            subject_name: Some("pairs".to_string().into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::constr_known(KnownConstructor::None, vec![]),
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
                        then_branch: PBox::new(PseudoExpr::constr_known(
                            KnownConstructor::Some,
                            vec![PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "snd".to_string(),
                            )],
                        )),
                        else_branch: PBox::new(PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::BinOp {
                                op: BinaryOp::Lt,
                                left: PBox::new(PseudoExpr::var("needle")),
                                right: PBox::new(PseudoExpr::field_access(
                                    PseudoExpr::var("entry"),
                                    "fst".to_string(),
                                )),
                            }),
                            then_branch: PBox::new(PseudoExpr::constr_known(
                                KnownConstructor::None,
                                vec![],
                            )),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("rec_fn_9")),
                                args: vec![PseudoExpr::var("tail"), PseudoExpr::var("needle")]
                                    .into(),
                            }),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_9", &value),
        Some("lookup".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_lookup_rec_with_false_none_payload() {
    let value = PseudoExpr::RecFn {
        name: "rec_fn_9".to_string().into(),
        params: vec!["pairs".to_string().into(), "needle".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("pairs")),
            subject_name: Some("pairs".to_string().into()),
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
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "fst".to_string(),
                            )),
                            right: PBox::new(PseudoExpr::var("needle")),
                        }),
                        then_branch: PBox::new(PseudoExpr::constr_known(
                            KnownConstructor::Some,
                            vec![PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "snd".to_string(),
                            )],
                        )),
                        else_branch: PBox::new(PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::BinOp {
                                op: BinaryOp::Lt,
                                left: PBox::new(PseudoExpr::var("needle")),
                                right: PBox::new(PseudoExpr::field_access(
                                    PseudoExpr::var("entry"),
                                    "fst".to_string(),
                                )),
                            }),
                            then_branch: PBox::new(PseudoExpr::bool(false)),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("rec_fn_9")),
                                args: vec![PseudoExpr::var("tail"), PseudoExpr::var("needle")]
                                    .into(),
                            }),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_9", &value),
        Some("lookup".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_lookup_rec_with_le_cutoff_payload() {
    let value = PseudoExpr::RecFn {
        name: "rec_fn_9".to_string().into(),
        params: vec!["pairs".to_string().into(), "needle".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("pairs")),
            subject_name: Some("pairs".to_string().into()),
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
                            left: PBox::new(PseudoExpr::var("needle")),
                            right: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "fst".to_string(),
                            )),
                        }),
                        then_branch: PBox::new(PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::BinOp {
                                op: BinaryOp::Eq,
                                left: PBox::new(PseudoExpr::var("needle")),
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
                            function: PBox::new(PseudoExpr::var("rec_fn_9")),
                            args: vec![PseudoExpr::var("tail"), PseudoExpr::var("needle")].into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_9", &value),
        Some("lookup".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_lookup_rec_with_builtin_payload_transform() {
    let value = PseudoExpr::RecFn {
        name: "rec_fn_9".to_string().into(),
        params: vec!["pairs".to_string().into(), "needle".to_string().into()],
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
                        then_branch: PBox::new(PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.un_int"),
                            args: vec![PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "snd".to_string(),
                            )]
                            .into(),
                        }),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("rec_fn_9")),
                            args: vec![PseudoExpr::var("tail"), PseudoExpr::var("needle")].into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_9", &value),
        Some("lookup".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_lookup_rec_with_empty_pairs_and_builtin_payload() {
    let value = PseudoExpr::RecFn {
        name: "rec_fn_9".to_string().into(),
        params: vec!["pairs".to_string().into(), "needle".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("pairs")),
            subject_name: Some("pairs".to_string().into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::builtin("List.empty_pairs", vec![PseudoExpr::var("Void")]),
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
                        then_branch: PBox::new(PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.un_map"),
                            args: vec![PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "snd".to_string(),
                            )]
                            .into(),
                        }),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("rec_fn_9")),
                            args: vec![PseudoExpr::var("tail"), PseudoExpr::var("needle")].into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_9", &value),
        Some("lookup".to_string())
    );
}
