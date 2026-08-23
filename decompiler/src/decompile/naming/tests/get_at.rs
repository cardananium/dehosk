use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_get_at_wrapper() {
    let value = PseudoExpr::Lambda {
        params: vec!["xs".to_string().into(), "idx".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "rec_fn".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "rec_fn".to_string().into(),
                params: vec!["list".to_string().into(), "index".to_string().into()],
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("list")),
                    subject_name: Some("list".to_string().into()),
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
                                elements: vec!["head".into()],
                                tail: Some("tail".into()),
                            },
                            PseudoExpr::If {
                                condition: PBox::new(PseudoExpr::BinOp {
                                    op: BinaryOp::Eq,
                                    left: PBox::new(PseudoExpr::var("index")),
                                    right: PBox::new(PseudoExpr::int(0)),
                                }),
                                then_branch: PBox::new(PseudoExpr::constr_known(
                                    KnownConstructor::Some,
                                    vec![PseudoExpr::var("head")],
                                )),
                                else_branch: PBox::new(PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("rec_fn")),
                                    args: vec![
                                        PseudoExpr::var("tail"),
                                        PseudoExpr::BinOp {
                                            op: BinaryOp::Sub,
                                            left: PBox::new(PseudoExpr::var("index")),
                                            right: PBox::new(PseudoExpr::int(1)),
                                        },
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
                args: vec![PseudoExpr::var("xs"), PseudoExpr::var("idx")].into(),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_11", &value),
        Some("get_at".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_direct_rec_get_at() {
    let value = PseudoExpr::RecFn {
        name: "fn_12".to_string().into(),
        params: vec!["idx".to_string().into(), "xs".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("xs")),
            subject_name: Some("xs".to_string().into()),
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
                        elements: vec!["head".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::var("idx")),
                            right: PBox::new(PseudoExpr::int(0)),
                        }),
                        then_branch: PBox::new(PseudoExpr::constr_known(
                            KnownConstructor::Some,
                            vec![PseudoExpr::var("head")],
                        )),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("fn_12")),
                            args: vec![
                                PseudoExpr::BinOp {
                                    op: BinaryOp::Sub,
                                    left: PBox::new(PseudoExpr::var("idx")),
                                    right: PBox::new(PseudoExpr::int(1)),
                                },
                                PseudoExpr::var("tail"),
                            ]
                            .into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_12", &value),
        Some("get_at".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_direct_rec_get_at_with_false_none() {
    let value = PseudoExpr::RecFn {
        name: "fn_12".to_string().into(),
        params: vec!["idx".to_string().into(), "xs".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("xs")),
            subject_name: Some("xs".to_string().into()),
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
                        elements: vec!["head".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::var("idx")),
                            right: PBox::new(PseudoExpr::int(0)),
                        }),
                        then_branch: PBox::new(PseudoExpr::constr_known(
                            KnownConstructor::Some,
                            vec![PseudoExpr::var("head")],
                        )),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("fn_12")),
                            args: vec![
                                PseudoExpr::BinOp {
                                    op: BinaryOp::Sub,
                                    left: PBox::new(PseudoExpr::var("idx")),
                                    right: PBox::new(PseudoExpr::int(1)),
                                },
                                PseudoExpr::var("tail"),
                            ]
                            .into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_12", &value),
        Some("get_at".to_string())
    );
}

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_get_at_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let value = PseudoExpr::RecFn {
        name: "fn_12".to_string().into(),
        params: vec!["idx".to_string().into(), "xs".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("xs")),
            subject_name: Some("xs".to_string().into()),
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
                        elements: vec!["head".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::var("idx")),
                            right: PBox::new(PseudoExpr::int(0)),
                        }),
                        then_branch: PBox::new(PseudoExpr::constr_known(
                            KnownConstructor::Some,
                            vec![PseudoExpr::var("head")],
                        )),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("fn_12")),
                            args: vec![
                                PseudoExpr::BinOp {
                                    op: BinaryOp::Sub,
                                    left: PBox::new(PseudoExpr::var("idx")),
                                    right: PBox::new(PseudoExpr::int(1)),
                                },
                                PseudoExpr::var_with_id("tail", outer_tail_id),
                            ]
                            .into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(analyze_function_binding("fn_12", &value), None);
}
