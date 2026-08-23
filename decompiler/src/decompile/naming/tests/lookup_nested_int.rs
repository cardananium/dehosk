use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_lookup_nested_int_wrapper() {
    let value = PseudoExpr::Lambda {
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
                        subject: PBox::new(PseudoExpr::var("lookup_result_2")),
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
    };

    assert_eq!(
        analyze_function_binding("fn_2", &value),
        Some("lookup_nested_int".to_string())
    );
}

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_lookup_nested_int_bridge_subject() {
    let outer_lookup_result_id = VarId::fresh_binding();
    let value = PseudoExpr::Lambda {
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
    };

    assert_eq!(analyze_function_binding("fn_2", &value), None);
}
