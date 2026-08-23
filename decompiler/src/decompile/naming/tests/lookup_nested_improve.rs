use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_renames_nested_lookup_int_wrapper_and_params() {
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

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "lookup_nested_int");
            let PseudoExpr::Lambda {
                params,
                body: lambda_body,
            } = value.as_ref()
            else {
                panic!("expected lambda value, got: {value:?}");
            };
            assert_eq!(params[0].as_str(), "pairs");
            assert_eq!(params[1].as_str(), "needle");
            assert_eq!(params[2].as_str(), "nested_needle");
            let body_str = format!("{lambda_body:?}");
            assert!(
                body_str.contains("name: \"pairs\"")
                    && body_str.contains("name: \"needle\"")
                    && body_str.contains("name: \"nested_needle\"")
                    && !body_str.contains("x_6")
                    && !body_str.contains("y_3")
                    && !body_str.contains("z_2")
                    && !body_str.contains("name: \"l2\""),
                "expected nested lookup int wrapper params to rename through body, got: {body_str}"
            );
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, .. }
                        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "lookup_nested_int")
                ),
                "expected call site to rename fn_2, got: {body:?}"
            );
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}
