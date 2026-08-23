use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_renames_single_letter_result_from_known_function_rename() {
    let expr = PseudoExpr::Let {
        name: "fn_3".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["xs".to_string().into(), "needle".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("any_2")),
                args: vec![
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_list"),
                        args: vec![PseudoExpr::var("xs")].into(),
                    },
                    PseudoExpr::Lambda {
                        params: vec!["item".to_string().into()],
                        body: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::var("item")),
                            right: PBox::new(PseudoExpr::var("needle")),
                        }),
                    },
                ]
                .into(),
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "g".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("fn_3")),
                args: vec![PseudoExpr::var("inputs"), PseudoExpr::var("target")].into(),
            }),
            body: PBox::new(PseudoExpr::var("g")),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "contains");
            assert!(matches!(value.as_ref(), PseudoExpr::Lambda { .. }));
            match body.as_ref() {
                PseudoExpr::Let {
                    name, value, body, ..
                } => {
                    assert_eq!(name, "contains_result");
                    assert!(
                        matches!(
                            value.as_ref(),
                            PseudoExpr::Apply { function, .. }
                                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "contains")
                        ),
                        "expected contains call, got: {value:?}"
                    );
                    assert!(
                        matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "contains_result"),
                        "expected renamed result var, got: {body:?}"
                    );
                }
                other => panic!("expected inner let, got: {other:?}"),
            }
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_renames_numeric_suffix_result_from_known_function_rename() {
    let id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "fn_3".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["xs".to_string().into(), "needle".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("any_2")),
                args: vec![
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_list"),
                        args: vec![PseudoExpr::var("xs")].into(),
                    },
                    PseudoExpr::Lambda {
                        params: vec!["item".to_string().into()],
                        body: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::var("item")),
                            right: PBox::new(PseudoExpr::var("needle")),
                        }),
                    },
                ]
                .into(),
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "x_2".to_string(),
            id: Some(id),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("fn_3")),
                args: vec![PseudoExpr::var("inputs"), PseudoExpr::var("target")].into(),
            }),
            body: PBox::new(PseudoExpr::var_with_id("x_2", id)),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "contains");
            assert!(matches!(value.as_ref(), PseudoExpr::Lambda { .. }));
            match body.as_ref() {
                PseudoExpr::Let {
                    name, value, body, ..
                } => {
                    assert_eq!(name, "contains_result");
                    assert!(
                        matches!(
                            value.as_ref(),
                            PseudoExpr::Apply { function, .. }
                                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "contains")
                        ),
                        "expected contains call, got: {value:?}"
                    );
                    assert!(
                        matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "contains_result"),
                        "expected renamed numeric-suffix result var, got: {body:?}"
                    );
                }
                other => panic!("expected inner let, got: {other:?}"),
            }
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_contains_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "rec_fn_3".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "rec_fn_3".to_string().into(),
            params: vec!["list_2".to_string().into()],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("list_2")),
                subject_name: Some("list_2".to_string().into()),
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
                                left: PBox::new(PseudoExpr::var("head")),
                                right: PBox::new(PseudoExpr::var("needle")),
                            }),
                            then_branch: PBox::new(PseudoExpr::bool(true)),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("rec_fn_3")),
                                args: vec![PseudoExpr::var_with_id("tail", outer_tail_id)].into(),
                            }),
                        },
                    ),
                ],
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("rec_fn_3")),
            args: vec![PseudoExpr::var("inputs")].into(),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "rec_fn_3");
            let PseudoExpr::RecFn {
                name: rec_name,
                params,
                ..
            } = value.as_ref()
            else {
                panic!("expected recfn value, got: {value:?}");
            };
            assert_eq!(rec_name.as_str(), "rec_fn_3");
            assert_eq!(params[0].as_str(), "list_2");
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, .. }
                        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "rec_fn_3")
                ),
                "expected false-positive contains helper to stay unrenamed, got: {body:?}"
            );
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_direct_rec_any_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "fn_2".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "fn_2".to_string().into(),
            params: vec!["xs_2".to_string().into(), "pred_3".to_string().into()],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("xs_2")),
                subject_name: Some("xs_2".to_string().into()),
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec![],
                            tail: None,
                        },
                        PseudoExpr::Bool(false),
                    ),
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec!["head".into()],
                            tail: Some("tail".into()),
                        },
                        PseudoExpr::BinOp {
                            op: BinaryOp::Or,
                            left: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("pred_3")),
                                args: vec![PseudoExpr::var("head")].into(),
                            }),
                            right: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("fn_2")),
                                args: vec![
                                    PseudoExpr::var_with_id("tail", outer_tail_id),
                                    PseudoExpr::var("pred_3"),
                                ]
                                .into(),
                            }),
                        },
                    ),
                ],
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("fn_2")),
            args: vec![PseudoExpr::var("inputs"), PseudoExpr::var("predicate")].into(),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "fn_2");
            let PseudoExpr::RecFn {
                name: rec_name,
                params,
                ..
            } = value.as_ref()
            else {
                panic!("expected recfn value, got: {value:?}");
            };
            assert_eq!(rec_name.as_str(), "fn_2");
            assert_eq!(params[0].as_str(), "xs_2");
            assert_eq!(params[1].as_str(), "pred_3");
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, .. }
                        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "fn_2")
                ),
                "expected false-positive any helper to stay unrenamed, got: {body:?}"
            );
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_if_empty_all_tail_ref() {
    let wrong_list_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "rec_fn_39".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "rec_fn_39".to_string().into(),
            params: vec!["x_148".to_string().into(), "y_41".to_string().into()],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::ListIsEmpty,
                    args: vec![PseudoExpr::var("x_148")].into(),
                }),
                then_branch: PBox::new(PseudoExpr::bool(true)),
                else_branch: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::And,
                    left: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("y_41")),
                        args: vec![PseudoExpr::field_access(
                            PseudoExpr::var_with_id("x_148", wrong_list_id),
                            "head".to_string(),
                        )]
                        .into(),
                    }),
                    right: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("rec_fn_39")),
                        args: vec![
                            PseudoExpr::BuiltinCall {
                                name: crate::BuiltinId::ListTail,
                                args: vec![PseudoExpr::var_with_id("x_148", wrong_list_id)].into(),
                            },
                            PseudoExpr::var("y_41"),
                        ]
                        .into(),
                    }),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("rec_fn_39")),
            args: vec![PseudoExpr::var("inputs"), PseudoExpr::var("predicate")].into(),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "rec_fn_39");
            let PseudoExpr::RecFn {
                name: rec_name,
                params,
                ..
            } = value.as_ref()
            else {
                panic!("expected recfn value, got: {value:?}");
            };
            assert_eq!(rec_name.as_str(), "rec_fn_39");
            assert_eq!(params[0].as_str(), "x_148");
            assert_eq!(params[1].as_str(), "y_41");
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, .. }
                        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "rec_fn_39")
                ),
                "expected false-positive if_empty all helper to stay unrenamed, got: {body:?}"
            );
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_renames_rec_fn_result_from_known_function_rename() {
    let id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "rec_fn_3".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "rec_fn_3".to_string().into(),
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
                                function: PBox::new(PseudoExpr::var("rec_fn_3")),
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
        body: PBox::new(PseudoExpr::Let {
            name: "rec_fn_3_result".to_string(),
            id: Some(id),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("rec_fn_3")),
                args: vec![PseudoExpr::var("values"), PseudoExpr::var("idx")].into(),
            }),
            body: PBox::new(PseudoExpr::var_with_id("rec_fn_3_result", id)),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "get_at");
            match body.as_ref() {
                PseudoExpr::Let { name, body, .. } => {
                    assert_eq!(name, "get_at_result");
                    assert!(
                        matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "get_at_result"),
                        "expected rec_fn result alias to rename through body, got: {body:?}"
                    );
                }
                other => panic!("expected inner let, got: {other:?}"),
            }
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}
