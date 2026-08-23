use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_renames_let_bound_recfn_binder_without_duplicate_analysis() {
    let expr = PseudoExpr::Let {
        name: "rec_fn_3".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "rec_fn_3".to_string().into(),
            params: vec!["list_2".to_string().into(), "acc_3".to_string().into()],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("list_2")),
                subject_name: Some("list_2".to_string().into()),
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
                                left: PBox::new(PseudoExpr::var("acc_3")),
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
                                        left: PBox::new(PseudoExpr::var("acc_3")),
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
            function: PBox::new(PseudoExpr::var("rec_fn_3")),
            args: vec![PseudoExpr::var("values"), PseudoExpr::var("idx")].into(),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "get_at");
            let PseudoExpr::RecFn {
                name: rec_name,
                params,
                body: rec_body,
            } = value.as_ref()
            else {
                panic!("expected let-bound recfn value, got: {value:?}");
            };
            assert_eq!(rec_name.as_str(), "get_at");
            assert_eq!(params[0].as_str(), "list");
            assert_eq!(params[1].as_str(), "index");
            let body_str = format!("{rec_body:?}");
            assert!(
                body_str.contains("name: \"get_at\"")
                    && body_str.contains("subject_name: Some(Binder { name: \"list\"")
                    && body_str.contains("name: \"index\"")
                    && !body_str.contains("rec_fn_3")
                    && !body_str.contains("list_2")
                    && !body_str.contains("acc_3"),
                "expected let-bound recfn rename to propagate without duplicate analysis, got: {body_str}"
            );
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, .. }
                        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "get_at")
                ),
                "expected call site to reuse renamed let-bound recfn, got: {body:?}"
            );
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_renames_get_at_params_to_list_and_index() {
    let expr = PseudoExpr::RecFn {
        name: "rec_fn_7".to_string().into(),
        params: vec!["list_2".to_string().into(), "acc_3".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("list_2")),
            subject_name: Some("list_2".to_string().into()),
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
                            left: PBox::new(PseudoExpr::var("acc_3")),
                            right: PBox::new(PseudoExpr::int(0)),
                        }),
                        then_branch: PBox::new(PseudoExpr::constr_known(
                            KnownConstructor::Some,
                            vec![PseudoExpr::var("head")],
                        )),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("rec_fn_7")),
                            args: vec![
                                PseudoExpr::var("tail"),
                                PseudoExpr::BinOp {
                                    op: BinaryOp::Sub,
                                    left: PBox::new(PseudoExpr::var("acc_3")),
                                    right: PBox::new(PseudoExpr::int(1)),
                                },
                            ]
                            .into(),
                        }),
                    },
                ),
            ],
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::RecFn { name, params, body } => {
            assert_eq!(name.as_str(), "get_at");
            assert_eq!(params[0].as_str(), "list");
            assert_eq!(params[1].as_str(), "index");
            let body_str = format!("{body:?}");
            assert!(
                body_str.contains("subject_name: Some(Binder { name: \"list\"")
                    && body_str.contains("name: \"index\"")
                    && !body_str.contains("list_2")
                    && !body_str.contains("acc_3"),
                "expected get_at params to rename through body, got: {body_str}"
            );
        }
        other => panic!("expected recfn, got: {other:?}"),
    }
}
