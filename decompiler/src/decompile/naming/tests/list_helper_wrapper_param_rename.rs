use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_renames_outer_decode_credential_wrapper_params() {
    let expr = PseudoExpr::RecFn {
        name: "decode_credential".to_string().into(),
        params: vec!["list_4".to_string().into(), "acc".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "decode_credential_2".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "decode_credential_2".to_string().into(),
                params: vec!["list_5".to_string().into(), "acc_2".to_string().into()],
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("list_5")),
                    subject_name: Some("list_5".to_string().into()),
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            PseudoExpr::var("acc_2"),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec!["head".into()],
                                tail: Some("tail".into()),
                            },
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("decode_credential_2")),
                                args: vec![PseudoExpr::var("tail"), PseudoExpr::var("acc_2")]
                                    .into(),
                            },
                        ),
                    ],
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("decode_credential_2")),
                args: vec![PseudoExpr::var("list_4"), PseudoExpr::var("acc")].into(),
            }),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::RecFn { params, body, .. } => {
            assert_eq!(params[0].as_str(), "list");
            assert_eq!(params[1].as_str(), "acc");
            let body_str = format!("{body:?}");
            assert!(
                !body_str.contains("list_4") && !body_str.contains("list_5"),
                "expected wrapper list params to rename through outer and inner helpers, got: {body_str}"
            );
        }
        other => panic!("expected recfn, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_renames_let_wrapped_single_param_list_helper() {
    let expr = PseudoExpr::RecFn {
        name: "decode_credential_3".to_string().into(),
        params: vec!["list_6".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "decode_credential_4".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "decode_credential_4".to_string().into(),
                params: vec!["list_7".to_string().into(), "acc_3".to_string().into()],
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("list_7")),
                    subject_name: Some("list_7".to_string().into()),
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            PseudoExpr::var("acc_3"),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec!["head".into()],
                                tail: Some("tail".into()),
                            },
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("decode_credential_4")),
                                args: vec![PseudoExpr::var("tail"), PseudoExpr::var("acc_3")]
                                    .into(),
                            },
                        ),
                    ],
                }),
            }),
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("list_6")),
                subject_name: Some("list_6".to_string().into()),
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec![],
                            tail: None,
                        },
                        PseudoExpr::list(vec![PseudoExpr::var("seed")]),
                    ),
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec!["entry".into()],
                            tail: Some("tail".into()),
                        },
                        PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::var("cond")),
                            then_branch: PBox::new(PseudoExpr::var("seed")),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("decode_credential_3")),
                                args: vec![PseudoExpr::var("tail")].into(),
                            }),
                        },
                    ),
                ],
            }),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::RecFn { params, body, .. } => {
            assert_eq!(params[0].as_str(), "list");
            let body_str = format!("{body:?}");
            assert!(
                !body_str.contains("list_6"),
                "expected let-wrapped single-param helper to rename through body, got: {body_str}"
            );
        }
        other => panic!("expected recfn, got: {other:?}"),
    }
}
