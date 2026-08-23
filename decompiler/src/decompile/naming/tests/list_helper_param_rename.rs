use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_renames_multi_suffix_list_acc_params() {
    let expr = PseudoExpr::RecFn {
        name: "decode_credential".to_string().into(),
        params: vec!["list_2_2".to_string().into(), "acc".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("list_2_2")),
            subject_name: Some("list_2_2".to_string().into()),
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
                        elements: vec!["head".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("decode_credential")),
                        args: vec![PseudoExpr::var("tail"), PseudoExpr::var("acc")].into(),
                    },
                ),
            ],
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::RecFn { params, body, .. } => {
            assert_eq!(params[0].as_str(), "list");
            assert_eq!(params[1].as_str(), "acc");
            let body_str = format!("{body:?}");
            assert!(
                !body_str.contains("list_2_2"),
                "expected multi-suffix list param to rename through body, got: {body_str}"
            );
        }
        other => panic!("expected recfn, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_renames_nested_accumulator_helper_params() {
    let expr = PseudoExpr::RecFn {
        name: "decode_credential_2".to_string().into(),
        params: vec!["list".to_string().into(), "acc_2".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("list")),
            subject_name: Some("list".to_string().into()),
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
                        elements: vec!["entry".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("decode_credential_2")),
                        args: vec![
                            PseudoExpr::var("tail"),
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("decode_credential_3")),
                                args: vec![PseudoExpr::var("acc_2")].into(),
                            },
                        ]
                        .into(),
                    },
                ),
            ],
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::RecFn { params, body, .. } => {
            assert_eq!(params[0].as_str(), "list");
            assert_eq!(params[1].as_str(), "acc");
            let body_str = format!("{body:?}");
            assert!(
                !body_str.contains("acc_2"),
                "expected accumulator helper param to rename through body, got: {body_str}"
            );
        }
        other => panic!("expected recfn, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_renames_outer_decode_credential_list_param() {
    let expr = PseudoExpr::RecFn {
        name: "decode_credential".to_string().into(),
        params: vec!["list_4".to_string().into(), "acc".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("list_4")),
            subject_name: Some("list_4".to_string().into()),
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
                        elements: vec!["head".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("decode_credential")),
                        args: vec![
                            PseudoExpr::var("tail"),
                            PseudoExpr::If {
                                condition: PBox::new(PseudoExpr::var("cond")),
                                then_branch: PBox::new(PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("decode_credential_2")),
                                    args: vec![PseudoExpr::var("acc"), PseudoExpr::var("payload")]
                                        .into(),
                                }),
                                else_branch: PBox::new(PseudoExpr::var("acc")),
                            },
                        ]
                        .into(),
                    },
                ),
            ],
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::RecFn { params, body, .. } => {
            assert_eq!(params[0].as_str(), "list");
            assert_eq!(params[1].as_str(), "acc");
            let body_str = format!("{body:?}");
            assert!(
                !body_str.contains("list_4"),
                "expected outer decode_credential list param to rename through body, got: {body_str}"
            );
        }
        other => panic!("expected recfn, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_renames_nested_single_param_list_helper() {
    let expr = PseudoExpr::RecFn {
        name: "decode_credential_3".to_string().into(),
        params: vec!["list_6".to_string().into()],
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
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::RecFn { params, body, .. } => {
            assert_eq!(params[0].as_str(), "list");
            let body_str = format!("{body:?}");
            assert!(
                !body_str.contains("list_6"),
                "expected nested single-param list helper to rename through body, got: {body_str}"
            );
        }
        other => panic!("expected recfn, got: {other:?}"),
    }
}
