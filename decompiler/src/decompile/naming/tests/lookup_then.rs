use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_lookup_then_rec() {
    let value = PseudoExpr::RecFn {
        name: "rec_fn_3".to_string().into(),
        params: vec!["cont".to_string().into(), "pairs".to_string().into()],
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
                        then_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("cont")),
                            args: vec![
                                PseudoExpr::var("cont"),
                                PseudoExpr::BuiltinCall {
                                    name: crate::BuiltinId::expect_known("Data.un_map"),
                                    args: vec![PseudoExpr::field_access(
                                        PseudoExpr::var("entry"),
                                        "snd".to_string(),
                                    )]
                                    .into(),
                                },
                            ]
                            .into(),
                        }),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("rec_fn_3")),
                            args: vec![PseudoExpr::var("cont"), PseudoExpr::var("tail")].into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_3", &value),
        Some("lookup_then".to_string())
    );
}

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_lookup_then_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let value = PseudoExpr::RecFn {
        name: "rec_fn_3".to_string().into(),
        params: vec!["cont".to_string().into(), "pairs".to_string().into()],
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
                        then_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("cont")),
                            args: vec![
                                PseudoExpr::var("cont"),
                                PseudoExpr::BuiltinCall {
                                    name: crate::BuiltinId::expect_known("Data.un_map"),
                                    args: vec![PseudoExpr::field_access(
                                        PseudoExpr::var("entry"),
                                        "snd".to_string(),
                                    )]
                                    .into(),
                                },
                            ]
                            .into(),
                        }),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("rec_fn_3")),
                            args: vec![
                                PseudoExpr::var("cont"),
                                PseudoExpr::var_with_id("tail", outer_tail_id),
                            ]
                            .into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(analyze_function_binding("rec_fn_3", &value), None);
}
