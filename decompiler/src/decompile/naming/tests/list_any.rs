use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_list_any_wrapper() {
    let value = PseudoExpr::Lambda {
        params: vec!["xs".to_string().into(), "pred".to_string().into()],
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
                                    function: PBox::new(PseudoExpr::var("predicate")),
                                    args: vec![PseudoExpr::var("head")].into(),
                                }),
                                right: PBox::new(PseudoExpr::Apply {
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
        analyze_function_binding("fn_2", &value),
        Some("any".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_direct_rec_any() {
    let value = PseudoExpr::RecFn {
        name: "fn_2".to_string().into(),
        params: vec!["xs".to_string().into(), "pred".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("xs")),
            subject_name: Some("xs".to_string().into()),
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
                            function: PBox::new(PseudoExpr::var("pred")),
                            args: vec![PseudoExpr::var("head")].into(),
                        }),
                        right: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("fn_2")),
                            args: vec![PseudoExpr::var("tail"), PseudoExpr::var("pred")].into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_2", &value),
        Some("any".to_string())
    );
}
