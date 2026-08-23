use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_list_find_wrapper() {
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
                            PseudoExpr::error(),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec!["head".into()],
                                tail: Some("tail".into()),
                            },
                            PseudoExpr::If {
                                condition: PBox::new(PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("predicate")),
                                    args: vec![PseudoExpr::var("head")].into(),
                                }),
                                then_branch: PBox::new(PseudoExpr::var("head")),
                                else_branch: PBox::new(PseudoExpr::Apply {
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
        analyze_function_binding("rec_fn_7", &value),
        Some("find".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_list_find_wrapper_with_false_none() {
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
                            PseudoExpr::bool(false),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec!["head".into()],
                                tail: Some("tail".into()),
                            },
                            PseudoExpr::If {
                                condition: PBox::new(PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("predicate")),
                                    args: vec![PseudoExpr::var("head")].into(),
                                }),
                                then_branch: PBox::new(PseudoExpr::constr_known(
                                    KnownConstructor::Some,
                                    vec![PseudoExpr::var("head")],
                                )),
                                else_branch: PBox::new(PseudoExpr::Apply {
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
        analyze_function_binding("rec_fn_7", &value),
        Some("find".to_string())
    );
}
