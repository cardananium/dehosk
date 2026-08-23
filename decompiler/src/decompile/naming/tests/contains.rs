use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_contains_wrapper() {
    let value = PseudoExpr::Lambda {
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
    };

    assert_eq!(
        analyze_function_binding("fn_3", &value),
        Some("contains".to_string())
    );
}

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_contains_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let value = PseudoExpr::RecFn {
        name: "rec_fn_3".to_string().into(),
        params: vec!["list".to_string().into()],
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
    };

    assert_eq!(analyze_function_binding("rec_fn_3", &value), None);
}

#[test]
fn test_analyze_function_binding_names_any_data_list_wrapper() {
    let value = PseudoExpr::Lambda {
        params: vec!["xs".to_string().into(), "pred".to_string().into()],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("any_2")),
            args: vec![
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_list"),
                    args: vec![PseudoExpr::var("xs")].into(),
                },
                PseudoExpr::var("pred"),
            ]
            .into(),
        }),
    };

    assert_eq!(
        analyze_function_binding("f_8", &value),
        Some("any_data_list".to_string())
    );
}
