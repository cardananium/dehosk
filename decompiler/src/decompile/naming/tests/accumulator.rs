use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_accumulator_sum_wrapper() {
    let value = PseudoExpr::RecFn {
        name: "fn_7".to_string().into(),
        params: vec!["list".to_string().into(), "acc".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("list")),
            subject_name: Some("list".to_string().into()),
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
                        function: PBox::new(PseudoExpr::var("fn_7")),
                        args: vec![
                            PseudoExpr::var("tail"),
                            PseudoExpr::BinOp {
                                op: BinaryOp::Add,
                                left: PBox::new(PseudoExpr::var("acc")),
                                right: PBox::new(PseudoExpr::var("head")),
                            },
                        ]
                        .into(),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_7", &value),
        Some("sum".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_accumulator_max_wrapper() {
    let value = PseudoExpr::RecFn {
        name: "fn_8".to_string().into(),
        params: vec!["list".to_string().into(), "current_max".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("list")),
            subject_name: Some("list".to_string().into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::var("current_max"),
                ),
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec!["head".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Gt,
                            left: PBox::new(PseudoExpr::var("head")),
                            right: PBox::new(PseudoExpr::var("current_max")),
                        }),
                        then_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("fn_8")),
                            args: vec![PseudoExpr::var("tail"), PseudoExpr::var("head")].into(),
                        }),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("fn_8")),
                            args: vec![PseudoExpr::var("tail"), PseudoExpr::var("current_max")]
                                .into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_8", &value),
        Some("max".to_string())
    );
}
