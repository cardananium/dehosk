use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_single_letter_lookup_helper() {
    let value = PseudoExpr::RecFn {
        name: "g".to_string().into(),
        params: vec!["pairs".to_string().into()],
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
                        then_branch: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var("entry"),
                            "snd".to_string(),
                        )),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("g")),
                            args: vec![PseudoExpr::var("tail")].into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(
        analyze_function_binding("g", &value),
        Some("lookup".to_string())
    );
}

#[test]
fn test_analyze_temporary_value_binding_names_single_letter_lookup_result() {
    let value = PseudoExpr::Let {
        name: "lookup_2".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "lookup_2".to_string().into(),
            params: vec!["pairs".to_string().into()],
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
                            then_branch: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "snd".to_string(),
                            )),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("lookup_2")),
                                args: vec![PseudoExpr::var("tail")].into(),
                            }),
                        },
                    ),
                ],
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("lookup_2")),
            args: vec![PseudoExpr::var("pairs_2")].into(),
        }),
    };

    assert_eq!(
        analyze_temporary_value_binding("g", &value),
        Some("lookup_result".to_string())
    );
}
