use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_single_param_list_rec_names_explicit_contains_shape() {
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("list")),
        subject_name: Some("list".into()),
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
                        args: vec![PseudoExpr::var("tail")].into(),
                    }),
                },
            ),
        ],
    };

    assert_eq!(
        analyze_single_param_list_rec(
            "rec_fn_3",
            Some(VarId::fresh_binding()),
            &["list".into()],
            &body,
        ),
        Some("contains".to_string())
    );
}

#[test]
fn test_analyze_single_param_list_rec_names_explicit_all_shape() {
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("list")),
        subject_name: Some("list".into()),
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::bool(true),
            ),
            WhenClause::new(
                WhenPattern::List {
                    elements: vec!["head".into()],
                    tail: Some("tail".into()),
                },
                PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("pred")),
                        args: vec![PseudoExpr::var("head")].into(),
                    }),
                    then_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("rec_fn_4")),
                        args: vec![PseudoExpr::var("tail")].into(),
                    }),
                    else_branch: PBox::new(PseudoExpr::bool(false)),
                },
            ),
        ],
    };

    assert_eq!(
        analyze_single_param_list_rec(
            "rec_fn_4",
            Some(VarId::fresh_binding()),
            &["list".into()],
            &body,
        ),
        Some("all".to_string())
    );
}

#[test]
fn test_analyze_single_param_list_rec_names_explicit_any_shape() {
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("list")),
        subject_name: Some("list".into()),
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
                        function: PBox::new(PseudoExpr::var("pred")),
                        args: vec![PseudoExpr::var("head")].into(),
                    }),
                    then_branch: PBox::new(PseudoExpr::bool(true)),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("rec_fn_5")),
                        args: vec![PseudoExpr::var("tail")].into(),
                    }),
                },
            ),
        ],
    };

    assert_eq!(
        analyze_single_param_list_rec(
            "rec_fn_5",
            Some(VarId::fresh_binding()),
            &["list".into()],
            &body,
        ),
        Some("any".to_string())
    );
}

#[test]
fn test_analyze_single_param_list_rec_names_explicit_count_shape() {
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("list")),
        subject_name: Some("list".into()),
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
                    elements: vec!["head".into()],
                    tail: Some("tail".into()),
                },
                PseudoExpr::Let {
                    name: "count_result".to_string(),
                    id: Some(VarId::fresh_compat_placeholder()),
                    value: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("rec_fn_6")),
                        args: vec![PseudoExpr::var("tail")].into(),
                    }),
                    body: PBox::new(PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("pred")),
                            args: vec![PseudoExpr::var("head")].into(),
                        }),
                        then_branch: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Add,
                            left: PBox::new(PseudoExpr::var("count_result")),
                            right: PBox::new(PseudoExpr::int(1)),
                        }),
                        else_branch: PBox::new(PseudoExpr::var("count_result")),
                    }),
                },
            ),
        ],
    };

    assert_eq!(
        analyze_single_param_list_rec(
            "rec_fn_6",
            Some(VarId::fresh_binding()),
            &["list".into()],
            &body,
        ),
        Some("count".to_string())
    );
}
