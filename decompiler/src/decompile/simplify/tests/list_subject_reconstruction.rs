use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_if_on_list_subject_reconstructs_when_before_and_collapse() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("xs")),
        then_branch: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Or,
            left: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("pred")),
                args: vec![PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::var("xs")),
                    index: 0,
                }]
                .into(),
            }),
            right: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("rec")),
                args: vec![PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("List.tail"),
                    args: vec![PseudoExpr::var("xs")].into(),
                }]
                .into(),
            }),
        }),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(
                clauses.len(),
                2,
                "expected two list clauses, got: {clauses:?}"
            );
            assert!(
                matches!(
                    &clauses[0].pattern,
                    WhenPattern::List { elements, tail } if elements.is_empty() && tail.is_none()
                ),
                "expected empty-list first clause, got: {:?}",
                clauses[0].pattern
            );
            assert!(
                matches!(clauses[0].body, PseudoExpr::Bool(false)),
                "expected False empty branch, got: {:?}",
                clauses[0].body
            );
            assert!(
                matches!(
                    &clauses[1].pattern,
                    WhenPattern::List { elements, tail }
                        if elements == &vec!["xs_h".to_string()] && tail.as_ref().is_some_and(|b| b.as_str() == "xs_t")
                ),
                "expected [xs_h, ..xs_t] pattern, got: {:?}",
                clauses[1].pattern
            );
            let body_str = format!("{:?}", clauses[1].body);
            assert!(
                body_str.contains("xs_h"),
                "expected head binder in body: {body_str}"
            );
            assert!(
                body_str.contains("xs_t"),
                "expected tail binder in body: {body_str}"
            );
            assert!(
                !body_str.contains("List.tail"),
                "tail access should be rewritten structurally: {body_str}"
            );
        }
        other => panic!("expected When, got: {other:?}"),
    }
}

#[test]
fn test_if_on_list_subject_with_non_bool_else_reconstructs_when() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("xs")),
        then_branch: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("keep")),
                args: vec![PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::var("xs")),
                    index: 0,
                }]
                .into(),
            }),
            then_branch: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("List.cons"),
                args: vec![
                    PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::var("xs")),
                        index: 0,
                    },
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("go")),
                        args: vec![PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("List.tail"),
                            args: vec![PseudoExpr::var("xs")].into(),
                        }]
                        .into(),
                    },
                ]
                .into(),
            }),
            else_branch: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("go")),
                args: vec![PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("List.tail"),
                    args: vec![PseudoExpr::var("xs")].into(),
                }]
                .into(),
            }),
        }),
        else_branch: PBox::new(PseudoExpr::var("z")),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(
                clauses.len(),
                2,
                "expected two list clauses, got: {clauses:?}"
            );
            assert!(
                matches!(
                    &clauses[1].pattern,
                    WhenPattern::List { elements, tail }
                        if elements == &vec!["xs_h".to_string()] && tail.as_ref().is_some_and(|b| b.as_str() == "xs_t")
                ),
                "expected [xs_h, ..xs_t] pattern, got: {:?}",
                clauses[1].pattern
            );
            let body_str = format!("{:?}", clauses[1].body);
            assert!(
                body_str.contains("xs_h"),
                "expected head binder in body: {body_str}"
            );
            assert!(
                body_str.contains("xs_t"),
                "expected tail binder in body: {body_str}"
            );
            assert!(
                !body_str.contains("List.tail"),
                "tail access should be rewritten structurally: {body_str}"
            );
        }
        other => panic!("expected When, got: {other:?}"),
    }
}
