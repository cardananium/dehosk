use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_inline_list_pair_destructure() {
    // when xs is { _ -> xs[0].fst + f(List.tail(xs)) }
    // should become: when xs is { [xs_h, ..xs_t] -> xs_h.fst + f(xs_t) }
    let subject = PseudoExpr::var("xs");
    let head_access = PseudoExpr::field_access(
        PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("xs")),
            index: 0,
        },
        "fst".to_string(),
    );
    let tail_access = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![PseudoExpr::var("xs")].into(),
        }]
        .into(),
    };
    let body = PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(head_access),
        right: PBox::new(tail_access),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body,
        }],
    };
    let simplified = simplify(expr);
    // Should have a List pattern now
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            match &clauses[0].pattern {
                WhenPattern::List { elements, tail } => {
                    assert_eq!(elements, &vec!["xs_h".to_string()]);
                    assert_eq!(tail.as_ref().map(|b| b.as_str()), Some("xs_t"));
                }
                other => panic!("expected List pattern, got: {:?}", other),
            }
            let body_str = format!("{:?}", clauses[0].body);
            assert!(
                body_str.contains("xs_h"),
                "body should contain xs_h: {:?}",
                clauses[0].body
            );
            assert!(
                body_str.contains("xs_t"),
                "body should contain xs_t: {:?}",
                clauses[0].body
            );
        }
        _ => panic!("expected When, got: {:?}", simplified),
    }
}

#[test]
fn test_if_on_list_subject_with_head_field_access_reconstructs_when() {
    let head = || PseudoExpr::field_access(PseudoExpr::var("xs"), "head".to_string());

    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("xs")),
        then_branch: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("keep")),
                args: vec![head()].into(),
            }),
            then_branch: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("List.cons"),
                args: vec![
                    head(),
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
                !body_str.contains("field: \"head\""),
                "head field access should be rewritten structurally: {body_str}"
            );
        }
        other => panic!("expected When, got: {other:?}"),
    }
}

#[test]
fn test_if_on_raw_constr_unpack_tag_comparison_becomes_constructor_when() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::field_access(
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Constr.unpack"),
                    args: vec![PseudoExpr::var("redeemer")].into(),
                },
                "fst".to_string(),
            )),
            right: PBox::new(PseudoExpr::int(0)),
        }),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Error { message: None }),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(
                matches!(subject.as_ref(), PseudoExpr::Var { name, .. } if name == "redeemer"),
                "expected redeemer subject, got: {subject:?}"
            );
            assert_eq!(clauses.len(), 2, "expected two clauses, got: {clauses:?}");
            assert!(
                matches!(
                    &clauses[0].pattern,
                    WhenPattern::Constructor {
                        tag: 0,
                        fields,
                        ..
                    } if fields.is_empty()
                ),
                "expected Constr<0> first clause, got: {:?}",
                clauses[0].pattern
            );
            assert!(
                matches!(clauses[0].body, PseudoExpr::Bool(true)),
                "expected true body in matching constructor branch, got: {:?}",
                clauses[0].body
            );
            assert!(
                matches!(clauses[1].pattern, WhenPattern::Wildcard),
                "expected wildcard fallback, got: {:?}",
                clauses[1].pattern
            );
        }
        other => panic!("expected constructor when, got: {other:?}"),
    }
}

#[test]
fn test_inline_list_head_only_destructure() {
    // when xs is { _ -> xs[0] + 1 }
    // should become: when xs is { [xs_h, .._] -> xs_h + 1 }
    let body = PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("xs")),
            index: 0,
        }),
        right: PBox::new(PseudoExpr::int(1)),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("xs")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body,
        }],
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => match &clauses[0].pattern {
            WhenPattern::List { elements, tail } => {
                assert_eq!(elements, &vec!["xs_h".to_string()]);
                assert_local_simplifier_binder(tail.as_ref().unwrap(), "_");
            }
            other => panic!("expected List pattern, got: {:?}", other),
        },
        _ => panic!("expected When, got: {:?}", simplified),
    }
}

#[test]
fn test_inline_list_head_field_access_destructure() {
    let body = PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("xs"),
            "head".to_string(),
        )),
        right: PBox::new(PseudoExpr::int(1)),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("xs")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body,
        }],
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => match &clauses[0].pattern {
            WhenPattern::List { elements, tail } => {
                assert_eq!(elements, &vec!["xs_h".to_string()]);
                assert_eq!(tail.as_ref().map(|b| b.as_str()), Some("_"));
            }
            other => panic!("expected List pattern, got: {:?}", other),
        },
        _ => panic!("expected When, got: {:?}", simplified),
    }
}

#[test]
fn test_inline_list_tail_only_destructure() {
    // when xs is { _ -> f(List.tail(xs)) }
    // should become: when xs is { [_, ..xs_t] -> f(xs_t) }
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![PseudoExpr::var("xs")].into(),
        }]
        .into(),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("xs")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body,
        }],
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => match &clauses[0].pattern {
            WhenPattern::List { elements, tail } => {
                assert_eq!(elements, &vec!["_".to_string()]);
                assert_local_simplifier_binder(&elements[0], "_");
                assert_eq!(tail.as_ref().map(|b| b.as_str()), Some("xs_t"));
            }
            other => panic!("expected List pattern, got: {:?}", other),
        },
        _ => panic!("expected When, got: {:?}", simplified),
    }
}

#[test]
fn test_inline_list_destructure_apply_form_tail() {
    // when xs is { _ -> Apply(BuiltinCall("List.tail", []), [xs]) }
    // should become: when xs is { [_, ..xs_t] -> xs_t }
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![].into(),
        }),
        args: vec![PseudoExpr::var("xs")].into(),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("xs")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body,
        }],
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => match &clauses[0].pattern {
            WhenPattern::List { elements, tail } => {
                assert_eq!(elements, &vec!["_".to_string()]);
                assert_local_simplifier_binder(&elements[0], "_");
                assert_eq!(tail.as_ref().map(|b| b.as_str()), Some("xs_t"));
            }
            other => panic!("expected List pattern, got: {:?}", other),
        },
        _ => panic!("expected When, got: {:?}", simplified),
    }
}

#[test]
fn test_inline_list_destructure_with_subject_name() {
    // when expr is xs { _ -> xs[0] + f(List.tail(xs)) }
    // should become: when expr is xs { [xs_h, ..xs_t] -> xs_h + f(xs_t) }
    let body = PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("xs")),
            index: 0,
        }),
        right: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("List.tail"),
                args: vec![PseudoExpr::var("xs")].into(),
            }]
            .into(),
        }),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::int(999)),
        subject_name: Some("xs".to_string().into()),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body,
        }],
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => match &clauses[0].pattern {
            WhenPattern::List { elements, tail } => {
                assert_eq!(elements, &vec!["xs_h".to_string()]);
                assert_eq!(tail.as_ref().map(|b| b.as_str()), Some("xs_t"));
            }
            other => panic!("expected List pattern, got: {:?}", other),
        },
        _ => panic!("expected When, got: {:?}", simplified),
    }
}
