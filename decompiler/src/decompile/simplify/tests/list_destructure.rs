use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_list_head_tail_destructure_both() {
    // when y is { [] -> Void; _ -> let h = y[0]; let t = List.tail(y); use(h, t) }
    // should become: when y is { [] -> Void; [h, ..t] -> use(h, t) }
    let h_id = VarId::new(131);
    let t_id = VarId::new(132);
    let use_body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("use")),
        args: vec![
            PseudoExpr::var_with_id("h", h_id),
            PseudoExpr::var_with_id("t", t_id),
        ]
        .into(),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("y")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::Unit,
            ),
            WhenClause::new(
                WhenPattern::Wildcard,
                PseudoExpr::Let {
                    name: "h".to_string(),
                    id: Some(h_id),
                    value: PBox::new(PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::var("y")),
                        index: 0,
                    }),
                    body: PBox::new(PseudoExpr::Let {
                        name: "t".to_string(),
                        id: Some(t_id),
                        value: PBox::new(PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("List.tail"),
                            args: vec![PseudoExpr::var("y")].into(),
                        }),
                        body: PBox::new(use_body),
                    }),
                },
            ),
        ],
    };

    let simplified = simplify(expr);
    let output = simplified.to_pretty();
    eprintln!("OUTPUT:\n{}", output);
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 2);
            match &clauses[1].pattern {
                WhenPattern::List { elements, tail } => {
                    assert_eq!(elements.len(), 1);
                    assert_eq!(elements[0].as_str(), "h");
                    assert_eq!(elements[0].id, h_id);
                    let Some(tail) = tail.as_ref() else {
                        panic!("expected tail binder");
                    };
                    assert_eq!(tail.as_str(), "t");
                    assert_eq!(tail.id, t_id);
                }
                other => panic!("expected List pattern, got {:?}", other),
            }
            assert!(
                matches!(
                    &clauses[1].body,
                    PseudoExpr::Apply { args, .. }
                        if matches!(&args[0], PseudoExpr::Var { name, id, .. } if name == "h" && *id == Some(h_id))
                            && matches!(&args[1], PseudoExpr::Var { name, id, .. } if name == "t" && *id == Some(t_id))
                ),
                "expected list destructure body to preserve head/tail ids, got: {:?}",
                clauses[1].body
            );
        }
        _ => panic!("expected When, got {:?}", simplified),
    }
}

#[test]
fn test_list_head_tail_destructure_apply_form() {
    // Same but with List.tail in Apply(BuiltinCall) form
    let h_id = VarId::new(133);
    let t_id = VarId::new(134);
    let use_body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("use")),
        args: vec![
            PseudoExpr::var_with_id("h", h_id),
            PseudoExpr::var_with_id("t", t_id),
        ]
        .into(),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("y")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::Unit,
            ),
            WhenClause::new(
                WhenPattern::Wildcard,
                PseudoExpr::Let {
                    name: "h".to_string(),
                    id: Some(h_id),
                    value: PBox::new(PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::var("y")),
                        index: 0,
                    }),
                    body: PBox::new(PseudoExpr::Let {
                        name: "t".to_string(),
                        id: Some(t_id),
                        value: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::BuiltinCall {
                                name: crate::BuiltinId::expect_known("List.tail"),
                                args: vec![].into(),
                            }),
                            args: vec![PseudoExpr::var("y")].into(),
                        }),
                        body: PBox::new(use_body),
                    }),
                },
            ),
        ],
    };

    let simplified = simplify(expr);
    let output = simplified.to_pretty();
    eprintln!("OUTPUT:\n{}", output);
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 2);
            match &clauses[1].pattern {
                WhenPattern::List { elements, tail } => {
                    assert_eq!(elements.len(), 1);
                    assert_eq!(elements[0].as_str(), "h");
                    assert_eq!(elements[0].id, h_id);
                    let Some(tail) = tail.as_ref() else {
                        panic!("expected tail binder");
                    };
                    assert_eq!(tail.as_str(), "t");
                    assert_eq!(tail.id, t_id);
                }
                other => panic!("expected List pattern, got {:?}", other),
            }
            assert!(
                matches!(
                    &clauses[1].body,
                    PseudoExpr::Apply { args, .. }
                        if matches!(&args[0], PseudoExpr::Var { name, id, .. } if name == "h" && *id == Some(h_id))
                            && matches!(&args[1], PseudoExpr::Var { name, id, .. } if name == "t" && *id == Some(t_id))
                ),
                "expected apply-form list destructure body to preserve head/tail ids, got: {:?}",
                clauses[1].body
            );
        }
        _ => panic!("expected When, got {:?}", simplified),
    }
}

#[test]
fn test_scott_list_emptiness_check() {
    // y_18(fn(_) { False }, True) -> when y_18 is { [] -> False; _ -> True }
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("y_18")),
        args: vec![
            PseudoExpr::Lambda {
                params: vec!["_".to_string().into()],
                body: PBox::new(PseudoExpr::Bool(false)),
            },
            PseudoExpr::Bool(true),
        ]
        .into(),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(matches!(subject.as_ref(), PseudoExpr::Var { .. }));
            assert_eq!(clauses.len(), 2);
            match &clauses[0].pattern {
                WhenPattern::List { elements, tail, .. } => {
                    assert!(elements.is_empty());
                    assert!(tail.is_none());
                }
                other => panic!("expected empty list pattern, got {:?}", other),
            }
            assert!(matches!(clauses[0].body, PseudoExpr::Bool(false)));
            assert!(matches!(clauses[1].pattern, WhenPattern::Wildcard));
            assert!(matches!(clauses[1].body, PseudoExpr::Bool(true)));
        }
        _ => panic!("expected When, got {:?}", simplified),
    }
}

#[test]
fn test_scott_list_emptiness_check_inverted() {
    // expr(fn(_) { True }, False) -> when expr is { [] -> True; _ -> False }
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("xs")),
        args: vec![
            PseudoExpr::Lambda {
                params: vec!["_".to_string().into()],
                body: PBox::new(PseudoExpr::Bool(true)),
            },
            PseudoExpr::Bool(false),
        ]
        .into(),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(matches!(subject.as_ref(), PseudoExpr::Var { .. }));
            assert_eq!(clauses.len(), 2);
            assert!(matches!(clauses[0].body, PseudoExpr::Bool(true)));
            assert!(matches!(clauses[1].body, PseudoExpr::Bool(false)));
        }
        _ => panic!("expected When, got {:?}", simplified),
    }
}
