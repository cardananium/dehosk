use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_expect_constructor_field_destructure_keeps_outer_binder_scope() {
    let payload = Binder::new("field_1", VarId::new(711));
    let inner_item = Binder::new("item_0", VarId::new(712));

    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("x")),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(
                        ConstructorShape::unknown_data(0, 1),
                        vec![payload.clone()],
                    ),
                    PseudoExpr::When {
                        subject: PBox::new(PseudoExpr::var_with_id(payload.as_str(), payload.id)),
                        subject_name: None,
                        clauses: vec![
                            WhenClause::new(
                                WhenPattern::constructor(
                                    ConstructorShape::unknown_data(2, 1),
                                    vec![inner_item.clone()],
                                ),
                                PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("expect!")),
                                    args: vec![PseudoExpr::When {
                                        subject: PBox::new(PseudoExpr::var_with_id(
                                            inner_item.as_str(),
                                            inner_item.id,
                                        )),
                                        subject_name: None,
                                        clauses: vec![
                                            WhenClause::new(
                                                WhenPattern::constructor(
                                                    ConstructorShape::unknown_data(1, 0),
                                                    vec![],
                                                ),
                                                PseudoExpr::Unit,
                                            ),
                                            WhenClause::new(
                                                WhenPattern::Wildcard,
                                                PseudoExpr::Error { message: None },
                                            ),
                                        ],
                                    }]
                                    .into(),
                                },
                            ),
                            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
                        ],
                    },
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }]
        .into(),
    };

    let output = simplify(expr).to_pretty();
    assert!(
        !output.contains("expect! when field_1 is {"),
        "expected outer constructor binder to stay scoped under its parent match, got:\n{}",
        output
    );
}

#[test]
fn test_expect_constructor_field_destructure_from_subject_fields_keeps_outer_match() {
    let payload = Binder::new("field_1", VarId::new(721));
    let item = Binder::new("item_0", VarId::new(722));
    let tail = Binder::new("tail", VarId::new(723));

    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("x")),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(
                        ConstructorShape::unknown_data(0, 1),
                        vec![payload.clone()],
                    ),
                    PseudoExpr::When {
                        subject: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var("x"),
                            "fields".to_string(),
                        )),
                        subject_name: None,
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
                                    elements: vec![item.clone()],
                                    tail: Some(tail.clone()),
                                },
                                PseudoExpr::When {
                                    subject: PBox::new(PseudoExpr::var_with_id(
                                        item.as_str(),
                                        item.id,
                                    )),
                                    subject_name: None,
                                    clauses: vec![
                                        WhenClause::new(
                                            WhenPattern::constructor(
                                                ConstructorShape::unknown_data(1, 0),
                                                vec![],
                                            ),
                                            PseudoExpr::Unit,
                                        ),
                                        WhenClause::new(
                                            WhenPattern::Wildcard,
                                            PseudoExpr::Error { message: None },
                                        ),
                                    ],
                                },
                            ),
                        ],
                    },
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }]
        .into(),
    };

    let output = simplify(expr).to_pretty();
    assert!(
        !output.contains("expect! when field_1 is {"),
        "expected outer constructor binder to remain under parent constructor match, got:\n{}",
        output
    );
    assert!(
        output.contains("Constr<0>(field_1)")
            || output.contains("expect! when x is {")
            || output.contains("when x is {"),
        "expected rewritten output to retain the parent constructor match, got:\n{}",
        output
    );
}

#[test]
fn test_constructor_when_fields_destructure_handles_missing_inner_subject_id() {
    let subject_id = VarId::new(7);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(subject_id),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var("x"),
                        "fields".to_string(),
                    )),
                    subject_name: None,
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
                                elements: vec!["head".to_string().into()],
                                tail: Some("tail".to_string().into()),
                            },
                            PseudoExpr::When {
                                subject: PBox::new(PseudoExpr::IndexAccess {
                                    collection: PBox::new(PseudoExpr::field_access(
                                        PseudoExpr::var("x"),
                                        "fields".to_string(),
                                    )),
                                    index: 0,
                                }),
                                subject_name: None,
                                clauses: vec![
                                    WhenClause::new(
                                        WhenPattern::constructor(
                                            ConstructorShape::unknown_data(4, 0),
                                            vec![],
                                        ),
                                        PseudoExpr::When {
                                            subject: PBox::new(PseudoExpr::var("tail")),
                                            subject_name: None,
                                            clauses: vec![
                                                WhenClause::new(
                                                    WhenPattern::List {
                                                        elements: vec![],
                                                        tail: None,
                                                    },
                                                    PseudoExpr::Bool(true),
                                                ),
                                                WhenClause::new(
                                                    WhenPattern::Wildcard,
                                                    PseudoExpr::Bool(false),
                                                ),
                                            ],
                                        },
                                    ),
                                    WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
                                ],
                            },
                        ),
                    ],
                },
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
        ],
    };

    let output = simplify(expr).to_pretty();
    // DEFAULT render (compilable-data-access OFF): the raw-Constr fields list
    // and its index stay the pseudo `x.fields` / `x.fields[0]`, not
    // `builtin.un_constr_data(x).2nd` and `builtin.head_list` of it.
    assert!(
        output.contains("x.fields is"),
        "expected authoritative outer subject id to prevent name-only collapse of missing inner subject ids, got:\n{}",
        output
    );
    assert!(
        output.contains("x.fields[0]"),
        "expected authoritative outer subject id to prevent name-only field rewrite of missing inner ids, got:\n{}",
        output
    );
}

#[test]
fn test_constructor_when_fields_destructure_handles_mismatched_inner_subject_id() {
    let subject_id = VarId::new(7);
    let mismatched_id = VarId::new(8);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(subject_id),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::Var {
                            name: "x".to_string(),
                            id: Some(mismatched_id),
                        },
                        "fields".to_string(),
                    )),
                    subject_name: None,
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
                                elements: vec!["head".to_string().into()],
                                tail: Some("tail".to_string().into()),
                            },
                            PseudoExpr::When {
                                subject: PBox::new(PseudoExpr::IndexAccess {
                                    collection: PBox::new(PseudoExpr::field_access(
                                        PseudoExpr::Var {
                                            name: "x".to_string(),
                                            id: Some(mismatched_id),
                                        },
                                        "fields".to_string(),
                                    )),
                                    index: 0,
                                }),
                                subject_name: None,
                                clauses: vec![
                                    WhenClause::new(
                                        WhenPattern::constructor(
                                            ConstructorShape::unknown_data(4, 0),
                                            vec![],
                                        ),
                                        PseudoExpr::When {
                                            subject: PBox::new(PseudoExpr::var("tail")),
                                            subject_name: None,
                                            clauses: vec![
                                                WhenClause::new(
                                                    WhenPattern::List {
                                                        elements: vec![],
                                                        tail: None,
                                                    },
                                                    PseudoExpr::Bool(true),
                                                ),
                                                WhenClause::new(
                                                    WhenPattern::Wildcard,
                                                    PseudoExpr::Bool(false),
                                                ),
                                            ],
                                        },
                                    ),
                                    WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
                                ],
                            },
                        ),
                    ],
                },
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
        ],
    };

    let output = simplify(expr).to_pretty();
    // DEFAULT render (compilable-data-access OFF): the raw-Constr fields list
    // and its index stay the pseudo `x.fields` / `x.fields[0]`, not
    // `builtin.un_constr_data(x).2nd` and `builtin.head_list` of it.
    assert!(
        output.contains("x.fields is"),
        "expected authoritative outer subject id to prevent name-only collapse of mismatched inner ids, got:\n{}",
        output
    );
    assert!(
        output.contains("x.fields[0]"),
        "expected authoritative outer subject id to prevent name-only field rewrite of mismatched inner ids, got:\n{}",
        output
    );
}

#[test]
fn test_constructor_when_fields_destructure_handles_lifted_payload_var() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var("x"),
                        "fields".to_string(),
                    )),
                    subject_name: None,
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
                                elements: vec!["head".to_string().into()],
                                tail: Some("tail".to_string().into()),
                            },
                            PseudoExpr::When {
                                subject: PBox::new(PseudoExpr::var("payload")),
                                subject_name: None,
                                clauses: vec![
                                    WhenClause::new(
                                        WhenPattern::constructor(
                                            ConstructorShape::unknown_data(4, 0),
                                            vec![],
                                        ),
                                        PseudoExpr::When {
                                            subject: PBox::new(PseudoExpr::var("tail")),
                                            subject_name: None,
                                            clauses: vec![
                                                WhenClause::new(
                                                    WhenPattern::List {
                                                        elements: vec![],
                                                        tail: None,
                                                    },
                                                    PseudoExpr::Bool(true),
                                                ),
                                                WhenClause::new(
                                                    WhenPattern::Wildcard,
                                                    PseudoExpr::Bool(false),
                                                ),
                                            ],
                                        },
                                    ),
                                    WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
                                ],
                            },
                        ),
                    ],
                },
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
        ],
    };

    let output = simplify(expr).to_pretty();
    assert!(
        output.contains("Constr<0>(payload)"),
        "expected lifted payload var to be stitched back into constructor pattern, got:\n{}",
        output
    );
    assert!(
        !output.contains("x.fields is"),
        "expected lifted payload var shape to collapse outer subject fields dispatch, got:\n{}",
        output
    );
}

#[test]
fn test_constructor_when_fields_destructure_lifted_payload_var_uses_local_synthetic_id() {
    let lifted_payload_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var("x"),
                        "fields".to_string(),
                    )),
                    subject_name: None,
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
                                elements: vec!["head".to_string().into()],
                                tail: Some("tail".to_string().into()),
                            },
                            PseudoExpr::When {
                                subject: PBox::new(PseudoExpr::var_with_id(
                                    "payload",
                                    lifted_payload_id,
                                )),
                                subject_name: None,
                                clauses: vec![
                                    WhenClause::new(
                                        WhenPattern::constructor(
                                            ConstructorShape::unknown_data(4, 0),
                                            vec![],
                                        ),
                                        PseudoExpr::When {
                                            subject: PBox::new(PseudoExpr::var("tail")),
                                            subject_name: None,
                                            clauses: vec![
                                                WhenClause::new(
                                                    WhenPattern::List {
                                                        elements: vec![],
                                                        tail: None,
                                                    },
                                                    PseudoExpr::Bool(true),
                                                ),
                                                WhenClause::new(
                                                    WhenPattern::Wildcard,
                                                    PseudoExpr::Bool(false),
                                                ),
                                            ],
                                        },
                                    ),
                                    WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
                                ],
                            },
                        ),
                    ],
                },
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
        ],
    };

    let simplified = simplify(expr);
    let (payload, body) = match simplified {
        PseudoExpr::When { clauses, .. } => clauses
            .into_iter()
            .find_map(|clause| match clause.pattern {
                WhenPattern::Constructor { fields, .. } if fields.len() == 1 => {
                    Some((fields[0].clone(), clause.body))
                }
                _ => None,
            })
            .expect("expected collapsed outer constructor clause with one payload binder"),
        other => panic!("expected outer When after collapse, got: {other:?}"),
    };

    assert_eq!(payload.as_str(), "payload");
    assert_ne!(payload.id, lifted_payload_id);
    assert!(
        !payload.id.is_compat_placeholder(),
        "expected lifted payload binder to stop using compat placeholder ids, got {}",
        payload.id
    );
    assert!(
        payload.id.as_u32() < 1_000_000_000,
        "expected lifted payload binder to use the simplifier-local synthetic range, got {}",
        payload.id
    );
    assert!(
        matches!(
            &body,
            PseudoExpr::When { subject, .. }
                if matches!(
                    subject.as_ref(),
                    PseudoExpr::Var { name, id, .. } if name == "payload" && *id == Some(payload.id)
                )
        ),
        "expected collapsed inner when to target the same lifted payload binder, got: {body:?}"
    );
}
