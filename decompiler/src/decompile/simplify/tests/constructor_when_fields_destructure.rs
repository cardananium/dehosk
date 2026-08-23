use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_constructor_when_fields_destructure_direct_subject_fields_accesses() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var("x"),
                            "fields".to_string(),
                        )),
                        index: 0,
                    }),
                    right: PBox::new(PseudoExpr::int(1)),
                },
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
        ],
    };

    let output = simplify(expr).to_pretty();
    assert!(
        output.contains("Constr<0>("),
        "expected constructor clause to bind direct subject fields, got:\n{}",
        output
    );
    assert!(
        !output.contains("x.fields[0]"),
        "expected direct subject field access to be rewritten, got:\n{}",
        output
    );
}

#[test]
fn test_constructor_when_fields_destructure_ignores_same_name_different_subject_id() {
    let subject_id = VarId::new(723);
    let other_id = VarId::new(724);
    let subject = PseudoExpr::var_with_id("x", subject_id);
    let subject_name = None;
    let mut simplifier = Simplifier::with_safe_mode(false);
    let clauses = simplifier.destructure_when_fields(
        &subject,
        &subject_name,
        vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("x", other_id),
                    "fields".to_string(),
                )),
                index: 0,
            },
        )],
    );

    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor clause, got: {:?}", clauses[0].pattern);
    };
    assert!(
        fields.is_empty(),
        "same-name subject refs with mismatched ids must not synthesize constructor fields"
    );
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::IndexAccess { collection, index: 0 }
                if matches!(
                    collection.as_ref(),
                    PseudoExpr::FieldAccess { record, selector, .. }
                        if selector.as_pretty_name() == "fields"
                            && matches!(
                                record.as_ref(),
                                PseudoExpr::Var { name, id, .. }
                                    if name == "x" && id.get() == Some(other_id)
                            )
                )
        ),
        "same-name subject refs with mismatched ids must remain untouched"
    );
}

#[test]
fn test_constructor_when_fields_destructure_freshens_field_binder_against_body_name() {
    let existing_field_id = VarId::new(721);
    let subject = PseudoExpr::var("x");
    let subject_name = None;
    let mut simplifier = Simplifier::with_safe_mode(false);
    let clauses = simplifier.destructure_when_fields(
        &subject,
        &subject_name,
        vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::Let {
                    name: "field_0".to_string(),
                    id: Some(existing_field_id),
                    value: PBox::new(PseudoExpr::int(1)),
                    body: PBox::new(PseudoExpr::Pair(
                        PBox::new(PseudoExpr::var_with_id("field_0", existing_field_id)),
                        PBox::new(PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var("x"),
                                "fields".to_string(),
                            )),
                            index: 0,
                        }),
                    )),
                },
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
        ],
    );
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor clause, got: {:?}", clauses[0].pattern);
    };
    let [field] = fields.as_slice() else {
        panic!("expected one generated field binder, got: {fields:?}");
    };
    assert_eq!(field.as_str(), "field_0_1");

    let PseudoExpr::Let { name, body, .. } = &clauses[0].body else {
        panic!(
            "expected original field_0 let to remain, got: {:?}",
            clauses[0].body
        );
    };
    assert_eq!(name, "field_0");
    let PseudoExpr::Pair(_, right) = body.as_ref() else {
        panic!("expected pair body, got: {body:?}");
    };
    assert!(
        matches!(
            right.as_ref(),
            PseudoExpr::Var { name, id } if name == "field_0_1" && id.get() == Some(field.id)
        ),
        "expected rewritten field access to use freshened binder id, got: {right:?}"
    );
}

#[test]
fn test_constructor_when_fields_destructure_nested_subject_fields_shape() {
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
    assert!(
        output.contains("Constr<0>("),
        "expected nested direct field shape to bind constructor payload, got:\n{}",
        output
    );
    assert!(
        !output.contains("x.fields is"),
        "expected nested outer subject fields dispatch to collapse, got:\n{}",
        output
    );
    assert!(
        !output.contains("x.fields[0]"),
        "expected nested direct subject field access to be rewritten, got:\n{}",
        output
    );
}

#[test]
fn test_constructor_when_fields_destructure_freshens_collapsed_single_field_binder() {
    let existing_field_id = VarId::new(722);
    let subject = PseudoExpr::var("x");
    let subject_name = None;
    let mut simplifier = Simplifier::with_safe_mode(false);
    let clauses = simplifier.destructure_when_fields(
        &subject,
        &subject_name,
        vec![
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
                                elements: vec!["_".to_string().into()],
                                tail: None,
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
                                        PseudoExpr::Let {
                                            name: "field_0".to_string(),
                                            id: Some(existing_field_id),
                                            value: PBox::new(PseudoExpr::int(1)),
                                            body: PBox::new(PseudoExpr::Pair(
                                                PBox::new(PseudoExpr::var_with_id(
                                                    "field_0",
                                                    existing_field_id,
                                                )),
                                                PBox::new(PseudoExpr::Unit),
                                            )),
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
    );
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor clause, got: {:?}", clauses[0].pattern);
    };
    let [field] = fields.as_slice() else {
        panic!("expected one collapsed field binder, got: {fields:?}");
    };
    assert_eq!(field.as_str(), "field_0_1");
}

#[test]
fn test_constructor_when_fields_destructure_already_bound_single_field_shape() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec!["variant".to_string().into()],
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
                                elements: vec!["head".to_string().into()],
                                tail: Some("tail".to_string().into()),
                            },
                            PseudoExpr::When {
                                subject: PBox::new(PseudoExpr::var("variant")),
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
        !output.contains("x.fields is"),
        "expected already-bound single-field shape to collapse outer subject fields dispatch, got:\n{}",
        output
    );
    assert!(
        output.contains("when variant is"),
        "expected already-bound binder to survive collapse, got:\n{}",
        output
    );
}

#[test]
fn test_constructor_when_fields_destructure_restitches_old_head_name_to_existing_field_binder() {
    let existing_field = Binder::new("field_1", VarId::new(701));
    let old_head = Binder::new("item_1_1_1_1_1_1_1_1_1_1", VarId::new(702));
    let tail = Binder::new("tail", VarId::new(703));

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec![existing_field.clone()],
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
                                elements: vec![old_head.clone()],
                                tail: Some(tail.clone()),
                            },
                            PseudoExpr::When {
                                subject: PBox::new(PseudoExpr::var_with_id(
                                    old_head.as_str(),
                                    old_head.id,
                                )),
                                subject_name: None,
                                clauses: vec![
                                    WhenClause::new(
                                        WhenPattern::constructor(
                                            ConstructorShape::unknown_data(4, 0),
                                            vec![],
                                        ),
                                        PseudoExpr::When {
                                            subject: PBox::new(PseudoExpr::var_with_id(
                                                tail.as_str(),
                                                tail.id,
                                            )),
                                            subject_name: None,
                                            clauses: vec![
                                                WhenClause::new(
                                                    WhenPattern::List {
                                                        elements: vec![],
                                                        tail: None,
                                                    },
                                                    PseudoExpr::BuiltinCall {
                                                        name: crate::BuiltinId::expect_known(
                                                            "Data.un_int",
                                                        ),
                                                        args: vec![PseudoExpr::IndexAccess {
                                                            collection: PBox::new(
                                                                PseudoExpr::field_access(
                                                                    PseudoExpr::var_with_id(
                                                                        old_head.as_str(),
                                                                        old_head.id,
                                                                    ),
                                                                    "fields".to_string(),
                                                                ),
                                                            ),
                                                            index: 0,
                                                        }]
                                                        .into(),
                                                    },
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
    let output = simplified.to_pretty();
    assert!(
        output.contains("when field_1 is"),
        "expected collapsed inner dispatch to be restitched onto the surviving field binder, got:\n{}",
        output
    );
    assert!(
        // surface `builtin.un_i_data` replaces pseudonym `Data.un_int`.
        output.contains("Constr<4>(field_0) -> builtin.un_i_data(field_0)"),
        "expected inner payload access to stay bound after collapse, got:\n{}",
        output
    );
    assert!(
        !output.contains("item_1_1_1_1_1_1_1_1_1_1"),
        "expected old list-head alias to be fully eliminated after collapse, got:\n{}",
        output
    );
    assert!(
        !output.contains("x.fields is"),
        "expected the nested subject-fields dispatch to collapse completely, got:\n{}",
        output
    );

    let report = audit_id_orphans(&simplified, &[]);
    assert_eq!(
        report.stranded + report.truly_free,
        0,
        "collapsed body refs should use the surviving field binder id, got audit {report:?}\n{output}"
    );
}

#[test]
fn test_constructor_when_fields_destructure_skips_same_name_mismatched_inner_subject_id() {
    let existing_field = Binder::new("field_1", VarId::new(714));
    let old_head = Binder::new("item_1_1_1_1_1_1_1_1_1_1", VarId::new(715));
    let mismatched_old_head_id = VarId::new(716);
    let tail = Binder::new("tail", VarId::new(717));
    let mut simplifier = Simplifier::with_safe_mode(false);

    let clauses = simplifier.destructure_when_fields(
        &PseudoExpr::var("x"),
        &None,
        vec![
            WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec![existing_field],
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
                                elements: vec![old_head.clone()],
                                tail: Some(tail.clone()),
                            },
                            PseudoExpr::When {
                                subject: PBox::new(PseudoExpr::var_with_id(
                                    old_head.as_str(),
                                    mismatched_old_head_id,
                                )),
                                subject_name: None,
                                clauses: vec![
                                    WhenClause::new(
                                        WhenPattern::constructor(
                                            ConstructorShape::unknown_data(4, 0),
                                            vec![],
                                        ),
                                        PseudoExpr::When {
                                            subject: PBox::new(PseudoExpr::var_with_id(
                                                tail.as_str(),
                                                tail.id,
                                            )),
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
    );

    let output = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses,
    }
    .to_pretty();

    // DEFAULT render (compilable-data-access OFF): the raw-Constr fields list
    // stays the pseudo `x.fields`, not `builtin.un_constr_data(x).2nd`.
    assert!(
        output.contains("x.fields is"),
        "same-name inner subjects with a different authoritative id must not collapse, got:\n{output}"
    );
}

#[test]
fn test_constructor_when_fields_destructure_skips_capture_under_existing_field_binder() {
    let existing_field = Binder::new("field_1", VarId::new(704));
    let old_head = Binder::new("item_1_1_1_1_1_1_1_1_1_1", VarId::new(705));
    let shadow_field = Binder::new("field_1", VarId::new(706));
    let mut simplifier = Simplifier::with_safe_mode(false);
    let clauses = simplifier.destructure_when_fields(
        &PseudoExpr::var("x"),
        &None,
        vec![
            WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec![existing_field.clone()],
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
                                elements: vec![old_head.clone()],
                                tail: None,
                            },
                            PseudoExpr::When {
                                subject: PBox::new(PseudoExpr::var_with_id(
                                    old_head.as_str(),
                                    old_head.id,
                                )),
                                subject_name: None,
                                clauses: vec![
                                    WhenClause::new(
                                        WhenPattern::constructor(
                                            ConstructorShape::unknown_data(4, 0),
                                            vec![],
                                        ),
                                        PseudoExpr::Let {
                                            name: shadow_field.name.clone(),
                                            id: Some(shadow_field.id),
                                            value: PBox::new(PseudoExpr::Int(0.into())),
                                            body: PBox::new(PseudoExpr::var_with_id(
                                                old_head.as_str(),
                                                old_head.id,
                                            )),
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
    );

    let output = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses,
    }
    .to_pretty();

    // DEFAULT render (compilable-data-access OFF): the raw-Constr fields list
    // stays the pseudo `x.fields`, not `builtin.un_constr_data(x).2nd`.
    assert!(
        output.contains("x.fields is"),
        "single-field collapse should be skipped when substituting into an inner field_1 binder would capture, got:\n{output}"
    );
}
