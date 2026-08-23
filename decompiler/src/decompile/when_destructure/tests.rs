use super::*;

#[test]
fn test_extract_complex_when_subjects_unwraps_identity_iife_subject() {
    let tmp_id = VarId::from_raw(9991);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("tmp", tmp_id)],
                body: PBox::new(PseudoExpr::var_with_id("tmp", tmp_id)),
            }),
            args: vec![PseudoExpr::var("xs")].into(),
        }),
        subject_name: None,
        clauses: vec![WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Unit)],
    };

    let extracted = extract_complex_when_subjects(expr);

    match extracted {
        PseudoExpr::When {
            subject,
            subject_name: None,
            clauses,
        } => {
            assert!(
                matches!(subject.as_ref(), PseudoExpr::Var { name, .. } if name == "xs"),
                "expected identity wrapper to collapse to xs, got: {subject:?}"
            );
            assert_eq!(clauses.len(), 1);
        }
        other => panic!("expected direct When without match_subject temp, got: {other:?}"),
    }
}

#[test]
fn test_extract_complex_when_subjects_preserves_existing_subject_name_identity() {
    let subject_id = VarId::from_raw(9992);
    let tmp_id = VarId::from_raw(9993);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("tmp", tmp_id)],
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("tmp", tmp_id),
                        PseudoExpr::Bool(true),
                    ]
                    .into(),
                )),
            }),
            args: vec![PseudoExpr::var("xs")].into(),
        }),
        subject_name: Some(Binder::new("payload", subject_id)),
        clauses: vec![WhenClause::new(
            WhenPattern::Wildcard,
            PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("payload", subject_id),
                    PseudoExpr::Bool(true),
                ]
                .into(),
            ),
        )],
    };

    let extracted = extract_complex_when_subjects(expr);

    match extracted {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            assert_eq!(name, "payload");
            assert_eq!(id, Some(subject_id));
            assert!(
                matches!(value.as_ref(), PseudoExpr::Apply { .. }),
                "expected complex subject to be hoisted into the let value, got: {value:?}"
            );
            match body.as_ref() {
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    assert!(
                        matches!(
                            subject.as_ref(),
                            PseudoExpr::Var { name, id }
                                if name == "payload" && *id == Some(subject_id)
                        ),
                        "expected hoisted when subject to reuse the existing subject_name identity, got: {subject:?}"
                    );
                    assert!(
                        subject_name.is_none(),
                        "outer let now owns the preserved subject identity, so the inner when must not duplicate it"
                    );
                    assert!(
                        matches!(
                            &clauses[0].body,
                            PseudoExpr::Tuple(items)
                                if matches!(
                                    &items[0],
                                    PseudoExpr::Var { name, id }
                                        if name == "payload" && *id == Some(subject_id)
                                )
                        ),
                        "expected clause body to keep the original subject_name ref id, got: {:?}",
                        clauses[0].body
                    );
                }
                other => panic!("expected when inside hoisted let, got: {other:?}"),
            }
        }
        other => panic!("expected extracted let around when, got: {other:?}"),
    }
}

#[test]
fn test_extract_complex_when_subjects_uses_fresh_generated_subject_name() {
    let existing_id = VarId::from_raw(9994);
    let tmp_id = VarId::from_raw(9995);
    let expr = PseudoExpr::Let {
        name: "match_subject_0".to_string(),
        id: Some(existing_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Lambda {
                    params: vec![Binder::new("tmp", tmp_id)],
                    body: PBox::new(PseudoExpr::Tuple(
                        vec![
                            PseudoExpr::var_with_id("tmp", tmp_id),
                            PseudoExpr::Bool(true),
                        ]
                        .into(),
                    )),
                }),
                args: vec![PseudoExpr::var("xs")].into(),
            }),
            subject_name: None,
            clauses: vec![WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Unit)],
        }),
    };

    let extracted = extract_complex_when_subjects(expr);

    match extracted {
        PseudoExpr::Let { body, .. } => match body.as_ref() {
            PseudoExpr::Let {
                name,
                body: inner_body,
                ..
            } => {
                assert_eq!(name, "match_subject_1");
                assert!(
                    matches!(
                        inner_body.as_ref(),
                        PseudoExpr::When {
                            subject,
                            subject_name: None,
                            ..
                        } if matches!(
                            subject.as_ref(),
                            PseudoExpr::Var { name, .. } if name == "match_subject_1"
                        )
                    ),
                    "expected generated subject name to be owned by the outer let only, got: {inner_body:?}"
                );
            }
            other => {
                panic!("expected generated subject let under existing let, got: {other:?}")
            }
        },
        other => panic!("expected existing let to remain outermost, got: {other:?}"),
    }
}

#[test]
fn test_lift_unpack_tag_when_subjects_promotes_constructor_patterns_and_fields() {
    let redeemer_id = VarId::from_raw(9990);
    let redeemer_var = || PseudoExpr::var_with_id("redeemer", redeemer_id);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::field_access(
            PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Constr.unpack"),
                args: vec![redeemer_var()].into(),
            },
            "fst".to_string(),
        )),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::Literal(PseudoExpr::int(2)),
                PseudoExpr::field_access(
                    PseudoExpr::field_access(
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Constr.unpack"),
                            args: vec![redeemer_var()].into(),
                        },
                        "snd".to_string(),
                    ),
                    "head".to_string(),
                ),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
        ],
    };

    let lifted = lift_unpack_tag_when_subjects(expr, None, None);
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&lifted),
        "lifted unpack/tag when should not introduce stale generated field refs"
    );

    match lifted {
        PseudoExpr::When {
            subject,
            subject_name: None,
            clauses,
        } => {
            assert!(
                matches!(subject.as_ref(), PseudoExpr::Var { name, .. } if name == "redeemer"),
                "expected redeemer subject, got: {subject:?}"
            );
            assert_eq!(clauses.len(), 2, "expected two clauses, got: {clauses:?}");
            assert!(
                matches!(
                    &clauses[0].pattern,
                    WhenPattern::Constructor { tag: 2, fields, .. }
                        if fields == &vec!["field_0".to_string()]
                ),
                "expected Constr<2>(field_0), got: {:?}",
                clauses[0].pattern
            );
            assert!(
                matches!(&clauses[0].body, PseudoExpr::Var { name, .. } if name == "field_0"),
                "expected field access to become binder, got: {:?}",
                clauses[0].body
            );
        }
        other => panic!("expected lifted When, got: {other:?}"),
    }
}

#[test]
fn test_destructure_when_fields_avoids_generated_binder_capture_under_lambda() {
    let redeemer_id = VarId::from_raw(9994);
    let capture_id = VarId::from_raw(9995);
    let redeemer_var = || PseudoExpr::var_with_id("redeemer", redeemer_id);
    let expr = PseudoExpr::When {
        subject: PBox::new(redeemer_var()),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
            PseudoExpr::Lambda {
                params: vec![Binder::new("field_0", capture_id)],
                body: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::field_access(
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Constr.unpack"),
                            args: vec![redeemer_var()].into(),
                        },
                        "snd".to_string(),
                    ),
                    "head".to_string(),
                )),
            },
        )],
    };

    let destructured = destructure_when_fields(expr, None, None);
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&destructured),
        "destructuring should not introduce a field_0 ref under a nearer field_0 lambda"
    );

    let PseudoExpr::When { clauses, .. } = destructured else {
        panic!("expected when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern");
    };
    assert_eq!(fields[0].as_str(), "field_0");
    assert_ne!(fields[0].id, capture_id);

    let PseudoExpr::Lambda { params, body } = &clauses[0].body else {
        panic!("expected capture lambda");
    };
    assert_eq!(params[0].as_str(), "field_0");
    assert_eq!(params[0].id, capture_id);
    assert!(
        matches!(body.as_ref(), PseudoExpr::FieldAccess { .. }),
        "captured subtree must keep the original field access instead of a stale generated Var, got: {body:?}"
    );
}

#[test]
fn test_destructure_when_fields_avoids_generated_binder_shadowing_existing_clause_ref() {
    let redeemer_id = VarId::from_raw(9998);
    let outer_field_id = VarId::from_raw(9999);
    let redeemer_var = || PseudoExpr::var_with_id("redeemer", redeemer_id);
    let field_zero_access = || {
        PseudoExpr::field_access(
            PseudoExpr::field_access(
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Constr.unpack"),
                    args: vec![redeemer_var()].into(),
                },
                "snd".to_string(),
            ),
            "head".to_string(),
        )
    };

    let expr = PseudoExpr::Let {
        name: "field_0".to_string(),
        id: Some(outer_field_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(redeemer_var()),
            subject_name: None,
            clauses: vec![WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
                PseudoExpr::Tuple(
                    vec![
                        field_zero_access(),
                        PseudoExpr::var_with_id("field_0", outer_field_id),
                    ]
                    .into(),
                ),
            )],
        }),
    };

    let destructured = destructure_when_fields(expr, None, None);
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&destructured),
        "destructuring should not introduce a generated pattern binder that shadows an existing outer field_0 ref"
    );

    let PseudoExpr::Let { body, .. } = destructured else {
        panic!("expected outer let");
    };
    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected when body");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern");
    };
    assert_eq!(fields.len(), 1);
    assert_ne!(fields[0].as_str(), "field_0");
    assert!(
        fields[0].as_str().starts_with("field_0_"),
        "expected generated field name to avoid field_0, got {}",
        fields[0]
    );
    let generated_name = fields[0].to_string();
    let generated_id = fields[0].var_id();

    let PseudoExpr::Tuple(items) = &clauses[0].body else {
        panic!("expected tuple body");
    };
    assert!(
        matches!(
            &items[0],
            PseudoExpr::Var { name, id } if name == &generated_name && *id == Some(generated_id)
        ),
        "expected extracted field access to use generated binder {generated_name}, got {:?}",
        items[0]
    );
    assert!(
        matches!(
            &items[1],
            PseudoExpr::Var { name, id } if name == "field_0" && *id == Some(outer_field_id)
        ),
        "expected outer field_0 ref to keep its original name/id, got {:?}",
        items[1]
    );
}

#[test]
fn test_destructure_when_fields_reuses_high_index_field_binder_id() {
    let redeemer_id = VarId::from_raw(9996);
    let redeemer_var = || PseudoExpr::var_with_id("redeemer", redeemer_id);
    let expr = PseudoExpr::When {
        subject: PBox::new(redeemer_var()),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
            PseudoExpr::Tuple(
                vec![PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Constr.unpack"),
                            args: vec![redeemer_var()].into(),
                        },
                        "snd".to_string(),
                    )),
                    index: 2,
                }]
                .into(),
            ),
        )],
    };

    let destructured = destructure_when_fields(expr, None, None);
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&destructured),
        "destructuring should reuse the generated high-index field binder id"
    );

    let PseudoExpr::When { clauses, .. } = destructured else {
        panic!("expected when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern");
    };
    assert_eq!(fields.len(), 3);
    let field_2_id = fields[2].var_id();

    let PseudoExpr::Tuple(items) = &clauses[0].body else {
        panic!("expected tuple body");
    };
    assert!(
        matches!(
            &items[0],
            PseudoExpr::Var { name, id } if name == "field_2" && *id == Some(field_2_id)
        ),
        "expected snd[2] to become field_2 with pattern binder id {field_2_id:?}, got: {:?}",
        items[0]
    );
}
