use super::*;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::OptionVarIdGet;

#[test]
fn readability_condition_name_allocation_uses_names_from_condition() {
    let condition_id = VarId::from_raw(9904);
    let subject_id = VarId::from_raw(9905);
    let condition = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![Binder::new("condition_ok", condition_id)],
                    shape: ConstructorShape::unknown_data(0, 1),
                },
                PseudoExpr::Bool(true),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
        ],
    };

    let mut used_names = HashSet::new();
    Simplifier::collect_var_names(&condition, &mut used_names);
    Simplifier::collect_var_names(&PseudoExpr::int(1), &mut used_names);
    Simplifier::collect_var_names(&PseudoExpr::int(2), &mut used_names);

    let base = Simplifier::suggest_boolish_name_from_expr(&condition)
        .unwrap_or_else(|| "condition_ok".to_string());
    let simplifier = Simplifier::with_safe_mode(false);
    let fresh = simplifier.fresh_name_for_scope(&mut used_names, base);

    assert_eq!(fresh, "condition_ok_1");
}

#[test]
fn direct_subject_field_rewrite_keeps_concrete_replacement_id() {
    let subject_id = VarId::from_raw(9910);
    let replacement_id = VarId::from_raw(9911);
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::field_access_typed(
            PseudoExpr::var_with_id("subject", subject_id),
            FieldSelector::NamedField("fields".to_string()),
        )),
        index: 0,
    };

    let rewritten = Simplifier::replace_direct_subject_fields_index_access(
        expr,
        "subject",
        Some(subject_id),
        0,
        "field_0",
        replacement_id,
    );

    match rewritten {
        PseudoExpr::Var { name, id } => {
            assert_eq!(name, "field_0");
            assert_eq!(id, Some(replacement_id));
        }
        other => panic!("expected rewritten var, got {other:?}"),
    }
}

#[test]
fn direct_subject_field_rewrite_ignores_same_name_different_id() {
    let subject_id = VarId::from_raw(9920);
    let other_id = VarId::from_raw(9921);
    let replacement_id = VarId::from_raw(9922);
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::field_access_typed(
            PseudoExpr::var_with_id("subject", other_id),
            FieldSelector::NamedField("fields".to_string()),
        )),
        index: 0,
    };

    let rewritten = Simplifier::replace_direct_subject_fields_index_access(
        expr,
        "subject",
        Some(subject_id),
        0,
        "field_0",
        replacement_id,
    );

    assert!(
        matches!(
            rewritten,
            PseudoExpr::IndexAccess { collection, index: 0 }
                if matches!(
                    collection.as_ref(),
                    PseudoExpr::FieldAccess { record, selector, .. }
                        if selector.as_pretty_name() == "fields"
                            && matches!(
                                record.as_ref(),
                                PseudoExpr::Var { name, id, .. }
                                    if name == "subject" && id.get() == Some(other_id)
                            )
                )
        ),
        "same-name refs with a different authoritative id must not be rewritten"
    );
}

#[test]
fn direct_subject_field_rewrite_respects_when_pattern_shadowing() {
    let subject_id = VarId::from_raw(9930);
    let replacement_id = VarId::from_raw(9931);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("scrutinee")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Var(Binder::new("subject", subject_id)),
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::field_access_typed(
                    PseudoExpr::var_with_id("subject", subject_id),
                    FieldSelector::NamedField("fields".to_string()),
                )),
                index: 0,
            },
        )],
    };

    let counts = Simplifier::collect_direct_subject_fields_index_access_counts(
        &expr,
        "subject",
        Some(subject_id),
    );
    assert!(counts.is_empty());

    let rewritten = Simplifier::replace_direct_subject_fields_index_access(
        expr,
        "subject",
        Some(subject_id),
        0,
        "field_0",
        replacement_id,
    );

    assert!(
        matches!(
            rewritten,
            PseudoExpr::When { clauses, .. }
                if matches!(
                    &clauses[0].body,
                    PseudoExpr::IndexAccess { collection, index: 0 }
                        if matches!(
                            collection.as_ref(),
                            PseudoExpr::FieldAccess { record, selector, .. }
                                if selector.as_pretty_name() == "fields"
                                    && matches!(
                                        record.as_ref(),
                                        PseudoExpr::Var { name, id, .. }
                                            if name == "subject" && id.get() == Some(subject_id)
                                    )
                        )
                )
        ),
        "when pattern binders must shadow direct subject field rewrites"
    );
}

#[test]
fn simplify_if_data_field_probe_ignores_same_name_different_condition_id() {
    let condition_id = VarId::from_raw(9932);
    let other_id = VarId::from_raw(9933);
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier.simplify_if(
        PseudoExpr::var_with_id("subject", condition_id),
        PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::field_access_typed(
                PseudoExpr::var_with_id("subject", other_id),
                FieldSelector::NamedField("fields".to_string()),
            )),
            index: 0,
        },
        PseudoExpr::int(0),
    );

    assert!(
        matches!(
            rewritten,
            PseudoExpr::If { condition, then_branch, .. }
                if matches!(
                    condition.as_ref(),
                    PseudoExpr::Var { name, id, .. } if name == "subject" && *id == Some(condition_id)
                )
                && matches!(
                    then_branch.as_ref(),
                    PseudoExpr::IndexAccess { collection, index: 0 }
                        if matches!(
                            collection.as_ref(),
                            PseudoExpr::FieldAccess { record, selector, .. }
                                if selector.as_pretty_name() == "fields"
                                    && matches!(
                                        record.as_ref(),
                                        PseudoExpr::Var { name, id, .. }
                                            if name == "subject" && *id == Some(other_id)
                                    )
                        )
                )
        ),
        "same-name fields access with a different authoritative id must not prove the condition is Data"
    );
}

#[test]
fn simplify_if_data_field_probe_accepts_matching_condition_id() {
    let condition_id = VarId::from_raw(9934);
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier.simplify_if(
        PseudoExpr::var_with_id("subject", condition_id),
        PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::field_access_typed(
                PseudoExpr::var_with_id("subject", condition_id),
                FieldSelector::NamedField("fields".to_string()),
            )),
            index: 0,
        },
        PseudoExpr::int(0),
    );

    assert!(
        matches!(
            rewritten,
            PseudoExpr::When { subject, clauses, .. }
                if matches!(
                    subject.as_ref(),
                    PseudoExpr::Var { name, id, .. } if name == "subject" && *id == Some(condition_id)
                )
                && matches!(
                    clauses.first().map(|clause| &clause.pattern),
                    Some(WhenPattern::Constructor { tag: 1, .. })
                )
        ),
        "matching subject.fields access should still prove the condition is Data-like"
    );
}

#[test]
fn simplify_if_does_not_fold_ordering_constr_into_boolean() {
    // Regression: `if cond { Constr<2> } else { Constr<1>=True }` must NOT fold
    // to `!cond || Constr<2>`. `Constr<2>` is a non-bool nullary sum variant
    // (e.g. an `Ordering::Less`/`Greater` from a 3-way `int.compare`); folding
    // it into `||` collapses a 3-way Ordering into a Bool — a semantics-losing,
    // non-compilable corruption. `can_short_circuit_with_boolean` rejects
    // nullary Constrs outside tag {0,1}, so the faithful `if` is preserved.
    let mut simplifier = Simplifier::with_safe_mode(false);
    let cond = PseudoExpr::BinOp {
        op: BinaryOp::Lte,
        left: PBox::new(PseudoExpr::var_with_id("a", VarId::from_raw(9970))),
        right: PBox::new(PseudoExpr::var_with_id("b", VarId::from_raw(9971))),
    };
    let constr2 = PseudoExpr::constr(ConstructorShape::unknown_data(2, 0), vec![]);
    let constr1_true = PseudoExpr::constr(ConstructorShape::unknown_data(1, 0), vec![]);
    let out = simplifier.simplify_if(cond, constr2, constr1_true);
    assert!(
        matches!(out, PseudoExpr::If { .. }),
        "a nullary Constr<2> (Ordering variant) must NOT fold into a boolean; got {out:?}"
    );
}

#[test]
fn simplify_if_still_folds_church_bool_constrs() {
    // The genuine 2-way church-bool `if cond { Constr<0>=False } else { Constr<1>=True }`
    // must STILL fold (to the inverted condition) — the {0,1}-tag restriction on
    // `can_short_circuit_with_boolean` must not break legitimate bool folds.
    let mut simplifier = Simplifier::with_safe_mode(false);
    let cond = PseudoExpr::BinOp {
        op: BinaryOp::Lte,
        left: PBox::new(PseudoExpr::var_with_id("a", VarId::from_raw(9972))),
        right: PBox::new(PseudoExpr::var_with_id("b", VarId::from_raw(9973))),
    };
    let constr0_false = PseudoExpr::constr(ConstructorShape::unknown_data(0, 0), vec![]);
    let constr1_true = PseudoExpr::constr(ConstructorShape::unknown_data(1, 0), vec![]);
    // `if a<=b { False } else { True }` -> `!(a<=b)` -> `a > b` (inverted comparison).
    let out = simplifier.simplify_if(cond, constr0_false, constr1_true);
    assert!(
        matches!(
            &out,
            PseudoExpr::BinOp {
                op: BinaryOp::Gt,
                ..
            }
        ),
        "church-bool 2-way fold must still produce the inverted comparison; got {out:?}"
    );
}

#[test]
fn expand_wildcard_if_to_clauses_ignores_same_name_different_subject_id() {
    let subject_id = VarId::from_raw(9940);
    let other_id = VarId::from_raw(9941);
    let subject = PseudoExpr::var_with_id("subject", subject_id);
    let clauses = vec![WhenClause::new(
        WhenPattern::Wildcard,
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var_with_id("subject", other_id)),
            then_branch: PBox::new(PseudoExpr::int(1)),
            else_branch: PBox::new(PseudoExpr::int(0)),
        },
    )];

    let expanded = Simplifier::expand_wildcard_if_to_clauses(clauses, &subject, &None);

    assert_eq!(expanded.len(), 1);
    assert!(
        matches!(
            &expanded[0],
            WhenClause {
                pattern: WhenPattern::Wildcard,
                body: PseudoExpr::If { condition, .. },
                ..
            } if matches!(
                condition.as_ref(),
                PseudoExpr::Var { name, id, .. } if name == "subject" && *id == Some(other_id)
            )
        ),
        "wildcard-if expansion must not treat same-name different-id refs as the when subject"
    );
}

#[test]
fn destructure_list_head_tail_ignores_same_name_different_subject_id() {
    let subject_id = VarId::from_raw(9950);
    let other_id = VarId::from_raw(9951);
    let head_id = VarId::from_raw(9952);
    let tail_id = VarId::from_raw(9953);
    let subject = PseudoExpr::var_with_id("xs", subject_id);
    let clauses = vec![
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
                name: "head".to_string(),
                id: Some(head_id),
                value: PBox::new(PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::var_with_id("xs", other_id)),
                    index: 0,
                }),
                body: PBox::new(PseudoExpr::Let {
                    name: "tail".to_string(),
                    id: Some(tail_id),
                    value: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("List.tail"),
                        args: vec![PseudoExpr::var_with_id("xs", other_id)].into(),
                    }),
                    body: PBox::new(PseudoExpr::Pair(
                        PBox::new(PseudoExpr::var_with_id("head", head_id)),
                        PBox::new(PseudoExpr::var_with_id("tail", tail_id)),
                    )),
                }),
            },
        ),
    ];

    let rewritten = Simplifier::destructure_list_head_tail(&subject, &None, clauses);

    assert!(
        matches!(&rewritten[1].pattern, WhenPattern::Wildcard),
        "same-name head/tail lets with a different authoritative subject id must not become a list pattern"
    );
}

fn empty_list_pattern() -> WhenPattern {
    WhenPattern::List {
        elements: vec![],
        tail: None,
    }
}

fn assert_list_is_empty_call(expr: &PseudoExpr, expected_subject: &str) {
    assert!(
        matches!(
            expr,
            PseudoExpr::Apply { function, args }
                if matches!(
                    function.as_ref(),
                    PseudoExpr::Var { name, .. } if name == "List.is_empty"
                )
                && matches!(
                    args.as_slice(),
                    [PseudoExpr::Var { name, .. }] if name == expected_subject
                )
        ),
        "expected List.is_empty({expected_subject}), got {expr:?}"
    );
}

fn assert_expect_call(expr: &PseudoExpr) -> &[PseudoExpr] {
    let PseudoExpr::Apply { function, args } = expr else {
        panic!("expected expect! call, got {expr:?}");
    };
    assert!(
        matches!(
            function.as_ref(),
            PseudoExpr::Var { name, .. } if name == "expect!"
        ),
        "expected expect! helper, got {function:?}"
    );
    args
}

fn assert_constructor_pattern_tag(pattern: &WhenPattern, expected_tag: usize) {
    assert!(
        matches!(
            pattern,
            WhenPattern::Constructor { tag, fields, .. }
                if *tag == expected_tag && fields.is_empty()
        ),
        "expected Constr<{expected_tag}> pattern with no fields, got {pattern:?}"
    );
}

#[test]
fn tag_field_when_literals_rewrite_to_constructor_when() {
    let subject_id = VarId::from_raw(9960);
    let subject = PseudoExpr::field_access_typed(
        PseudoExpr::var_with_id("x", subject_id),
        FieldSelector::NamedField("tag".to_string()),
    );
    let clauses = vec![
        WhenClause::new(
            WhenPattern::Literal(PseudoExpr::int(0)),
            PseudoExpr::int(10),
        ),
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::int(20)),
    ];
    let simplifier = Simplifier::with_safe_mode(false);

    let (rewritten_subject, rewritten_clauses) = simplifier
        .rewrite_tag_literal_when_subject(&subject, &clauses)
        .expect("expected tag-literal rewrite");

    assert!(
        matches!(
            &rewritten_subject,
            PseudoExpr::Var { name, id, .. } if name == "x" && *id == Some(subject_id)
        ),
        "expected original tag record subject, got {rewritten_subject:?}"
    );
    assert_eq!(rewritten_clauses.len(), 2);
    assert_constructor_pattern_tag(&rewritten_clauses[0].pattern, 0);
    assert!(matches!(
        rewritten_clauses[1].pattern,
        WhenPattern::Wildcard
    ));
}

#[test]
fn tag_literal_rewrite_is_wired_in_simplify_when() {
    let subject_id = VarId::from_raw(9963);
    let subject = PseudoExpr::field_access_typed(
        PseudoExpr::var_with_id("x", subject_id),
        FieldSelector::NamedField("tag".to_string()),
    );
    let clauses = vec![
        WhenClause::new(
            WhenPattern::Literal(PseudoExpr::int(0)),
            PseudoExpr::int(10),
        ),
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::int(20)),
    ];
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier.simplify_when(subject, None, clauses);

    assert!(
        matches!(
            &rewritten,
            PseudoExpr::When { subject, clauses, .. }
                if matches!(
                    subject.as_ref(),
                    PseudoExpr::Var { name, id, .. } if name == "x" && *id == Some(subject_id)
                )
                && matches!(
                    clauses.first().map(|clause| &clause.pattern),
                    Some(pattern) if {
                        assert_constructor_pattern_tag(pattern, 0);
                        true
                    }
                )
        ),
        "expected simplify_when to rewrite tag literal dispatch, got {rewritten:?}"
    );
}

#[test]
fn tag_field_when_rejects_non_literal_pattern() {
    let subject = PseudoExpr::field_access_typed(
        PseudoExpr::var("x"),
        FieldSelector::NamedField("tag".to_string()),
    );
    let clauses = vec![
        WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
            PseudoExpr::int(10),
        ),
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::int(20)),
    ];
    let simplifier = Simplifier::with_safe_mode(false);

    assert!(
        simplifier
            .rewrite_tag_literal_when_subject(&subject, &clauses)
            .is_none(),
        "non-literal tag clauses must not be rewritten"
    );
}

#[test]
fn tracked_tag_var_when_literals_rewrite_to_original_subject() {
    let subject_id = VarId::from_raw(9961);
    let tag_var_id = VarId::from_raw(9962);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.constructors.constr_tag_subjects.insert_binding(
        "m",
        Some(tag_var_id),
        PseudoExpr::var_with_id("x", subject_id),
    );

    let clauses = vec![
        WhenClause::new(
            WhenPattern::Literal(PseudoExpr::int(1)),
            PseudoExpr::int(10),
        ),
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::int(20)),
    ];

    let (rewritten_subject, rewritten_clauses) = simplifier
        .rewrite_tag_literal_when_subject(&PseudoExpr::var_with_id("m", tag_var_id), &clauses)
        .expect("expected tracked tag-var rewrite");

    assert!(
        matches!(
            &rewritten_subject,
            PseudoExpr::Var { name, id, .. } if name == "x" && *id == Some(subject_id)
        ),
        "expected tracked original subject, got {rewritten_subject:?}"
    );
    assert_constructor_pattern_tag(&rewritten_clauses[0].pattern, 1);
}

#[test]
fn tag_literal_rewrite_preserves_guards_and_bodies() {
    let subject = PseudoExpr::field_access_typed(
        PseudoExpr::var("x"),
        FieldSelector::NamedField("tag".to_string()),
    );
    let clauses = vec![
        WhenClause {
            pattern: WhenPattern::Literal(PseudoExpr::int(2)),
            guard: Some(PseudoExpr::Bool(true)),
            body: PseudoExpr::int(42),
        },
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::int(20)),
    ];
    let simplifier = Simplifier::with_safe_mode(false);

    let (_, rewritten_clauses) = simplifier
        .rewrite_tag_literal_when_subject(&subject, &clauses)
        .expect("expected tag-literal rewrite");

    assert_constructor_pattern_tag(&rewritten_clauses[0].pattern, 2);
    assert_eq!(rewritten_clauses[0].guard, Some(PseudoExpr::Bool(true)));
    assert_eq!(rewritten_clauses[0].body, PseudoExpr::int(42));
}

#[test]
fn tag_comparison_if_rewrites_to_constructor_when_before_boolean_collapse() {
    let subject_id = VarId::from_raw(9964);
    let eq_tag_comparison = Some((PseudoExpr::var_with_id("z", subject_id), 0));
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier
        .try_simplify_tag_comparison_if(
            &eq_tag_comparison,
            &PseudoExpr::int(10),
            &PseudoExpr::Bool(false),
        )
        .expect("expected tag-comparison if rewrite");

    assert!(
        matches!(
            &rewritten,
            PseudoExpr::When { subject, clauses, .. }
                if matches!(
                    subject.as_ref(),
                    PseudoExpr::Var { name, id, .. } if name == "z" && *id == Some(subject_id)
                )
                && matches!(
                    clauses.first().map(|clause| &clause.pattern),
                    Some(pattern) if {
                        assert_constructor_pattern_tag(pattern, 0);
                        true
                    }
                )
        ),
        "expected constructor when from tag comparison, got {rewritten:?}"
    );
}

#[test]
fn expect_tag_comparison_if_rewrites_true_fail_before_or_collapse() {
    let subject_id = VarId::from_raw(9965);
    let eq_tag_comparison = Some((PseudoExpr::var_with_id("purpose", subject_id), 1));
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier
        .try_simplify_expect_tag_comparison_if(
            &eq_tag_comparison,
            &PseudoExpr::Bool(true),
            &PseudoExpr::error(),
        )
        .expect("expected expect-like tag-comparison rewrite");

    assert!(
        matches!(
            &rewritten,
            PseudoExpr::When { subject, clauses, .. }
                if matches!(
                    subject.as_ref(),
                    PseudoExpr::Var { name, id, .. } if name == "purpose" && *id == Some(subject_id)
                )
                && matches!(
                    clauses.first().map(|clause| &clause.pattern),
                    Some(pattern) if {
                        assert_constructor_pattern_tag(pattern, 1);
                        true
                    }
                )
                && matches!(clauses.first().map(|clause| &clause.body), Some(PseudoExpr::Bool(true)))
                && matches!(clauses.get(1).map(|clause| &clause.body), Some(PseudoExpr::Error { .. }))
        ),
        "expected true/fail tag comparison to stay as constructor when, got {rewritten:?}"
    );
}

/// The inverse literal order: `if (tag == N) { fail } else { True }` is a
/// must-NOT-match check — the `Constr<N>` arm must receive the FAIL (then)
/// branch. Putting `True` there instead inverts the accept set of every
/// such membership guard.
#[test]
fn expect_tag_comparison_if_keeps_fail_on_matching_arm() {
    let subject_id = VarId::from_raw(9966);
    let eq_tag_comparison = Some((PseudoExpr::var_with_id("found", subject_id), 0));
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier
        .try_simplify_expect_tag_comparison_if(
            &eq_tag_comparison,
            &PseudoExpr::error(),
            &PseudoExpr::Bool(true),
        )
        .expect("expected expect-like tag-comparison rewrite");

    assert!(
        matches!(
            &rewritten,
            PseudoExpr::When { subject, clauses, .. }
                if matches!(
                    subject.as_ref(),
                    PseudoExpr::Var { name, id, .. } if name == "found" && *id == Some(subject_id)
                )
                && matches!(
                    clauses.first().map(|clause| &clause.pattern),
                    Some(pattern) if {
                        assert_constructor_pattern_tag(pattern, 0);
                        true
                    }
                )
                && matches!(clauses.first().map(|clause| &clause.body), Some(PseudoExpr::Error { .. }))
                && matches!(clauses.get(1).map(|clause| &clause.body), Some(PseudoExpr::Bool(true)))
        ),
        "the Constr<tag> arm must receive the then-branch (fail), got {rewritten:?}"
    );
}

#[test]
fn two_clause_empty_list_bool_rewrites_to_list_is_empty() {
    let subject = PseudoExpr::var("xs");
    let clauses = vec![
        WhenClause::new(empty_list_pattern(), PseudoExpr::Bool(true)),
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
    ];
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier
        .try_simplify_two_clause_wildcard_when(&subject, &None, &clauses)
        .expect("expected list emptiness rewrite");

    assert_list_is_empty_call(&rewritten, "xs");
}

#[test]
fn two_clause_wildcard_rewrite_is_wired_in_simplify_when() {
    let clauses = vec![
        WhenClause::new(empty_list_pattern(), PseudoExpr::Bool(true)),
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
    ];
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier.simplify_when(PseudoExpr::var("xs"), None, clauses);

    assert_list_is_empty_call(&rewritten, "xs");
}

#[test]
fn two_clause_empty_list_inverted_bool_rewrites_to_not_list_is_empty() {
    let subject = PseudoExpr::var("xs");
    let clauses = vec![
        WhenClause::new(empty_list_pattern(), PseudoExpr::Bool(false)),
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(true)),
    ];
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier
        .try_simplify_two_clause_wildcard_when(&subject, &None, &clauses)
        .expect("expected inverted list emptiness rewrite");

    assert!(
        matches!(
            &rewritten,
            PseudoExpr::UnOp { op: UnaryOp::Not, operand }
                if {
                    assert_list_is_empty_call(operand, "xs");
                    true
                }
        ),
        "expected !List.is_empty(xs), got {rewritten:?}"
    );
}

#[test]
fn two_clause_empty_list_unit_fail_rewrites_to_expect_is_empty() {
    let subject = PseudoExpr::var("xs");
    let clauses = vec![
        WhenClause::new(empty_list_pattern(), PseudoExpr::Unit),
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::error()),
    ];
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier
        .try_simplify_two_clause_wildcard_when(&subject, &None, &clauses)
        .expect("expected expect(List.is_empty(xs)) rewrite");

    let args = assert_expect_call(&rewritten);
    assert_eq!(args.len(), 1);
    assert_list_is_empty_call(&args[0], "xs");
}

#[test]
fn two_clause_empty_list_fail_value_rewrites_to_expect_not_empty() {
    let subject = PseudoExpr::var("xs");
    let clauses = vec![
        WhenClause::new(empty_list_pattern(), PseudoExpr::error()),
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::int(7)),
    ];
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier
        .try_simplify_two_clause_wildcard_when(&subject, &None, &clauses)
        .expect("expected expect(!List.is_empty(xs), value) rewrite");

    let args = assert_expect_call(&rewritten);
    assert_eq!(args.len(), 2);
    assert!(
        matches!(
            &args[0],
            PseudoExpr::UnOp { op: UnaryOp::Not, operand }
                if {
                    assert_list_is_empty_call(operand, "xs");
                    true
                }
        ),
        "expected !List.is_empty(xs), got {:?}",
        args[0]
    );
    assert_eq!(args[1], PseudoExpr::int(7));
}

#[test]
fn two_clause_fail_with_message_does_not_match_nomsg_expect_rewrite() {
    let subject = PseudoExpr::var("xs");
    let clauses = vec![
        WhenClause::new(empty_list_pattern(), PseudoExpr::Unit),
        WhenClause::new(
            WhenPattern::Wildcard,
            PseudoExpr::error_with_message("boom"),
        ),
    ];
    let mut simplifier = Simplifier::with_safe_mode(false);

    assert!(
        simplifier
            .try_simplify_two_clause_wildcard_when(&subject, &None, &clauses)
            .is_none(),
        "fail-message cases must stay out of the no-message expect rewrite"
    );
}

#[test]
fn two_clause_generic_pattern_unit_fail_rewrites_to_expect_when() {
    let subject = PseudoExpr::var("value");
    let clauses = vec![
        WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(0, 1), vec!["_".into()]),
            PseudoExpr::Unit,
        ),
        WhenClause::new(WhenPattern::Wildcard, PseudoExpr::error()),
    ];
    let mut simplifier = Simplifier::with_safe_mode(false);

    let rewritten = simplifier
        .try_simplify_two_clause_wildcard_when(&subject, &None, &clauses)
        .expect("expected generic expect(when ...) rewrite");

    let args = assert_expect_call(&rewritten);
    assert_eq!(args.len(), 2);
    assert_eq!(args[1], PseudoExpr::Unit);
}
