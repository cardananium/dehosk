use super::Simplifier;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

#[test]
fn count_binding_uses_by_id_matches_individual_shadow_aware_counts() {
    let outer_x = Binder::new("x", VarId::new(10));
    let outer_y = Binder::new("y", VarId::new(11));
    let inner_x = Binder::new("x", VarId::new(12));
    let rec_name = Binder::new("f", VarId::new(13));
    let rec_param = Binder::new("z", VarId::new(14));
    let clause_var = Binder::new("w", VarId::new(15));

    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![inner_x.clone()],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var_with_id("x", outer_x.id)),
                subject_name: None,
                clauses: vec![crate::pseudo::ast::WhenClause::new(
                    crate::pseudo::ast::WhenPattern::Var(clause_var),
                    PseudoExpr::RecFn {
                        name: rec_name.clone(),
                        params: vec![rec_param.clone()],
                        body: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var_with_id("x", outer_x.id)),
                            args: vec![
                                PseudoExpr::var_with_id("y", outer_y.id),
                                PseudoExpr::var_with_id("x", inner_x.id),
                                PseudoExpr::var_with_id("f", rec_name.id),
                            ]
                            .into(),
                        }),
                    },
                )],
            }),
        }),
        args: vec![PseudoExpr::var_with_id("y", outer_y.id)].into(),
    };

    let binders = vec![outer_x.clone(), outer_y.clone()];
    let binder_ids = vec![Some(outer_x.id), Some(outer_y.id)];
    let batched = Simplifier::count_binding_uses_by_id(&expr, &binders, &binder_ids);

    let individual: Vec<_> = binders
        .iter()
        .zip(binder_ids.iter().copied())
        .map(|(binder, id)| Simplifier::count_var_uses_by_id(&expr, binder.as_str(), id))
        .collect();

    assert_eq!(batched, individual);
    assert_eq!(batched, vec![2, 2]);
}

#[test]
fn count_binding_uses_by_id_counts_exact_refs_under_same_name_foreign_binders() {
    let outer_x = Binder::new("x", VarId::new(16));
    let outer_y = Binder::new("y", VarId::new(17));
    let foreign_x = Binder::new("x", VarId::new(18));
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Lambda {
                params: vec![foreign_x.clone()],
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("x", outer_x.id),
                        PseudoExpr::var_with_id("y", outer_y.id),
                        PseudoExpr::compat_var("x"),
                    ]
                    .into(),
                )),
            },
            PseudoExpr::Let {
                name: foreign_x.name.clone(),
                id: Some(foreign_x.id),
                value: PBox::new(PseudoExpr::Unit),
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("x", outer_x.id),
                        PseudoExpr::var_with_id("y", outer_y.id),
                        PseudoExpr::compat_var("x"),
                    ]
                    .into(),
                )),
            },
            PseudoExpr::RecFn {
                name: foreign_x,
                params: vec![],
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("x", outer_x.id),
                        PseudoExpr::var_with_id("y", outer_y.id),
                        PseudoExpr::compat_var("x"),
                    ]
                    .into(),
                )),
            },
        ]
        .into(),
    );

    let binders = vec![outer_x.clone(), outer_y.clone()];
    let binder_ids = vec![Some(outer_x.id), Some(outer_y.id)];

    assert_eq!(
        Simplifier::count_binding_uses_by_id(&expr, &binders, &binder_ids),
        vec![3, 3],
        "same-name different-id binders must shadow fallback refs but not exact-id refs"
    );
}

#[test]
fn count_var_uses_by_id_keeps_fallback_shadow_separate_from_exact_refs() {
    let outer_x = Binder::new("x", VarId::new(19));
    let foreign_x = Binder::new("x", VarId::new(20));
    let expr = PseudoExpr::Lambda {
        params: vec![foreign_x],
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("x", outer_x.id),
                PseudoExpr::compat_var("x"),
            ]
            .into(),
        )),
    };

    assert_eq!(
        Simplifier::count_var_uses_by_id(&expr, outer_x.as_str(), Some(outer_x.id)),
        1,
        "exact outer ref should count under same-name foreign lambda, but compat fallback should not"
    );
    assert_eq!(
        Simplifier::count_binding_uses_by_id(
            &expr,
            std::slice::from_ref(&outer_x),
            &[Some(outer_x.id)]
        ),
        vec![1],
        "single-target batched path should match count_var_uses_by_id"
    );
}

#[test]
fn count_var_uses_by_id_counts_exact_refs_under_same_name_foreign_when_binders() {
    let outer_x = Binder::new("x", VarId::new(51));
    let outer_y = Binder::new("y", VarId::new(52));
    let foreign_subject_x = Binder::new("x", VarId::new(53));
    let foreign_pattern_x = Binder::new("x", VarId::new(54));

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", outer_x.id)),
        subject_name: Some(foreign_subject_x),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Var(foreign_pattern_x),
            guard: Some(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("x", outer_x.id),
                    PseudoExpr::compat_var("x"),
                ]
                .into(),
            )),
            body: PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("x", outer_x.id),
                    PseudoExpr::var_with_id("y", outer_y.id),
                    PseudoExpr::compat_var("x"),
                ]
                .into(),
            ),
        }],
    };

    assert_eq!(
        Simplifier::count_var_uses_by_id(&expr, outer_x.as_str(), Some(outer_x.id)),
        3,
        "same-name foreign when binders must shadow fallback refs but not exact outer refs"
    );
    assert_eq!(
        Simplifier::count_binding_uses_by_id(
            &expr,
            &[outer_x.clone(), outer_y.clone()],
            &[Some(outer_x.id), Some(outer_y.id)]
        ),
        vec![3, 1],
        "batched counting should use the same id-aware when shadow semantics"
    );
}

#[test]
fn expr_size_preserves_existing_when_contract() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Literal(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("ignored_pattern")),
                    args: vec![PseudoExpr::int(1)].into(),
                }),
                guard: Some(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("ignored_guard")),
                    args: vec![PseudoExpr::int(2)].into(),
                }),
                body: PseudoExpr::Force(PBox::new(PseudoExpr::var("kept_body"))),
            },
            WhenClause::new(
                WhenPattern::Wildcard,
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(3))),
            ),
        ],
    };

    assert_eq!(
        Simplifier::expr_size(&expr),
        6,
        "expr_size must continue counting only when subject and clause bodies"
    );
}

#[test]
fn count_binding_uses_by_id_single_target_matches_shadow_aware_single_count() {
    let outer_x = Binder::new("x", VarId::new(21));
    let inner_x = Binder::new("x", VarId::new(22));

    let expr = PseudoExpr::Let {
        name: outer_x.to_string(),
        id: Some(outer_x.id),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("x", outer_x.id)),
            args: vec![PseudoExpr::var_with_id("x", outer_x.id)].into(),
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![inner_x],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var_with_id("x", outer_x.id)),
                subject_name: None,
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::Literal(PseudoExpr::var("x")),
                        PseudoExpr::var_with_id("x", outer_x.id),
                    ),
                    WhenClause::new(WhenPattern::Wildcard, PseudoExpr::var("x")),
                ],
            }),
        }),
    };

    assert_eq!(
        Simplifier::count_binding_uses_by_id(
            &expr,
            std::slice::from_ref(&outer_x),
            &[Some(outer_x.id)]
        ),
        vec![Simplifier::count_var_uses_by_id(
            &expr,
            outer_x.as_str(),
            Some(outer_x.id)
        )]
    );
}

#[test]
fn count_var_uses_ignores_when_subject_name_shadowing() {
    let outer_x = Binder::new("x", VarId::new(31));
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", outer_x.id)),
        subject_name: Some(Binder::synthetic("x")),
        clauses: vec![WhenClause::new(
            WhenPattern::Wildcard,
            PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var("x"),
                    PseudoExpr::When {
                        subject: PBox::new(PseudoExpr::var("x")),
                        subject_name: Some(Binder::synthetic("x")),
                        clauses: vec![WhenClause::new(WhenPattern::Wildcard, PseudoExpr::var("x"))],
                    },
                ]
                .into(),
            ),
        )],
    };

    assert_eq!(
        Simplifier::count_var_uses(&expr, "x"),
        1,
        "expected clause/body uses shadowed by when subject_name to be ignored"
    );
}

#[test]
fn count_var_uses_by_id_ignores_when_subject_name_shadowing() {
    let outer_x = Binder::new("x", VarId::new(41));
    let compat_subject_x = || Binder::new("x", VarId::fresh_compat_placeholder());
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", outer_x.id)),
        subject_name: Some(compat_subject_x()),
        clauses: vec![WhenClause::new(
            WhenPattern::Wildcard,
            PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("x", outer_x.id),
                    PseudoExpr::When {
                        subject: PBox::new(PseudoExpr::var_with_id("x", outer_x.id)),
                        subject_name: Some(compat_subject_x()),
                        clauses: vec![WhenClause::new(
                            WhenPattern::Wildcard,
                            PseudoExpr::var_with_id("x", outer_x.id),
                        )],
                    },
                ]
                .into(),
            ),
        )],
    };

    assert_eq!(
        Simplifier::count_var_uses_by_id(&expr, outer_x.as_str(), Some(outer_x.id)),
        1,
        "expected when subject_name to shadow VarId-aware use counting inside clauses"
    );
    assert_eq!(
        Simplifier::count_binding_uses_by_id(
            &expr,
            std::slice::from_ref(&outer_x),
            &[Some(outer_x.id)]
        ),
        vec![1],
        "expected batched binding use counting to match subject_name shadowing semantics"
    );
}
