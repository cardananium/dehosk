use super::Simplifier;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

#[test]
fn count_force_of_bindings_matches_individual_shadow_aware_counts() {
    let x = Binder::new("x", VarId::new(10));
    let y = Binder::new("y", VarId::new(11));
    let inner_x = Binder::new("x", VarId::new(12));

    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("x")))),
        args: vec![
            PseudoExpr::Lambda {
                params: vec![inner_x],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("x")))),
                    args: vec![
                        PseudoExpr::Force(PBox::new(PseudoExpr::var("y"))),
                        PseudoExpr::RecFn {
                            name: Binder::new("f", VarId::new(13)),
                            params: vec![Binder::new("y", VarId::new(14))],
                            body: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var(
                                    "x",
                                )))),
                                args: vec![PseudoExpr::Force(PBox::new(PseudoExpr::var("y")))]
                                    .into(),
                            }),
                        },
                    ]
                    .into(),
                }),
            },
            PseudoExpr::Force(PBox::new(PseudoExpr::var("y"))),
        ]
        .into(),
    };

    let binders = vec![x.clone(), y.clone()];
    let batched = Simplifier::count_force_of_bindings(&expr, &binders);
    let individual = vec![
        Simplifier::count_force_of_var(&expr, x.as_str()),
        Simplifier::count_force_of_var(&expr, y.as_str()),
    ];

    assert_eq!(batched, individual);
    assert_eq!(batched, vec![1, 2]);
}

#[test]
fn count_force_of_bindings_ignores_same_name_different_id_force_ref() {
    let target = Binder::new("x", VarId::new(21));
    let foreign_id = VarId::new(22);
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", foreign_id))),
            PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", foreign_id))),
            PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", foreign_id))),
        ]
        .into(),
    );

    assert_eq!(
        Simplifier::count_force_of_bindings(&expr, &[target]),
        vec![0]
    );
}

#[test]
fn count_force_of_bindings_does_not_shadow_authoritative_target_by_name_only() {
    let target = Binder::new("x", VarId::new(23));
    let foreign = Binder::new("x", VarId::new(24));
    let force_target = || PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", target.id)));
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Lambda {
                params: vec![foreign.clone()],
                body: PBox::new(force_target()),
            },
            PseudoExpr::Let {
                name: foreign.name.clone(),
                id: Some(foreign.id),
                value: PBox::new(PseudoExpr::Unit),
                body: PBox::new(force_target()),
            },
            PseudoExpr::RecFn {
                name: foreign,
                params: vec![],
                body: PBox::new(force_target()),
            },
        ]
        .into(),
    );

    assert_eq!(
        Simplifier::count_force_of_bindings(&expr, &[target]),
        vec![3]
    );
}

#[test]
fn count_force_of_bindings_shadows_compat_refs_under_same_name_when_binders() {
    let target = Binder::new("x", VarId::new(28));
    let foreign_subject = Binder::new("x", VarId::new(29));
    let foreign_pattern = Binder::new("x", VarId::new(30));
    let compat_force_x = || PseudoExpr::Force(PBox::new(PseudoExpr::compat_var("x")));
    let exact_force_x = || PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", target.id)));

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: Some(foreign_subject),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Var(foreign_pattern),
            guard: Some(compat_force_x()),
            body: PseudoExpr::Tuple((vec![compat_force_x(), exact_force_x()]).into()),
        }],
    };

    assert_eq!(
        Simplifier::count_force_of_bindings(&expr, &[target]),
        vec![1],
        "foreign authoritative when binders should preserve exact refs but shadow compat/name fallback refs"
    );
}

#[test]
fn replace_force_of_var_with_id_uses_replacement_id_for_compat_same_name_ref() {
    let x_id = VarId::new(20);
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::compat_var("x")));

    let replaced = Simplifier::replace_force_of_var_with_id(expr, "x", Some(x_id), "x", x_id);

    assert!(
        matches!(
            &replaced,
            PseudoExpr::Var { name, id } if name == "x" && *id == Some(x_id)
        ),
        "same-name force replacement should use the lambda param id when the forced ref is compat, got: {replaced:?}"
    );
}

#[test]
fn replace_force_of_var_with_id_respects_param_id_under_same_name_shadow() {
    let target_id = VarId::new(25);
    let foreign = Binder::new("x", VarId::new(26));
    let alias_id = VarId::new(27);

    let expr = PseudoExpr::Lambda {
        params: vec![foreign.clone()],
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", target_id))),
                PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", foreign.id))),
                PseudoExpr::Force(PBox::new(PseudoExpr::compat_var("x"))),
            ]
            .into(),
        )),
    };

    let replaced =
        Simplifier::replace_force_of_var_with_id(expr, "x", Some(target_id), "x_forced", alias_id);

    assert!(
        matches!(
            &replaced,
            PseudoExpr::Lambda { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::Tuple(items)
                        if matches!(
                            &items[0],
                            PseudoExpr::Var { name, id, .. }
                                if name == "x_forced" && *id == Some(alias_id)
                        )
                        && matches!(
                            &items[1],
                            PseudoExpr::Force(inner)
                                if matches!(
                                    inner.as_ref(),
                                    PseudoExpr::Var { name, id, .. }
                                        if name == "x" && *id == Some(foreign.id)
                                )
                        )
                        && matches!(
                            &items[2],
                            PseudoExpr::Force(inner)
                                if matches!(
                                    inner.as_ref(),
                                    PseudoExpr::Var { name, id, .. }
                                        if name == "x" && id.is_none()
                                )
                        )
                )
        ),
        "only the authoritative target force should be replaced under a same-name shadow, got: {replaced:?}"
    );
}

#[test]
fn replace_force_of_var_with_id_shadows_compat_refs_under_same_name_when_binders() {
    let target_id = VarId::new(31);
    let alias_id = VarId::new(32);
    let foreign_subject = Binder::new("x", VarId::new(33));
    let foreign_pattern = Binder::new("x", VarId::new(34));
    let compat_force_x = || PseudoExpr::Force(PBox::new(PseudoExpr::compat_var("x")));
    let exact_force_x = || PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", target_id)));

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: Some(foreign_subject),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Var(foreign_pattern),
            guard: Some(compat_force_x()),
            body: PseudoExpr::Tuple((vec![compat_force_x(), exact_force_x()]).into()),
        }],
    };

    let replaced =
        Simplifier::replace_force_of_var_with_id(expr, "x", Some(target_id), "x_forced", alias_id);

    assert!(
        matches!(
            &replaced,
            PseudoExpr::When { clauses, .. }
                if matches!(
                    clauses.as_slice(),
                    [WhenClause {
                        guard: Some(PseudoExpr::Force(guard_inner)),
                        body: PseudoExpr::Tuple(items),
                        ..
                    }]
                        if matches!(
                            guard_inner.as_ref(),
                            PseudoExpr::Var { name, id } if name == "x" && id.get().is_none()
                        )
                        && matches!(
                            items.as_slice(),
                            [
                                PseudoExpr::Force(body_inner),
                                PseudoExpr::Var { name, id }
                            ] if matches!(
                                body_inner.as_ref(),
                                PseudoExpr::Var { name, id } if name == "x" && id.get().is_none()
                            ) && name == "x_forced" && *id == Some(alias_id)
                        )
                )
        ),
        "when binders should block compat/name force replacement but keep exact-id replacement active, got: {replaced:?}"
    );
}
