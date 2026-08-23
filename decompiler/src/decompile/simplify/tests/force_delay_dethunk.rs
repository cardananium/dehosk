use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_nested_dethunk_rewrites_force_var_inside_apply() {
    let selector = PseudoExpr::Lambda {
        params: vec!["x".to_string().into(), "_".to_string().into()],
        body: PBox::new(PseudoExpr::var("x")),
    };
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(selector))),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::Force(PBox::new(PseudoExpr::var("k")))].into(),
        }),
    };

    let simplified = simplify(expr);
    assert!(!matches!(
        simplified,
        PseudoExpr::Apply { args, .. }
            if matches!(
                args.first(),
                Some(PseudoExpr::Force(inner))
                    if matches!(inner.as_ref(), PseudoExpr::Var { name, .. } if name == "k")
            )
    ));
}

#[test]
fn test_nested_dethunk_respects_shadowing() {
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::int(42)))),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["k".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![PseudoExpr::Force(PBox::new(PseudoExpr::var("k")))].into(),
            }),
        }),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Lambda { body, .. } => match body.as_ref() {
            PseudoExpr::Apply { args, .. } => {
                assert!(matches!(args.first(), Some(PseudoExpr::Force(_))));
            }
            _ => panic!("expected apply inside lambda"),
        },
        _ => panic!("expected outer let to be dropped"),
    }
}

#[test]
fn test_force_when_unwraps_delayed_clause_bodies() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};

    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("s")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
            },
            WhenClause {
                pattern: WhenPattern::Var("x".to_string().into()),
                guard: None,
                body: PseudoExpr::Delay(PBox::new(PseudoExpr::Bool(true))),
            },
        ],
    }));

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When { clauses, .. } => {
            assert!(matches!(clauses[0].body, PseudoExpr::Int(_)));
            assert!(matches!(clauses[1].body, PseudoExpr::Bool(_)));
        }
        _ => panic!("expected when"),
    }
}

#[test]
fn test_let_triple_force_dethunk_closed_value() {
    let delayed = PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(
        PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into(), "_".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }),
    )))));
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(delayed),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(
            PseudoExpr::Force(PBox::new(PseudoExpr::var("k"))),
        ))))),
    };

    let simplified = simplify(expr);
    assert!(!matches!(
        simplified,
        PseudoExpr::Force(inner1)
            if matches!(
                inner1.as_ref(),
                PseudoExpr::Force(inner2)
                    if matches!(
                        inner2.as_ref(),
                        PseudoExpr::Force(inner3)
                            if matches!(inner3.as_ref(), PseudoExpr::Var { name, .. } if name == "k")
                    )
            )
    ));
}

#[test]
fn test_force_let_pushdown() {
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("x")))),
    }));

    let simplified = simplify(expr);
    // force(let x = 1 in delay(x)) -> let x = 1 in x -> 1 (single-use inlined)
    assert!(
        matches!(simplified, PseudoExpr::Int(ref n) if *n == 1.into()),
        "Expected Int(1), got: {:?}",
        simplified
    );
}

#[test]
fn test_force_trace_pushdown() {
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::string("m")),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::int(7)))),
    }));

    let simplified = simplify(expr);
    assert!(matches!(
        simplified,
        PseudoExpr::Trace { value, .. } if matches!(value.as_ref(), PseudoExpr::Int(_))
    ));
}

#[test]
fn test_apply_trace_reconstitution_moves_args_and_preserves_ids() {
    let message_id = VarId::new(9251);
    let value_id = VarId::new(9252);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("trace"),
            args: vec![].into(),
        }),
        args: vec![
            PseudoExpr::var_with_id("message", message_id),
            PseudoExpr::Lambda {
                params: vec![Binder::new("value", value_id)],
                body: PBox::new(PseudoExpr::var_with_id("value", value_id)),
            },
        ]
        .into(),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::Trace { message, value }
                if matches!(message.as_ref(), PseudoExpr::Var { name, id } if name == "message" && *id == Some(message_id))
                    && matches!(
                        value.as_ref(),
                        PseudoExpr::Lambda { params, body }
                            if matches!(params.as_slice(), [binder] if binder.as_str() == "value" && binder.id == value_id)
                                && matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "value" && *id == Some(value_id))
                    )
        ),
        "expected trace reconstitution to move message/value args with ids intact, got: {simplified:?}"
    );
}

#[test]
fn test_delay_force_known_delayed_var_to_var() {
    let delayed_fn = PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
        params: vec!["x".to_string().into()],
        body: PBox::new(PseudoExpr::var("x")),
    }));
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(delayed_fn),
        body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Force(PBox::new(
            PseudoExpr::var("k"),
        ))))),
    };

    let simplified = simplify(expr);
    assert!(!matches!(
        simplified,
        PseudoExpr::Let { body, .. }
            if matches!(
                body.as_ref(),
                PseudoExpr::Delay(inner)
                    if matches!(
                        inner.as_ref(),
                        PseudoExpr::Force(force_inner)
                            if matches!(force_inner.as_ref(), PseudoExpr::Var { name, .. } if name == "k")
                    )
            )
    ));
}

#[test]
fn test_delay_force_known_var_preserves_observed_ref_id_over_name_lookup() {
    let mut simplifier = Simplifier::with_safe_mode(false);
    let outer_id = VarId::new(9_831);
    let inner_id = VarId::new(9_832);

    simplifier
        .naming
        .name_to_id
        .insert("x".to_string(), outer_id);
    simplifier.delays.delayed_value_depths.insert(outer_id, 1);
    simplifier.delays.delayed_value_depths.insert(inner_id, 1);

    let simplified = simplifier.simplify_delay(PseudoExpr::Force(PBox::new(
        PseudoExpr::var_with_id("x", inner_id),
    )));

    assert!(
        matches!(
            &simplified,
            PseudoExpr::Var { name, id } if name == "x" && *id == Some(inner_id)
        ),
        "delay(force(x@inner)) must preserve the observed ref id, got: {simplified:?}"
    );
}

#[test]
fn test_replace_forced_var_matches_force_chain_by_var_id_not_name() {
    let mut simplifier = Simplifier::with_safe_mode(false);
    let target_id = VarId::new(9_833);
    let foreign_id = VarId::new(9_834);
    let inner_id = VarId::new(9_835);

    let force_twice = |expr| PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(expr))));
    let expr = PseudoExpr::Tuple(
        vec![
            force_twice(PseudoExpr::var_with_id("k", target_id)),
            force_twice(PseudoExpr::var_with_id("k", foreign_id)),
            PseudoExpr::Let {
                name: "k".to_string(),
                id: Some(inner_id),
                value: PBox::new(PseudoExpr::int(0)),
                body: PBox::new(force_twice(PseudoExpr::var_with_id("k", target_id))),
            },
        ]
        .into(),
    );

    let replaced =
        simplifier.replace_forced_var(expr, "k", Some(target_id), &PseudoExpr::int(9), 2);

    let PseudoExpr::Tuple(items) = replaced else {
        panic!("expected tuple after replacement");
    };
    assert!(matches!(&items[0], PseudoExpr::Int(n) if *n == 9.into()));
    assert!(
        matches!(
            &items[1],
            PseudoExpr::Force(first)
                if matches!(
                    first.as_ref(),
                    PseudoExpr::Force(second)
                        if matches!(
                            second.as_ref(),
                            PseudoExpr::Var { name, id } if name == "k" && *id == Some(foreign_id)
                        )
                )
        ),
        "same-name foreign force chain should not be replaced: {:?}",
        items[1]
    );
    assert!(
        matches!(
            &items[2],
            PseudoExpr::Let { name, id, body, .. }
                if name == "k" && *id == Some(inner_id)
                    && matches!(body.as_ref(), PseudoExpr::Int(n) if *n == 9.into())
        ),
        "same-name foreign binder should not shadow the target id: {:?}",
        items[2]
    );
}

#[test]
fn test_delayed_let_force_chain_inline_rewrites_target_id_under_same_name_let() {
    let outer_id = VarId::new(9_836);
    let inner_id = VarId::new(9_837);
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
            PseudoExpr::int(1),
        ))))),
        body: PBox::new(PseudoExpr::Let {
            name: "k".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::int(0)),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(
                        PseudoExpr::var_with_id("k", outer_id),
                    )))),
                    PseudoExpr::var_with_id("k", inner_id),
                    PseudoExpr::var_with_id("k", inner_id),
                ]
                .into(),
            )),
        }),
    };

    let simplified = simplify(expr);

    let PseudoExpr::Let { name, id, body, .. } = &simplified else {
        panic!("expected inner let after delayed-force inline, got: {simplified:?}");
    };
    assert_eq!(name, "k");
    assert_eq!(*id, Some(inner_id));
    let PseudoExpr::Tuple(items) = body.as_ref() else {
        panic!("expected tuple body, got: {body:?}");
    };
    assert!(matches!(&items[0], PseudoExpr::Int(n) if *n == 1.into()));
    assert!(
        matches!(&items[1], PseudoExpr::Var { name, id } if name == "k" && *id == Some(inner_id))
    );
    assert!(
        matches!(&items[2], PseudoExpr::Var { name, id } if name == "k" && *id == Some(inner_id))
    );
    assert_eq!(
        Simplifier::count_force_chain_uses_by_id(&simplified, "k", Some(outer_id), 2),
        0
    );
}

#[test]
fn test_delay_double_force_known_double_delayed_var_to_single_force() {
    let delayed_twice = PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
        PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        },
    ))));

    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(delayed_twice),
        body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Force(PBox::new(
            PseudoExpr::Force(PBox::new(PseudoExpr::var("k"))),
        ))))),
    };

    let simplified = simplify(expr);
    assert!(!matches!(
        simplified,
        PseudoExpr::Let { body, .. }
            if matches!(
                body.as_ref(),
                PseudoExpr::Delay(inner)
                    if matches!(
                        inner.as_ref(),
                        PseudoExpr::Force(inner2)
                            if matches!(
                                inner2.as_ref(),
                                PseudoExpr::Force(inner3)
                                    if matches!(inner3.as_ref(), PseudoExpr::Var { name, .. } if name == "k")
                            )
                    )
            )
    ));
}
