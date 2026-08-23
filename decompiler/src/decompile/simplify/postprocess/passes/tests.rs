use super::*;
use crate::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

#[test]
fn test_convert_expect_tag_to_constr_when_moves_value_arg_and_preserves_id() {
    let subject_id = VarId::new(9951);
    let value_id = VarId::new(9952);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::expect_helper()),
        args: vec![
            PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("x", subject_id),
                    "tag".to_string(),
                )),
                right: PBox::new(PseudoExpr::int(0)),
            },
            PseudoExpr::var_with_id("value", value_id),
        ]
        .into(),
    };

    let converted = convert_expect_tag_to_constr_when(expr);

    let PseudoExpr::When {
        subject, clauses, ..
    } = converted
    else {
        panic!("expected expect-tag rewrite to produce When");
    };
    assert!(
        matches!(
            subject.as_ref(),
            PseudoExpr::Var { name, id } if name == "x" && *id == Some(subject_id)
        ),
        "expect-tag rewrite should preserve subject id, got: {subject:?}"
    );
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::Var { name, id } if name == "value" && *id == Some(value_id)
        ),
        "expect-tag rewrite should move value arg with id intact, got: {:?}",
        clauses[0].body
    );
}

#[test]
fn test_normalize_list_cons_literals_rewrites_let_bound_prepend_alias_chain() {
    // Uses authoritative VarIds (`fresh_binding`, `var_with_id`)
    // so the test hits the id-based dispatch the nameless
    // implementation uses; legacy matches the same shape
    // through its name-keyed scope stack.
    let c_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(c_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("List.prepend"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("c", c_id)),
            args: vec![
                PseudoExpr::int(1),
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("c", c_id)),
                    args: vec![
                        PseudoExpr::int(2),
                        PseudoExpr::List {
                            elements: vec![].into(),
                            tail: None,
                        },
                    ]
                    .into(),
                },
            ]
            .into(),
        }),
    };

    let normalized = normalize_list_cons_literals(expr);

    assert!(
        matches!(
            normalized,
            PseudoExpr::List { ref elements, tail: None }
                if elements.len() == 2
                    && matches!(&elements[0], PseudoExpr::Int(n) if n == &1.into())
                    && matches!(&elements[1], PseudoExpr::Int(n) if n == &2.into())
        ),
        "expected let-bound List.prepend alias chain to normalize into a plain list literal, got: {normalized:?}"
    );
}

#[test]
fn test_normalize_list_cons_literals_respects_let_alias_shadowing() {
    let outer_id = VarId::new(9111);
    let inner_id = VarId::new(9112);
    let expr = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("List.prepend"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "c".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::int(0)),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("c", inner_id)),
                args: vec![
                    PseudoExpr::int(1),
                    PseudoExpr::List {
                        elements: vec![].into(),
                        tail: None,
                    },
                ]
                .into(),
            }),
        }),
    };

    let normalized = normalize_list_cons_literals(expr);

    fn contains_shadowed_apply(expr: &PseudoExpr, inner_id: VarId) -> bool {
        match expr {
            PseudoExpr::Let { id, body, .. } if *id == Some(inner_id) => matches!(
                body.as_ref(),
                PseudoExpr::Apply { function, .. }
                    if matches!(function.as_ref(), PseudoExpr::Var { id, .. } if *id == Some(inner_id))
            ),
            PseudoExpr::Let { body, .. } => contains_shadowed_apply(body, inner_id),
            _ => false,
        }
    }

    assert!(
        contains_shadowed_apply(&normalized, inner_id),
        "expected inner shadowing `c` call to stay as an apply, got: {normalized:?}"
    );
}

#[test]
fn test_normalize_list_cons_literals_respects_lambda_alias_shadowing() {
    let alias_id = VarId::new(9121);
    let param_id = VarId::new(9122);
    let expr = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(alias_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("List.prepend"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("c", param_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("c", param_id)),
                args: vec![
                    PseudoExpr::int(1),
                    PseudoExpr::List {
                        elements: vec![].into(),
                        tail: None,
                    },
                ]
                .into(),
            }),
        }),
    };

    let normalized = normalize_list_cons_literals(expr);

    fn contains_shadowed_lambda_apply(expr: &PseudoExpr, param_id: VarId) -> bool {
        match expr {
            PseudoExpr::Lambda { body, .. } => matches!(
                body.as_ref(),
                PseudoExpr::Apply { function, .. }
                    if matches!(function.as_ref(), PseudoExpr::Var { id, .. } if *id == Some(param_id))
            ),
            PseudoExpr::Let { body, .. } => contains_shadowed_lambda_apply(body, param_id),
            _ => false,
        }
    }

    assert!(
        contains_shadowed_lambda_apply(&normalized, param_id),
        "expected lambda-shadowed `c` call to stay as an apply, got: {normalized:?}"
    );
}

#[test]
fn test_cancel_force_delay_vars_list_index_root_moves_selected_items() {
    let item_id = VarId::new(9221);
    let tail_id = VarId::new(9222);

    let selected = cancel_force_delay_vars(PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::List {
            elements: vec![
                PseudoExpr::var_with_id("picked", item_id),
                PseudoExpr::var("dropped"),
            ]
            .into(),
            tail: None,
        }),
        index: 0,
    });
    assert!(
        matches!(
            &selected,
            PseudoExpr::Var { name, id } if name == "picked" && *id == Some(item_id)
        ),
        "expected list index root to return the selected item, got: {selected:?}"
    );

    let selected_tail = cancel_force_delay_vars(PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::List {
            elements: vec![PseudoExpr::int(1)].into(),
            tail: Some(PBox::new(PseudoExpr::var_with_id("tail", tail_id))),
        }),
        index: 1,
    });
    assert!(
        matches!(
            &selected_tail,
            PseudoExpr::Var { name, id } if name == "tail" && *id == Some(tail_id)
        ),
        "expected list index at element length to return the list tail, got: {selected_tail:?}"
    );
}

#[test]
fn test_cancel_force_delay_vars_builtin_field_access_root_moves_projected_args() {
    fn assert_var(expr: PseudoExpr, expected_name: &str, expected_id: VarId) {
        assert!(
            matches!(
                &expr,
                PseudoExpr::Var { name, id }
                    if name == expected_name && *id == Some(expected_id)
            ),
            "expected {expected_name}/{expected_id:?}, got: {expr:?}"
        );
    }

    let tag_id = VarId::new(9231);
    let fields_id = VarId::new(9232);
    assert_var(
        cancel_force_delay_vars(PseudoExpr::field_access(
            PseudoExpr::BuiltinCall {
                name: BuiltinId::expect_known("Data.Constr"),
                args: vec![
                    PseudoExpr::var_with_id("tag_arg", tag_id),
                    PseudoExpr::var_with_id("fields_arg", fields_id),
                ]
                .into(),
            },
            "tag",
        )),
        "tag_arg",
        tag_id,
    );
    assert_var(
        cancel_force_delay_vars(PseudoExpr::field_access(
            PseudoExpr::BuiltinCall {
                name: BuiltinId::expect_known("Data.Constr"),
                args: vec![
                    PseudoExpr::var_with_id("tag_arg", tag_id),
                    PseudoExpr::var_with_id("fields_arg", fields_id),
                ]
                .into(),
            },
            "fields",
        )),
        "fields_arg",
        fields_id,
    );

    let fst_id = VarId::new(9233);
    let snd_id = VarId::new(9234);
    assert_var(
        cancel_force_delay_vars(PseudoExpr::field_access(
            PseudoExpr::BuiltinCall {
                name: BuiltinId::expect_known("Pair.new"),
                args: vec![
                    PseudoExpr::var_with_id("fst_arg", fst_id),
                    PseudoExpr::var_with_id("snd_arg", snd_id),
                ]
                .into(),
            },
            "fst",
        )),
        "fst_arg",
        fst_id,
    );
    assert_var(
        cancel_force_delay_vars(PseudoExpr::field_access(
            PseudoExpr::BuiltinCall {
                name: BuiltinId::expect_known("Pair.new"),
                args: vec![
                    PseudoExpr::var_with_id("fst_arg", fst_id),
                    PseudoExpr::var_with_id("snd_arg", snd_id),
                ]
                .into(),
            },
            "snd",
        )),
        "snd_arg",
        snd_id,
    );

    let list_id = VarId::new(9235);
    let head_projection = cancel_force_delay_vars(PseudoExpr::field_access(
        PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("List.head"),
            args: vec![PseudoExpr::var_with_id("items", list_id)].into(),
        },
        "head",
    ));
    assert!(
        matches!(
            &head_projection,
            PseudoExpr::IndexAccess { collection, index: 0 }
                if matches!(
                    collection.as_ref(),
                    PseudoExpr::Var { name, id } if name == "items" && *id == Some(list_id)
                )
        ),
        "expected List.head field root to move its list arg into index 0, got: {head_projection:?}"
    );

    let tail_projection = cancel_force_delay_vars(PseudoExpr::field_access(
        PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("List.tail"),
            args: vec![PseudoExpr::var_with_id("items", list_id)].into(),
        },
        "tail",
    ));
    assert!(
        matches!(
            &tail_projection,
            PseudoExpr::IndexAccess { collection, index: 1 }
                if matches!(
                    collection.as_ref(),
                    PseudoExpr::Var { name, id } if name == "items" && *id == Some(list_id)
                )
        ),
        "expected List.tail field root to move its list arg into index 1, got: {tail_projection:?}"
    );
}

#[test]
fn test_strip_force_on_var_respects_let_shadowing() {
    let shadow_id = VarId::new(777);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(shadow_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("x")))),
    };

    let stripped = strip_force_on_var(expr.clone(), "x", None);

    assert_eq!(stripped, expr);
}

#[test]
fn test_strip_force_on_var_respects_when_subject_and_pattern_shadowing() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: Some(Binder::new("x", VarId::fresh_compat_placeholder())),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Var(Binder::new("x", VarId::fresh_compat_placeholder())),
            guard: Some(PseudoExpr::Force(PBox::new(PseudoExpr::var("x")))),
            body: PseudoExpr::Force(PBox::new(PseudoExpr::var("x"))),
        }],
    };

    let stripped = strip_force_on_var(expr.clone(), "x", None);

    assert_eq!(stripped, expr);
}

#[test]
fn test_count_var_usages_counts_forced_hits_once_and_respects_shadowing() {
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Force(PBox::new(PseudoExpr::var("x"))),
            PseudoExpr::var("x"),
            PseudoExpr::Let {
                name: "x".to_string(),
                id: Some(VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::int(1)),
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::Force(PBox::new(PseudoExpr::var("x"))),
                        PseudoExpr::var("x"),
                    ]
                    .into(),
                )),
            },
            PseudoExpr::Lambda {
                params: vec!["x".to_string().into()],
                body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("x")))),
            },
            PseudoExpr::RecFn {
                name: "loop".to_string().into(),
                params: vec!["x".to_string().into()],
                body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("x")))),
            },
        ]
        .into(),
    );

    let (force_uses, total_uses) = count_var_usages(&expr, "x", None);

    assert_eq!(force_uses, 1);
    assert_eq!(total_uses, 2);
}

#[test]
fn test_count_var_usages_respects_when_subject_and_pattern_shadowing() {
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Force(PBox::new(PseudoExpr::var("x"))),
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("subject")),
                subject_name: Some(Binder::new("x", VarId::fresh_compat_placeholder())),
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Var(Binder::new("x", VarId::fresh_compat_placeholder())),
                    guard: Some(PseudoExpr::Force(PBox::new(PseudoExpr::var("x")))),
                    body: PseudoExpr::Force(PBox::new(PseudoExpr::var("x"))),
                }],
            },
        ]
        .into(),
    );

    let (force_uses, total_uses) = count_var_usages(&expr, "x", None);

    assert_eq!(force_uses, 1);
    assert_eq!(total_uses, 1);
}

#[test]
fn test_cancel_force_delay_vars_alias_collapse_preserves_unique_let_names() {
    let y_id = VarId::new(781);
    let x_id = VarId::new(782);
    let z_id = VarId::new(783);
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(y_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(x_id),
            value: PBox::new(PseudoExpr::var_with_id("y", y_id)),
            body: PBox::new(PseudoExpr::Let {
                name: "z".to_string(),
                id: Some(z_id),
                value: PBox::new(PseudoExpr::int(2)),
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("x", x_id),
                        PseudoExpr::var_with_id("z", z_id),
                    ]
                    .into(),
                )),
            }),
        }),
    };

    let out = cancel_force_delay_vars(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { name, id, body, .. }
                if name == "y"
                    && *id == Some(y_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Let { name, id, body, .. }
                            if name == "z"
                                && *id == Some(z_id)
                                && matches!(
                                    body.as_ref(),
                                    PseudoExpr::Tuple(items)
                                        if matches!(
                                            items.as_slice(),
                                            [
                                                PseudoExpr::Var { name: left_name, id: left_id },
                                                PseudoExpr::Var { name: right_name, id: right_id },
                                            ] if left_name == "y"
                                                && *left_id == Some(y_id)
                                                && right_name == "z"
                                                && *right_id == Some(z_id)
                                        )
                                )
                    )
        ),
        "expected alias collapse to remove only x and keep unique let names y/z, got: {out:?}"
    );
}

#[test]
fn test_cancel_force_delay_vars_ignores_same_name_different_id_force() {
    let binding_id = VarId::new(791);
    let foreign_id = VarId::new(792);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::int(1)))),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id(
            "x", foreign_id,
        )))),
    };

    let out = cancel_force_delay_vars(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { name, id, value, body }
                if name == "x"
                    && *id == Some(binding_id)
                    && matches!(value.as_ref(), PseudoExpr::Delay(inner) if matches!(inner.as_ref(), PseudoExpr::Int(n) if n == &1.into()))
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Force(inner)
                            if matches!(
                                inner.as_ref(),
                                PseudoExpr::Var { name, id } if name == "x" && *id == Some(foreign_id)
                            )
                    )
        ),
        "force/delay cancellation must ignore a same-name ref with a different VarId, got: {out:?}"
    );
}

#[test]
fn test_cancel_force_delay_vars_trivial_let_requires_matching_var_id() {
    let binding_id = VarId::new(793);
    let foreign_id = VarId::new(794);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::var_with_id("x", foreign_id)),
    };

    let out = cancel_force_delay_vars(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { name, id, value, body }
                if name == "x"
                    && *id == Some(binding_id)
                    && matches!(value.as_ref(), PseudoExpr::Int(n) if n == &1.into())
                    && matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "x" && *id == Some(foreign_id))
        ),
        "trivial let inlining must require the body ref to target the let binder, got: {out:?}"
    );
}

#[test]
fn test_cancel_force_delay_vars_identity_value_let_requires_matching_var_id() {
    let outer_id = VarId::new(795);
    let inner_binding_id = VarId::new(796);
    let foreign_id = VarId::new(797);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(inner_binding_id),
            value: PBox::new(PseudoExpr::int(1)),
            body: PBox::new(PseudoExpr::var_with_id("y", foreign_id)),
        }),
        body: PBox::new(PseudoExpr::var_with_id("x", outer_id)),
    };

    let out = cancel_force_delay_vars(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { name, id, value, body }
                if name == "y"
                    && *id == Some(inner_binding_id)
                    && matches!(value.as_ref(), PseudoExpr::Int(n) if n == &1.into())
                    && matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "y" && *id == Some(foreign_id))
        ),
        "identity value-let collapse must require the inner body ref to target the inner binder, got: {out:?}"
    );
}

#[test]
fn test_cancel_force_delay_vars_respects_when_pattern_shadowing() {
    let x_id = VarId::fresh_compat_placeholder();
    let pattern_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::int(1)))),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("subject")),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Var(Binder::new("x", pattern_id)),
                guard: None,
                body: PseudoExpr::Force(PBox::new(PseudoExpr::var("x"))),
            }],
        }),
    };

    let out = cancel_force_delay_vars(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { name, id, value, body }
                if name == "x"
                    && *id == Some(x_id)
                    && matches!(value.as_ref(), PseudoExpr::Delay(inner) if matches!(inner.as_ref(), PseudoExpr::Int(n) if n == &1.into()))
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::When { clauses, .. }
                            if matches!(
                                clauses.as_slice(),
                                [WhenClause { body, .. }]
                                    if matches!(
                                        body,
                                        PseudoExpr::Force(inner)
                                            if matches!(
                                                inner.as_ref(),
                                                PseudoExpr::Var { name, .. } if name == "x"
                                            )
                                    )
                            )
                    )
        ),
        "force/delay cancellation must not strip force(x) bound by a when pattern, got: {out:?}"
    );
}

#[test]
fn test_cancel_force_delay_vars_avoids_alias_capture_under_shadowed_alias_name() {
    let outer_y_id = VarId::new(778);
    let x_id = VarId::new(779);
    let inner_y_id = VarId::new(780);
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(outer_y_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(x_id),
            value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Var {
                name: "y".to_string(),
                id: Some(outer_y_id),
            }))),
            body: PBox::new(PseudoExpr::Let {
                name: "y".to_string(),
                id: Some(inner_y_id),
                value: PBox::new(PseudoExpr::int(0)),
                body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Var {
                    name: "x".to_string(),
                    id: Some(x_id),
                }))),
            }),
        }),
    };

    let out = cancel_force_delay_vars(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::Let { name, id, body, .. }
                        if name == "x"
                            && *id == Some(x_id)
                            && matches!(
                                body.as_ref(),
                                PseudoExpr::Let { body, .. }
                                    if matches!(
                                        body.as_ref(),
                                        PseudoExpr::Var { name, id } if name == "x" && *id == Some(x_id)
                                    )
                            )
                )
        ),
        "cancel_force_delay_vars must keep the x binder when substituting x := y would capture under a shadowed y binder, got: {out:?}"
    );
}
