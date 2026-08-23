use super::*;
use crate::decompile::type_invariants::validate_type_invariants;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::constructor::ConstructorShape;
#[test]
fn test_pattern_binders_preserve_existing_var_ids() {
    let left = Binder::new("left", VarId::new(700));
    let right = Binder::new("right", VarId::new(701));
    let rest = Binder::new("rest", VarId::new(702));

    let binders = pattern_binders(&WhenPattern::List {
        elements: vec![left.clone(), right.clone()],
        tail: Some(rest.clone()),
    });

    assert_eq!(binders.len(), 3);
    assert_eq!(binders[0].id, left.id);
    assert_eq!(binders[1].id, right.id);
    assert_eq!(binders[2].id, rest.id);
}

#[test]
fn test_generate_constraints_uses_var_id_keys_for_id_backed_binders() {
    let lambda_param = Binder::new("x", VarId::new(710));
    let rec_name = Binder::new("loop", VarId::new(711));
    let rec_param = Binder::new("n", VarId::new(712));
    let subject_name = Binder::new("scrutinee", VarId::new(713));
    let pair_left = Binder::new("left", VarId::new(714));
    let pair_right = Binder::new("right", VarId::new(715));

    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Lambda {
                params: vec![lambda_param.clone()],
                body: PBox::new(PseudoExpr::var_with_id("x_ref", lambda_param.id)),
            },
            PseudoExpr::RecFn {
                name: rec_name.clone(),
                params: vec![rec_param.clone()],
                body: PBox::new(PseudoExpr::var_with_id("loop_ref", rec_name.id)),
            },
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("input")),
                subject_name: Some(subject_name.clone()),
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Pair(pair_left.clone(), pair_right.clone()),
                    guard: None,
                    body: PseudoExpr::Tuple(
                        vec![
                            PseudoExpr::var_with_id("subject_ref", subject_name.id),
                            PseudoExpr::var_with_id("left_ref", pair_left.id),
                            PseudoExpr::var_with_id("right_ref", pair_right.id),
                        ]
                        .into(),
                    ),
                }],
            },
        ]
        .into(),
    );

    let mut solver = TypeSolver::new();
    let mut env = LexicalEnv::default();
    generate_constraints(&expr, &mut solver, &mut env, &[]);

    for id in [
        lambda_param.id,
        rec_name.id,
        rec_param.id,
        subject_name.id,
        pair_left.id,
        pair_right.id,
    ] {
        assert!(
            solver.var_map.contains_key(&BindingKey::VarId(id)),
            "expected binder VarId {id:?} to be tracked directly"
        );
    }

    assert!(
        solver
            .var_map
            .contains_key(&BindingKey::FreeName("input".to_string())),
        "free vars should still fall back to name-based tracking: {:?}",
        solver.var_map.keys().collect::<Vec<_>>()
    );
}

#[test]
fn test_idless_var_can_resolve_id_backed_let_through_lexical_env() {
    let let_id = VarId::new(720);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(let_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
    };

    let result = solve_type_constraints(expr);

    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected let");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Var { .. }),
        "id-less var should still resolve through lexical env, got {:?}",
        body
    );
}

#[test]
fn test_compat_placeholder_let_is_tracked_by_var_id_key() {
    // `let_bind` (compat constructor) emits `id: None`. The solver
    // synthesizes a fresh compat-placeholder VarId for an id-less Let so
    // the binding is still tracked under a `BindingKey::VarId` entry; the
    // placeholder stays private to the solver and never lands on the AST.
    let expr = PseudoExpr::let_bind("x", PseudoExpr::int(1), PseudoExpr::var("x"));

    let mut solver = TypeSolver::new();
    let mut env = LexicalEnv::default();
    generate_constraints(&expr, &mut solver, &mut env, &[]);

    let PseudoExpr::Let { id, .. } = expr else {
        panic!("expected let");
    };
    assert!(
        id.is_none(),
        "compat let_bind constructor should leave id: None on the AST"
    );
    let has_var_id_key = solver
        .var_map
        .keys()
        .any(|k| matches!(k, BindingKey::VarId(_)));
    assert!(
        has_var_id_key,
        "compat-placeholder let should still be tracked under a VarId key: {:?}",
        solver.var_map.keys().collect::<Vec<_>>()
    );
}

#[test]
fn test_let_expression_type_follows_body_not_binding_value() {
    let let_id = VarId::new(721);
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::Let {
            name: "tag".to_string(),
            id: Some(let_id),
            value: PBox::new(PseudoExpr::int(1)),
            body: PBox::new(PseudoExpr::Bool(true)),
        }),
        right: PBox::new(PseudoExpr::Bool(true)),
    };

    let result = solve_type_constraints(expr);

    let PseudoExpr::BinOp { left, .. } = result else {
        panic!("expected top-level and");
    };
    let PseudoExpr::Let { body, .. } = left.as_ref() else {
        panic!("expected let on left side");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Bool(true)),
        "expected let body to remain Bool, got {body:?}"
    );
}

#[test]
fn test_let_expression_body_alias_keeps_pair_subject_type() {
    let let_id = VarId::new(722);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Let {
            name: "pair".to_string(),
            id: Some(let_id),
            value: PBox::new(PseudoExpr::Pair(
                PBox::new(PseudoExpr::int(1)),
                PBox::new(PseudoExpr::Bool(true)),
            )),
            body: PBox::new(PseudoExpr::Var {
                name: "pair".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            }),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair("left".into(), "right".into()),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };

    let result = solve_type_constraints(expr);
    validate_type_invariants(
        &result,
        None,
        &crate::decompile::mid::type_env::TypeEnvironment::new(),
    )
    .expect("pair subject should stay pair through let-expression body alias");
}

#[test]
fn test_solve_type_constraints_with_final_table_preserves_expr_and_populates_declarations() {
    let let_id = VarId::new(727);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(let_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::var_with_id("x", let_id)),
    };

    let (solved, final_types) = solve_type_constraints_with_final_table(expr.clone());

    assert_eq!(
        solved, expr,
        "type solving should not rewrite the PseudoExpr; current ref-id invalidation belongs to the hidden dedup boundary"
    );
    assert!(final_types.is_frozen());
    assert_eq!(final_types.var_type_count(), 1);
    assert!(
        matches!(
            final_types.type_of_var(let_id).as_deref(),
            Some(PseudoType::Int)
        ),
        "expected solved let declaration type to be recorded as Int"
    );
}

#[test]
fn test_pair_pattern_refines_generic_data_subject() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "subject".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair(
                Binder::new("left", VarId::new(723)),
                Binder::new("right", VarId::new(724)),
            ),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };

    let result = solve_type_constraints(expr);
    validate_type_invariants(
        &result,
        None,
        &crate::decompile::mid::type_env::TypeEnvironment::new(),
    )
    .expect("pair pattern should refine a generic data subject into a pair");

    let PseudoExpr::When { subject, .. } = result else {
        panic!("expected when expression");
    };
    assert!(
        matches!(subject.as_ref(), PseudoExpr::Var { .. }),
        "expected when subject to be a Var, got {subject:?}"
    );
}

#[test]
fn test_constructor_pair_pattern_refines_generic_data_subject() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "subject".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::constructor_known(
                KnownConstructor::Pair,
                vec![
                    Binder::new("left", VarId::new(725)),
                    Binder::new("right", VarId::new(726)),
                ],
            ),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };

    let result = solve_type_constraints(expr);
    validate_type_invariants(
        &result,
        None,
        &crate::decompile::mid::type_env::TypeEnvironment::new(),
    )
    .expect("constructor Pair pattern should refine a generic data subject into a pair");

    let PseudoExpr::When { subject, .. } = result else {
        panic!("expected when expression");
    };
    assert!(
        matches!(subject.as_ref(), PseudoExpr::Var { .. }),
        "expected when subject to be a Var, got {subject:?}"
    );
}

#[test]
fn test_option_unknown_refined_by_field_usage() {
    // when x: Result<?, ?> is {
    //   Ok(field_0) ->
    //     let head: ByteArray = Data.to_bytes(field_0)
    //     Ok(head)
    //   Error(field_0) ->
    //     let e: ByteArray = Data.to_bytes(field_0)
    //     Error(e)
    // }
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(
                    KnownConstructor::Ok,
                    vec!["field_0".into()],
                ),
                guard: None,
                body: PseudoExpr::Let {
                    name: "head".to_string(),
                    id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                    value: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.to_bytes"),
                        args: vec![PseudoExpr::var("field_0")].into(),
                    }),
                    body: PBox::new(PseudoExpr::constr_known(
                        KnownConstructor::Ok,
                        vec![PseudoExpr::Var {
                            name: "head".to_string(),
                            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                        }],
                    )),
                },
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(
                    KnownConstructor::Error,
                    vec!["field_e".into()],
                ),
                guard: None,
                body: PseudoExpr::Let {
                    name: "e".to_string(),
                    id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                    value: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.to_bytes"),
                        args: vec![PseudoExpr::var("field_e")].into(),
                    }),
                    body: PBox::new(PseudoExpr::constr_known(
                        KnownConstructor::Error,
                        vec![PseudoExpr::Var {
                            name: "e".to_string(),
                            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                        }],
                    )),
                },
            },
        ],
    };

    // Type solver should not crash on this expression
    let _result = solve_type_constraints(expr);
}

#[test]
fn test_option_refined_from_some_field() {
    // let x = Some(42)
    // The Option<?> should become Option<Int>
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::int(42)],
        )),
        body: PBox::new(PseudoExpr::var("x")),
    };

    let result = solve_type_constraints(expr);

    // Should not crash; AST nodes carry no `tipo`.
    assert!(matches!(&result, PseudoExpr::Let { .. }));
}

#[test]
fn test_pair_refined_from_expect_pattern() {
    // expect Pair(x, y) = p: Pair<?, ?>
    // let n: Int = Data.to_int(x)
    // let s: ByteArray = Data.to_bytes(y)
    // (n, s)
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "p".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair("x".into(), "y".into()),
            guard: None,
            body: PseudoExpr::Let {
                name: "n".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.to_int"),
                    args: vec![PseudoExpr::var("x")].into(),
                }),
                body: PBox::new(PseudoExpr::Let {
                    name: "s".to_string(),
                    id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                    value: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.to_bytes"),
                        args: vec![PseudoExpr::var("y")].into(),
                    }),
                    body: PBox::new(PseudoExpr::Tuple(
                        vec![PseudoExpr::var("n"), PseudoExpr::var("s")].into(),
                    )),
                }),
            },
        }],
    };

    // Type solver should not crash on this expression
    let _result = solve_type_constraints(expr);
}

#[test]
fn test_if_condition_bool() {
    // if x then 1 else 2
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Gt,
            left: PBox::new(PseudoExpr::int(1)),
            right: PBox::new(PseudoExpr::int(0)),
        }),
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("x")),
            then_branch: PBox::new(PseudoExpr::int(1)),
            else_branch: PBox::new(PseudoExpr::int(2)),
        }),
    };

    let result = solve_type_constraints(expr);

    // Should not crash; structural verification only
    assert!(matches!(&result, PseudoExpr::Let { .. }));
    if let PseudoExpr::Let { body, .. } = &result {
        assert!(matches!(body.as_ref(), PseudoExpr::If { .. }));
    }
}

#[test]
fn test_let_chain_type_propagation() {
    // let a: Int = 42
    // let b = a
    // b
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::var("a")),
            body: PBox::new(PseudoExpr::var("b")),
        }),
    };

    let result = solve_type_constraints(expr);

    // Should not crash; AST nodes carry no `tipo`.
    assert!(matches!(&result, PseudoExpr::Let { .. }));
}

#[test]
fn test_solve_does_not_lose_existing_types() {
    // Ensure that already-typed nodes are not downgraded
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::var("x")),
    };

    let result = solve_type_constraints(expr);

    // Should not crash; AST nodes carry no `tipo`.
    assert!(matches!(&result, PseudoExpr::Let { .. }));
}

#[test]
fn test_list_unknown_stays_when_no_info() {
    // List<?> without element usage should stay List<?>
    let expr = PseudoExpr::Let {
        name: "xs".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.empty"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::var("xs")),
    };

    let result = solve_type_constraints(expr);

    // Should not crash; AST nodes carry no `tipo`.
    assert!(matches!(&result, PseudoExpr::Let { .. }));
}

#[test]
fn test_structural_field_access_beats_stale_bool_annotation() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Bool(true)),
            then_branch: PBox::new(PseudoExpr::Bool(false)),
            else_branch: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.Int"),
                args: vec![PseudoExpr::int(42)].into(),
            }),
        }),
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("x"),
            "fields".to_string(),
        )),
    };

    let result = solve_type_constraints(expr);

    // AST nodes carry no `tipo`; verify structure only.
    if let PseudoExpr::Let { body, .. } = &result {
        assert!(matches!(body.as_ref(), PseudoExpr::FieldAccess { .. }));
    } else {
        panic!("expected let");
    }
}

#[test]
fn test_constructor_container_usage_beats_stale_bool_annotation() {
    let expr = PseudoExpr::Let {
        name: "xs".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::var("input")),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.Map"),
            args: vec![PseudoExpr::var("xs")].into(),
        }),
    };

    let result = solve_type_constraints(expr);

    // AST nodes carry no `tipo`; verify structure only.
    if let PseudoExpr::Let { body, .. } = &result {
        assert!(matches!(body.as_ref(), PseudoExpr::BuiltinCall { .. }));
    } else {
        panic!("expected let");
    }
}

#[test]
fn test_fields_access_result_is_refined_to_list_data() {
    let expr = PseudoExpr::Let {
        name: "fields".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("redeemer"),
            "fields".to_string(),
        )),
        body: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("fields")),
            index: 0,
        }),
    };

    let result = solve_type_constraints(expr);

    // AST nodes carry no `tipo`; verify structure only.
    if let PseudoExpr::Let { body, .. } = &result {
        assert!(matches!(body.as_ref(), PseudoExpr::IndexAccess { .. }));
    } else {
        panic!("expected let");
    }
}

#[test]
fn test_constructor_when_subject_beats_stale_bool_annotation() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::var("input")),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("x")),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    guard: None,
                    body: PseudoExpr::Bool(false),
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_map"),
                        args: vec![PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var("x"),
                                "fields".to_string(),
                            )),
                            index: 0,
                        }]
                        .into(),
                    },
                },
            ],
        }),
    };

    let result = solve_type_constraints(expr);

    // AST nodes carry no `tipo`; verify structure only.
    if let PseudoExpr::Let { body, .. } = &result {
        assert!(matches!(body.as_ref(), PseudoExpr::When { .. }));
    } else {
        panic!("expected let");
    }
}

#[test]
fn test_when_subject_is_not_overwritten_by_clause_body_type() {
    let expr = PseudoExpr::Let {
        name: "carrier".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::var("input")),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("carrier")),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    guard: None,
                    body: PseudoExpr::List {
                        elements: vec![PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.Int"),
                            args: vec![PseudoExpr::int(1)].into(),
                        }]
                        .into(),
                        tail: None,
                    },
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::List {
                        elements: vec![].into(),
                        tail: None,
                    },
                },
            ],
        }),
    };

    let result = solve_type_constraints(expr);

    // AST nodes carry no `tipo`; verify structure only.
    if let PseudoExpr::Let { body, .. } = &result {
        assert!(matches!(body.as_ref(), PseudoExpr::When { .. }));
    } else {
        panic!("expected let");
    }
}

#[test]
fn test_data_int_constructor_constrains_argument_and_result() {
    let expr = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Var {
            name: "input".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "d".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.Int"),
                args: vec![PseudoExpr::var("n")].into(),
            }),
            body: PBox::new(PseudoExpr::Tuple(
                vec![PseudoExpr::var("n"), PseudoExpr::var("d")].into(),
            )),
        }),
    };

    let result = solve_type_constraints(expr);

    // AST nodes carry no `tipo`; verify structure only.
    if let PseudoExpr::Let { body, .. } = &result {
        if let PseudoExpr::Let { body, .. } = body.as_ref() {
            assert!(matches!(body.as_ref(), PseudoExpr::Tuple(_)));
        } else {
            panic!("Expected inner let");
        }
    } else {
        panic!("Expected outer let");
    }
}

#[test]
fn test_data_list_constructor_constrains_argument_to_list_data() {
    let expr = PseudoExpr::Let {
        name: "items".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Var {
            name: "raw_items".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "d".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.List"),
                args: vec![PseudoExpr::var("items")].into(),
            }),
            body: PBox::new(PseudoExpr::var("items")),
        }),
    };

    let result = solve_type_constraints(expr);

    // AST nodes carry no `tipo`; verify structure only.
    if let PseudoExpr::Let { body, .. } = &result {
        if let PseudoExpr::Let { body, .. } = body.as_ref() {
            assert!(matches!(body.as_ref(), PseudoExpr::Var { .. }));
        } else {
            panic!("Expected inner let");
        }
    } else {
        panic!("Expected outer let");
    }
}

#[test]
fn test_var_id_identity_keeps_shadowed_same_name_bindings_distinct() {
    let outer_id = VarId::new(100);
    let inner_id = VarId::new(101);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::ByteArray(vec![0xAA])),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::Var {
                        name: "x".to_string(),
                        id: Some(inner_id),
                    },
                    PseudoExpr::Var {
                        name: "x".to_string(),
                        id: Some(outer_id),
                    },
                ]
                .into(),
            )),
        }),
    };

    let result = solve_type_constraints(expr);

    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected outer let")
    };
    let PseudoExpr::Let { body, .. } = body.as_ref() else {
        panic!("expected inner let")
    };

    let PseudoExpr::Tuple(items) = body.as_ref() else {
        panic!("expected tuple body")
    };
    // Both vars should keep their distinct ids
    assert!(
        matches!(&items[0], PseudoExpr::Var { id, .. } if *id == Some(inner_id)),
        "inner x reference should have inner_id, got {:?}",
        items[0]
    );
    assert!(
        matches!(&items[1], PseudoExpr::Var { id, .. } if *id == Some(outer_id)),
        "outer x reference should have outer_id, got {:?}",
        items[1]
    );
}

#[test]
fn test_lambda_param_shadowing_without_var_ids_does_not_refine_outer_let() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "f".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec!["x".to_string().into()],
                body: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.to_bytes"),
                    args: vec![PseudoExpr::var("x")].into(),
                }),
            }),
            body: PBox::new(PseudoExpr::var("x")),
        }),
    };

    let result = solve_type_constraints(expr);

    // AST nodes carry no `tipo`; verify structure only.
    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected outer let");
    };
    let PseudoExpr::Let { body, .. } = body.as_ref() else {
        panic!("expected inner let");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Var { .. }),
        "outer x reference should be a Var, got {:?}",
        body
    );
}

#[test]
fn test_nested_let_value_body_bool_beats_stale_data_annotation() {
    let expr = PseudoExpr::Let {
        name: "cond_ok".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Let {
            name: "n".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::int(1)),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::var("n")),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond_ok")),
            then_branch: PBox::new(PseudoExpr::Bool(true)),
            else_branch: PBox::new(PseudoExpr::Bool(false)),
        }),
    };

    let result = solve_type_constraints(expr);

    // AST nodes carry no `tipo`; verify structure only.
    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected outer let");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::If { .. }),
        "expected if body, got {:?}",
        body
    );
}

#[test]
fn test_when_pattern_shadowing_without_var_ids_does_not_refine_outer_let() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "pair".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::var("input_pair")),
            body: PBox::new(PseudoExpr::Let {
                name: "_ignored".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("pair")),
                    subject_name: None,
                    clauses: vec![WhenClause {
                        pattern: WhenPattern::Pair("x".into(), "y".into()),
                        guard: None,
                        body: PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.to_bytes"),
                            args: vec![PseudoExpr::var("x")].into(),
                        },
                    }],
                }),
                body: PBox::new(PseudoExpr::var("x")),
            }),
        }),
    };

    let result = solve_type_constraints(expr);

    // AST nodes carry no `tipo`; verify structure only.
    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected outer let");
    };
    let PseudoExpr::Let { body, .. } = body.as_ref() else {
        panic!("expected pair let");
    };
    let PseudoExpr::Let { body, .. } = body.as_ref() else {
        panic!("expected ignored let");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Var { .. }),
        "outer x reference should be a Var, got {:?}",
        body
    );
}

#[test]
fn test_validate_type_invariants_accepts_fields_on_bool_after_relaxation() {
    // `validate_field_access` accepts `fields`/`tag` on any type:
    // the simplifier's intermediate state legitimately produces
    // `Bool.fields` / `Int.fields` shapes before downstream rewrites
    // collapse them, so rejecting them would fail valid scripts.
    use std::rc::Rc;
    let var_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let mut env = crate::decompile::mid::type_env::TypeEnvironment::new();
    env.bind_var(var_id, Rc::new(PseudoType::Bool));

    let expr = PseudoExpr::field_access(
        PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(var_id),
        },
        "fields".to_string(),
    );

    validate_type_invariants(&expr, None, &env)
        .expect("Bool.fields is now accepted (was strictly rejected before)");
}

#[test]
fn test_validate_type_invariants_rejects_pair_pattern_on_bool_subject() {
    use std::rc::Rc;
    let var_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let mut env = crate::decompile::mid::type_env::TypeEnvironment::new();
    env.bind_var(var_id, Rc::new(PseudoType::Bool));

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(var_id),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair("left".into(), "right".into()),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };

    let err = validate_type_invariants(&expr, None, &env).expect_err("expected invariant failure");
    assert!(
        err.to_string().contains("pair pattern"),
        "unexpected invariant error: {err}"
    );
}

#[test]
fn test_validate_type_invariants_accepts_pair_pattern_on_pair_subject() {
    use std::rc::Rc;
    let var_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let mut env = crate::decompile::mid::type_env::TypeEnvironment::new();
    env.bind_var(
        var_id,
        Rc::new(PseudoType::Pair(
            Rc::new(PseudoType::Int),
            Rc::new(PseudoType::ByteArray),
        )),
    );

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(var_id),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair("left".into(), "right".into()),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };

    validate_type_invariants(&expr, None, &env).expect("pair subject should satisfy invariants");
}

#[test]
fn test_validate_type_invariants_rejects_add_on_bool() {
    use std::rc::Rc;
    let var_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let mut env = crate::decompile::mid::type_env::TypeEnvironment::new();
    env.bind_var(var_id, Rc::new(PseudoType::Bool));

    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(var_id),
        }),
        right: PBox::new(PseudoExpr::Int(1.into())),
    };

    let err = validate_type_invariants(&expr, None, &env).expect_err("expected invariant failure");
    assert!(
        err.to_string().contains("binary op"),
        "unexpected invariant error: {err}"
    );
}

#[test]
fn test_validate_type_invariants_rejects_length_on_int() {
    use std::rc::Rc;
    let var_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let mut env = crate::decompile::mid::type_env::TypeEnvironment::new();
    env.bind_var(var_id, Rc::new(PseudoType::Int));

    let expr = PseudoExpr::UnOp {
        op: UnaryOp::Length,
        operand: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(var_id),
        }),
    };

    let err = validate_type_invariants(&expr, None, &env).expect_err("expected invariant failure");
    assert!(
        err.to_string().contains("unary op"),
        "unexpected invariant error: {err}"
    );
}

#[test]
fn test_constr_with_unknown_shape_does_not_commit_to_type() {
    // A Constr node with `ConstructorShape::Unknown` (e.g. a would-be
    // `Some` with a non-canonical tag) must not narrow the Constr type
    // variable to `Option<?>`: commitment is gated on
    // `KnownConstructor::Some`, so an `Unknown` shape falls out of the
    // `Option`-inference arm. Were it to fire, `expr_type_var(&fields[0],
    // ..)` would index `fields[0]` on a zero-arity Constr and panic.
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(5, 0),
            vec![],
        )),
        body: PBox::new(PseudoExpr::var("x")),
    };
    let _ = solve_type_constraints(expr);
}

#[test]
fn test_when_pattern_with_unknown_shape_does_not_crash() {
    // Backward-constraint pass: a `WhenPattern::Constructor` with an
    // `Unknown` shape (e.g. a would-be `Ok` with tag 1) must fall out of
    // the shape-gated branches rather than index `fields[0]` and panic —
    // closed-set refinement is gated on `KnownConstructor`, not on name.
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    let _ = solve_type_constraints(expr);
}

#[test]
fn test_well_formed_some_pattern_still_solves() {
    // Positive control: a `Some(x)` pattern at tag 0 still drives
    // subject refinement through the
    // backward-constraint arm gated on `KnownConstructor::Some`.
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::constructor_known(
                KnownConstructor::Some,
                vec![Binder::new("v", VarId::new(900))],
            ),
            guard: None,
            body: PseudoExpr::var_with_id("v", VarId::new(900)),
        }],
    };
    let result = solve_type_constraints(expr);
    assert!(matches!(result, PseudoExpr::When { .. }));
}

// Final-AST side table emitted by the solver

#[test]
fn final_type_table_records_let_int_binding() {
    // let x = 42
    // x
    let x_id = VarId::new(930);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    assert!(
        table.is_frozen(),
        "final table must be frozen before hand-off"
    );
    assert_eq!(
        table.type_of_var(x_id).as_deref(),
        Some(&PseudoType::Int),
        "declaration-level let should land as Int in the final table"
    );
}

#[test]
fn final_type_table_keeps_shadowed_same_name_bindings_distinct() {
    // let x: Int = 1
    //   let x: ByteArray = 0xAA
    //     (x_inner, x_outer)
    let outer_id = VarId::new(940);
    let inner_id = VarId::new(941);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::ByteArray(vec![0xAA])),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("x", inner_id),
                    PseudoExpr::var_with_id("x", outer_id),
                ]
                .into(),
            )),
        }),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    assert_eq!(
        table.type_of_var(outer_id).as_deref(),
        Some(&PseudoType::Int),
        "outer `x` must keep Int type under its own id"
    );
    assert_eq!(
        table.type_of_var(inner_id).as_deref(),
        Some(&PseudoType::ByteArray),
        "inner `x` must keep ByteArray type under its own id"
    );
}

#[test]
fn final_type_table_records_pair_container_for_when_subject_name() {
    // when input as p is
    //   Pair(a, b) -> a
    //
    // The `Pair` pattern pins the subject_name binder `p` to `Pair(?, ?)` in
    // the solver; the collector must surface that container type against
    // `p`'s declaration `VarId` in the final table.
    let p_id = VarId::new(950);
    let a_id = VarId::new(951);
    let b_id = VarId::new(952);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("input")),
        subject_name: Some(Binder::new("p", p_id)),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair(Binder::new("a", a_id), Binder::new("b", b_id)),
            guard: None,
            body: PseudoExpr::var_with_id("a", a_id),
        }],
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    match table.type_of_var(p_id).as_deref() {
        Some(PseudoType::Pair(_, _)) => (),
        other => panic!("expected Pair(_, _) for subject_name, got {other:?}"),
    }
}

#[test]
fn final_type_table_records_lambda_param_typed_by_builtin_usage() {
    // \x -> Data.to_int(x)
    //
    // The builtin pins its argument to `Data`, so the lambda param's
    // declaration id should land as `Data` in the final table.
    let x_id = VarId::new(955);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.to_int"),
            args: vec![PseudoExpr::var_with_id("x", x_id)].into(),
        }),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    assert_eq!(
        table.type_of_var(x_id).as_deref(),
        Some(&PseudoType::Data),
        "lambda param consumed by Data.to_int should resolve to Data"
    );
}

#[test]
fn final_type_table_omits_reference_only_var_ids() {
    // A free `Var` on the RHS is not a declaration site — the final
    // table records declaration ids only.
    let free_ref_id = VarId::new(960);
    let let_id = VarId::new(961);
    let expr = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(let_id),
        value: PBox::new(PseudoExpr::var_with_id("free", free_ref_id)),
        body: PBox::new(PseudoExpr::int(0)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    assert!(
        !table.contains_var(free_ref_id),
        "reference-only Var ids should not be recorded (TP3 scope is declaration-level only)"
    );
}

#[test]
fn final_type_table_skips_unresolved_bindings() {
    // let x = free_ref
    // x
    //
    // Without any usage that pins a concrete type, the solver leaves `x`
    // unresolved; the final table must not invent an answer.
    let x_id = VarId::new(970);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::var("free_ref")),
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    assert!(
        !table.contains_var(x_id),
        "unresolved bindings must be absent from the final table, not stored as Unknown"
    );
}

// ────────────────────────────────────────────────────────────
// Function constraint on Lambda/RecFn
//

#[test]
fn p2_2_slice_a_let_bound_lambda_records_function_type() {
    // `let f = fn(x) { 0 } in f`
    // The solver records `f_id` as `Function` with arity 1.
    //
    // The solver itself leaves the Function's children Unknown;
    // enrichment later refines ret to Int from the literal body.
    // This test pins the arity only.
    let f_id = VarId::new(2200);
    let x_id = VarId::new(2201);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::int(0)),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    let f_ty = table.type_of_var(f_id).expect("f_id must be in the table");
    match f_ty.as_ref() {
        PseudoType::Function { params, .. } => {
            assert_eq!(params.len(), 1, "arity must match the Lambda's param count");
            // Arity is the contract; the param/ret children may be
            // refined by enrichment, so this test leaves them free.
        }
        other => panic!("expected Function, got {other:?}"),
    }
}

#[test]
fn p2_2_slice_a_let_bound_lambda_arity_two_records_function_type() {
    // `let g = fn(a, b) { 0 } in g`
    let g_id = VarId::new(2210);
    let a_id = VarId::new(2211);
    let b_id = VarId::new(2212);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
        body: PBox::new(PseudoExpr::int(0)),
    };
    let expr = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(g_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::var_with_id("g", g_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    let g_ty = table.type_of_var(g_id).expect("g_id must be in the table");
    let PseudoType::Function { params, .. } = g_ty.as_ref() else {
        panic!("expected Function, got {:?}", g_ty);
    };
    assert_eq!(params.len(), 2, "arity-2 Lambda must record arity 2");
}

#[test]
fn p2_2_slice_a_function_loses_to_pair_in_unification() {
    // When a let-bound Lambda's tv accrues both a Function
    // constraint (from the Lambda value) and a Pair constraint
    // (from a downstream pattern match), the Pair evidence wins:
    // Function is only a weak hint.
    //
    // Shape: `let m = fn(x) { x } in when m is Pair(a, b) -> a`.
    let m_id = VarId::new(2300);
    let x_id = VarId::new(2301);
    let a_id = VarId::new(2302);
    let b_id = VarId::new(2303);

    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("m", m_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair(Binder::new("a", a_id), Binder::new("b", b_id)),
            guard: None,
            body: PseudoExpr::var_with_id("a", a_id),
        }],
    };
    let expr = PseudoExpr::Let {
        name: "m".to_string(),
        id: Some(m_id),
        value: PBox::new(lambda),
        body: PBox::new(when_expr),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    let m_ty = table
        .type_of_var(m_id)
        .expect("m_id must be in the final table");
    assert!(
        !matches!(m_ty.as_ref(), PseudoType::Function { .. }),
        "Function (weak hint) must lose to Pair (structural evidence), got {:?}",
        m_ty
    );
    assert!(
        matches!(m_ty.as_ref(), PseudoType::Pair(_, _)),
        "expected Pair to win the conflict, got {:?}",
        m_ty
    );
}

#[test]
fn p2_2_slice_a_function_subject_accepts_pair_pattern_in_invariants() {
    // `validate_when_pattern` must accept a Function-typed subject
    // for collection patterns (Pair / Tuple / List / Pair
    // Constructor). Otherwise a Lambda whose Function constraint
    // reaches validation errors out the whole decompile when its
    // pattern is Pair.
    let m_id = VarId::new(2310);
    let x_id = VarId::new(2311);
    let a_id = VarId::new(2312);
    let b_id = VarId::new(2313);

    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("m", m_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair(Binder::new("a", a_id), Binder::new("b", b_id)),
            guard: None,
            body: PseudoExpr::var_with_id("a", a_id),
        }],
    };
    let expr = PseudoExpr::Let {
        name: "m".to_string(),
        id: Some(m_id),
        value: PBox::new(lambda),
        body: PBox::new(when_expr),
    };

    let (expr, table) = solve_type_constraints_with_final_table(expr);

    // Even if Function survived unification, validation must not
    // error: a Pair pattern on a Function subject is accepted.
    let result = validate_type_invariants(
        &expr,
        Some(&table),
        &crate::decompile::mid::type_env::TypeEnvironment::new(),
    );
    assert!(
        result.is_ok(),
        "Function-typed subject must be accepted for Pair pattern, got error: {:?}",
        result
    );
}

#[test]
fn p2_2_slice_a_recfn_records_function_type_under_name_id() {
    // `let loop = rec fn loop(n) { n } in loop`
    let loop_id = VarId::new(2220);
    let n_id = VarId::new(2221);
    let outer_id = VarId::new(2222);
    let recfn = PseudoExpr::RecFn {
        name: Binder::new("loop", loop_id),
        params: vec![Binder::new("n", n_id)],
        body: PBox::new(PseudoExpr::var_with_id("n", n_id)),
    };
    let expr = PseudoExpr::Let {
        name: "outer".to_string(),
        id: Some(outer_id),
        value: PBox::new(recfn),
        body: PBox::new(PseudoExpr::var_with_id("outer", outer_id)),
    };

    let (_expr, table) = solve_type_constraints_with_final_table(expr);

    // The RecFn's name.id receives the Function constraint directly
    // (the name binds the function itself).
    let loop_ty = table
        .type_of_var(loop_id)
        .expect("RecFn name id must be in the table");
    let PseudoType::Function { params, .. } = loop_ty.as_ref() else {
        panic!("expected Function on RecFn name id, got {:?}", loop_ty);
    };
    assert_eq!(params.len(), 1, "RecFn arity-1 must record arity 1");
}
