use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn collect_when_pattern_binder_display_name_hints_names_some_payload_from_get_at_subject() {
    let payload = Binder::synthetic("y2_2");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("get_at")),
            args: vec![PseudoExpr::var("items"), PseudoExpr::int(0)].into(),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(
                    KnownConstructor::Some,
                    vec![payload.clone()],
                ),
                guard: None,
                body: PseudoExpr::var_with_id("y2_2", payload.id),
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
        ],
    };

    let hints = collect_when_pattern_binder_display_name_hints(&expr);
    assert_eq!(hints.get(&payload.id).map(String::as_str), Some("item"));
}

#[test]
fn semantic_and_render_naming_leave_constructor_pattern_hint_to_nameless_owner() {
    let payload = Binder::synthetic("y2_2");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("get_at")),
            args: vec![PseudoExpr::var("items"), PseudoExpr::int(0)].into(),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(
                    KnownConstructor::Some,
                    vec![payload.clone()],
                ),
                guard: None,
                body: PseudoExpr::var_with_id("y2_2", payload.id),
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
        ],
    };

    let semantic = semantic_improve_variable_names(expr.clone());
    let render = render_improve_variable_names(expr.clone());
    let PseudoExpr::When {
        clauses: semantic_clauses,
        ..
    } = semantic
    else {
        panic!("expected semantic when");
    };
    let WhenPattern::Constructor { fields, .. } = &semantic_clauses[0].pattern else {
        panic!("expected semantic Some pattern");
    };
    assert_eq!(fields[0].name, "y2_2");
    let PseudoExpr::Var { name, .. } = &semantic_clauses[0].body else {
        panic!("expected semantic payload var body");
    };
    assert_eq!(name, "y2_2");

    let PseudoExpr::When { clauses, .. } = render else {
        panic!("expected render when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected render Some pattern");
    };
    assert_eq!(fields[0].name, "y2_2");
    let PseudoExpr::Var { name, .. } = &clauses[0].body else {
        panic!("expected render payload var body");
    };
    assert_eq!(name, "y2_2");

    let hints = collect_when_pattern_binder_display_name_hints(&expr);
    assert_eq!(hints.get(&payload.id).map(String::as_str), Some("item"));
}

#[test]
fn test_improve_variable_names_leaves_lookup_result_some_pattern_binder_to_nameless_owner() {
    let value_binder = Binder::synthetic("fields_0");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("lookup_result")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(
                    KnownConstructor::Some,
                    vec![value_binder.clone()],
                ),
                guard: Some(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::var_with_id("fields_0", value_binder.id)),
                    right: PBox::new(PseudoExpr::int(0)),
                }),
                body: PseudoExpr::var_with_id("fields_0", value_binder.id),
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
        ],
    };

    let improved = render_improve_variable_names(expr.clone());

    let PseudoExpr::When { clauses, .. } = improved else {
        panic!("expected when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected Some pattern");
    };
    assert_eq!(fields[0].name, "fields_0");
    let Some(PseudoExpr::BinOp { left, .. }) = &clauses[0].guard else {
        panic!("expected guard to survive");
    };
    assert!(
        matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == "fields_0"),
        "expected render naming to leave pattern binder guard to nameless owner, got: {:?}",
        clauses[0].guard
    );
    let PseudoExpr::Var { name, .. } = &clauses[0].body else {
        panic!("expected body var");
    };
    assert_eq!(name, "fields_0");

    let hints = collect_when_pattern_binder_display_name_hints(&expr);
    assert_eq!(
        hints.get(&value_binder.id).map(String::as_str),
        Some("value")
    );
}

#[test]
fn test_improve_variable_names_leaves_generated_constructor_fields_to_nameless_owner() {
    let variant = Binder::synthetic("item_0");
    let map = Binder::synthetic("fields_1");
    let value = Binder::synthetic("y2_0");
    let payload = Binder::synthetic("l3_0");

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("item")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::constructor(
                ConstructorShape::unknown_data(2, 3),
                vec![variant.clone(), map.clone(), value.clone()],
            ),
            guard: None,
            body: PseudoExpr::Let {
                name: "pairs".to_string(),
                id: Some(VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_map"),
                    args: vec![PseudoExpr::var_with_id("fields_1", map.id)].into(),
                }),
                body: PBox::new(PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::BinOp {
                        op: BinaryOp::Eq,
                        left: PBox::new(PseudoExpr::var_with_id("y2_0", value.id)),
                        right: PBox::new(PseudoExpr::constr(
                            ConstructorShape::unknown_data(0, 0),
                            vec![],
                        )),
                    }),
                    then_branch: PBox::new(PseudoExpr::When {
                        subject: PBox::new(PseudoExpr::var_with_id("item_0", variant.id)),
                        subject_name: None,
                        clauses: vec![
                            WhenClause {
                                pattern: WhenPattern::constructor(
                                    ConstructorShape::unknown_data(1, 1),
                                    vec![payload.clone()],
                                ),
                                guard: None,
                                body: PseudoExpr::var_with_id("l3_0", payload.id),
                            },
                            WhenClause {
                                pattern: WhenPattern::Wildcard,
                                guard: None,
                                body: PseudoExpr::Bool(false),
                            },
                        ],
                    }),
                    else_branch: PBox::new(PseudoExpr::Bool(false)),
                }),
            },
        }],
    };

    let improved = render_improve_variable_names(expr.clone());

    let PseudoExpr::When { clauses, .. } = improved else {
        panic!("expected outer when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern");
    };
    assert_eq!(fields[0].name, "item_0");
    assert_eq!(fields[1].name, "fields_1");
    assert_eq!(fields[2].name, "y2_0");

    let hints = collect_when_pattern_binder_display_name_hints(&expr);
    assert_eq!(hints.get(&variant.id).map(String::as_str), Some("variant"));
    assert_eq!(hints.get(&map.id).map(String::as_str), Some("map"));
    assert_eq!(hints.get(&value.id).map(String::as_str), Some("value"));
}

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_generated_constructor_field_usage() {
    let variant = Binder::new("item_0", VarId::fresh_binding());
    let map = Binder::new("fields_1", VarId::fresh_binding());
    let value = Binder::new("y2_0", VarId::fresh_binding());
    let outer_variant_id = VarId::fresh_binding();
    let outer_map_id = VarId::fresh_binding();
    let outer_value_id = VarId::fresh_binding();

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("item")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::constructor(
                ConstructorShape::unknown_data(2, 3),
                vec![variant.clone(), map.clone(), value.clone()],
            ),
            guard: None,
            body: PseudoExpr::Let {
                name: "pairs".to_string(),
                id: Some(VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_map"),
                    args: vec![PseudoExpr::var_with_id("fields_1", outer_map_id)].into(),
                }),
                body: PBox::new(PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::BinOp {
                        op: BinaryOp::Eq,
                        left: PBox::new(PseudoExpr::var_with_id("y2_0", outer_value_id)),
                        right: PBox::new(PseudoExpr::int(0)),
                    }),
                    then_branch: PBox::new(PseudoExpr::When {
                        subject: PBox::new(PseudoExpr::var_with_id("item_0", outer_variant_id)),
                        subject_name: None,
                        clauses: vec![WhenClause::new(
                            WhenPattern::Wildcard,
                            PseudoExpr::Bool(true),
                        )],
                    }),
                    else_branch: PBox::new(PseudoExpr::Bool(false)),
                }),
            },
        }],
    };

    let hints = collect_when_pattern_binder_display_name_hints(&expr);
    assert_eq!(hints.get(&variant.id), None);
    assert_eq!(hints.get(&map.id), None);
    assert_eq!(hints.get(&value.id), None);

    let improved = improve_variable_names(expr);

    let PseudoExpr::When { clauses, .. } = improved else {
        panic!("expected outer when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern");
    };
    assert_eq!(fields[0].name, "item_0");
    assert_eq!(fields[1].name, "fields_1");
    assert_eq!(fields[2].name, "y2_0");
}

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_constructor_payload_field_access() {
    let payload = Binder::new("l3_0", VarId::fresh_binding());
    let outer_payload_id = VarId::fresh_binding();

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("item")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::constructor(
                ConstructorShape::unknown_data(1, 1),
                vec![payload.clone()],
            ),
            guard: None,
            body: PseudoExpr::field_access(
                PseudoExpr::var_with_id("l3_0", outer_payload_id),
                "fields".to_string(),
            ),
        }],
    };

    let improved = improve_variable_names(expr);

    let PseudoExpr::When { clauses, .. } = improved else {
        panic!("expected when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern");
    };
    assert_eq!(fields[0].name, "l3_0");
}
