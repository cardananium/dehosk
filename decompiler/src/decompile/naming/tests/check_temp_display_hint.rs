use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn collect_check_temp_display_name_hints_names_unused_void_temp_binding() {
    let check_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(check_id),

        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("redeemer")),
            subject_name: Some("redeemer".into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::Unit,
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
        body: PBox::new(PseudoExpr::Bool(true)),
    };

    let hints = collect_check_temp_display_name_hints(&expr);
    assert_eq!(
        hints.get(&check_id).map(String::as_str),
        Some("check_redeemer")
    );
}

#[test]
fn semantic_and_render_naming_leave_check_temp_to_nameless_owner() {
    fn assert_check_temp_split(name: &str) {
        let expr = PseudoExpr::Let {
            name: name.to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("redeemer")),
                subject_name: Some("redeemer".into()),
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                        PseudoExpr::Unit,
                    ),
                    WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
                ],
            }),
            body: PBox::new(PseudoExpr::Bool(true)),
        };

        let semantic = semantic_improve_variable_names(expr.clone());
        let render = render_improve_variable_names(expr);
        let PseudoExpr::Let {
            name: semantic_name,
            ..
        } = semantic
        else {
            panic!("expected semantic let");
        };
        assert_eq!(semantic_name, name);
        let PseudoExpr::Let {
            name: render_name, ..
        } = render
        else {
            panic!("expected render let");
        };
        assert_eq!(render_name, name);
    }

    assert_check_temp_split("k");
    assert_check_temp_split("check_2");
}

#[test]
fn semantic_and_render_naming_leave_arithmetic_temp_to_nameless_owner() {
    fn assert_arithmetic_split(value: PseudoExpr, original_name: &str, display_name: &str) {
        let temp_id = VarId::fresh_binding();
        let expr = PseudoExpr::Let {
            name: original_name.to_string(),
            id: Some(temp_id),
            value: PBox::new(value),
            body: PBox::new(PseudoExpr::var_with_id(original_name, temp_id)),
        };

        let semantic = semantic_improve_variable_names(expr.clone());
        let render = render_improve_variable_names(expr.clone());
        assert_let_name_and_body_ref(semantic, original_name, temp_id);
        assert_let_name_and_body_ref(render, original_name, temp_id);

        let hints = collect_arithmetic_temp_display_name_hints(&expr);
        assert_eq!(hints.get(&temp_id).map(String::as_str), Some(display_name));
    }

    fn assert_let_name_and_body_ref(expr: PseudoExpr, expected_name: &str, expected_id: VarId) {
        let PseudoExpr::Let { name, body, .. } = expr else {
            panic!("expected let");
        };
        assert_eq!(name, expected_name);
        assert!(
            matches!(body.as_ref(), PseudoExpr::Var { name, id, .. } if name == expected_name && *id == Some(expected_id)),
            "expected body ref to follow {expected_name}, got: {body:?}"
        );
    }

    assert_arithmetic_split(
        PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var("int")),
            right: PBox::new(PseudoExpr::var("int_2")),
        },
        "t2",
        "sum",
    );
    assert_arithmetic_split(
        PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var("count_result")),
            right: PBox::new(PseudoExpr::int(1)),
        },
        "n2",
        "count",
    );
}

#[test]
fn semantic_and_render_naming_leave_option_wrapper_temp_to_nameless_owner() {
    fn assert_option_wrapper_split(value: PseudoExpr, original_name: &str, display_name: &str) {
        let temp_id = VarId::fresh_binding();
        let expr = PseudoExpr::Let {
            name: original_name.to_string(),
            id: Some(temp_id),
            value: PBox::new(value),
            body: PBox::new(PseudoExpr::var_with_id(original_name, temp_id)),
        };

        let semantic = semantic_improve_variable_names(expr.clone());
        let render = render_improve_variable_names(expr.clone());
        assert_let_name_and_body_ref(semantic, original_name, temp_id);
        assert_let_name_and_body_ref(render, original_name, temp_id);

        let hints = collect_option_wrapper_temp_display_name_hints(&expr);
        assert_eq!(hints.get(&temp_id).map(String::as_str), Some(display_name));
    }

    fn assert_let_name_and_body_ref(expr: PseudoExpr, expected_name: &str, expected_id: VarId) {
        let PseudoExpr::Let { name, body, .. } = expr else {
            panic!("expected let");
        };
        assert_eq!(name, expected_name);
        assert!(
            matches!(body.as_ref(), PseudoExpr::Var { name, id, .. } if name == expected_name && *id == Some(expected_id)),
            "expected body ref to follow {expected_name}, got: {body:?}"
        );
    }

    assert_option_wrapper_split(
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond")),
            then_branch: PBox::new(PseudoExpr::constr_known(KnownConstructor::None, vec![])),
            else_branch: PBox::new(PseudoExpr::constr_known(
                KnownConstructor::Some,
                vec![PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Int"),
                    args: vec![PseudoExpr::var("t2")].into(),
                }],
            )),
        },
        "u2",
        "int_option",
    );
    assert_option_wrapper_split(
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond")),
            then_branch: PBox::new(PseudoExpr::constr_known(KnownConstructor::None, vec![])),
            else_branch: PBox::new(PseudoExpr::constr_known(
                KnownConstructor::Some,
                vec![PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Map"),
                    args: vec![PseudoExpr::var("pairs")].into(),
                }],
            )),
        },
        "w2",
        "map_option",
    );
}

#[test]
fn collect_check_temp_display_name_hints_ignores_same_name_shadow_ref() {
    let outer_check_id = VarId::fresh_binding();
    let inner_check_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "check_2".to_string(),
        id: Some(outer_check_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("redeemer")),
            subject_name: Some("redeemer".into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::Unit,
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "check_2".to_string(),
            id: Some(inner_check_id),
            value: PBox::new(PseudoExpr::Bool(false)),
            body: PBox::new(PseudoExpr::var_with_id("check_2", inner_check_id)),
        }),
    };

    let hints = collect_check_temp_display_name_hints(&expr);
    assert_eq!(
        hints.get(&outer_check_id).map(String::as_str),
        Some("check_redeemer")
    );

    let improved = render_improve_variable_names(expr);
    let PseudoExpr::Let { name, .. } = improved else {
        panic!("expected let");
    };
    assert_eq!(name, "check_2");
}

#[test]
fn test_improve_variable_names_keeps_check_binding_when_actual_ref_remains() {
    let check_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "check_2".to_string(),
        id: Some(check_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("redeemer")),
            subject_name: Some("redeemer".into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::Unit,
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
        body: PBox::new(PseudoExpr::var_with_id("check_2", check_id)),
    };

    let hints = collect_check_temp_display_name_hints(&expr);
    assert!(
        !hints.contains_key(&check_id),
        "live check binding should stay out of display hint collector"
    );

    let improved = render_improve_variable_names(expr);
    let PseudoExpr::Let { name, .. } = improved else {
        panic!("expected let");
    };
    assert_eq!(name, "check_2");
}

#[test]
fn collect_check_temp_display_name_hints_names_variant_void_temp_binding() {
    let check_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "check_2".to_string(),
        id: Some(check_id),

        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("variant_3")),
            subject_name: Some("variant_3".into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::Unit,
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
        body: PBox::new(PseudoExpr::Bool(true)),
    };

    let hints = collect_check_temp_display_name_hints(&expr);
    assert_eq!(
        hints.get(&check_id).map(String::as_str),
        Some("check_variant")
    );
}

#[test]
fn collect_check_temp_display_name_hints_names_nested_variant_validation() {
    let check_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "check_5".to_string(),
        id: Some(check_id),

        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("r")),
            subject_name: Some("r".into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(
                        ConstructorShape::unknown_data(1, 1),
                        vec!["l3".into()],
                    ),
                    PseudoExpr::Let {
                        name: "check_6".to_string(),
                        id: Some(VarId::fresh_compat_placeholder()),

                        value: PBox::new(PseudoExpr::When {
                            subject: PBox::new(PseudoExpr::var("l3")),
                            subject_name: Some("l3".into()),
                            clauses: vec![
                                WhenClause::new(
                                    WhenPattern::constructor(
                                        ConstructorShape::unknown_data(0, 0),
                                        vec![],
                                    ),
                                    PseudoExpr::Unit,
                                ),
                                WhenClause::new(
                                    WhenPattern::Wildcard,
                                    PseudoExpr::Error { message: None },
                                ),
                            ],
                        }),
                        body: PBox::new(PseudoExpr::Unit),
                    },
                ),
                WhenClause::new(
                    WhenPattern::constructor(
                        ConstructorShape::unknown_data(0, 1),
                        vec!["e3".into()],
                    ),
                    PseudoExpr::Let {
                        name: "check_7".to_string(),
                        id: Some(VarId::fresh_compat_placeholder()),

                        value: PBox::new(PseudoExpr::When {
                            subject: PBox::new(PseudoExpr::var("e3")),
                            subject_name: Some("e3".into()),
                            clauses: vec![
                                WhenClause::new(
                                    WhenPattern::constructor(
                                        ConstructorShape::unknown_data(0, 0),
                                        vec![],
                                    ),
                                    PseudoExpr::Unit,
                                ),
                                WhenClause::new(
                                    WhenPattern::Wildcard,
                                    PseudoExpr::Error { message: None },
                                ),
                            ],
                        }),
                        body: PBox::new(PseudoExpr::Unit),
                    },
                ),
            ],
        }),
        body: PBox::new(PseudoExpr::Bool(true)),
    };

    let hints = collect_check_temp_display_name_hints(&expr);
    assert_eq!(
        hints.get(&check_id).map(String::as_str),
        Some("check_variant")
    );
}

#[test]
fn collect_check_temp_display_name_hints_uses_consistent_subject_field_access() {
    let subject_id = VarId::fresh_binding();
    let check_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "value_2".to_string(),
        id: Some(subject_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Let {
            name: "check_2".to_string(),
            id: Some(check_id),
            value: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var_with_id("value_2", subject_id)),
                subject_name: Some(Binder::new("value_2", subject_id)),
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                        PseudoExpr::field_access(
                            PseudoExpr::var_with_id("value_2", subject_id),
                            "fields".to_string(),
                        ),
                    ),
                    WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
                ],
            }),
            body: PBox::new(PseudoExpr::Bool(true)),
        }),
    };

    let hints = collect_check_temp_display_name_hints(&expr);
    assert_eq!(
        hints.get(&check_id).map(String::as_str),
        Some("check_variant")
    );

    let improved = render_improve_variable_names(expr);
    let PseudoExpr::Let { body, .. } = improved else {
        panic!("expected outer let");
    };
    let PseudoExpr::Let { name, .. } = body.as_ref() else {
        panic!("expected inner let");
    };
    assert_eq!(name, "check_2");
}

#[test]
fn collect_check_temp_display_name_hints_uses_subject_name_for_inconsistent_subject_field_access() {
    let subject_id = VarId::fresh_binding();
    let stale_subject_id = VarId::fresh_binding();
    let check_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "check_2".to_string(),
        id: Some(check_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("value_2", subject_id)),
            subject_name: Some(Binder::new("value_2", subject_id)),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::field_access(
                        PseudoExpr::var_with_id("value_2", stale_subject_id),
                        "fields".to_string(),
                    ),
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
        body: PBox::new(PseudoExpr::Bool(true)),
    };

    let hints = collect_check_temp_display_name_hints(&expr);
    assert_eq!(
        hints.get(&check_id).map(String::as_str),
        Some("check_value")
    );

    let improved = render_improve_variable_names(expr);
    let PseudoExpr::Let { name, .. } = improved else {
        panic!("expected let");
    };
    assert_eq!(name, "check_2");
}
