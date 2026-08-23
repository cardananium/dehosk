use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_temporary_value_binding_names_map_entry_alias() {
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.un_map"),
                args: vec![PseudoExpr::var("payload")].into(),
            }),
            index: 0,
        }),
        body: PBox::new(PseudoExpr::var_with_id("h", temp_id)),
    };

    let hints = collect_field_payload_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("entry"));
}

#[test]
fn test_analyze_temporary_value_binding_names_constructor_payload_alias() {
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "q3".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("variant_2")),
            subject_name: Some("variant_2".into()),
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    guard: None,
                    body: PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var("variant_2"),
                            "fields".to_string(),
                        )),
                        index: 0,
                    },
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::Error { message: None },
                },
            ],
        }),
        body: PBox::new(PseudoExpr::var_with_id("q3", temp_id)),
    };

    let hints = collect_field_payload_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("payload"));
}

#[test]
fn test_analyze_temporary_value_binding_ignores_same_name_different_id_constructor_payload_alias() {
    let subject_id = VarId::fresh_binding();
    let outer_variant_id = VarId::fresh_binding();
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "q3".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("variant_2", subject_id)),
            subject_name: Some(Binder::new("variant_2", subject_id)),
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    guard: None,
                    body: PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id("variant_2", outer_variant_id),
                            "fields".to_string(),
                        )),
                        index: 0,
                    },
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::Error { message: None },
                },
            ],
        }),
        body: PBox::new(PseudoExpr::var_with_id("q3", temp_id)),
    };

    let hints = collect_field_payload_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id), None);
}

#[test]
fn test_analyze_temporary_value_binding_names_constructor_payload_identity_alias() {
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "q3".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("variant")),
            subject_name: Some("variant".into()),
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    guard: None,
                    body: PseudoExpr::var("variant"),
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::Error { message: None },
                },
            ],
        }),
        body: PBox::new(PseudoExpr::var_with_id("q3", temp_id)),
    };

    let hints = collect_field_payload_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("payload"));
}

#[test]
fn test_analyze_temporary_value_binding_ignores_same_name_different_id_constructor_payload_identity_alias()
 {
    let subject_id = VarId::fresh_binding();
    let outer_variant_id = VarId::fresh_binding();
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "q3".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("variant", subject_id)),
            subject_name: Some(Binder::new("variant", subject_id)),
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    guard: None,
                    body: PseudoExpr::var_with_id("variant", outer_variant_id),
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::Error { message: None },
                },
            ],
        }),
        body: PBox::new(PseudoExpr::var_with_id("q3", temp_id)),
    };

    let hints = collect_field_payload_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id), None);
}

#[test]
fn test_analyze_temporary_value_binding_names_payload_item_alias() {
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "q".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("payload"),
                "fields".to_string(),
            )),
            index: 2,
        }),
        body: PBox::new(PseudoExpr::var_with_id("q", temp_id)),
    };

    let hints = collect_field_payload_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("item"));
}

#[test]
fn test_analyze_temporary_value_binding_with_consistency_ignores_inconsistent_payload_item_alias() {
    let payload_id = VarId::fresh_binding();
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "q".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var_with_id("payload", payload_id),
                "fields".to_string(),
            )),
            index: 2,
        }),
        body: PBox::new(PseudoExpr::var_with_id("q", temp_id)),
    };

    let hints = collect_field_payload_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id), None);
}
