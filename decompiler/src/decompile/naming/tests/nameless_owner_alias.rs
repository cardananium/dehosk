use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_leaves_single_letter_bytearray_extractor_alias_to_nameless_owner() {
    let id = Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder());
    let expr = PseudoExpr::Let {
        name: "g".to_string(),
        id,
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var("datum")].into(),
        }),
        body: PBox::new(PseudoExpr::Var {
            name: "g".to_string(),
            id,
        }),
    };

    let improved = render_improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "g");
            assert!(matches!(value.as_ref(), PseudoExpr::BuiltinCall { .. }));
            assert!(
                matches!(body.as_ref(), PseudoExpr::Var { name, id: body_id, .. } if name == "g" && *body_id == id),
                "expected render naming to leave extractor alias to nameless owner, got: {body:?}"
            );
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_leaves_numeric_suffix_extractor_alias_to_nameless_owner() {
    let id = Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder());
    let expr = PseudoExpr::Let {
        name: "z_2".to_string(),
        id,
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var("datum")].into(),
        }),
        body: PBox::new(PseudoExpr::Var {
            name: "z_2".to_string(),
            id,
        }),
    };

    let improved = render_improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "z_2");
            assert!(matches!(value.as_ref(), PseudoExpr::BuiltinCall { .. }));
            assert!(
                matches!(body.as_ref(), PseudoExpr::Var { name, id: body_id, .. } if name == "z_2" && *body_id == id),
                "expected render naming to leave numeric-suffix extractor alias to nameless owner, got: {body:?}"
            );
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}

#[test]
fn test_improve_variable_names_leaves_payload_item_field_alias_to_nameless_owner() {
    let payload_id = VarId::fresh_binding();
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "payload".to_string(),
        id: Some(payload_id),
        value: PBox::new(PseudoExpr::var("seed")),
        body: PBox::new(PseudoExpr::Let {
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
        }),
    };

    let semantic = semantic_improve_variable_names(expr.clone());
    let render = render_improve_variable_names(expr.clone());

    for improved in [semantic, render] {
        let PseudoExpr::Let { body, .. } = improved else {
            panic!("expected outer let");
        };
        let PseudoExpr::Let {
            name, value, body, ..
        } = body.as_ref()
        else {
            panic!("expected inner let");
        };
        assert_eq!(name, "q");
        assert!(matches!(value.as_ref(), PseudoExpr::IndexAccess { .. }));
        assert!(
            matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "q" && *id == Some(temp_id)),
            "expected payload item alias to stay with nameless owner, got: {body:?}"
        );
    }

    let hints = collect_field_payload_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("item"));
}

#[test]
fn test_field_payload_display_hint_ignores_inconsistent_payload_item_field_alias() {
    let outer_payload_id = VarId::fresh_binding();
    let inner_payload_id = VarId::fresh_binding();
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "payload".to_string(),
        id: Some(outer_payload_id),
        value: PBox::new(PseudoExpr::var("seed")),
        body: PBox::new(PseudoExpr::Let {
            name: "payload".to_string(),
            id: Some(inner_payload_id),
            value: PBox::new(PseudoExpr::var("shadow")),
            body: PBox::new(PseudoExpr::Let {
                name: "q".to_string(),
                id: Some(temp_id),
                value: PBox::new(PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("payload", outer_payload_id),
                        "fields".to_string(),
                    )),
                    index: 2,
                }),
                body: PBox::new(PseudoExpr::var_with_id("q", temp_id)),
            }),
        }),
    };

    let hints = collect_field_payload_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id), None);
}

#[test]
fn test_improve_variable_names_ignores_inconsistent_payload_item_field_alias() {
    let outer_payload_id = VarId::fresh_binding();
    let inner_payload_id = VarId::fresh_binding();
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "payload".to_string(),
        id: Some(outer_payload_id),
        value: PBox::new(PseudoExpr::var("seed")),
        body: PBox::new(PseudoExpr::Let {
            name: "payload".to_string(),
            id: Some(inner_payload_id),
            value: PBox::new(PseudoExpr::var("shadow")),
            body: PBox::new(PseudoExpr::Let {
                name: "q".to_string(),
                id: Some(temp_id),
                value: PBox::new(PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("payload", outer_payload_id),
                        "fields".to_string(),
                    )),
                    index: 2,
                }),
                body: PBox::new(PseudoExpr::var_with_id("q", temp_id)),
            }),
        }),
    };

    let improved = improve_variable_names(expr);

    let PseudoExpr::Let { body, .. } = improved else {
        panic!("expected outer let");
    };
    let PseudoExpr::Let { body, .. } = body.as_ref() else {
        panic!("expected shadowing let");
    };
    let PseudoExpr::Let {
        name, value, body, ..
    } = body.as_ref()
    else {
        panic!("expected inner let");
    };
    assert_eq!(name, "q");
    assert!(matches!(value.as_ref(), PseudoExpr::IndexAccess { .. }));
    assert!(
        matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "q"),
        "expected inconsistent payload alias to stay unrenamed, got: {body:?}"
    );
}
