use super::*;
use crate::decompile::ScriptVersion;
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

#[test]
fn test_may_require_large_data_literal_hoist_filters_small_scalars() {
    assert!(!Simplifier::may_require_large_data_literal_hoist(
        &PseudoExpr::int(1)
    ));
    assert!(!Simplifier::may_require_large_data_literal_hoist(
        &PseudoExpr::byte_array(vec![0xaa; 28])
    ));
    assert!(Simplifier::may_require_large_data_literal_hoist(
        &PseudoExpr::list(vec![PseudoExpr::int(1)])
    ));
    assert!(Simplifier::may_require_large_data_literal_hoist(
        &PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.Constr"),
            args: vec![PseudoExpr::int(0), PseudoExpr::list(vec![])].into(),
        }
    ));
}

#[test]
fn test_static_data_expr_node_count_matches_expr_node_count_for_static_exprs() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::int(0),
            PseudoExpr::list(vec![
                PseudoExpr::int(1),
                PseudoExpr::constr(
                    ConstructorShape::unknown_data(0, 1),
                    vec![PseudoExpr::byte_array(vec![0xaa; 28])],
                ),
            ]),
        ]
        .into(),
    };

    assert_eq!(
        Simplifier::static_data_expr_node_count(&expr),
        Some(Simplifier::expr_node_count(&expr))
    );
    assert_eq!(
        Simplifier::static_data_expr_node_count(&PseudoExpr::var("x")),
        None
    );
}

#[test]
fn resolve_context_field_name_ignores_same_name_foreign_context_ref() {
    let real_ctx_id = VarId::new(780);
    let foreign_ctx_id = VarId::new(781);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.script_version = Some(ScriptVersion::PlutusV3);
    simplifier
        .context
        .context_field_names
        .insert("ctx".to_string(), "script_context".to_string());
    simplifier
        .context
        .context_field_names_by_id
        .insert(real_ctx_id, "script_context".to_string());

    let real_ref = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("ctx", real_ctx_id)),
            selector: crate::pseudo::FieldSelector::from_display_name("fields"),
        }),
        index: 0,
    };
    assert_eq!(
        simplifier.resolve_expr_context_name(&real_ref),
        Some("tx_info".to_string())
    );

    let foreign_ref = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("ctx", foreign_ctx_id)),
            selector: crate::pseudo::FieldSelector::from_display_name("fields"),
        }),
        index: 0,
    };
    assert_eq!(
        simplifier.resolve_expr_context_name(&foreign_ref),
        None,
        "same-name foreign context ref must not inherit context metadata registered for another id"
    );
}

#[test]
fn get_var_context_info_ignores_same_name_foreign_context_ref() {
    let real_ctx_id = VarId::new(782);
    let foreign_ctx_id = VarId::new(783);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier
        .context
        .context_field_names
        .insert("ctx".to_string(), "script_context".to_string());
    simplifier
        .context
        .context_var_types
        .insert("script_context".to_string(), "ScriptContext".to_string());
    simplifier
        .context
        .context_field_names_by_id
        .insert(real_ctx_id, "script_context".to_string());
    simplifier
        .context
        .context_var_types_by_id
        .insert(real_ctx_id, "ScriptContext".to_string());

    assert_eq!(
        simplifier.get_var_context_info("ctx", Some(real_ctx_id)),
        Some(("ScriptContext".to_string(), "script_context".to_string()))
    );
    assert_eq!(
        simplifier.get_var_context_info("ctx", Some(foreign_ctx_id)),
        None,
        "same-name foreign context arg must not inherit context metadata registered for another id"
    );
}

#[test]
fn resolve_context_field_name_uses_singular_for_inputs_index() {
    // Indexing a list-typed context field binds the singular
    // element name ("input" for `inputs`).
    let inputs_id = VarId::new(840);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.script_version = Some(ScriptVersion::PlutusV3);
    simplifier
        .context
        .context_field_names
        .insert("inputs".to_string(), "inputs".to_string());
    simplifier
        .context
        .context_field_names_by_id
        .insert(inputs_id, "inputs".to_string());

    let value = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::var_with_id("inputs", inputs_id)),
        index: 0,
    };
    assert_eq!(
        simplifier.resolve_context_field_name("v3", &value),
        Some("input".to_string()),
        "inputs[0] should bind a new `input` (singular of TxInInfo list)"
    );
}

#[test]
fn resolve_context_field_name_uses_singular_for_list_head_inputs() {
    // List.head(inputs) should yield "input" too.
    let inputs_id = VarId::new(841);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.script_version = Some(ScriptVersion::PlutusV3);
    simplifier
        .context
        .context_field_names
        .insert("inputs".to_string(), "inputs".to_string());
    simplifier
        .context
        .context_field_names_by_id
        .insert(inputs_id, "inputs".to_string());

    let value = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::ListHead,
        args: vec![PseudoExpr::var_with_id("inputs", inputs_id)].into(),
    };
    assert_eq!(
        simplifier.resolve_context_field_name("hd", &value),
        Some("input".to_string()),
        "List.head(inputs) should bind a new `input`"
    );
}

#[test]
fn resolve_context_field_name_uses_singular_for_outputs_index() {
    let outputs_id = VarId::new(842);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.script_version = Some(ScriptVersion::PlutusV3);
    simplifier
        .context
        .context_field_names
        .insert("outputs".to_string(), "outputs".to_string());
    simplifier
        .context
        .context_field_names_by_id
        .insert(outputs_id, "outputs".to_string());

    let value = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::var_with_id("outputs", outputs_id)),
        index: 2,
    };
    assert_eq!(
        simplifier.resolve_context_field_name("v", &value),
        Some("output".to_string()),
    );
}

#[test]
fn test_collect_call_arg_observations_handles_curried_calls_and_delay_wrappers() {
    let x_id = VarId::new(790);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("target")),
            args: vec![PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
                "x", x_id,
            )))]
            .into(),
        }),
        args: vec![PseudoExpr::int(1)].into(),
    };

    let results = Simplifier::collect_call_arg_observations(&expr, "target", None);
    assert_eq!(
        results,
        vec![CallArgObservation {
            first_var_args: vec![Some(("x".to_string(), Some(x_id))), None],
            delayed_args: vec![true, false],
        }]
    );
}
