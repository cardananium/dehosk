use super::*;
use crate::builtins::BuiltinId;
use crate::decompile::ScriptVersion;
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

#[test]
fn test_has_any_var_named_detects_binders_and_refs() {
    let expr = PseudoExpr::Let {
        name: "fields".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".into(), "payload".into()],
            body: PBox::new(PseudoExpr::var("x")),
        }),
        body: PBox::new(PseudoExpr::RecFn {
            name: "loop".into(),
            params: vec!["acc".into()],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("subject")),
                subject_name: Some("subject_alias".into()),
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Var("pattern_value".into()),
                    guard: None,
                    body: PseudoExpr::var("payload"),
                }],
            }),
        }),
    };

    assert!(has_any_var_named(&expr, "fields"));
    assert!(has_any_var_named(&expr, "payload"));
    assert!(has_any_var_named(&expr, "loop"));
    assert!(has_any_var_named(&expr, "subject_alias"));
    assert!(has_any_var_named(&expr, "pattern_value"));
    assert!(!has_any_var_named(&expr, "missing"));
}

#[test]
fn test_collect_call_sites_simplified_collects_nested_multi_arg_calls() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("outer")),
        args: vec![
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("target")),
                args: vec![PseudoExpr::int(1), PseudoExpr::var("x")].into(),
            },
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("subject")),
                subject_name: None,
                clauses: vec![WhenClause::new(
                    WhenPattern::Wildcard,
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("target")),
                        args: vec![PseudoExpr::int(2)].into(),
                    },
                )],
            },
        ]
        .into(),
    };

    let mut results = Vec::new();
    collect_call_sites_simplified(&expr, "target", None, &mut results);

    assert_eq!(results.len(), 2);
    assert_eq!(results[0].len(), 2);
    assert_eq!(results[1].len(), 1);
}

#[test]
fn test_rename_var_simple_avoids_capture_under_when_subject_name() {
    let old_id = VarId::fresh_binding();
    let subject_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: Some(Binder::new("policy_id", subject_id)),
        clauses: vec![WhenClause::new(
            WhenPattern::Wildcard,
            PseudoExpr::var_with_id("fields_0_2", old_id),
        )],
    };

    let result = rename_var_simple(expr, "fields_0_2", "policy_id");

    let PseudoExpr::When { clauses, .. } = result else {
        panic!("expected when");
    };
    assert!(
        matches!(&clauses[0].body, PseudoExpr::Var { name, id } if name == "fields_0_2" && *id == Some(old_id))
    );
}

#[test]
fn test_prepare_inline_when_clause_jobs_renames_purpose_constructor_fields() {
    let field_id = VarId::fresh_binding();
    // `Known(Mint)` is ScriptPurpose tag 0, arity 1. The longer
    // "Minting" form comes from the `BlueprintHintRegistry` at
    // display time; this test covers only the `subject_ctx` + tag
    // rename path.
    let clauses = vec![WhenClause {
        pattern: WhenPattern::constructor_known(
            KnownConstructor::Mint,
            vec![Binder::new("fields_0", field_id)],
        ),
        guard: Some(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var_with_id("fields_0", field_id)),
            right: PBox::new(PseudoExpr::var_with_id("fields_0", field_id)),
        }),
        body: PseudoExpr::var_with_id("fields_0", field_id),
    }];

    let mut context_names = InlineNames::new();
    context_names.insert("purpose".to_string(), "purpose".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("purpose".to_string(), "purpose".to_string());

    let (clause_meta, clause_jobs) = prepare_inline_when_clause_jobs(
        clauses,
        Some("purpose"),
        Some("purpose"),
        &context_names,
        &context_types,
        &InlineOverrides::new(),
        ScriptVersion::PlutusV2,
    );

    let WhenPattern::Constructor { fields, .. } = &clause_meta[0].0 else {
        panic!("expected constructor pattern metadata");
    };
    assert_eq!(fields[0].as_str(), "policy_id");
    assert_eq!(fields[0].id, field_id);
    assert!(clause_meta[0].1);

    let (guard, body, ctx) = &clause_jobs[0];
    let overrides = ctx.overrides.as_ref();
    let Some(PseudoExpr::BinOp { left, right, .. }) = guard else {
        panic!("expected renamed guard");
    };
    assert!(
        matches!(left.as_ref(), PseudoExpr::Var { name, id, .. } if name == "policy_id" && *id == Some(field_id))
            && matches!(right.as_ref(), PseudoExpr::Var { name, id, .. } if name == "policy_id" && *id == Some(field_id))
    );
    assert!(
        matches!(body, PseudoExpr::Var { name, id, .. } if name == "policy_id" && *id == Some(field_id))
    );
    assert_eq!(
        overrides.get("purpose"),
        Some(&vec!["policy_id".to_string()])
    );
}

#[test]
fn test_prepare_inline_when_clause_jobs_skips_semantic_rename_on_capture_name() {
    let field_id = VarId::fresh_binding();
    let capture_id = VarId::fresh_binding();
    let clauses = vec![WhenClause {
        pattern: WhenPattern::constructor_known(
            KnownConstructor::Mint,
            vec![Binder::new("fields_0", field_id)],
        ),
        guard: None,
        body: PseudoExpr::Lambda {
            params: vec![Binder::new("policy_id", capture_id)],
            body: PBox::new(PseudoExpr::var_with_id("fields_0", field_id)),
        },
    }];

    let mut context_names = InlineNames::new();
    context_names.insert("purpose".to_string(), "purpose".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("purpose".to_string(), "purpose".to_string());

    let (clause_meta, clause_jobs) = prepare_inline_when_clause_jobs(
        clauses,
        Some("purpose"),
        Some("purpose"),
        &context_names,
        &context_types,
        &InlineOverrides::new(),
        ScriptVersion::PlutusV2,
    );

    let WhenPattern::Constructor { fields, .. } = &clause_meta[0].0 else {
        panic!("expected constructor pattern metadata");
    };
    assert_eq!(fields[0].as_str(), "fields_0");
    assert_eq!(fields[0].id, field_id);

    let (_guard, body, _ctx) = &clause_jobs[0];
    let PseudoExpr::Lambda { params, body } = body else {
        panic!("expected capture lambda");
    };
    assert_eq!(params[0].as_str(), "policy_id");
    assert!(
        matches!(body.as_ref(), PseudoExpr::Var { name, id, .. } if name == "fields_0" && *id == Some(field_id))
    );
}

#[test]
fn test_prepare_inline_when_clause_jobs_renames_only_matching_authoritative_field_id() {
    let field_id = VarId::new(9431);
    let other_id = VarId::new(9432);
    let clauses = vec![WhenClause {
        pattern: WhenPattern::constructor_known(
            KnownConstructor::Mint,
            vec![Binder::new("fields_0", field_id)],
        ),
        guard: None,
        body: PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("fields_0", field_id),
                PseudoExpr::var_with_id("fields_0", other_id),
            ]
            .into(),
        ),
    }];

    let mut context_names = InlineNames::new();
    context_names.insert("purpose".to_string(), "purpose".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("purpose".to_string(), "purpose".to_string());

    let (clause_meta, clause_jobs) = prepare_inline_when_clause_jobs(
        clauses,
        Some("purpose"),
        Some("purpose"),
        &context_names,
        &context_types,
        &InlineOverrides::new(),
        ScriptVersion::PlutusV2,
    );

    let WhenPattern::Constructor { fields, .. } = &clause_meta[0].0 else {
        panic!("expected constructor pattern metadata");
    };
    assert_eq!(fields[0].as_str(), "policy_id");
    assert_eq!(fields[0].id, field_id);

    let (_guard, body, _ctx) = &clause_jobs[0];
    assert!(
        matches!(
            body,
            PseudoExpr::Tuple(items)
                if matches!(&items[0], PseudoExpr::Var { name, id, .. }
                    if name == "policy_id" && *id == Some(field_id))
                && matches!(&items[1], PseudoExpr::Var { name, id, .. }
                    if name == "fields_0" && *id == Some(other_id))
        ),
        "semantic constructor-field rename must target only the pattern binder id"
    );
}

#[test]
fn test_prepare_inline_let_value_contexts_propagates_consistent_lambda_param_types() {
    let value = PseudoExpr::Lambda {
        params: vec!["ctx".into(), "_".into()],
        body: PBox::new(PseudoExpr::var("ctx")),
    };
    let body = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("lookup")),
                args: vec![PseudoExpr::var("tx_info"), PseudoExpr::int(1)].into(),
            },
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("lookup")),
                args: vec![PseudoExpr::var("tx_info"), PseudoExpr::int(2)].into(),
            },
        ]
        .into(),
    );

    let mut context_names = InlineNames::new();
    context_names.insert("tx_info".to_string(), "tx_info".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("tx_info".to_string(), "tx_info".to_string());

    let (value_names, value_types) = prepare_inline_let_value_contexts(
        "lookup",
        None,
        &value,
        &body,
        &context_names,
        &context_types,
        &ByIdNames::new(),
    );

    assert_eq!(value_names.get("ctx"), Some(&"ctx".to_string()));
    assert_eq!(value_types.get("ctx"), Some(&"tx_info".to_string()));
    assert!(!value_names.contains_key("_"));
    assert!(!value_types.contains_key("_"));
}

#[test]
fn test_prepare_inline_let_value_contexts_skips_mixed_lambda_param_types() {
    let value = PseudoExpr::Lambda {
        params: vec!["ctx".into()],
        body: PBox::new(PseudoExpr::var("ctx")),
    };
    let body = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("lookup")),
                args: vec![PseudoExpr::var("tx_info")].into(),
            },
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("lookup")),
                args: vec![PseudoExpr::var("purpose")].into(),
            },
        ]
        .into(),
    );

    let mut context_names = InlineNames::new();
    context_names.insert("tx_info".to_string(), "tx_info".to_string());
    context_names.insert("purpose".to_string(), "purpose".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("tx_info".to_string(), "tx_info".to_string());
    context_types.insert("purpose".to_string(), "purpose".to_string());

    let (value_names, value_types) = prepare_inline_let_value_contexts(
        "lookup",
        None,
        &value,
        &body,
        &context_names,
        &context_types,
        &ByIdNames::new(),
    );

    assert!(!value_names.contains_key("ctx"));
    assert!(!value_types.contains_key("ctx"));
}

#[test]
fn test_prepare_inline_let_value_contexts_ignores_same_name_foreign_call_site() {
    let target_lookup_id = VarId::new(9831);
    let foreign_lookup_id = VarId::new(9832);
    let value = PseudoExpr::Lambda {
        params: vec!["ctx".into()],
        body: PBox::new(PseudoExpr::var("ctx")),
    };
    let body = PseudoExpr::Let {
        name: "lookup".to_string(),
        id: Some(foreign_lookup_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("lookup", foreign_lookup_id)),
            args: vec![PseudoExpr::var("tx_info")].into(),
        }),
    };

    let mut context_names = InlineNames::new();
    context_names.insert("tx_info".to_string(), "tx_info".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("tx_info".to_string(), "tx_info".to_string());

    let (value_names, value_types) = prepare_inline_let_value_contexts(
        "lookup",
        Some(target_lookup_id),
        &value,
        &body,
        &context_names,
        &context_types,
        &ByIdNames::new(),
    );

    assert!(!value_names.contains_key("ctx"));
    assert!(!value_types.contains_key("ctx"));
}

#[test]
fn test_prepare_inline_let_value_contexts_uses_matching_call_site_id() {
    let target_lookup_id = VarId::new(9833);
    let value = PseudoExpr::Lambda {
        params: vec!["ctx".into()],
        body: PBox::new(PseudoExpr::var("ctx")),
    };
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("lookup", target_lookup_id)),
        args: vec![PseudoExpr::var("tx_info")].into(),
    };

    let mut context_names = InlineNames::new();
    context_names.insert("tx_info".to_string(), "tx_info".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("tx_info".to_string(), "tx_info".to_string());

    let (value_names, value_types) = prepare_inline_let_value_contexts(
        "lookup",
        Some(target_lookup_id),
        &value,
        &body,
        &context_names,
        &context_types,
        &ByIdNames::new(),
    );

    assert_eq!(value_names.get("ctx"), Some(&"ctx".to_string()));
    assert_eq!(value_types.get("ctx"), Some(&"tx_info".to_string()));
}

#[test]
fn test_prepare_inline_apply_arg_jobs_renames_single_param_lambda_to_input() {
    let param_id = VarId::fresh_binding();
    let args = vec![
        PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("Data.to_list"),
            args: vec![PseudoExpr::var("inputs")].into(),
        },
        PseudoExpr::Lambda {
            params: vec![Binder::new("item_0", param_id)],
            body: PBox::new(PseudoExpr::var_with_id("item_0", param_id)),
        },
    ];

    let mut context_names = InlineNames::new();
    context_names.insert("inputs".to_string(), "inputs".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("inputs".to_string(), "tx_in_info".to_string());

    let arg_jobs = prepare_inline_apply_arg_jobs(
        args,
        &context_names,
        &context_types,
        &InlineOverrides::new(),
        &ByIdNames::new(),
    );

    let (_guard, renamed_lambda, ctx) = &arg_jobs[1];
    let PseudoExpr::Lambda { params, body } = renamed_lambda else {
        panic!("expected lambda arg");
    };
    assert_eq!(params[0].as_str(), "input");
    assert_eq!(params[0].id, param_id);
    assert!(
        matches!(body.as_ref(), PseudoExpr::Var { name, id, .. } if name == "input" && *id == Some(param_id))
    );
    assert_eq!(ctx.names.get("input"), Some(&"input".to_string()));
    assert_eq!(ctx.types.get("input"), Some(&"tx_in_info".to_string()));
}

#[test]
fn test_prepare_inline_apply_arg_jobs_skips_param_rename_on_capture_name() {
    let param_id = VarId::fresh_binding();
    let capture_id = VarId::fresh_binding();
    let args = vec![
        PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("Data.to_list"),
            args: vec![PseudoExpr::var("inputs")].into(),
        },
        PseudoExpr::Lambda {
            params: vec![Binder::new("item_0", param_id)],
            body: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("input", capture_id)],
                body: PBox::new(PseudoExpr::var_with_id("item_0", param_id)),
            }),
        },
    ];

    let mut context_names = InlineNames::new();
    context_names.insert("inputs".to_string(), "inputs".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("inputs".to_string(), "tx_in_info".to_string());

    let arg_jobs = prepare_inline_apply_arg_jobs(
        args,
        &context_names,
        &context_types,
        &InlineOverrides::new(),
        &ByIdNames::new(),
    );

    let (_guard, lambda, ctx) = &arg_jobs[1];
    let PseudoExpr::Lambda { params, body } = lambda else {
        panic!("expected lambda arg");
    };
    assert_eq!(params[0].as_str(), "item_0");
    assert!(matches!(body.as_ref(), PseudoExpr::Lambda { params, body }
            if params[0].as_str() == "input"
                && matches!(body.as_ref(), PseudoExpr::Var { name, id, .. } if name == "item_0" && *id == Some(param_id))));
    assert_eq!(ctx.names.get("item_0"), Some(&"item_0".to_string()));
    assert_eq!(ctx.types.get("item_0"), Some(&"tx_in_info".to_string()));
    assert!(!ctx.names.contains_key("input"));
}

#[test]
fn test_prepare_inline_apply_arg_jobs_renames_only_matching_authoritative_param_id() {
    let param_id = VarId::new(9441);
    let other_id = VarId::new(9442);
    let args = vec![
        PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("Data.to_list"),
            args: vec![PseudoExpr::var("inputs")].into(),
        },
        PseudoExpr::Lambda {
            params: vec![Binder::new("item_0", param_id)],
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("item_0", param_id),
                    PseudoExpr::var_with_id("item_0", other_id),
                ]
                .into(),
            )),
        },
    ];

    let mut context_names = InlineNames::new();
    context_names.insert("inputs".to_string(), "inputs".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("inputs".to_string(), "tx_in_info".to_string());

    let arg_jobs = prepare_inline_apply_arg_jobs(
        args,
        &context_names,
        &context_types,
        &InlineOverrides::new(),
        &ByIdNames::new(),
    );

    let (_guard, renamed_lambda, _ctx) = &arg_jobs[1];
    let PseudoExpr::Lambda { params, body } = renamed_lambda else {
        panic!("expected lambda arg");
    };
    assert_eq!(params[0].as_str(), "input");
    assert_eq!(params[0].id, param_id);
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Tuple(items)
                if matches!(&items[0], PseudoExpr::Var { name, id, .. }
                    if name == "input" && *id == Some(param_id))
                && matches!(&items[1], PseudoExpr::Var { name, id, .. }
                    if name == "item_0" && *id == Some(other_id))
        ),
        "semantic lambda-param rename must target only the lambda param id"
    );
}

#[test]
fn test_prepare_inline_apply_arg_jobs_keeps_multi_param_lambda_unchanged() {
    let args = vec![
        PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("Data.to_list"),
            args: vec![PseudoExpr::var("inputs")].into(),
        },
        PseudoExpr::Lambda {
            params: vec!["x".into(), "y".into()],
            body: PBox::new(PseudoExpr::Tuple(
                vec![PseudoExpr::var("x"), PseudoExpr::var("y")].into(),
            )),
        },
    ];

    let mut context_names = InlineNames::new();
    context_names.insert("inputs".to_string(), "inputs".to_string());
    let mut context_types = InlineTypes::new();
    context_types.insert("inputs".to_string(), "tx_in_info".to_string());

    let arg_jobs = prepare_inline_apply_arg_jobs(
        args,
        &context_names,
        &context_types,
        &InlineOverrides::new(),
        &ByIdNames::new(),
    );

    let (_guard, lambda, ctx) = &arg_jobs[1];
    let PseudoExpr::Lambda { params, body } = lambda else {
        panic!("expected lambda arg");
    };
    assert_eq!(params[0].as_str(), "x");
    assert_eq!(params[1].as_str(), "y");
    assert!(matches!(body.as_ref(), PseudoExpr::Tuple(_)));
    assert!(!ctx.names.contains_key("input"));
    assert!(!ctx.types.contains_key("input"));
}

#[test]
fn test_resolve_inline_index_access_rewrites_sum_fields_projection_with_override() {
    let resolved = resolve_inline_index_access(
        PseudoExpr::field_access(PseudoExpr::var("purpose"), "fields".to_string()),
        0,
        &InlineNames::from([("purpose".to_string(), "purpose".to_string())]),
        &InlineTypes::from([("purpose".to_string(), "purpose".to_string())]),
        &InlineOverrides::from([("purpose".to_string(), vec!["policy_id".to_string()])]),
        &ByIdNames::new(),
        ScriptVersion::PlutusV2,
    );

    assert!(
        matches!(
            resolved,
            PseudoExpr::FieldAccess {
                ref record,
                ref selector,
                ..
            }
                if matches!(record.as_ref(), PseudoExpr::Var { name, .. } if name == "purpose")
                    && selector.as_pretty_name() == "policy_id"
        ),
        "expected semantic field access rewrite, got: {resolved:?}"
    );
}

#[test]
fn test_finalize_inline_let_binding_renames_generic_field_alias_without_collision() {
    let mut used_let_names = HashSet::from(["fields_0_2".to_string()]);
    let binding_id = VarId::fresh_compat_placeholder();
    let (final_name, final_value, final_body) = finalize_inline_let_binding(
        "fields_0_2".to_string(),
        binding_id,
        PseudoExpr::field_access(PseudoExpr::var("purpose"), "policy_id".to_string()),
        PseudoExpr::var("fields_0_2"),
        &mut used_let_names,
    );

    assert_eq!(final_name, "policy_id");
    assert!(used_let_names.contains("policy_id"));
    assert!(matches!(
        final_value,
        PseudoExpr::FieldAccess { selector, .. } if selector.as_pretty_name() == "policy_id"
    ));
    assert!(matches!(final_body, PseudoExpr::Var { name, .. } if name == "policy_id"));
}

#[test]
fn test_finalize_inline_let_binding_keeps_generic_field_alias_on_collision() {
    let mut used_let_names = HashSet::from(["fields_0_2".to_string()]);
    let binding_id = VarId::fresh_compat_placeholder();
    let (final_name, _final_value, final_body) = finalize_inline_let_binding(
        "fields_0_2".to_string(),
        binding_id,
        PseudoExpr::field_access(PseudoExpr::var("purpose"), "policy_id".to_string()),
        PseudoExpr::Tuple(vec![PseudoExpr::var("fields_0_2"), PseudoExpr::var("policy_id")].into()),
        &mut used_let_names,
    );

    assert_eq!(final_name, "fields_0_2");
    assert!(matches!(final_body, PseudoExpr::Tuple(_)));
}

#[test]
fn test_finalize_inline_let_binding_keeps_generic_field_alias_on_reserved_let_name() {
    let mut used_let_names = HashSet::from(["fields_0_2".to_string(), "policy_id".to_string()]);
    let binding_id = VarId::fresh_compat_placeholder();
    let (final_name, _final_value, final_body) = finalize_inline_let_binding(
        "fields_0_2".to_string(),
        binding_id,
        PseudoExpr::field_access(PseudoExpr::var("purpose"), "policy_id".to_string()),
        PseudoExpr::var("fields_0_2"),
        &mut used_let_names,
    );

    assert_eq!(final_name, "fields_0_2");
    assert!(matches!(final_body, PseudoExpr::Var { name, .. } if name == "fields_0_2"));
}

#[test]
fn test_finalize_inline_let_binding_renames_only_matching_authoritative_id() {
    let mut used_let_names = HashSet::from(["fields_0_2".to_string()]);
    let binding_id = VarId::new(9421);
    let other_id = VarId::new(9422);
    let (final_name, _final_value, final_body) = finalize_inline_let_binding(
        "fields_0_2".to_string(),
        binding_id,
        PseudoExpr::field_access(PseudoExpr::var("purpose"), "policy_id".to_string()),
        PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("fields_0_2", binding_id),
                PseudoExpr::var_with_id("fields_0_2", other_id),
            ]
            .into(),
        ),
        &mut used_let_names,
    );

    assert_eq!(final_name, "policy_id");
    assert!(
        matches!(
            final_body,
            PseudoExpr::Tuple(items)
                if matches!(&items[0], PseudoExpr::Var { name, id, .. }
                    if name == "policy_id" && *id == Some(binding_id))
                && matches!(&items[1], PseudoExpr::Var { name, id, .. }
                    if name == "fields_0_2" && *id == Some(other_id))
        ),
        "semantic alias rename must target only refs for the let binder id"
    );
}

#[test]
fn test_resolve_inline_field_accesses_keeps_let_names_unique_across_semantic_alias_renames() {
    let outer_id = VarId::fresh_binding();
    let inner_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "fields_0_2".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("purpose"),
            "policy_id".to_string(),
        )),
        body: PBox::new(PseudoExpr::Let {
            name: "fields_0_3".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("purpose"),
                "policy_id".to_string(),
            )),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("fields_0_2", outer_id),
                    PseudoExpr::var_with_id("fields_0_3", inner_id),
                ]
                .into(),
            )),
        }),
    };

    let result = resolve_inline_field_accesses(
        expr,
        ScriptVersion::PlutusV2,
        &InlineNames::new(),
        &InlineTypes::new(),
        &InlineOverrides::new(),
        &ByIdNames::new(),
        &ByIdNames::new(),
    );

    let PseudoExpr::Let {
        name: outer_name,
        id: Some(final_outer_id),
        body,
        ..
    } = &result
    else {
        panic!("expected outer let");
    };
    let PseudoExpr::Let {
        name: inner_name,
        id: Some(final_inner_id),
        body: inner_body,
        ..
    } = body.as_ref()
    else {
        panic!("expected inner let");
    };

    assert_ne!(outer_name, inner_name);
    assert_eq!(outer_name, "fields_0_2");
    assert_eq!(inner_name, "policy_id");
    assert_eq!(*final_outer_id, outer_id);
    assert_eq!(*final_inner_id, inner_id);
    assert!(matches!(inner_body.as_ref(), PseudoExpr::Tuple(items)
            if matches!(&items[0], PseudoExpr::Var { name, id } if name == "fields_0_2" && *id == Some(outer_id))
                && matches!(&items[1], PseudoExpr::Var { name, id } if name == "policy_id" && *id == Some(inner_id))));
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "resolve_field_accesses should preserve ref-id consistency"
    );
}

#[test]
fn test_resolve_inline_field_accesses_rebases_fields_carrier_to_parent_field() {
    let parent_id = VarId::fresh_binding();
    let carrier_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "tx_info".to_string(),
        id: Some(parent_id),
        value: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("script_context"),
            "tx_info",
        )),
        body: PBox::new(PseudoExpr::Let {
            name: "tx_info_fields".to_string(),
            id: Some(carrier_id),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var_with_id("tx_info", parent_id),
                "fields",
            )),
            body: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.un_list"),
                args: vec![PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::var_with_id("tx_info_fields", carrier_id)),
                    index: 2,
                }]
                .into(),
            }),
        }),
    };

    let mut context_names = InlineNames::new();
    context_names.insert("tx_info".to_string(), "tx_info".to_string());
    let mut field_names_by_id = ByIdNames::new();
    field_names_by_id.insert(parent_id, "tx_info".to_string());
    field_names_by_id.insert(carrier_id, "tx_info_fields".to_string());

    let result = resolve_inline_field_accesses(
        expr,
        ScriptVersion::PlutusV2,
        &context_names,
        &InlineTypes::new(),
        &InlineOverrides::new(),
        &field_names_by_id,
        &ByIdNames::new(),
    );
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "rebased parent field access must preserve ref-id consistency"
    );

    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected parent let after inline field resolution");
    };
    let PseudoExpr::Let { body, .. } = body.as_ref() else {
        panic!("expected carrier let after inline field resolution");
    };
    let PseudoExpr::BuiltinCall { args, .. } = body.as_ref() else {
        panic!("expected Data.un_list call after inline field resolution");
    };
    assert!(
        matches!(
            args.as_slice(),
            [PseudoExpr::FieldAccess { record, selector, .. }]
                if selector.as_pretty_name() == "outputs"
                    && matches!(
                        record.as_ref(),
                        PseudoExpr::Var { name, id } if name == "tx_info" && *id == Some(parent_id)
                    )
        ),
        "expected tx_info_fields[2] to rebase to tx_info.outputs with parent id, got: {body:?}"
    );
}

#[test]
fn test_resolve_inline_index_access_uses_parent_id_only_for_unambiguous_id_resolution() {
    let carrier_id = VarId::fresh_binding();
    let parent_id = VarId::fresh_binding();

    let mut field_names_by_id = ByIdNames::new();
    field_names_by_id.insert(carrier_id, "tx_info_fields".to_string());
    field_names_by_id.insert(parent_id, "tx_info".to_string());

    let result = resolve_inline_index_access(
        PseudoExpr::var_with_id("tx_info_fields", carrier_id),
        2,
        &InlineNames::new(),
        &InlineTypes::new(),
        &InlineOverrides::new(),
        &field_names_by_id,
        ScriptVersion::PlutusV2,
    );

    assert!(
        matches!(
            result,
            PseudoExpr::FieldAccess { record, selector, .. }
                if selector.as_pretty_name() == "outputs"
                    && matches!(
                        record.as_ref(),
                        PseudoExpr::Var { name, id } if name == "tx_info" && *id == Some(parent_id)
                    )
        ),
        "id-resolved carrier should rebase through the unambiguous parent id"
    );
}

#[test]
fn test_resolve_inline_index_access_ambiguous_or_name_fallback_parent_stays_compat() {
    let carrier_id = VarId::fresh_binding();
    let first_parent_id = VarId::fresh_binding();
    let second_parent_id = VarId::fresh_binding();

    let mut field_names_by_id = ByIdNames::new();
    field_names_by_id.insert(carrier_id, "tx_info_fields".to_string());
    field_names_by_id.insert(first_parent_id, "tx_info".to_string());
    field_names_by_id.insert(second_parent_id, "tx_info".to_string());

    let ambiguous_parent = resolve_inline_index_access(
        PseudoExpr::var_with_id("tx_info_fields", carrier_id),
        2,
        &InlineNames::new(),
        &InlineTypes::new(),
        &InlineOverrides::new(),
        &field_names_by_id,
        ScriptVersion::PlutusV2,
    );

    assert!(
        matches!(
            ambiguous_parent,
            PseudoExpr::FieldAccess { record, selector, .. }
                if selector.as_pretty_name() == "outputs"
                    && matches!(
                        record.as_ref(),
                        PseudoExpr::Var { name, id } if name == "tx_info" && id.get().is_none()
                    )
        ),
        "ambiguous parent id should not make the rebased receiver authoritative"
    );

    let mut context_names = InlineNames::new();
    context_names.insert("tx_info_fields".to_string(), "tx_info_fields".to_string());
    let mut parent_only_names_by_id = ByIdNames::new();
    parent_only_names_by_id.insert(first_parent_id, "tx_info".to_string());

    let name_fallback = resolve_inline_index_access(
        PseudoExpr::var_with_id("tx_info_fields", carrier_id),
        2,
        &context_names,
        &InlineTypes::new(),
        &InlineOverrides::new(),
        &parent_only_names_by_id,
        ScriptVersion::PlutusV2,
    );

    assert!(
        matches!(
            name_fallback,
            PseudoExpr::FieldAccess { record, selector, .. }
                if selector.as_pretty_name() == "outputs"
                    && matches!(
                        record.as_ref(),
                        PseudoExpr::Var { name, id } if name == "tx_info" && id.get().is_none()
                    )
        ),
        "name-resolved carrier should preserve legacy compat receiver semantics"
    );
}

#[test]
fn test_rebuild_apply_from_results_preserves_function_and_arg_order() {
    let mut results = vec![
        PseudoExpr::var("target"),
        PseudoExpr::int(1),
        PseudoExpr::int(2),
    ];

    let rebuilt = rebuild_apply_from_results(&mut results, 2);

    let PseudoExpr::Apply { function, args } = rebuilt else {
        panic!("expected apply");
    };
    assert!(matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "target"));
    assert_eq!(args, vec![PseudoExpr::int(1), PseudoExpr::int(2)].into());
    assert!(results.is_empty());
}

#[test]
fn test_rebuild_list_from_results_preserves_elements_and_tail() {
    let mut results = vec![
        PseudoExpr::int(1),
        PseudoExpr::int(2),
        PseudoExpr::var("tail"),
    ];

    let rebuilt = rebuild_list_from_results(&mut results, 2, true);

    let PseudoExpr::List { elements, tail } = rebuilt else {
        panic!("expected list");
    };
    assert_eq!(
        elements,
        vec![PseudoExpr::int(1), PseudoExpr::int(2)].into()
    );
    let Some(tail) = tail else {
        panic!("expected tail");
    };
    assert!(matches!(tail.as_ref(), PseudoExpr::Var { name, .. } if name == "tail"));
    assert!(results.is_empty());
}

#[test]
fn test_rebuild_when_from_results_preserves_clause_guard_and_body_order() {
    let mut results = vec![
        PseudoExpr::var("guard_1"),
        PseudoExpr::var("body_1"),
        PseudoExpr::var("body_2"),
    ];

    let rebuilt = rebuild_when_from_results(
        &mut results,
        PseudoExpr::var("subject"),
        Some("subject_alias".into()),
        vec![
            (WhenPattern::Var("x".into()), true),
            (WhenPattern::Wildcard, false),
        ],
    );

    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = rebuilt
    else {
        panic!("expected when");
    };
    assert!(matches!(subject.as_ref(), PseudoExpr::Var { name, .. } if name == "subject"));
    assert_eq!(
        subject_name.as_ref().map(|b| b.as_str()),
        Some("subject_alias")
    );
    assert_eq!(clauses.len(), 2);
    assert!(matches!(
        clauses[0].guard.as_ref(),
        Some(PseudoExpr::Var { name, .. }) if name == "guard_1"
    ));
    assert!(matches!(&clauses[0].body, PseudoExpr::Var { name, .. } if name == "body_1"));
    assert!(clauses[1].guard.is_none());
    assert!(matches!(&clauses[1].body, PseudoExpr::Var { name, .. } if name == "body_2"));
    assert!(results.is_empty());
}

#[test]
fn test_rebuild_if_from_results_preserves_branch_order() {
    let mut results = vec![
        PseudoExpr::var("condition"),
        PseudoExpr::var("then_branch"),
        PseudoExpr::var("else_branch"),
    ];

    let rebuilt = rebuild_if_from_results(&mut results);

    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = rebuilt
    else {
        panic!("expected if");
    };
    assert!(matches!(condition.as_ref(), PseudoExpr::Var { name, .. } if name == "condition"));
    assert!(matches!(then_branch.as_ref(), PseudoExpr::Var { name, .. } if name == "then_branch"));
    assert!(matches!(else_branch.as_ref(), PseudoExpr::Var { name, .. } if name == "else_branch"));
    assert!(results.is_empty());
}

#[test]
fn test_rebuild_trace_from_results_preserves_message_and_value_order() {
    let mut results = vec![PseudoExpr::string("message"), PseudoExpr::var("value")];

    let rebuilt = rebuild_trace_from_results(&mut results);

    let PseudoExpr::Trace { message, value } = rebuilt else {
        panic!("expected trace");
    };
    assert!(matches!(message.as_ref(), PseudoExpr::String(s) if s == "message"));
    assert!(matches!(value.as_ref(), PseudoExpr::Var { name, .. } if name == "value"));
    assert!(results.is_empty());
}

#[test]
fn test_rebuild_pair_from_results_preserves_element_order() {
    let mut results = vec![PseudoExpr::var("first"), PseudoExpr::var("second")];

    let rebuilt = rebuild_pair_from_results(&mut results);

    let PseudoExpr::Pair(first, second) = rebuilt else {
        panic!("expected pair");
    };
    assert!(matches!(first.as_ref(), PseudoExpr::Var { name, .. } if name == "first"));
    assert!(matches!(second.as_ref(), PseudoExpr::Var { name, .. } if name == "second"));
    assert!(results.is_empty());
}

#[test]
fn test_schedule_enter_apply_pushes_exit_args_then_function_in_stack_order() {
    let mut tasks = Vec::new();
    schedule_enter_apply(
        &mut tasks,
        PseudoExpr::var("target"),
        vec![PseudoExpr::var("x"), PseudoExpr::var("y")],
        InlineCtx::new(
            InlineNames::new(),
            InlineTypes::new(),
            InlineOverrides::new(),
        ),
        &ByIdNames::new(),
    );

    assert!(matches!(tasks[0], ResolveTask::ExitApply { args_len: 2 }));
    assert!(matches!(
        &tasks[1],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "y"
    ));
    assert!(matches!(
        &tasks[2],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "x"
    ));
    assert!(matches!(
        &tasks[3],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "target"
    ));
}

#[test]
fn test_schedule_enter_when_pushes_subject_after_after_when_subject() {
    let mut tasks = Vec::new();
    schedule_enter_when(
        &mut tasks,
        PseudoExpr::var("subject"),
        Some("subject_alias".into()),
        vec![WhenClause::new(
            WhenPattern::Wildcard,
            PseudoExpr::var("body"),
        )],
        InlineCtx::new(
            InlineNames::new(),
            InlineTypes::new(),
            InlineOverrides::new(),
        ),
    );

    assert!(matches!(
        &tasks[0],
        ResolveTask::AfterWhenSubject {
            subject_name,
            clauses,
            ..
        } if subject_name.as_ref().map(|b| b.as_str()) == Some("subject_alias") && clauses.len() == 1
    ));
    assert!(matches!(
        &tasks[1],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "subject"
    ));
}

#[test]
fn test_schedule_enter_let_preserves_body_order_and_augments_value_context() {
    let mut tasks = Vec::new();
    schedule_enter_let(
        &mut tasks,
        "lookup".to_string(),
        VarId::fresh_compat_placeholder(),
        PseudoExpr::Lambda {
            params: vec!["ctx".into()],
            body: PBox::new(PseudoExpr::var("ctx")),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("lookup")),
            args: vec![PseudoExpr::var("tx_info")].into(),
        },
        InlineCtx::new(
            InlineNames::from([("tx_info".to_string(), "tx_info".to_string())]),
            InlineTypes::from([("tx_info".to_string(), "tx_info".to_string())]),
            InlineOverrides::new(),
        ),
        &ByIdNames::new(),
    );

    assert!(matches!(&tasks[0], ResolveTask::ExitLet { name, .. } if name == "lookup"));
    assert!(matches!(
        &tasks[1],
        ResolveTask::Enter {
            expr: PseudoExpr::Apply { .. },
            ..
        }
    ));
    assert!(matches!(
        &tasks[2],
        ResolveTask::Enter {
            expr: PseudoExpr::Lambda { .. },
            ctx,
            ..
        } if ctx.types.get("ctx") == Some(&"tx_info".to_string())
    ));
}

#[test]
fn test_schedule_structural_builtin_call_pushes_args_in_stack_order_for_left_to_right_eval() {
    let mut tasks = Vec::new();
    let leaf = schedule_structural(
        &mut tasks,
        PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("sha2_256"),
            args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
        },
        InlineCtx::new(
            InlineNames::new(),
            InlineTypes::new(),
            InlineOverrides::new(),
        ),
    );
    assert!(leaf.is_none());

    assert!(matches!(
        tasks[0],
        ResolveTask::ExitBuiltinCall { args_len: 2, .. }
    ));
    assert_eq!(
        tasks
            .iter()
            .skip(1)
            .filter_map(|task| match task {
                ResolveTask::Enter {
                    expr: PseudoExpr::Int(n),
                    ..
                } => Some(n.clone()),
                _ => None,
            })
            .collect::<Vec<_>>(),
        vec![2.into(), 1.into()]
    );
}

#[test]
fn test_schedule_structural_list_pushes_tail_then_elements_in_stack_order() {
    let mut tasks = Vec::new();
    let leaf = schedule_structural(
        &mut tasks,
        PseudoExpr::List {
            elements: vec![PseudoExpr::var("head"), PseudoExpr::var("next")].into(),
            tail: Some(PBox::new(PseudoExpr::var("tail"))),
        },
        InlineCtx::new(
            InlineNames::new(),
            InlineTypes::new(),
            InlineOverrides::new(),
        ),
    );
    assert!(leaf.is_none());

    assert!(matches!(
        tasks[0],
        ResolveTask::ExitList {
            elements_len: 2,
            has_tail: true
        }
    ));
    assert!(matches!(
        &tasks[1],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "tail"
    ));
    assert!(matches!(
        &tasks[2],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "next"
    ));
    assert!(matches!(
        &tasks[3],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "head"
    ));
}

#[test]
fn test_schedule_structural_pair_pushes_second_then_first() {
    let mut tasks = Vec::new();
    let leaf = schedule_structural(
        &mut tasks,
        PseudoExpr::Pair(
            PBox::new(PseudoExpr::var("first")),
            PBox::new(PseudoExpr::var("second")),
        ),
        InlineCtx::new(
            InlineNames::new(),
            InlineTypes::new(),
            InlineOverrides::new(),
        ),
    );
    assert!(leaf.is_none());

    assert!(matches!(tasks[0], ResolveTask::ExitPair));
    assert!(matches!(
        &tasks[1],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "second"
    ));
    assert!(matches!(
        &tasks[2],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "first"
    ));
}

#[test]
fn test_schedule_structural_passes_leaves_through_without_scheduling() {
    let mut tasks = Vec::new();
    let result = schedule_structural(
        &mut tasks,
        PseudoExpr::Var {
            name: "x".to_string(),
            id: None,
        },
        InlineCtx::new(
            InlineNames::new(),
            InlineTypes::new(),
            InlineOverrides::new(),
        ),
    );
    assert!(matches!(result, Some(PseudoExpr::Var { ref name, .. }) if name == "x"));
    assert!(tasks.is_empty(), "leaves must not schedule any tasks");
}

#[test]
fn test_schedule_structural_constr_preserves_tag_shape_and_fields_in_exit_task() {
    let mut tasks = Vec::new();
    let leaf = schedule_structural(
        &mut tasks,
        PseudoExpr::Constr {
            type_hint: None,
            tag: 3,
            shape: ConstructorShape::unknown_data(3, 2),
            fields: vec![PseudoExpr::var("a"), PseudoExpr::var("b")].into(),
        },
        InlineCtx::new(
            InlineNames::new(),
            InlineTypes::new(),
            InlineOverrides::new(),
        ),
    );
    assert!(leaf.is_none());

    assert!(matches!(
        &tasks[0],
        ResolveTask::ExitConstr {
            tag: 3,
            fields_len: 2,
            shape: ConstructorShape::Unknown {
                tag: 3,
                arity: 2,
                ..
            },
            type_hint: None,
            ..
        }
    ));
    assert!(matches!(
        &tasks[1],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "b"
    ));
    assert!(matches!(
        &tasks[2],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "a"
    ));
}

#[test]
fn test_schedule_after_when_subject_pushes_exit_when_then_body_then_guard() {
    let mut tasks = Vec::new();
    schedule_after_when_subject(
        &mut tasks,
        PseudoExpr::var("purpose"),
        Some("purpose_alias".into()),
        vec![WhenClause {
            pattern: WhenPattern::constructor_known(
                KnownConstructor::Mint,
                vec!["fields_0".into()],
            ),
            guard: Some(PseudoExpr::var("fields_0")),
            body: PseudoExpr::var("fields_0"),
        }],
        InlineCtx::new(
            InlineNames::from([("purpose".to_string(), "purpose".to_string())]),
            InlineTypes::from([("purpose".to_string(), "purpose".to_string())]),
            InlineOverrides::new(),
        ),
        &ByIdNames::new(),
        ScriptVersion::PlutusV2,
    );

    assert!(matches!(
        &tasks[0],
        ResolveTask::ExitWhen {
            subject,
            subject_name,
            clauses,
        }
            if matches!(subject, PseudoExpr::Var { name, .. } if name == "purpose")
                && subject_name.as_ref().map(|b| b.as_str()) == Some("purpose_alias")
                && matches!(
                    &clauses[..],
                    [(
                        WhenPattern::Constructor { fields, .. },
                        true
                    )] if fields[0].as_str() == "policy_id"
                )
    ));
    assert!(matches!(
        &tasks[1],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "policy_id"
    ));
    assert!(matches!(
        &tasks[2],
        ResolveTask::Enter {
            expr: PseudoExpr::Var { name, .. },
            ..
        } if name == "policy_id"
    ));
}

#[test]
fn test_finalize_index_access_from_results_rewrites_sum_fields_projection() {
    let mut results = vec![PseudoExpr::field_access(
        PseudoExpr::var("purpose"),
        "fields".to_string(),
    )];

    let finalized = finalize_index_access_from_results(
        &mut results,
        0,
        &InlineNames::from([("purpose".to_string(), "purpose".to_string())]),
        &InlineTypes::from([("purpose".to_string(), "purpose".to_string())]),
        &InlineOverrides::from([("purpose".to_string(), vec!["policy_id".to_string()])]),
        &ByIdNames::new(),
        ScriptVersion::PlutusV2,
    );

    assert!(matches!(
        finalized,
        PseudoExpr::FieldAccess {
            ref record,
            ref selector,
            ..
        }
            if matches!(record.as_ref(), PseudoExpr::Var { name, .. } if name == "purpose")
                && selector.as_pretty_name() == "policy_id"
    ));
    assert!(results.is_empty());
}

#[test]
fn test_finalize_let_from_results_renames_generic_field_binding() {
    let mut results = vec![
        PseudoExpr::field_access(PseudoExpr::var("purpose"), "policy_id".to_string()),
        PseudoExpr::var("fields_0_2"),
    ];
    let mut used_let_names = HashSet::from(["fields_0_2".to_string()]);

    let finalized = finalize_let_from_results(
        &mut results,
        "fields_0_2".to_string(),
        VarId::fresh_compat_placeholder(),
        &mut used_let_names,
    );

    let PseudoExpr::Let {
        name, value, body, ..
    } = finalized
    else {
        panic!("expected let");
    };
    assert_eq!(name, "policy_id");
    assert!(
        matches!(value.as_ref(), PseudoExpr::FieldAccess { selector, .. } if selector.as_pretty_name() == "policy_id")
    );
    assert!(matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "policy_id"));
    assert!(results.is_empty());
}

#[test]
fn test_finalize_binop_from_results_expands_tx_out_ref_fields_equality() {
    let mut results = vec![
        PseudoExpr::field_access(PseudoExpr::var("tx_out_ref"), "fields".to_string()),
        PseudoExpr::List {
            elements: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
            tail: None,
        },
    ];

    let finalized =
        finalize_binop_from_results(&mut results, BinaryOp::Eq, ScriptVersion::PlutusV2);

    let PseudoExpr::BinOp { op, left, right } = finalized else {
        panic!("expected expanded and-chain");
    };
    assert_eq!(op, BinaryOp::And);
    assert!(matches!(
        left.as_ref(),
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        }
            if matches!(left.as_ref(), PseudoExpr::FieldAccess { selector, .. } if selector.as_pretty_name() == "tx_id")
                && matches!(right.as_ref(), PseudoExpr::Int(n) if *n == 1.into())
    ));
    assert!(matches!(
        right.as_ref(),
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        }
            if matches!(left.as_ref(), PseudoExpr::FieldAccess { selector, .. } if selector.as_pretty_name() == "output_index")
                && matches!(right.as_ref(), PseudoExpr::Int(n) if *n == 2.into())
    ));
    assert!(results.is_empty());
}

#[test]
fn test_finalize_binop_from_results_skips_fields_equality_when_receiver_has_binder() {
    let address_id = VarId::new(9_911);
    let tmp_id = VarId::new(9_912);
    let receiver = PseudoExpr::field_access(
        PseudoExpr::Let {
            name: "tmp".to_string(),
            id: Some(tmp_id),
            value: PBox::new(PseudoExpr::Int(0.into())),
            body: PBox::new(PseudoExpr::var_with_id("address", address_id)),
        },
        "address".to_string(),
    );
    let mut results = vec![
        PseudoExpr::field_access(receiver, "fields".to_string()),
        PseudoExpr::List {
            elements: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
            tail: None,
        },
    ];

    let finalized =
        finalize_binop_from_results(&mut results, BinaryOp::Eq, ScriptVersion::PlutusV2);

    assert!(
        matches!(
            finalized,
            PseudoExpr::BinOp { op: BinaryOp::Eq, left, right }
                if matches!(
                    left.as_ref(),
                    PseudoExpr::FieldAccess { record, selector, .. }
                        if selector.as_pretty_name() == "fields"
                            && matches!(
                                record.as_ref(),
                                PseudoExpr::FieldAccess { record, selector, .. }
                                    if selector.as_pretty_name() == "address"
                                        && matches!(record.as_ref(), PseudoExpr::Let { name, id, .. } if name == "tmp" && *id == Some(tmp_id))
                            )
                )
                && matches!(right.as_ref(), PseudoExpr::List { elements, .. } if elements.len() == 2)
        ),
        "binder-bearing fields receiver should not be cloned into a field-by-field expansion"
    );
    assert!(results.is_empty());
}

#[test]
fn test_finalize_unop_from_results_preserves_operand() {
    let mut results = vec![PseudoExpr::var("value")];

    let finalized = finalize_unop_from_results(&mut results, UnaryOp::Not);

    assert!(matches!(
        finalized,
        PseudoExpr::UnOp {
            op: UnaryOp::Not,
            ref operand,
        } if matches!(operand.as_ref(), PseudoExpr::Var { name, .. } if name == "value")
    ));
    assert!(results.is_empty());
}
