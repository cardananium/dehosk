//! Unit tests for `resolve_cardano_field_names` and
//! `resolve_data_{constr,case}`.

#![cfg(test)]

use crate::DecompileOptions;
use crate::ScriptVersion;
use crate::decompile::blueprint_registry::{BlueprintHintRegistry, DATA_TYPE_HINT_NAME};
use crate::decompile::cardano_context_naming::{
    propagate_types_and_name_constructors, resolve_cardano_field_names,
    resolve_cardano_field_names_with_var_kinds,
};
use crate::decompile::data_resolution::{resolve_data_case, resolve_data_constr};
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PVec;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

// resolve_cardano_field_names

fn assert_cardano_context_kind(
    annotations: &std::collections::HashMap<VarId, VarKind>,
    id: VarId,
    expected_context_type: &str,
) {
    match annotations.get(&id) {
        Some(VarKind::CardanoContext { context_type }) => {
            assert_eq!(context_type, expected_context_type);
        }
        other => panic!("expected CardanoContext annotation for {id:?}, got {other:?}"),
    }
}

#[test]
fn test_resolve_cardano_field_names_hash_index_on_script_context() {
    let expr = PseudoExpr::Lambda {
        params: vec!["datum".into(), "redeemer".into(), "script_context".into()],
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("script_context"),
            "#1".to_string(),
        )),
    };
    let result = resolve_cardano_field_names(expr, ScriptVersion::PlutusV2);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".tx_info"),
        "Expected .tx_info but got: {pretty}"
    );
    assert!(!pretty.contains(".#1"), "Expected no .#1 but got: {pretty}");
}

/// `resolve_cardano_field_names` must resolve a positional field-access
/// chain of ARBITRARY DEPTH rooted at `script_context`, threading the
/// inferred type through each level. Here a depth-4 chain
/// `script_context.#1.<valid_range>.#2.#1` must become
/// `script_context.tx_info.valid_range.upper_bound.bound_type` — exercising
/// ScriptContext -> TxInfo -> Interval -> UpperBound -> IntervalBoundType.
/// `valid_range_hash` is the 1-based `#N` for the `valid_range` slot, which
/// differs by version (TxInfo index 6 in V1, 7 in V2/V3).
fn assert_resolves_deep_field_chain(version: ScriptVersion, valid_range_hash: &str) {
    let body = PseudoExpr::field_access(
        PseudoExpr::field_access(
            PseudoExpr::field_access(
                PseudoExpr::field_access(PseudoExpr::var("script_context"), "#1".to_string()),
                valid_range_hash.to_string(),
            ),
            "#2".to_string(),
        ),
        "#1".to_string(),
    );
    let expr = PseudoExpr::Lambda {
        params: vec!["datum".into(), "redeemer".into(), "script_context".into()],
        body: PBox::new(body),
    };
    let pretty = resolve_cardano_field_names(expr, version).to_pretty();
    for field in [".tx_info", ".valid_range", ".upper_bound", ".bound_type"] {
        assert!(
            pretty.contains(field),
            "{version:?}: expected `{field}` in the resolved deep chain, got: {pretty}",
        );
    }
    assert!(
        !pretty.contains(".#"),
        "{version:?}: an unresolved positional accessor (`.#N`) remains: {pretty}",
    );
}

#[test]
fn resolves_script_context_field_chain_at_depth_v1() {
    // V1 TxInfo: valid_range is index 6 (no reference_inputs) → `#7`.
    assert_resolves_deep_field_chain(ScriptVersion::PlutusV1, "#7");
}

#[test]
fn resolves_script_context_field_chain_at_depth_v2() {
    // V2 TxInfo: valid_range is index 7 (reference_inputs at 1) → `#8`.
    assert_resolves_deep_field_chain(ScriptVersion::PlutusV2, "#8");
}

#[test]
fn resolves_script_context_field_chain_at_depth_v3() {
    // V3 TxInfo: valid_range is index 7 → `#8` (V3 prefix matches V2).
    assert_resolves_deep_field_chain(ScriptVersion::PlutusV3, "#8");
}

#[test]
fn test_resolve_cardano_field_names_hash_index_on_tx_info() {
    let expr = PseudoExpr::Lambda {
        params: vec!["datum".into(), "redeemer".into(), "script_context".into()],
        body: PBox::new(PseudoExpr::Let {
            name: "ctx".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("script_context"),
                "tx_info".to_string(),
            )),
            body: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("ctx"),
                "#1".to_string(),
            )),
        }),
    };
    let result = resolve_cardano_field_names(expr, ScriptVersion::PlutusV2);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".inputs"),
        "Expected .inputs but got: {pretty}"
    );
}

#[test]
fn test_resolve_cardano_field_names_fst_snd_on_script_context() {
    let expr = PseudoExpr::Lambda {
        params: vec!["datum".into(), "redeemer".into(), "script_context".into()],
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("script_context"),
            "fst".to_string(),
        )),
    };
    let result = resolve_cardano_field_names(expr, ScriptVersion::PlutusV2);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".tx_info"),
        "Expected .tx_info but got: {pretty}"
    );
}

#[test]
fn test_resolve_cardano_field_names_snd_on_script_context() {
    let expr = PseudoExpr::Lambda {
        params: vec!["datum".into(), "redeemer".into(), "script_context".into()],
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("script_context"),
            "snd".to_string(),
        )),
    };
    let result = resolve_cardano_field_names(expr, ScriptVersion::PlutusV2);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".purpose"),
        "Expected .purpose but got: {pretty}"
    );
}

#[test]
fn test_resolve_cardano_field_names_index_access() {
    let expr = PseudoExpr::Lambda {
        params: vec!["datum".into(), "redeemer".into(), "script_context".into()],
        body: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("script_context")),
            index: 0,
        }),
    };
    let result = resolve_cardano_field_names(expr, ScriptVersion::PlutusV2);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".tx_info"),
        "Expected .tx_info but got: {pretty}"
    );
}

#[test]
fn test_resolve_cardano_field_names_when_pattern_propagation() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let expr = PseudoExpr::Lambda {
        params: vec!["datum".into(), "redeemer".into(), "script_context".into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("script_context")),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 2),
                    vec!["field_0".into(), "field_1".into()],
                ),
                guard: None,
                body: PseudoExpr::field_access(PseudoExpr::var("field_0"), "#1".to_string()),
            }],
        }),
    };
    let result = resolve_cardano_field_names(expr, ScriptVersion::PlutusV2);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".inputs"),
        "Expected .inputs (tx_info field 0) but got: {pretty}"
    );
}

#[test]
fn test_resolve_cardano_field_names_no_change_for_non_context() {
    let expr = PseudoExpr::Lambda {
        params: vec!["x".into()],
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("x"),
            "#1".to_string(),
        )),
    };
    let result = resolve_cardano_field_names(expr, ScriptVersion::PlutusV2);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".#1"),
        "Expected .#1 to remain but got: {pretty}"
    );
}

#[test]
fn test_resolve_cardano_field_names_v3_single_param() {
    let expr = PseudoExpr::Lambda {
        params: vec!["script_context".into()],
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("script_context"),
            "#1".to_string(),
        )),
    };
    let result = resolve_cardano_field_names(expr, ScriptVersion::PlutusV3);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".tx_info"),
        "Expected .tx_info for V3 but got: {pretty}"
    );
}

#[test]
fn test_resolve_cardano_field_names_deep_propagation() {
    // Walks `script_context.tx_info` and then accesses an
    // `outputs` field. The propagator tracks `outputs` as
    // `list<tx_out>`, so deep propagation surfaces as the named
    // `tx.outputs` access rather than `.#N`.
    let expr = PseudoExpr::Lambda {
        params: vec!["datum".into(), "redeemer".into(), "script_context".into()],
        body: PBox::new(PseudoExpr::Let {
            name: "tx".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("script_context"),
                "tx_info".to_string(),
            )),
            body: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("tx"),
                "#3".to_string(), // V2 TxInfo field index 2 → outputs
            )),
        }),
    };
    let result = resolve_cardano_field_names(expr, ScriptVersion::PlutusV2);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".outputs"),
        "Expected .outputs (TxInfo index 2 for V2, surfaced via deep propagation) but got: {pretty}"
    );
}

/// `record_cardano_context_kind` skips the `redeemer` / `datum`
/// slots of a V1/V2 spend validator even when the body uses them
/// like a context: otherwise both `redeemer` and `script_context`
/// get CardanoContext-tagged with the same context type, collide
/// in `assign_names::candidate_name` dedup, and one is suffixed
/// `script_context_1`.
#[test]
fn record_cardano_context_kind_skips_redeemer_slot_named_binder() {
    let datum = Binder::new("datum", VarId::new(9800));
    let redeemer = Binder::new("redeemer", VarId::new(9801));
    let script_context = Binder::new("script_context", VarId::new(9802));
    // The body deliberately projects `.tx_info` on the REDEEMER
    // param: without the redeemer-slot skip that access pattern
    // would tag the redeemer binder `CardanoContext { context_type:
    // "script_context" }`.
    let expr = PseudoExpr::Lambda {
        params: vec![datum.clone(), redeemer.clone(), script_context.clone()],
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var_with_id("redeemer", redeemer.var_id()),
            "tx_info".to_string(),
        )),
    };
    let mut annotations = std::collections::HashMap::new();
    let _ =
        resolve_cardano_field_names_with_var_kinds(expr, ScriptVersion::PlutusV2, &mut annotations);

    // `redeemer` slot MUST NOT have a CardanoContext annotation:
    // with no entry, `assign_names` leaves the display name
    // `redeemer` alone.
    assert!(
        !annotations.contains_key(&redeemer.var_id()),
        "redeemer slot must NOT receive CardanoContext kind: {annotations:?}"
    );
    // `datum` slot likewise.
    assert!(
        !annotations.contains_key(&datum.var_id()),
        "datum slot must NOT receive CardanoContext kind: {annotations:?}"
    );
    // `script_context` SHOULD still be tagged (canonical site);
    // `resolve_cardano_field_names_records_let_alias_context_kind`
    // pins that case.
}

#[test]
fn resolve_cardano_field_names_records_let_alias_context_kind() {
    let script_context = Binder::new("script_context", VarId::new(9701));
    let tx_id = VarId::new(9702);
    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone()],
        body: PBox::new(PseudoExpr::Let {
            name: "tx".to_string(),
            id: Some(tx_id),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var_with_id("script_context", script_context.var_id()),
                "tx_info".to_string(),
            )),
            body: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var_with_id("tx", tx_id),
                "#1".to_string(),
            )),
        }),
    };
    let mut annotations = std::collections::HashMap::new();

    let result =
        resolve_cardano_field_names_with_var_kinds(expr, ScriptVersion::PlutusV2, &mut annotations);

    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".inputs"),
        "Expected .inputs through tx_info alias but got: {pretty}"
    );
    assert_cardano_context_kind(&annotations, script_context.var_id(), "script_context");
    assert_cardano_context_kind(&annotations, tx_id, "tx_info");
}

#[test]
fn resolve_cardano_field_names_records_when_pattern_context_kinds() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};

    let script_context = Binder::new("script_context", VarId::new(9703));
    let field_0 = Binder::new("field_0", VarId::new(9704));
    let field_1 = Binder::new("field_1", VarId::new(9705));
    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(
                "script_context",
                script_context.var_id(),
            )),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 2),
                    vec![field_0.clone(), field_1.clone()],
                ),
                guard: None,
                body: PseudoExpr::field_access(
                    PseudoExpr::var_with_id("field_0", field_0.var_id()),
                    "#1".to_string(),
                ),
            }],
        }),
    };
    let mut annotations = std::collections::HashMap::new();

    let result =
        resolve_cardano_field_names_with_var_kinds(expr, ScriptVersion::PlutusV2, &mut annotations);

    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".inputs"),
        "Expected .inputs (tx_info field 0) but got: {pretty}"
    );
    assert_cardano_context_kind(&annotations, field_0.var_id(), "tx_info");
    assert_cardano_context_kind(&annotations, field_1.var_id(), "purpose");
}

#[test]
fn test_resolve_cardano_field_names_does_not_leak_inner_lambda_shadowing() {
    let script_context = Binder::new("script_context", VarId::fresh_binding());
    let outer_ctx = Binder::new("ctx", VarId::fresh_binding());
    let inner_ctx_id = VarId::fresh_binding();

    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone(), outer_ctx.clone()],
        body: PBox::new(PseudoExpr::let_bind_with_id(
            "ignored",
            VarId::fresh_compat_placeholder(),
            PseudoExpr::lambda_with_binders(
                vec![],
                PseudoExpr::let_bind_with_id(
                    "ctx",
                    inner_ctx_id,
                    PseudoExpr::field_access(
                        PseudoExpr::var_with_id("script_context", script_context.var_id()),
                        "tx_info".to_string(),
                    ),
                    PseudoExpr::var_with_id("ctx", inner_ctx_id),
                ),
            ),
            PseudoExpr::field_access(
                PseudoExpr::var_with_id("ctx", outer_ctx.var_id()),
                "#1".to_string(),
            ),
        )),
    };

    let result = resolve_cardano_field_names(expr, ScriptVersion::PlutusV2);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".#1"),
        "outer ctx should stay unresolved; got: {pretty}"
    );
    assert!(
        !pretty.contains(".inputs"),
        "inner lambda-scoped ctx leaked into outer body: {pretty}"
    );
}

#[test]
fn test_resolve_cardano_field_names_does_not_leak_when_pattern_bindings_across_clauses() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};

    let script_context = Binder::new("script_context", VarId::fresh_binding());
    let outer_field_0 = Binder::new("field_0", VarId::fresh_binding());
    let clause_field_0 = Binder::new("field_0", VarId::fresh_binding());
    let clause_field_1 = Binder::new("field_1", VarId::fresh_binding());

    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone(), outer_field_0.clone()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(
                "script_context",
                script_context.var_id(),
            )),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::constructor(
                        ConstructorShape::unknown_data(0, 2),
                        vec![clause_field_0.clone(), clause_field_1.clone()],
                    ),
                    guard: None,
                    body: PseudoExpr::Int(0.into()),
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::field_access(
                        PseudoExpr::var_with_id("field_0", outer_field_0.var_id()),
                        "#1".to_string(),
                    ),
                },
            ],
        }),
    };

    let mut annotations = std::collections::HashMap::new();
    let result =
        resolve_cardano_field_names_with_var_kinds(expr, ScriptVersion::PlutusV2, &mut annotations);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".#1"),
        "outer field_0 should stay unresolved; got: {pretty}"
    );
    assert!(
        !pretty.contains(".inputs"),
        "pattern binder from an earlier clause leaked into a sibling clause: {pretty}"
    );
    assert_cardano_context_kind(&annotations, clause_field_0.var_id(), "tx_info");
    assert_cardano_context_kind(&annotations, clause_field_1.var_id(), "purpose");
    assert!(
        !annotations.contains_key(&outer_field_0.var_id()),
        "outer same-name field_0 should not inherit clause payload metadata"
    );
}

// List-combinator lambda param inference
//
// When `find` / `map` / `foldl` calls over a Cardano list are folded
// by `cardano_context_naming`, the lambda's element parameter is
// bound to the list's element type before the body is processed, so
// `.#N` / `.fst` / `.snd` inside the body resolve to named fields.

#[test]
fn list_combinator_find_lambda_param_bound_as_tx_in_info() {
    // find(script_context.tx_info.inputs, fn(input) { input.#2 })
    //   → input.resolved (TxInInfo schema is [OutRef, Resolved];
    //   `parse_hash_index` is 1-based so `.#2` → index 1 → `Resolved`).
    let script_context = Binder::new("script_context", VarId::fresh_binding());
    let input = Binder::new("input", VarId::fresh_binding());
    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone()],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("find")),
            args: vec![
                PseudoExpr::field_access(
                    PseudoExpr::field_access(
                        PseudoExpr::var_with_id("script_context", script_context.var_id()),
                        "tx_info".to_string(),
                    ),
                    "inputs".to_string(),
                ),
                PseudoExpr::Lambda {
                    params: vec![input.clone()],
                    body: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("input", input.var_id()),
                        "#2".to_string(),
                    )),
                },
            ]
            .into(),
        }),
    };
    let mut annotations = std::collections::HashMap::new();
    let result =
        resolve_cardano_field_names_with_var_kinds(expr, ScriptVersion::PlutusV2, &mut annotations);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".resolved"),
        "expected `input.resolved` inside find callback, got: {pretty}"
    );
    assert!(
        !pretty.contains("input.#2"),
        "raw `.#2` should be resolved inside find callback: {pretty}"
    );
    assert_cardano_context_kind(&annotations, input.var_id(), "tx_in_info");
}

#[test]
fn list_combinator_map_lambda_param_bound_as_tx_out() {
    // map(script_context.tx_info.outputs, fn(output) { output.#1 })
    //   → output.address (TxOut V2 schema: [Address, Value, Datum,
    //   ReferenceScript]; 1-based → `.#1` is `Address`).
    let script_context = Binder::new("script_context", VarId::fresh_binding());
    let output = Binder::new("output", VarId::fresh_binding());
    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone()],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("map")),
            args: vec![
                PseudoExpr::field_access(
                    PseudoExpr::field_access(
                        PseudoExpr::var_with_id("script_context", script_context.var_id()),
                        "tx_info".to_string(),
                    ),
                    "outputs".to_string(),
                ),
                PseudoExpr::Lambda {
                    params: vec![output.clone()],
                    body: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("output", output.var_id()),
                        "#1".to_string(),
                    )),
                },
            ]
            .into(),
        }),
    };
    let mut annotations = std::collections::HashMap::new();
    let result =
        resolve_cardano_field_names_with_var_kinds(expr, ScriptVersion::PlutusV2, &mut annotations);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".address"),
        "expected `output.address` inside map callback, got: {pretty}"
    );
    assert_cardano_context_kind(&annotations, output.var_id(), "tx_out");
}

#[test]
fn list_combinator_foldl_binds_first_param_as_element() {
    // foldl(inputs, init, fn(input, acc) { input.#1 })
    //   → element param (index 0) is bound as TxInInfo → input.out_ref
    //   (TxInInfo schema [OutRef, Resolved]; 1-based → `.#1` is OutRef).
    let script_context = Binder::new("script_context", VarId::fresh_binding());
    let input = Binder::new("input", VarId::fresh_binding());
    let acc = Binder::new("acc", VarId::fresh_binding());
    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone()],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("foldl")),
            args: vec![
                PseudoExpr::field_access(
                    PseudoExpr::field_access(
                        PseudoExpr::var_with_id("script_context", script_context.var_id()),
                        "tx_info".to_string(),
                    ),
                    "inputs".to_string(),
                ),
                PseudoExpr::int(0),
                PseudoExpr::Lambda {
                    params: vec![input.clone(), acc.clone()],
                    body: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("input", input.var_id()),
                        "#1".to_string(),
                    )),
                },
            ]
            .into(),
        }),
    };
    let mut annotations = std::collections::HashMap::new();
    let result =
        resolve_cardano_field_names_with_var_kinds(expr, ScriptVersion::PlutusV2, &mut annotations);
    let pretty = result.to_pretty();
    assert!(
        pretty.contains(".out_ref"),
        "expected `input.out_ref` inside foldl callback, got: {pretty}"
    );
    assert_cardano_context_kind(&annotations, input.var_id(), "tx_in_info");
    // The accumulator is *not* a list element — it must not pick up a
    // CardanoContext annotation from the inference path.
    assert!(
        !annotations.contains_key(&acc.var_id()),
        "accumulator must not be tagged as a Cardano context type"
    );
}

// resolve_data_case

#[test]
fn test_resolve_data_case_collapses_repeated_var_fallbacks() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};

    let constr_handler = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("c1")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::Int(1.into()),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::var("d")),
        ],
    };

    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.case"),
        args: vec![
            PseudoExpr::var("c1"),
            constr_handler.clone(),
            PseudoExpr::var("d"),
            PseudoExpr::var("d"),
            PseudoExpr::var("d"),
            PseudoExpr::var("d"),
        ]
        .into(),
    };

    let result = resolve_data_case(expr);
    match result {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(
                matches!(subject.as_ref(), PseudoExpr::Var { name, .. } if name == "c1"),
                "expected subject Var(c1), got {subject:?}"
            );
            assert_eq!(clauses.len(), 2);
            match &clauses[0].pattern {
                WhenPattern::Constructor { type_hint, tag, .. } => {
                    assert_eq!(*tag, 0);
                    assert_eq!(
                        type_hint.as_ref().map(|h| h.as_str()),
                        Some(DATA_TYPE_HINT_NAME)
                    );
                }
                other => panic!("expected Constructor, got {:?}", other),
            }
            assert_eq!(clauses[0].body, constr_handler);
            assert!(matches!(clauses[1].pattern, WhenPattern::Wildcard));
            assert!(
                matches!(&clauses[1].body, PseudoExpr::Var { name, .. } if name == "d"),
                "expected wildcard fallback Var(d), got {:?}",
                clauses[1].body
            );
        }
        other => panic!("expected When, got {:?}", other),
    }
}

#[test]
fn test_resolve_data_case_collapses_apply_form_with_repeated_var_fallbacks() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};

    let constr_handler = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("c1")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::Int(1.into()),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::var("d")),
        ],
    };

    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.case"),
            args: vec![].into(),
        }),
        args: vec![
            PseudoExpr::var("c1"),
            constr_handler.clone(),
            PseudoExpr::var("d"),
            PseudoExpr::var("d"),
            PseudoExpr::var("d"),
            PseudoExpr::var("d"),
        ]
        .into(),
    };

    let result = resolve_data_case(expr);
    match result {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(
                matches!(subject.as_ref(), PseudoExpr::Var { name, .. } if name == "c1"),
                "expected subject Var(c1), got {subject:?}"
            );
            assert_eq!(clauses.len(), 2);
            match &clauses[0].pattern {
                WhenPattern::Constructor { type_hint, tag, .. } => {
                    assert_eq!(*tag, 0);
                    assert_eq!(
                        type_hint.as_ref().map(|h| h.as_str()),
                        Some(DATA_TYPE_HINT_NAME)
                    );
                }
                other => panic!("expected Constructor, got {:?}", other),
            }
            assert_eq!(clauses[0].body, constr_handler);
            assert!(matches!(clauses[1].pattern, WhenPattern::Wildcard));
            assert!(
                matches!(&clauses[1].body, PseudoExpr::Var { name, .. } if name == "d"),
                "expected wildcard fallback Var(d), got {:?}",
                clauses[1].body
            );
        }
        other => panic!("expected When, got {:?}", other),
    }
}

#[test]
fn test_resolve_data_case_freshens_inserted_lambda_param_let_name() {
    use crate::pseudo::ast::{Binder, WhenPattern};

    let outer_payload_id = crate::pseudo::var_id::VarId::fresh_binding();
    let data_id = crate::pseudo::var_id::VarId::fresh_binding();
    let handler_payload_id = crate::pseudo::var_id::VarId::fresh_binding();
    let fallback = PseudoExpr::Constr {
        type_hint: None,
        tag: 2,
        fields: PVec::new(),
        shape: ConstructorShape::unknown_data(2, 0),
    };

    let expr = PseudoExpr::Let {
        name: "payload".to_string(),
        id: Some(outer_payload_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.case"),
            args: vec![
                PseudoExpr::var_with_id("data", data_id),
                PseudoExpr::Lambda {
                    params: vec![Binder::new("payload", handler_payload_id)],
                    body: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("payload", handler_payload_id),
                        "fields".to_string(),
                    )),
                },
                fallback.clone(),
                fallback.clone(),
                fallback.clone(),
                fallback,
            ]
            .into(),
        }),
    };

    let result = resolve_data_case(expr);
    let PseudoExpr::Let { name, body, .. } = result else {
        panic!("expected outer payload let");
    };
    assert_eq!(name, "payload");

    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected resolved Data.case when, got {body:?}");
    };
    assert!(matches!(
        clauses[0].pattern,
        WhenPattern::Constructor { tag: 0, .. }
    ));
    let PseudoExpr::Let {
        name,
        id,
        body: handler_body,
        ..
    } = &clauses[0].body
    else {
        panic!("expected handler payload let, got {:?}", clauses[0].body);
    };
    assert_eq!(name, "payload_2");
    assert_eq!(*id, Some(handler_payload_id));
    assert!(matches!(
        handler_body.as_ref(),
        PseudoExpr::FieldAccess { record, .. }
            if matches!(
                record.as_ref(),
                PseudoExpr::Var { name, id } if name == "payload_2" && *id == Some(handler_payload_id)
            )
    ));
}

#[test]
fn test_resolve_data_case_freshens_compat_body_ref_for_authoritative_param() {
    use crate::pseudo::ast::{Binder, WhenPattern};

    let outer_payload_id = crate::pseudo::var_id::VarId::fresh_binding();
    let data_id = crate::pseudo::var_id::VarId::fresh_binding();
    let handler_payload_id = crate::pseudo::var_id::VarId::fresh_binding();
    let fallback = PseudoExpr::Constr {
        type_hint: None,
        tag: 2,
        fields: PVec::new(),
        shape: ConstructorShape::unknown_data(2, 0),
    };

    let expr = PseudoExpr::Let {
        name: "payload".to_string(),
        id: Some(outer_payload_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.case"),
            args: vec![
                PseudoExpr::var_with_id("data", data_id),
                PseudoExpr::Lambda {
                    params: vec![Binder::new("payload", handler_payload_id)],
                    body: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::compat_var("payload"),
                        "fields".to_string(),
                    )),
                },
                fallback.clone(),
                fallback.clone(),
                fallback.clone(),
                fallback,
            ]
            .into(),
        }),
    };

    let result = resolve_data_case(expr);
    let PseudoExpr::Let { body, .. } = &result else {
        panic!("expected outer payload let, got {result:?}");
    };
    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected resolved Data.case when, got {body:?}");
    };
    assert!(matches!(
        clauses[0].pattern,
        WhenPattern::Constructor { tag: 0, .. }
    ));
    let PseudoExpr::Let {
        name,
        id,
        body: handler_body,
        ..
    } = &clauses[0].body
    else {
        panic!("expected handler payload let, got {:?}", clauses[0].body);
    };
    assert_eq!(name, "payload_2");
    assert_eq!(*id, Some(handler_payload_id));
    assert!(matches!(
        handler_body.as_ref(),
        PseudoExpr::FieldAccess { record, .. }
            if matches!(
                record.as_ref(),
                PseudoExpr::Var { name, id } if name == "payload_2" && id.get().is_none()
            )
    ));
}

#[test]
fn test_resolve_data_case_freshen_authoritative_param_skips_shadowed_compat_refs_but_renames_exact_refs()
 {
    use crate::pseudo::ast::{Binder, WhenPattern};

    let outer_payload_id = crate::pseudo::var_id::VarId::fresh_binding();
    let data_id = crate::pseudo::var_id::VarId::fresh_binding();
    let handler_payload_id = crate::pseudo::var_id::VarId::fresh_binding();
    let inner_payload_id = crate::pseudo::var_id::VarId::fresh_binding();
    let fallback = PseudoExpr::Constr {
        type_hint: None,
        tag: 2,
        fields: PVec::new(),
        shape: ConstructorShape::unknown_data(2, 0),
    };

    let expr = PseudoExpr::Let {
        name: "payload".to_string(),
        id: Some(outer_payload_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.case"),
            args: vec![
                PseudoExpr::var_with_id("data", data_id),
                PseudoExpr::Lambda {
                    params: vec![Binder::new("payload", handler_payload_id)],
                    body: PBox::new(PseudoExpr::Let {
                        name: "payload".to_string(),
                        id: Some(inner_payload_id),
                        value: PBox::new(PseudoExpr::int(1)),
                        body: PBox::new(PseudoExpr::Tuple(
                            vec![
                                PseudoExpr::field_access(
                                    PseudoExpr::compat_var("payload"),
                                    "fields".to_string(),
                                ),
                                PseudoExpr::field_access(
                                    PseudoExpr::var_with_id("payload", handler_payload_id),
                                    "fields".to_string(),
                                ),
                            ]
                            .into(),
                        )),
                    }),
                },
                fallback.clone(),
                fallback.clone(),
                fallback.clone(),
                fallback,
            ]
            .into(),
        }),
    };

    let result = resolve_data_case(expr);
    let PseudoExpr::Let { body, .. } = &result else {
        panic!("expected outer payload let, got {result:?}");
    };
    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected resolved Data.case when, got {body:?}");
    };
    assert!(matches!(
        clauses[0].pattern,
        WhenPattern::Constructor { tag: 0, .. }
    ));
    let PseudoExpr::Let {
        name,
        id,
        body: handler_body,
        ..
    } = &clauses[0].body
    else {
        panic!("expected handler payload let, got {:?}", clauses[0].body);
    };
    assert_eq!(name, "payload_2");
    assert_eq!(*id, Some(handler_payload_id));

    let PseudoExpr::Let {
        name,
        id,
        body: inner_body,
        ..
    } = handler_body.as_ref()
    else {
        panic!("expected nested payload let, got {handler_body:?}");
    };
    assert_eq!(name, "payload");
    assert_eq!(*id, Some(inner_payload_id));

    let PseudoExpr::Tuple(items) = inner_body.as_ref() else {
        panic!("expected nested tuple body, got {inner_body:?}");
    };
    let [compat_access, exact_access] = items.as_slice() else {
        panic!("expected compat and exact field accesses, got {items:?}");
    };
    assert!(
        matches!(
            compat_access,
            PseudoExpr::FieldAccess { record, selector }
                if selector.as_pretty_name() == "fields"
                    && matches!(
                        record.as_ref(),
                        PseudoExpr::Var { name, id }
                            if name == "payload" && id.get().is_none()
                    )
        ),
        "compat fallback under the nested payload let must stay shadowed, got {compat_access:?}"
    );
    assert!(
        matches!(
            exact_access,
            PseudoExpr::FieldAccess { record, selector }
                if selector.as_pretty_name() == "fields"
                    && matches!(
                        record.as_ref(),
                        PseudoExpr::Var { name, id }
                            if name == "payload_2" && *id == Some(handler_payload_id)
                    )
        ),
        "authoritative handler refs must still be renamed under a same-name foreign binder, got {exact_access:?}"
    );
}

#[test]
fn test_resolve_data_case_freshen_compat_param_skips_shadowed_same_name_refs() {
    use crate::pseudo::ast::{Binder, WhenPattern};

    let outer_payload_id = crate::pseudo::var_id::VarId::fresh_binding();
    let data_id = crate::pseudo::var_id::VarId::fresh_binding();
    let handler_payload_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let inner_payload_id = crate::pseudo::var_id::VarId::fresh_binding();
    let fallback = PseudoExpr::Constr {
        type_hint: None,
        tag: 2,
        fields: PVec::new(),
        shape: ConstructorShape::unknown_data(2, 0),
    };

    let expr = PseudoExpr::Let {
        name: "payload".to_string(),
        id: Some(outer_payload_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.case"),
            args: vec![
                PseudoExpr::var_with_id("data", data_id),
                PseudoExpr::Lambda {
                    params: vec![Binder::new("payload", handler_payload_id)],
                    body: PBox::new(PseudoExpr::Let {
                        name: "payload".to_string(),
                        id: Some(inner_payload_id),
                        value: PBox::new(PseudoExpr::int(1)),
                        body: PBox::new(PseudoExpr::var_with_id("payload", inner_payload_id)),
                    }),
                },
                fallback.clone(),
                fallback.clone(),
                fallback.clone(),
                fallback,
            ]
            .into(),
        }),
    };

    let result = resolve_data_case(expr);
    let PseudoExpr::Let { body, .. } = &result else {
        panic!("expected outer payload let, got {result:?}");
    };
    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected resolved Data.case when, got {body:?}");
    };
    assert!(matches!(
        clauses[0].pattern,
        WhenPattern::Constructor { tag: 0, .. }
    ));
    let PseudoExpr::Let {
        name,
        id,
        body: handler_body,
        ..
    } = &clauses[0].body
    else {
        panic!("expected handler payload let, got {:?}", clauses[0].body);
    };
    assert_eq!(name, "payload_2");
    assert_eq!(*id, Some(handler_payload_id));
    assert!(
        matches!(
            handler_body.as_ref(),
            PseudoExpr::Let { name, id, body, .. }
                if name == "payload"
                    && *id == Some(inner_payload_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Var { name, id, .. }
                            if name == "payload" && *id == Some(inner_payload_id)
                    )
        ),
        "freshening a compat handler param must not rename refs shadowed by an inner payload let, got {handler_body:?}"
    );

    let report =
        crate::decompile::name_orphan_audit::audit_id_orphans(&result, &[("data".into(), data_id)]);
    assert_eq!(
        report.stranded, 0,
        "Data.case freshening should not strand nested payload refs: {:?}",
        report.stranded_by_name
    );
}

#[test]
fn test_blueprint_hints_raw_is_none() {
    let opts = DecompileOptions::raw();
    assert!(opts.blueprint_hints.is_none());
}

// resolve_data_constr

#[test]
fn test_resolve_data_constr_literal_list() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::Int(0.into()),
            PseudoExpr::List {
                elements: vec![].into(),
                tail: None,
            },
        ]
        .into(),
    };
    let result = resolve_data_constr(expr);
    match result {
        PseudoExpr::Constr {
            tag, fields, shape, ..
        } => {
            assert_eq!(tag, 0);
            assert!(matches!(shape, ConstructorShape::Unknown { .. }));
            assert!(fields.is_empty());
        }
        other => panic!("Expected Constr, got: {:?}", other),
    }
}

#[test]
fn test_resolve_data_constr_with_fields() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::Int(1.into()),
            PseudoExpr::List {
                elements: vec![PseudoExpr::var("x")].into(),
                tail: None,
            },
        ]
        .into(),
    };
    let result = resolve_data_constr(expr);
    match result {
        PseudoExpr::Constr { tag, fields, .. } => {
            assert_eq!(tag, 1);
            assert_eq!(fields.len(), 1);
        }
        other => panic!("Expected Constr, got: {:?}", other),
    }
}

#[test]
fn test_resolve_data_constr_var_list() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![PseudoExpr::Int(0.into()), PseudoExpr::var("my_fields")].into(),
    };
    let result = resolve_data_constr(expr);
    match result {
        PseudoExpr::Constr { tag, fields, .. } => {
            assert_eq!(tag, 0);
            assert_eq!(fields.len(), 1);
            match &fields[0] {
                PseudoExpr::Var { name, .. } => assert_eq!(name, "my_fields"),
                other => panic!("Expected Var, got: {:?}", other),
            }
        }
        other => panic!("Expected Constr, got: {:?}", other),
    }
}

#[test]
fn test_resolve_data_constr_list_cons_chain() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::Int(0.into()),
            PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("List.cons"),
                args: vec![
                    PseudoExpr::var("a"),
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("List.cons"),
                        args: vec![
                            PseudoExpr::var("b"),
                            PseudoExpr::List {
                                elements: vec![].into(),
                                tail: None,
                            },
                        ]
                        .into(),
                    },
                ]
                .into(),
            },
        ]
        .into(),
    };
    let result = resolve_data_constr(expr);
    match result {
        PseudoExpr::Constr { tag, fields, .. } => {
            assert_eq!(tag, 0);
            assert_eq!(fields.len(), 2);
            assert!(matches!(fields[0], PseudoExpr::Var { ref name, .. } if name == "a"));
            assert!(matches!(fields[1], PseudoExpr::Var { ref name, .. } if name == "b"));
        }
        other => panic!("Expected Constr, got: {:?}", other),
    }
}

#[test]
fn test_resolve_data_constr_nested() {
    let inner = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::Int(1.into()),
            PseudoExpr::List {
                elements: vec![].into(),
                tail: None,
            },
        ]
        .into(),
    };
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::Int(0.into()),
            PseudoExpr::List {
                elements: vec![inner].into(),
                tail: None,
            },
        ]
        .into(),
    };
    let result = resolve_data_constr(expr);
    match result {
        PseudoExpr::Constr { tag: 0, fields, .. } => {
            assert_eq!(fields.len(), 1);
            match &fields[0] {
                PseudoExpr::Constr {
                    tag: 1,
                    fields: inner_fields,
                    ..
                } => {
                    assert!(inner_fields.is_empty());
                }
                other => panic!("Expected inner Constr, got: {:?}", other),
            }
        }
        other => panic!("Expected Constr, got: {:?}", other),
    }
}

#[test]
fn test_resolve_data_constr_preserves_other_builtins() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.to_int"),
        args: vec![PseudoExpr::var("x")].into(),
    };
    let result = resolve_data_constr(expr.clone());
    assert_eq!(result, expr);
}

#[test]
fn test_resolve_data_constr_in_let_body() {
    let expr = PseudoExpr::Let {
        name: "m".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.Constr"),
            args: vec![
                PseudoExpr::Int(1.into()),
                PseudoExpr::List {
                    elements: vec![].into(),
                    tail: None,
                },
            ]
            .into(),
        }),
        body: PBox::new(PseudoExpr::var("m")),
    };
    let result = resolve_data_constr(expr);
    match result {
        PseudoExpr::Let { value, .. } => match value.into_inner() {
            PseudoExpr::Constr { tag: 1, fields, .. } => {
                assert!(fields.is_empty());
            }
            other => panic!("Expected Constr in let value, got: {:?}", other),
        },
        other => panic!("Expected Let, got: {:?}", other),
    }
}

#[test]
fn test_resolve_data_constr_data_literal() {
    use crate::pseudo::ast::PseudoData;
    let expr = PseudoExpr::Data(Box::new(PseudoData::Constr(
        1,
        vec![PseudoData::Constr(0, vec![])],
    )));
    let result = resolve_data_constr(expr);
    match result {
        PseudoExpr::Constr { tag: 1, fields, .. } => {
            assert_eq!(fields.len(), 1);
            match &fields[0] {
                PseudoExpr::Constr {
                    tag: 0,
                    fields: inner,
                    ..
                } => {
                    assert!(inner.is_empty());
                }
                other => panic!("Expected inner Constr<0>, got: {:?}", other),
            }
        }
        other => panic!("Expected Constr<1>, got: {:?}", other),
    }
}

// propagate_types_and_name_constructors — scoping safety

#[test]
fn test_propagate_types_and_name_constructors_does_not_leak_inner_lambda_shadowing() {
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
    use crate::pseudo::var_id::VarId;

    let script_context = Binder::new("script_context", VarId::fresh_binding());
    let outer_purpose = Binder::new("purpose", VarId::fresh_binding());
    let inner_purpose_id = VarId::fresh_binding();

    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone(), outer_purpose.clone()],
        body: PBox::new(PseudoExpr::let_bind_with_id(
            "ignored",
            VarId::fresh_compat_placeholder(),
            PseudoExpr::lambda_with_binders(
                vec![],
                PseudoExpr::let_bind_with_id(
                    "purpose",
                    inner_purpose_id,
                    PseudoExpr::field_access(
                        PseudoExpr::var_with_id("script_context", script_context.var_id()),
                        "purpose".to_string(),
                    ),
                    PseudoExpr::var_with_id("purpose", inner_purpose_id),
                ),
            ),
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var_with_id("purpose", outer_purpose.var_id())),
                subject_name: None,
                clauses: vec![WhenClause {
                    pattern: WhenPattern::constructor(
                        ConstructorShape::unknown_data(0, 1),
                        vec![Binder::new("policy_id", VarId::fresh_binding())],
                    ),
                    guard: None,
                    body: PseudoExpr::Int(0.into()),
                }],
            },
        )),
    };

    let mut registry = BlueprintHintRegistry::new();
    let result =
        propagate_types_and_name_constructors(expr, ScriptVersion::PlutusV2, &mut registry);

    match result {
        PseudoExpr::Lambda { body, .. } => match body.into_inner() {
            PseudoExpr::Let { body, .. } => match body.into_inner() {
                PseudoExpr::When { clauses, .. } => match &clauses[0].pattern {
                    WhenPattern::Constructor {
                        type_hint, shape, ..
                    } => {
                        assert!(
                            type_hint.is_none(),
                            "inner lambda-scoped purpose leaked into outer when pattern"
                        );
                        assert!(
                            matches!(
                                shape,
                                ConstructorShape::Unknown {
                                    tag: 0,
                                    arity: 1,
                                    ..
                                }
                            ),
                            "expected outer purpose match to stay unresolved, got {shape:?}"
                        );
                    }
                    other => panic!("expected Constructor pattern, got: {other:?}"),
                },
                other => panic!("expected outer When, got: {other:?}"),
            },
            other => panic!("expected outer Let, got: {other:?}"),
        },
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn test_resolve_data_constr_data_with_map_stays() {
    use crate::pseudo::ast::PseudoData;
    let expr = PseudoExpr::Data(Box::new(PseudoData::Constr(
        0,
        vec![PseudoData::Map(vec![(
            PseudoData::Integer(1.into()),
            PseudoData::Integer(2.into()),
        )])],
    )));
    let result = resolve_data_constr(expr);
    assert!(matches!(result, PseudoExpr::Data(_)));
}

// list-element type tracking

#[test]
fn resolve_cardano_field_names_indexing_into_inputs_yields_tx_in_info_kind() {
    let script_context = Binder::new("script_context", VarId::new(9801));
    let tx = Binder::new("tx", VarId::new(9802));
    let inputs = Binder::new("inputs", VarId::new(9803));
    let first_input = Binder::new("first_input", VarId::new(9804));

    // fn(script_context) {
    //   let tx = script_context.tx_info
    //   let inputs = tx.inputs
    //   let first_input = inputs[0] // tx_in_info
    //   first_input.out_ref // tx_out_ref
    // }
    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone()],
        body: PBox::new(PseudoExpr::Let {
            name: "tx".to_string(),
            id: Some(tx.var_id()),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var_with_id("script_context", script_context.var_id()),
                "tx_info".to_string(),
            )),
            body: PBox::new(PseudoExpr::Let {
                name: "inputs".to_string(),
                id: Some(inputs.var_id()),
                value: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("tx", tx.var_id()),
                    "inputs".to_string(),
                )),
                body: PBox::new(PseudoExpr::Let {
                    name: "first_input".to_string(),
                    id: Some(first_input.var_id()),
                    value: PBox::new(PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::var_with_id("inputs", inputs.var_id())),
                        index: 0,
                    }),
                    body: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("first_input", first_input.var_id()),
                        "#1".to_string(),
                    )),
                }),
            }),
        }),
    };
    let mut annotations = std::collections::HashMap::new();
    let result =
        resolve_cardano_field_names_with_var_kinds(expr, ScriptVersion::PlutusV3, &mut annotations);
    let pretty = result.to_pretty();
    // first_input.#1 should resolve to .out_ref (TxInInfo field 0).
    assert!(
        pretty.contains(".out_ref"),
        "Expected .out_ref via list-element tx_in_info typing but got: {pretty}"
    );
    // first_input is tx_in_info (the singular element of List<TxInInfo>).
    assert_cardano_context_kind(&annotations, first_input.var_id(), "tx_in_info");
    // The list-typed binder itself (`inputs`) should NOT receive a
    // CardanoContext { context_type: "list<...>" } annotation since
    // that string is not a valid render name.
    assert!(
        !annotations.contains_key(&inputs.var_id()),
        "list-typed binder should not get a list<...> CardanoContext kind"
    );
}

#[test]
fn resolve_cardano_field_names_list_head_on_inputs_yields_tx_in_info() {
    let script_context = Binder::new("script_context", VarId::new(9811));
    let tx = Binder::new("tx", VarId::new(9812));
    let inputs = Binder::new("inputs", VarId::new(9813));
    let head_input = Binder::new("head_input", VarId::new(9814));

    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone()],
        body: PBox::new(PseudoExpr::Let {
            name: "tx".to_string(),
            id: Some(tx.var_id()),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var_with_id("script_context", script_context.var_id()),
                "tx_info".to_string(),
            )),
            body: PBox::new(PseudoExpr::Let {
                name: "inputs".to_string(),
                id: Some(inputs.var_id()),
                value: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("tx", tx.var_id()),
                    "inputs".to_string(),
                )),
                body: PBox::new(PseudoExpr::Let {
                    name: "head_input".to_string(),
                    id: Some(head_input.var_id()),
                    value: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::ListHead,
                        args: vec![PseudoExpr::var_with_id("inputs", inputs.var_id())].into(),
                    }),
                    body: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("head_input", head_input.var_id()),
                        "#2".to_string(),
                    )),
                }),
            }),
        }),
    };
    let mut annotations = std::collections::HashMap::new();
    let result =
        resolve_cardano_field_names_with_var_kinds(expr, ScriptVersion::PlutusV3, &mut annotations);
    let pretty = result.to_pretty();
    // .#2 on tx_in_info -> .resolved (field 1 = resolved : TxOut)
    assert!(
        pretty.contains(".resolved"),
        "Expected .resolved via List.head(inputs) typing but got: {pretty}"
    );
    assert_cardano_context_kind(&annotations, head_input.var_id(), "tx_in_info");
}

// Pair.fst / Pair.snd Cardano return typing

#[test]
fn resolve_cardano_field_names_pair_first_on_tx_in_info_yields_tx_out_ref() {
    let script_context = Binder::new("script_context", VarId::new(9821));
    let tx = Binder::new("tx", VarId::new(9822));
    let inputs = Binder::new("inputs", VarId::new(9823));
    let input = Binder::new("input", VarId::new(9824));
    let out_ref = Binder::new("out_ref", VarId::new(9825));

    let expr = PseudoExpr::Lambda {
        params: vec![script_context.clone()],
        body: PBox::new(PseudoExpr::Let {
            name: "tx".to_string(),
            id: Some(tx.var_id()),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var_with_id("script_context", script_context.var_id()),
                "tx_info".to_string(),
            )),
            body: PBox::new(PseudoExpr::Let {
                name: "inputs".to_string(),
                id: Some(inputs.var_id()),
                value: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("tx", tx.var_id()),
                    "inputs".to_string(),
                )),
                body: PBox::new(PseudoExpr::Let {
                    name: "input".to_string(),
                    id: Some(input.var_id()),
                    value: PBox::new(PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::var_with_id("inputs", inputs.var_id())),
                        index: 0,
                    }),
                    body: PBox::new(PseudoExpr::Let {
                        name: "out_ref".to_string(),
                        id: Some(out_ref.var_id()),
                        value: PBox::new(PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::PairFirst,
                            args: vec![PseudoExpr::var_with_id("input", input.var_id())].into(),
                        }),
                        body: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id("out_ref", out_ref.var_id()),
                            "#1".to_string(),
                        )),
                    }),
                }),
            }),
        }),
    };
    let mut annotations = std::collections::HashMap::new();
    let result =
        resolve_cardano_field_names_with_var_kinds(expr, ScriptVersion::PlutusV3, &mut annotations);
    let pretty = result.to_pretty();
    // out_ref.#1 on tx_out_ref -> .tx_id (TxOutRef field 0)
    assert!(
        pretty.contains(".tx_id"),
        "Expected .tx_id via Pair.first(input) typing but got: {pretty}"
    );
    assert_cardano_context_kind(&annotations, out_ref.var_id(), "tx_out_ref");
}
