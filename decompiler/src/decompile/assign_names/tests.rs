use super::*;
use crate::pseudo::nameless::VarOrigin;

fn id() -> VarId {
    VarId::fresh_compat_placeholder()
}

fn insert(table: &mut VarTable, var_id: VarId, name: Option<&str>, kind: VarKind) {
    table.insert(
        var_id,
        VarMetadata {
            origin: VarOrigin::LetBinder,
            name_hint: name.map(String::from),
            display_name_hint: None,
            kind,
        },
    );
}

#[test]
fn field_index_alias_assigns_field_n() {
    let parent = id();
    let alias = id();
    let mut table = VarTable::new();
    insert(&mut table, parent, Some("ctx"), VarKind::User);
    insert(
        &mut table,
        alias,
        Some("whatever"),
        VarKind::FieldIndexAlias { parent, index: 3 },
    );

    let rewritten = assign_names(&mut table);
    assert_eq!(rewritten, 1);
    assert_eq!(
        table.get(alias).and_then(|m| m.render_name_hint()),
        Some("field_3")
    );
    assert_eq!(
        table.get(alias).and_then(|m| m.name_hint.as_deref()),
        Some("whatever"),
        "assign_names must preserve the original source hint"
    );
    // User binder's name is unchanged.
    assert_eq!(
        table.get(parent).and_then(|m| m.render_name_hint()),
        Some("ctx")
    );
}

#[test]
fn call_result_derives_from_callee_name() {
    let callee = id();
    let result = id();
    let mut table = VarTable::new();
    insert(
        &mut table,
        callee,
        Some("validate_signature"),
        VarKind::User,
    );
    insert(&mut table, result, None, VarKind::CallResult { callee });
    assign_names(&mut table);
    assert_eq!(
        table.get(result).and_then(|m| m.render_name_hint()),
        Some("validate_signature_result")
    );
}

#[test]
fn cardano_context_assigns_context_type() {
    let ctx = id();
    let mut table = VarTable::new();
    insert(
        &mut table,
        ctx,
        Some("y_25"),
        VarKind::CardanoContext {
            context_type: "script_context".to_string(),
        },
    );
    assign_names(&mut table);
    assert_eq!(
        table.get(ctx).and_then(|m| m.render_name_hint()),
        Some("script_context")
    );
    assert_eq!(
        table.get(ctx).and_then(|m| m.name_hint.as_deref()),
        Some("y_25")
    );
}

#[test]
fn data_literal_hoist_assigns_data_literal() {
    let lit = id();
    let mut table = VarTable::new();
    insert(&mut table, lit, None, VarKind::DataLiteralHoist);
    assign_names(&mut table);
    assert_eq!(
        table.get(lit).and_then(|m| m.render_name_hint()),
        Some("data_literal")
    );
}

#[test]
fn duplicate_names_are_deduplicated_with_suffixes() {
    // Two FieldIndexAlias entries with the same index get
    // `field_2` and `field_2_2`.
    let parent = id();
    let a = id();
    let b = id();
    let mut table = VarTable::new();
    insert(&mut table, parent, Some("ctx"), VarKind::User);
    insert(
        &mut table,
        a,
        None,
        VarKind::FieldIndexAlias { parent, index: 2 },
    );
    insert(
        &mut table,
        b,
        None,
        VarKind::FieldIndexAlias { parent, index: 2 },
    );
    assign_names(&mut table);
    let name_a = table
        .get(a)
        .and_then(|m| m.render_name_hint().map(str::to_string))
        .unwrap();
    let name_b = table
        .get(b)
        .and_then(|m| m.render_name_hint().map(str::to_string))
        .unwrap();
    assert_ne!(name_a, name_b);
    assert!(name_a == "field_2" || name_b == "field_2");
    assert!(name_a == "field_2_2" || name_b == "field_2_2");
}

#[test]
fn user_and_synthetic_kinds_keep_existing_names() {
    let a = id();
    let b = id();
    let mut table = VarTable::new();
    insert(&mut table, a, Some("x"), VarKind::User);
    insert(&mut table, b, Some("tmp_3"), VarKind::Synthetic);
    let rewritten = assign_names(&mut table);
    assert_eq!(rewritten, 0);
    assert_eq!(table.get(a).and_then(|m| m.render_name_hint()), Some("x"));
    assert_eq!(
        table.get(b).and_then(|m| m.render_name_hint()),
        Some("tmp_3")
    );
}

#[test]
fn constr_payload_assigns_item_n() {
    let payload = id();
    let mut table = VarTable::new();
    insert(
        &mut table,
        payload,
        None,
        VarKind::ConstrPayload {
            pattern_id: 7,
            index: 0,
        },
    );
    assign_names(&mut table);
    assert_eq!(
        table.get(payload).and_then(|m| m.render_name_hint()),
        Some("item_0")
    );
}

#[test]
fn slice_tail_alias_keeps_existing_name() {
    // Slice aliases get no canonical name here; the
    // binding is typically inlined before rendering
    // (`inline_slice_chain_nameless`), so the attached
    // hint stands.
    let parent = id();
    let alias = id();
    let mut table = VarTable::new();
    insert(&mut table, parent, Some("xs"), VarKind::User);
    insert(
        &mut table,
        alias,
        Some("some_slice"),
        VarKind::SliceTailAlias { parent, depth: 2 },
    );
    let _ = assign_names(&mut table);
    assert_eq!(
        table.get(alias).and_then(|m| m.render_name_hint()),
        Some("some_slice")
    );
}

#[test]
fn p4_2_cardano_context_late_binder_wins_canonical_name() {
    // Several `CardanoContext { tx_info }` entries can share a
    // context_type (simplifier-spawned intermediate aliases); the live
    // binder is the highest-VarId one. Descending-VarId allocation
    // gives it the canonical `tx_info`, and the dead intermediates take
    // suffixes that never surface in render. Ascending order would
    // label the live binder `tx_info_3`.
    let early = id();
    let middle = id();
    let late = id();
    let mut table = VarTable::new();
    let kind = VarKind::CardanoContext {
        context_type: "tx_info".to_string(),
    };
    insert(&mut table, early, None, kind.clone());
    insert(&mut table, middle, None, kind.clone());
    insert(&mut table, late, None, kind);
    assign_names(&mut table);
    assert_eq!(
        table.get(late).and_then(|m| m.render_name_hint()),
        Some("tx_info"),
        "highest-VarId CardanoContext entry must own the canonical name"
    );
    // The dead intermediates take suffixes (any order, but no `tx_info` clash).
    let early_name = table.get(early).and_then(|m| m.render_name_hint()).unwrap();
    let middle_name = table
        .get(middle)
        .and_then(|m| m.render_name_hint())
        .unwrap();
    assert_ne!(early_name, "tx_info");
    assert_ne!(middle_name, "tx_info");
    assert_ne!(early_name, middle_name);
    assert!(early_name.starts_with("tx_info_"));
    assert!(middle_name.starts_with("tx_info_"));
}

#[test]
fn p4_2_field_index_alias_dedup_order_unchanged() {
    // Non-CardanoContext kinds keep ascending-VarId dedup: two
    // FieldIndexAlias entries allocate lowest-VarId first.
    let parent = id();
    let a = id();
    let b = id();
    let mut table = VarTable::new();
    insert(&mut table, parent, Some("ctx"), VarKind::User);
    insert(
        &mut table,
        a,
        None,
        VarKind::FieldIndexAlias { parent, index: 1 },
    );
    insert(
        &mut table,
        b,
        None,
        VarKind::FieldIndexAlias { parent, index: 1 },
    );
    assign_names(&mut table);
    // Lower VarId (a) wins canonical, higher VarId (b) gets suffix —
    // ascending-VarId allocation for FieldIndexAlias.
    assert_eq!(
        table.get(a).and_then(|m| m.render_name_hint()),
        Some("field_1")
    );
    assert_eq!(
        table.get(b).and_then(|m| m.render_name_hint()),
        Some("field_1_2")
    );
}

/// The validator entry's `redeemer` (V1/V2 spend) param can pick up
/// `VarKind::CardanoContext` from a later pass when the body uses the
/// redeemer like a context (passes it to a helper that projects
/// `.tx_info`). Without special handling it collides with the real
/// `script_context` slot for the candidate name and one of the two is
/// suffixed to `script_context_2`, hiding the semantic `redeemer` slot.
/// `assign_names` preserves the existing hint when the binder origin is
/// a Lambda param AND the hint matches a protected validator-param name
/// (datum / redeemer / script_context).
#[test]
fn cardano_context_preserves_redeemer_display_hint_on_lambda_param() {
    let redeemer_id = id();
    let ctx_id = id();
    let mut table = VarTable::new();
    // `rename_validator_params_with_var_kinds` renamed the
    // redeemer slot (display_name_hint = "redeemer");
    // `cardano_context_naming` then tagged it `CardanoContext`
    // because the body uses it like a context.
    table.insert(
        redeemer_id,
        VarMetadata {
            origin: VarOrigin::UserBinder,
            name_hint: Some("v_17".to_string()),
            display_name_hint: Some("redeemer".to_string()),
            kind: VarKind::CardanoContext {
                context_type: "script_context".to_string(),
            },
        },
    );
    // The real script_context slot.
    table.insert(
        ctx_id,
        VarMetadata {
            origin: VarOrigin::UserBinder,
            name_hint: Some("v_18".to_string()),
            display_name_hint: Some("script_context".to_string()),
            kind: VarKind::CardanoContext {
                context_type: "script_context".to_string(),
            },
        },
    );
    assign_names(&mut table);
    // Both names preserved — redeemer NOT clobbered to `script_context_2`.
    assert_eq!(
        table.get(redeemer_id).and_then(|m| m.render_name_hint()),
        Some("redeemer")
    );
    assert_eq!(
        table.get(ctx_id).and_then(|m| m.render_name_hint()),
        Some("script_context")
    );
}

/// The protected-name guard must not shadow a user-level
/// `let datum = ...` binder: it fires only for Lambda-param
/// origins (UserBinder / LambdaParam), so a LetBinder named
/// "datum" that picks up CardanoContext is renamed normally.
#[test]
fn cardano_context_let_binder_named_datum_still_renamed() {
    let let_id = id();
    let mut table = VarTable::new();
    table.insert(
        let_id,
        VarMetadata {
            origin: VarOrigin::LetBinder,
            name_hint: Some("datum".to_string()),
            display_name_hint: Some("datum".to_string()),
            kind: VarKind::CardanoContext {
                context_type: "script_context".to_string(),
            },
        },
    );
    assign_names(&mut table);
    // Renamed to `script_context` — LetBinder origin doesn't get
    // the protected-name guard.
    assert_eq!(
        table.get(let_id).and_then(|m| m.render_name_hint()),
        Some("script_context")
    );
}

/// An AUTHORITATIVE `ValidatorEntryParam` (the TRUE entry, per the late
/// rename) claims the bare role name over a NON-authoritative
/// `ValidatorEntryParam` (a helper the early rename named with the same
/// role) — REGARDLESS of VarId.
///
/// VarId/fold-order is not a sound discriminator: helper collisions occur
/// in both directions — the entry's param sometimes has the higher VarId
/// than the helper's, sometimes the lower. The marker yields the same
/// "entry wins" result either way, which both loop iterations pin down.
#[test]
fn validator_entry_param_marker_wins_over_competitor_regardless_of_varid() {
    for entry_higher in [true, false] {
        // Allocate ids so the entry is higher- or lower-VarId than the
        // competitor depending on the case.
        let (entry_id, competitor_id) = if entry_higher {
            let competitor = id();
            let entry = id();
            (entry, competitor)
        } else {
            let entry = id();
            let competitor = id();
            (entry, competitor)
        };
        let mut table = VarTable::new();
        // The TRUE entry's redeemer param (authoritative). Its hint is
        // suffixed or bare depending on the case; either way the
        // candidate comes from the marker's `param_name`, not the hint.
        table.insert(
            entry_id,
            VarMetadata {
                origin: VarOrigin::UserBinder,
                name_hint: Some("v_entry".to_string()),
                display_name_hint: Some(
                    if entry_higher {
                        "redeemer_2"
                    } else {
                        "redeemer"
                    }
                    .to_string(),
                ),
                kind: VarKind::ValidatorEntryParam {
                    param_name: "redeemer".to_string(),
                    authoritative: true,
                },
            },
        );
        // A non-entry helper param the EARLY rename also named `redeemer`
        // (non-authoritative marker).
        table.insert(
            competitor_id,
            VarMetadata {
                origin: VarOrigin::UserBinder,
                name_hint: Some("v_helper".to_string()),
                display_name_hint: Some("redeemer".to_string()),
                kind: VarKind::ValidatorEntryParam {
                    param_name: "redeemer".to_string(),
                    authoritative: false,
                },
            },
        );
        assign_names(&mut table);
        assert_eq!(
            table.get(entry_id).and_then(|m| m.render_name_hint()),
            Some("redeemer"),
            "authoritative entry param must claim the bare role name (entry_higher={entry_higher})"
        );
        assert_eq!(
            table.get(competitor_id).and_then(|m| m.render_name_hint()),
            Some("redeemer_2"),
            "non-authoritative competitor must yield/suffix (entry_higher={entry_higher})"
        );
    }
}

/// A genuine user binding named exactly `redeemer` (kind `User` — what
/// `Let`/lambda binders actually get; lowering records them with
/// `VarOrigin::UserBinder`, NOT `LetBinder`) must NOT be demoted by the
/// entry-param mechanism. Only NON-authoritative `ValidatorEntryParam`
/// markers yield; `User` binders never do, so user code keeps its name
/// and the authoritative entry takes the fallback suffix instead.
#[test]
fn validator_entry_param_never_demotes_user_kind_binder() {
    let entry_id = id();
    let user_id = id();
    let mut table = VarTable::new();
    table.insert(
        entry_id,
        VarMetadata {
            origin: VarOrigin::UserBinder,
            name_hint: Some("v_entry".to_string()),
            display_name_hint: Some("redeemer_2".to_string()),
            kind: VarKind::ValidatorEntryParam {
                param_name: "redeemer".to_string(),
                authoritative: true,
            },
        },
    );
    // A genuine user binding named exactly `redeemer`, kind User.
    table.insert(
        user_id,
        VarMetadata {
            origin: VarOrigin::UserBinder,
            name_hint: Some("redeemer".to_string()),
            display_name_hint: Some("redeemer".to_string()),
            kind: VarKind::User,
        },
    );
    assign_names(&mut table);
    assert_eq!(
        table.get(user_id).and_then(|m| m.render_name_hint()),
        Some("redeemer"),
        "a kind-User binder named `redeemer` must never be demoted by the entry-param rule"
    );
}
