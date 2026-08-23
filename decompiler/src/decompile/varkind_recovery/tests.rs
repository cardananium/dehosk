use super::*;

fn legacy_predicate(name: &str) -> bool {
    name == "fields" || name == "item" || name.starts_with("fields_")
}

#[test]
fn use_varkind_off_dispatches_to_legacy_only() {
    let id = VarId::fresh_binding();
    let kinds: HashMap<VarId, VarKind> = HashMap::new();
    // legacy_predicate("item") is true, no kind annotation, but
    // use_varkind_recovery=false → legacy result.
    assert!(is_orphan_payload_ref_typed_or_legacy(
        "item",
        id,
        &kinds,
        false,
        legacy_predicate,
        "test",
    ));
    assert!(!is_orphan_payload_ref_typed_or_legacy(
        "x",
        id,
        &kinds,
        false,
        legacy_predicate,
        "test",
    ));
}

#[test]
fn typed_match_alone_returns_true() {
    let id = VarId::fresh_binding();
    let mut kinds: HashMap<VarId, VarKind> = HashMap::new();
    kinds.insert(id, VarKind::Synthetic);
    // legacy says no for "x", but typed (Synthetic) says yes.
    assert!(is_orphan_payload_ref_typed_or_legacy(
        "x",
        id,
        &kinds,
        true,
        legacy_predicate,
        "test",
    ));
}

#[test]
fn legacy_match_alone_returns_true() {
    let id = VarId::fresh_binding();
    let kinds: HashMap<VarId, VarKind> = HashMap::new();
    // Typed says no (no annotation), but legacy says yes.
    // Should still return true (strict-superset semantics).
    assert!(is_orphan_payload_ref_typed_or_legacy(
        "fields_3",
        id,
        &kinds,
        true,
        legacy_predicate,
        "test",
    ));
}

#[test]
fn neither_match_returns_false() {
    let id = VarId::fresh_binding();
    let kinds: HashMap<VarId, VarKind> = HashMap::new();
    assert!(!is_orphan_payload_ref_typed_or_legacy(
        "x",
        id,
        &kinds,
        true,
        legacy_predicate,
        "test",
    ));
}

#[test]
fn user_kind_alone_does_not_match_typed_path() {
    // The legacy predicate may still catch a User binder
    // through the OR, but the typed half must reject `User`
    // regardless of name.
    let id = VarId::fresh_binding();
    let mut kinds: HashMap<VarId, VarKind> = HashMap::new();
    kinds.insert(id, VarKind::User);
    // legacy says no for "x" with User kind → overall false.
    assert!(!is_orphan_payload_ref_typed_or_legacy(
        "x",
        id,
        &kinds,
        true,
        legacy_predicate,
        "test",
    ));
}

#[test]
fn callresult_kind_now_matches_typed_path() {
    // CallResult is auto-generated
    // (Simplifier mints `<callee>_result`-named binders), so the
    // typed path must catch a free CallResult ref even if the
    // legacy name predicate misses.
    let id = VarId::fresh_binding();
    let callee = VarId::fresh_binding();
    let mut kinds: HashMap<VarId, VarKind> = HashMap::new();
    kinds.insert(id, VarKind::CallResult { callee });
    // legacy says no for "anything" → typed path's CallResult
    // match should still flip overall to true.
    assert!(is_orphan_payload_ref_typed_or_legacy(
        "anything",
        id,
        &kinds,
        true,
        legacy_predicate,
        "test",
    ));
}

#[test]
fn is_auto_generated_kind_excludes_only_user() {
    let callee = VarId::fresh_binding();
    assert!(!is_auto_generated_kind(&VarKind::User));
    assert!(is_auto_generated_kind(&VarKind::Synthetic));
    assert!(is_auto_generated_kind(&VarKind::FieldIndexAlias {
        parent: callee,
        index: 0
    }));
    assert!(is_auto_generated_kind(&VarKind::SliceTailAlias {
        parent: callee,
        depth: 0
    }));
    assert!(is_auto_generated_kind(&VarKind::CallResult { callee }));
    assert!(is_auto_generated_kind(&VarKind::DataLiteralHoist));
    assert!(is_auto_generated_kind(&VarKind::ConstrPayload {
        pattern_id: 0,
        index: 0
    }));
}
