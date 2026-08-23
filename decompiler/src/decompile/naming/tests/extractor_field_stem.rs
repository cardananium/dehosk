//! Tests for `extractor_source_stem` recognising a
//! `PseudoExpr::FieldAccess` selector whose name is a
//! `ContextField`: the schema field becomes the rename stem
//! (`Data.un_int(tx_info.fee)` → `fee_int`). Anything else falls
//! back to the extractor's generic stem (`int_value`, `bytes`, …).

use super::*;
use crate::pseudo::ast::PBox;

fn temp_with_extractor(extractor: &str, source: PseudoExpr) -> (PseudoExpr, VarId) {
    let temp_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known(extractor),
            args: vec![source].into(),
        }),
        body: PBox::new(PseudoExpr::var_with_id("g", temp_id)),
    };
    (expr, temp_id)
}

#[test]
fn data_un_int_on_context_field_preserves_field_stem() {
    let (expr, temp_id) = temp_with_extractor(
        "Data.un_int",
        PseudoExpr::field_access(PseudoExpr::var("tx_info"), "fee".to_string()),
    );

    let hints = collect_extractor_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("fee_int"));
}

#[test]
fn data_un_bytearray_on_context_field_preserves_field_stem() {
    let (expr, temp_id) = temp_with_extractor(
        "Data.un_bytearray",
        PseudoExpr::field_access(PseudoExpr::var("tx_info"), "id".to_string()),
    );

    let hints = collect_extractor_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("id_bytes"));
}

#[test]
fn data_un_list_on_context_field_preserves_field_stem() {
    let (expr, temp_id) = temp_with_extractor(
        "Data.un_list",
        PseudoExpr::field_access(PseudoExpr::var("tx_info"), "inputs".to_string()),
    );

    let hints = collect_extractor_temp_display_name_hints(&expr);
    assert_eq!(
        hints.get(&temp_id).map(String::as_str),
        Some("inputs_items")
    );
}

#[test]
fn data_un_map_on_context_field_preserves_field_stem() {
    let (expr, temp_id) = temp_with_extractor(
        "Data.un_map",
        PseudoExpr::field_access(PseudoExpr::var("tx_info"), "withdrawals".to_string()),
    );

    let hints = collect_extractor_temp_display_name_hints(&expr);
    assert_eq!(
        hints.get(&temp_id).map(String::as_str),
        Some("withdrawals_pairs")
    );
}

#[test]
fn data_un_int_on_non_context_field_falls_back_to_generic_stem() {
    // `foo` is not a `ContextField`.
    let (expr, temp_id) = temp_with_extractor(
        "Data.un_int",
        PseudoExpr::field_access(PseudoExpr::var("payload"), "foo".to_string()),
    );

    let hints = collect_extractor_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("int_value"));
}

#[test]
fn data_un_int_on_pair_fst_still_uses_pair_stem() {
    // The pair-selector arm outranks the `ContextField` arm.
    let (expr, temp_id) = temp_with_extractor(
        "Data.un_int",
        PseudoExpr::field_access(PseudoExpr::var("entry"), "fst".to_string()),
    );

    let hints = collect_extractor_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("fst_int"));
}
