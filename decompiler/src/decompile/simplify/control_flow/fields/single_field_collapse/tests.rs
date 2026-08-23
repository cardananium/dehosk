use super::*;
use crate::decompile::ScriptVersion;

/// A sum-type constructor's single field resolves to the
/// schema's field name (`Purpose::Spending(out_ref)`).
#[test]
fn single_field_cardano_name_resolves_sum_constructor() {
    let subject_id = VarId::fresh_binding();
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.script_version = Some(ScriptVersion::PlutusV1);
    simplifier
        .context
        .context_field_names_by_id
        .insert(subject_id, "purpose".to_string());
    let name = simplifier.single_field_cardano_name("p", Some(subject_id), 1);
    assert_eq!(
        name.as_deref(),
        Some("output_reference"),
        "Purpose::Spending payload should be named `output_reference`"
    );
}

/// Unknown subject types yield `None`, so the caller keeps the
/// generic `field_0` name for user-defined ADTs.
#[test]
fn single_field_cardano_name_returns_none_for_unknown_subject() {
    let subject_id = VarId::fresh_binding();
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.script_version = Some(ScriptVersion::PlutusV3);
    // No context-tracking entry — subject is a user ADT.
    let name = simplifier.single_field_cardano_name("user_ty", Some(subject_id), 0);
    assert_eq!(
        name, None,
        "unknown subject types must yield None so caller falls back to field_N"
    );
}
