use super::*;

/// Every legacy parent-type name accepted by `context_field_at`
/// in `context.rs` must round-trip through [`ContextType`].
const CONTEXT_TYPE_DISPLAY_NAMES: &[&str] = &[
    "script_context",
    "tx_info",
    "tx_in_info",
    "tx_out",
    "tx_out_ref",
    "address",
    "interval",
    "lower_bound",
    "upper_bound",
    "proposal_procedure",
    "protocol_version",
    "rational",
    "constitution",
    "gov_action_id",
];

/// Every legacy sum-type name accepted by
/// `sum_type_constructor_names` / `sum_type_constructor_fields`
/// in `context.rs` must round-trip through [`SumTypeId`].
const SUM_TYPE_DISPLAY_NAMES: &[&str] = &[
    "purpose",
    "script_info",
    "credential",
    "output_datum",
    "interval_bound_type",
    "certificate",
    "voter",
    "drep",
    "governance_action",
    "vote",
    "bool",
    "staking_credential",
];

/// Every field name referenced by the positional field tables or
/// by `context_field_type` / `sum_type_constructor_fields` in
/// `context.rs` must round-trip through [`ContextField`].
const CONTEXT_FIELD_DISPLAY_NAMES: &[&str] = &[
    // ScriptContext
    "tx_info",
    "purpose",
    "redeemer",
    "script_info",
    // TxInfo
    "inputs",
    "reference_inputs",
    "outputs",
    "fee",
    "mint",
    "certificates",
    "withdrawals",
    "valid_range",
    "signatories",
    "redeemers",
    "datums",
    "transaction_id",
    "votes",
    "proposal_procedures",
    "current_treasury_amount",
    "treasury_donation",
    // TxInInfo
    "out_ref",
    "resolved",
    // TxOut
    "address",
    "value",
    "datum_hash",
    "datum",
    "reference_script",
    // TxOutRef
    "tx_id",
    "output_index",
    // Address
    "payment_credential",
    "stake_credential",
    // Interval
    "lower_bound",
    "upper_bound",
    "bound_type",
    "is_inclusive",
    // Fallback type-name fields
    "credential",
    "output_reference",
    // Constructor-introduced fields
    "policy_id",
    "index",
    "certificate",
    "voter",
    "proposal_procedure",
    "hash",
    // V3 ProposalProcedure field labels
    "deposit",
    "return_address",
    "governance_action",
    // V3 governance record field labels
    "major",
    "minor",
    "numerator",
    "denominator",
    // StakeCredential Pointer field labels
    "slot_number",
    "transaction_index",
    "certificate_index",
    // V1/V2 Certificate (DCert) payload labels
    "delegator",
    "delegatee",
    "pool_id",
    "vrf",
    "epoch",
    // V3 GovernanceAction payload labels
    "ancestor",
    "new_parameters",
    "guardrails",
    "new_version",
    "beneficiaries",
    "evicted_members",
    "added_members",
    "quorum",
    "constitution",
];

#[test]
fn context_type_round_trips_every_legacy_name() {
    for name in CONTEXT_TYPE_DISPLAY_NAMES {
        let parsed = ContextType::from_display_name(name)
            .unwrap_or_else(|| panic!("{name:?} must parse to a ContextType"));
        assert_eq!(
            parsed.display_name(),
            *name,
            "round-trip failed for {name:?}",
        );
    }
}

#[test]
fn sum_type_id_round_trips_every_legacy_name() {
    for name in SUM_TYPE_DISPLAY_NAMES {
        let parsed = SumTypeId::from_display_name(name)
            .unwrap_or_else(|| panic!("{name:?} must parse to a SumTypeId"));
        assert_eq!(
            parsed.display_name(),
            *name,
            "round-trip failed for {name:?}",
        );
    }
}

#[test]
fn context_field_round_trips_every_legacy_name() {
    for name in CONTEXT_FIELD_DISPLAY_NAMES {
        let parsed = ContextField::from_display_name(name)
            .unwrap_or_else(|| panic!("{name:?} must parse to a ContextField"));
        assert_eq!(
            parsed.display_name(),
            *name,
            "round-trip failed for {name:?}",
        );
    }
}

/// The two fields whose rendered name differs from the ledger's.
///
/// `uplc`'s `TxInfo` serialises them as `id` and `data`; the render
/// spells them `transaction_id` and `datums`, which say the same thing
/// without reading as a generic identifier or as the `Data` TYPE. The
/// ledger spelling still parses, so a persisted one resolves to the same
/// field.
#[test]
fn ledger_spellings_parse_to_the_same_fields() {
    for (ledger, rendered, field) in [
        ("id", "transaction_id", ContextField::Id),
        ("data", "datums", ContextField::Data),
    ] {
        assert_eq!(ContextField::from_display_name(ledger), Some(field));
        assert_eq!(ContextField::from_display_name(rendered), Some(field));
        assert_eq!(field.display_name(), rendered);
    }
}

#[test]
fn unknown_names_return_none() {
    for bogus in [
        "",
        "not_a_field",
        "ScriptContext",  // case-sensitive
        "txInfo",         // camelCase
        "script-context", // kebab-case
        "foo",
    ] {
        assert_eq!(
            ContextType::from_display_name(bogus),
            None,
            "ContextType accepted {bogus:?}",
        );
        assert_eq!(
            SumTypeId::from_display_name(bogus),
            None,
            "SumTypeId accepted {bogus:?}",
        );
        assert_eq!(
            ContextField::from_display_name(bogus),
            None,
            "ContextField accepted {bogus:?}",
        );
    }
}

#[test]
fn context_type_and_context_field_share_names_but_distinct_namespaces() {
    // Some legacy names exist as both a parent-type and a field
    // name (e.g. "tx_info" — the field on ScriptContext is of type
    // TxInfo). The typed enums intentionally keep these distinct.
    for shared in ["tx_info", "address", "lower_bound", "upper_bound"] {
        let ct = ContextType::from_display_name(shared).unwrap();
        let cf = ContextField::from_display_name(shared).unwrap();
        // The variant discriminants live in separate enums; equality
        // is only meaningful via the legacy-name string.
        assert_eq!(ct.display_name(), cf.display_name());
    }
}

#[test]
fn sum_type_id_and_context_field_share_names_but_distinct_namespaces() {
    // Similar: "certificate", "voter", "credential" are both sum
    // type names and constructor-field names.
    for shared in ["certificate", "voter", "credential"] {
        let sum = SumTypeId::from_display_name(shared).unwrap();
        let field = ContextField::from_display_name(shared).unwrap();
        assert_eq!(sum.display_name(), field.display_name());
    }
}

#[test]
fn field_type_ref_round_trips_context_type_names() {
    for name in CONTEXT_TYPE_DISPLAY_NAMES {
        let parsed = FieldTypeRef::from_display_name(name)
            .unwrap_or_else(|| panic!("{name:?} must parse to FieldTypeRef"));
        assert!(
            matches!(parsed, FieldTypeRef::Context(_)),
            "{name:?} should resolve as Context, got {parsed:?}",
        );
        assert_eq!(parsed.display_name(), *name);
    }
}

#[test]
fn field_type_ref_round_trips_sum_type_names() {
    // Names that exist *only* in the SumTypeId namespace (i.e. not
    // also accepted by ContextType::from_display_name).
    for name in [
        "purpose",
        "script_info",
        "credential",
        "output_datum",
        "interval_bound_type",
        "certificate",
        "voter",
        "drep",
        "governance_action",
        "vote",
        "bool",
        "staking_credential",
    ] {
        let parsed = FieldTypeRef::from_display_name(name)
            .unwrap_or_else(|| panic!("{name:?} must parse to FieldTypeRef"));
        assert!(
            matches!(parsed, FieldTypeRef::Sum(_)),
            "{name:?} should resolve as Sum, got {parsed:?}",
        );
        assert_eq!(parsed.display_name(), name);
    }
}

#[test]
fn field_type_ref_prefers_context_when_namespaces_collide() {
    // "lower_bound" / "upper_bound" exist in both namespaces — by
    // design, FieldTypeRef::from_display_name picks ContextType first.
    for shared in ["lower_bound", "upper_bound"] {
        let parsed = FieldTypeRef::from_display_name(shared).unwrap();
        assert!(matches!(parsed, FieldTypeRef::Context(_)));
    }
}

#[test]
fn field_type_ref_rejects_unknown_names() {
    for bogus in ["", "not_a_type", "TxInfo", "foo"] {
        assert_eq!(FieldTypeRef::from_display_name(bogus), None);
    }
}
