use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::WhenClause;
use crate::pseudo::constructor::ConstructorShape;
use std::collections::{HashMap, HashSet};

// ---------------------------------------------------------------------------
// ScriptContext type-graph consistency — "fields at any depth"
//
// These tests walk the entire ScriptContext type graph from `ScriptContext`
// through records and sum payloads, for each Plutus version, asserting that
// every reachable record field and sum constructor is self-consistent: names
// round-trip, field types resolve, every reachable sum has constructor names
// for that version, and per-constructor field labels round-trip. The walk is
// transitive, so a broken edge, wrong name, or missing schema entry at any
// nesting depth fails here even when no fixture exercises that path.
// ---------------------------------------------------------------------------

/// Assert a `ContextField`'s legacy name round-trips through
/// `from_display_name`: the field-name <-> enum mapping is a bijection.
fn assert_field_roundtrips(version: ScriptVersion, field: ContextField) {
    assert_eq!(
        ContextField::from_display_name(field.display_name()),
        Some(field),
        "{version:?}: ContextField {field:?} (\"{}\") must round-trip",
        field.display_name(),
    );
}

fn assert_script_context_graph_consistent(
    version: ScriptVersion,
    // The sum type the top-level dispatch resolves to for this version
    // (`Purpose` for V1/V2, `ScriptInfo` for V3) — must be reachable.
    expected_dispatch_sum: SumTypeId,
) {
    let mut records_seen: HashSet<ContextType> = HashSet::new();
    let mut sums_seen: HashSet<SumTypeId> = HashSet::new();
    let mut record_queue: Vec<ContextType> = vec![ContextType::ScriptContext];
    let mut sum_queue: Vec<SumTypeId> = Vec::new();

    let push_type =
        |tref: CardanoTypeRef, rq: &mut Vec<ContextType>, sq: &mut Vec<SumTypeId>| match tref {
            CardanoTypeRef::Record(c)
            | CardanoTypeRef::ListOfRecords(c)
            | CardanoTypeRef::OptionOfRecord(c) => rq.push(c),
            CardanoTypeRef::Sum(s)
            | CardanoTypeRef::ListOfSums(s)
            | CardanoTypeRef::OptionOfSum(s)
            | CardanoTypeRef::MapKeyedBySum(s)
            | CardanoTypeRef::SumKeyedPair(s) => sq.push(s),
        };

    while !record_queue.is_empty() || !sum_queue.is_empty() {
        if let Some(ct) = record_queue.pop() {
            if !records_seen.insert(ct) {
                continue;
            }
            let mut idx = 0usize;
            let mut field_count = 0usize;
            while let Some(field) = context_field_at(ct, idx, version) {
                field_count += 1;
                assert_field_roundtrips(version, field);
                if let Some(tref) = context_field_type_full(field, version) {
                    push_type(tref, &mut record_queue, &mut sum_queue);
                }
                idx += 1;
            }
            assert!(
                field_count > 0,
                "{version:?}: record type {ct:?} has no positional fields",
            );
            continue;
        }

        let s = sum_queue.pop().expect("sum_queue non-empty");
        if !sums_seen.insert(s) {
            continue;
        }
        let names = sum_type_constructor_names(s, version);
        assert!(
            names.is_some(),
            "{version:?}: sum type {s:?} is reachable from ScriptContext but has no \
             constructor names for this version (a field points at a sum the schema \
             cannot name here)",
        );
        let names = names.unwrap();
        assert!(
            !names.is_empty(),
            "{version:?}: sum type {s:?} has an empty constructor list",
        );
        for (tag, _name) in names.iter().enumerate() {
            if let Some(fields) = sum_type_constructor_fields(s, tag, version) {
                for (cf, ftref) in fields {
                    assert_field_roundtrips(version, cf);
                    if let Some(ft) = ftref {
                        push_type(
                            CardanoTypeRef::from_field_type_ref(ft),
                            &mut record_queue,
                            &mut sum_queue,
                        );
                    }
                }
            }
        }
    }

    // All 9 record types are reachable from ScriptContext in every version.
    for ct in [
        ContextType::ScriptContext,
        ContextType::TxInfo,
        ContextType::TxInInfo,
        ContextType::TxOut,
        ContextType::TxOutRef,
        ContextType::Address,
        ContextType::Interval,
        ContextType::LowerBound,
        ContextType::UpperBound,
    ] {
        assert!(
            records_seen.contains(&ct),
            "{version:?}: record type {ct:?} is unreachable from ScriptContext",
        );
    }

    // Deep sums reachable in every version: Credential (Address.payment_credential),
    // IntervalBoundType (valid_range -> bounds -> bound_type), Certificate
    // (tx_info.certificates) — plus the version's dispatch sum.
    for s in [
        SumTypeId::Credential,
        SumTypeId::IntervalBoundType,
        SumTypeId::Certificate,
        expected_dispatch_sum,
    ] {
        assert!(
            sums_seen.contains(&s),
            "{version:?}: sum type {s:?} is unreachable from ScriptContext",
        );
    }
}

#[test]
fn script_context_type_graph_is_consistent_at_any_depth_v1() {
    assert_script_context_graph_consistent(ScriptVersion::PlutusV1, SumTypeId::Purpose);
}

#[test]
fn script_context_type_graph_is_consistent_at_any_depth_v2() {
    assert_script_context_graph_consistent(ScriptVersion::PlutusV2, SumTypeId::Purpose);
}

#[test]
fn script_context_type_graph_is_consistent_at_any_depth_v3() {
    assert_script_context_graph_consistent(ScriptVersion::PlutusV3, SumTypeId::ScriptInfo);
}

/// `sum_type_constructor_fields` and `sum_type_constructor_names`
/// must agree on which tags exist, for every sum and version; a table/name
/// mismatch either way desyncs the all-or-nothing arity gate.
#[test]
fn sum_type_names_and_fields_tables_agree() {
    let sums = [
        SumTypeId::Purpose,
        SumTypeId::ScriptInfo,
        SumTypeId::Credential,
        SumTypeId::OutputDatum,
        SumTypeId::IntervalBoundType,
        SumTypeId::Certificate,
        SumTypeId::Voter,
        SumTypeId::DRep,
        SumTypeId::GovernanceAction,
        SumTypeId::Vote,
        SumTypeId::Bool,
    ];
    for version in [
        ScriptVersion::PlutusV1,
        ScriptVersion::PlutusV2,
        ScriptVersion::PlutusV3,
    ] {
        for s in sums {
            let Some(names) = sum_type_constructor_names(s, version) else {
                continue;
            };
            for (tag, name) in names.iter().enumerate() {
                assert!(
                    !name.is_empty(),
                    "{version:?}: {s:?} tag {tag} has an empty constructor name",
                );
                if let Some(fields) = sum_type_constructor_fields(s, tag, version) {
                    for (cf, _) in fields {
                        assert_field_roundtrips(version, cf);
                    }
                }
            }
            // No field table may exist for a tag beyond the names list.
            assert!(
                sum_type_constructor_fields(s, names.len(), version).is_none(),
                "{version:?}: {s:?} has a field table at tag {} past its {} constructor names",
                names.len(),
                names.len(),
            );
        }
    }
}

#[test]
fn test_detect_sum_type_overrides_finds_single_non_fail_constructor() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("purpose")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::int(1),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::error()),
        ],
    };

    let overrides = detect_sum_type_overrides(
        &expr,
        ScriptVersion::PlutusV2,
        &HashMap::new(),
        &HashMap::new(),
    );

    assert_eq!(
        overrides.get("purpose"),
        Some(&vec!["policy_id".to_string()])
    );
}

/// Pin the typed entry table for every `(ContextType, version)` pair:
/// [`context_field_at`] returns the expected [`ContextField`]
/// at each index, and `None` out of range.
#[test]
fn context_field_at_typed_covers_entry_table() {
    let cases: &[(ContextType, ScriptVersion, &[&str])] = &[
        (
            ContextType::ScriptContext,
            ScriptVersion::PlutusV2,
            &["tx_info", "purpose"],
        ),
        (
            ContextType::ScriptContext,
            ScriptVersion::PlutusV3,
            &["tx_info", "redeemer", "script_info"],
        ),
        (
            ContextType::TxInInfo,
            ScriptVersion::PlutusV3,
            &["out_ref", "resolved"],
        ),
        (
            ContextType::TxOut,
            ScriptVersion::PlutusV1,
            &["address", "value", "datum_hash"],
        ),
        (
            ContextType::TxOut,
            ScriptVersion::PlutusV3,
            &["address", "value", "datum", "reference_script"],
        ),
        (
            ContextType::Address,
            ScriptVersion::PlutusV3,
            &["payment_credential", "stake_credential"],
        ),
        (
            ContextType::Interval,
            ScriptVersion::PlutusV3,
            &["lower_bound", "upper_bound"],
        ),
        (
            ContextType::LowerBound,
            ScriptVersion::PlutusV3,
            &["bound_type", "is_inclusive"],
        ),
    ];
    for (parent, version, expected) in cases {
        for (i, name) in expected.iter().enumerate() {
            let typed = context_field_at(*parent, i, *version)
                .unwrap_or_else(|| panic!("typed lookup missing for {parent:?}.{i}"));
            assert_eq!(typed.display_name(), *name);
        }
        assert_eq!(
            context_field_at(*parent, expected.len(), *version),
            None,
            "out-of-range typed lookup must return None for {parent:?}",
        );
    }
}

/// Every `(ContextField → FieldTypeRef)` entry must round-trip through
/// [`context_field_type_from_display_name`]: the field name yields a
/// [`FieldTypeRef`] whose display name is that type.
///
/// Each case also declares the versions the field EXISTS at, and the
/// lookup must fail closed at the others — a name that has no slot at a
/// version must not hand back a type for it.
#[test]
fn context_field_type_covers_every_display_name() {
    use ScriptVersion::{PlutusV1, PlutusV2, PlutusV3};
    const ALL: &[ScriptVersion] = &[PlutusV1, PlutusV2, PlutusV3];
    let cases: &[(&str, &str, &[ScriptVersion])] = &[
        ("inputs", "tx_in_info", ALL),
        ("reference_inputs", "tx_in_info", &[PlutusV2, PlutusV3]),
        ("outputs", "tx_out", ALL),
        ("valid_range", "interval", ALL),
        ("out_ref", "tx_out_ref", ALL),
        ("resolved", "tx_out", ALL),
        ("output_reference", "tx_out_ref", ALL),
        ("address", "address", ALL),
        ("lower_bound", "lower_bound", ALL),
        ("upper_bound", "upper_bound", ALL),
        ("payment_credential", "credential", ALL),
        // `stake_credential` is deliberately absent — `FieldTypeRef` cannot
        // express its `Option<StakeCredential>` type, so
        // `context_field_type` returns `None` for it.
        //
        // `credential` IS version-invariant: at V1/V2 the name covers both an
        // Inline-wrapped StakeCredential (`Purpose::Rewarding`) and a plain
        // Credential (`StakeCredential::Inline`), so the depth follows the
        // parent and only `sum_type_constructor_fields` can settle it.
        ("credential", "credential", ALL),
        ("bound_type", "interval_bound_type", ALL),
        // V3 swapped `ScriptContext.purpose` for `script_info`.
        ("purpose", "purpose", &[PlutusV1, PlutusV2]),
        ("script_info", "script_info", &[PlutusV3]),
        ("tx_info", "tx_info", ALL),
        // `TxOut.datum : OutputDatum` arrives with V2; V1 carries a
        // `datum_hash` instead and has no `OutputDatum` sum.
        ("datum", "output_datum", &[PlutusV2, PlutusV3]),
        ("governance_action", "governance_action", &[PlutusV3]),
    ];
    for (field_name, expected_type, live) in cases {
        let field = ContextField::from_display_name(field_name)
            .unwrap_or_else(|| panic!("ContextField missing for {field_name:?}"));
        for version in ALL {
            let typed = context_field_type(field, *version);
            let via_name = context_field_type_from_display_name(field_name, *version);
            if live.contains(version) {
                let typed = typed.unwrap_or_else(|| {
                    panic!("typed lookup missing for {field_name:?} {version:?}")
                });
                assert_eq!(typed.display_name(), *expected_type);
                let via_name = via_name.unwrap_or_else(|| {
                    panic!("name bridge missing for {field_name:?} {version:?}")
                });
                assert_eq!(via_name.display_name(), *expected_type);
            } else {
                assert_eq!(
                    typed, None,
                    "{field_name:?} has no slot at {version:?} and must not type",
                );
                assert_eq!(
                    via_name, None,
                    "{field_name:?} has no slot at {version:?}; the name bridge must fail closed",
                );
            }
        }
    }
}

/// Echo-identity inputs (`tx_in_info`/`tx_out`/`tx_out_ref`) aren't
/// field names but reach [`context_field_type_from_display_name`]
/// when `cardano_context_naming` recurses after resolving a field's
/// static type; they must echo the matching [`ContextType`].
#[test]
fn context_field_type_from_legacy_name_echoes_type_shaped_inputs() {
    let cases: &[(&str, ContextType)] = &[
        ("tx_in_info", ContextType::TxInInfo),
        ("tx_out", ContextType::TxOut),
        ("tx_out_ref", ContextType::TxOutRef),
    ];
    for (name, expected) in cases {
        assert_eq!(
            context_field_type_from_display_name(name, ScriptVersion::PlutusV3),
            Some(FieldTypeRef::Context(*expected)),
        );
    }
}

#[test]
fn context_field_type_from_legacy_name_returns_none_for_unknown() {
    assert_eq!(
        context_field_type_from_display_name("not_a_field", ScriptVersion::PlutusV3),
        None,
    );
}

#[test]
fn context_element_type_name_typed_resolves_element_types() {
    assert_eq!(
        context_element_type_name(ContextType::TxInInfo),
        Some("input"),
    );
    assert_eq!(
        context_element_type_name(ContextType::TxOut),
        Some("output"),
    );
    // Element types outside the {TxInInfo, TxOut} pair return None.
    assert_eq!(context_element_type_name(ContextType::TxInfo), None);
}

/// Probes pinning the typed constructor-name table for a handful of
/// (sum_type, version) pairs.
#[test]
fn sum_type_constructor_names_typed_covers_versioned_tables() {
    let cases: &[(SumTypeId, ScriptVersion, Option<&[&str]>)] = &[
        (
            SumTypeId::Purpose,
            ScriptVersion::PlutusV2,
            Some(&["Minting", "Spending", "Rewarding", "Certifying"]),
        ),
        (SumTypeId::Purpose, ScriptVersion::PlutusV3, None),
        (
            SumTypeId::ScriptInfo,
            ScriptVersion::PlutusV3,
            Some(&[
                "Minting",
                "Spending",
                "Rewarding",
                "Certifying",
                "Voting",
                "Proposing",
            ]),
        ),
        (SumTypeId::ScriptInfo, ScriptVersion::PlutusV2, None),
        (
            SumTypeId::OutputDatum,
            ScriptVersion::PlutusV2,
            Some(&["NoDatum", "DatumHash", "InlineDatum"]),
        ),
        (SumTypeId::OutputDatum, ScriptVersion::PlutusV1, None),
        (
            SumTypeId::Bool,
            ScriptVersion::PlutusV3,
            Some(&["False", "True"]),
        ),
    ];
    for (parent, version, expected) in cases {
        assert_eq!(
            sum_type_constructor_names(*parent, *version),
            *expected,
            "typed mismatch for {parent:?} @ {version:?}",
        );
    }
}

/// Pin the typed mixed-shape table — `sum_type_constructor_fields`;
/// `output_reference` carries a `Some(tx_out_ref)` hint exercising
/// the [`FieldTypeRef`] plumbing.
#[test]
fn sum_type_constructor_fields_typed_covers_mixed_shape_table() {
    let typed_v3_spending =
        sum_type_constructor_fields(SumTypeId::ScriptInfo, 1, ScriptVersion::PlutusV3)
            .expect("ScriptInfo.Spending must have fields");
    assert_eq!(typed_v3_spending.len(), 2);
    assert_eq!(typed_v3_spending[0].0, ContextField::OutputReference);
    assert_eq!(
        typed_v3_spending[0].1,
        Some(FieldTypeRef::Context(ContextType::TxOutRef)),
    );
    assert_eq!(typed_v3_spending[1], (ContextField::Datum, None));

    assert_eq!(
        sum_type_constructor_fields(SumTypeId::Purpose, 3, ScriptVersion::PlutusV2,),
        Some(vec![(
            ContextField::Certificate,
            Some(FieldTypeRef::Sum(SumTypeId::Certificate)),
        )]),
    );
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::Credential, 0, ScriptVersion::PlutusV3),
        Some(vec![(ContextField::Hash, None)]),
    );
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::Credential, 1, ScriptVersion::PlutusV3,),
        Some(vec![(ContextField::Hash, None)]),
    );
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::IntervalBoundType, 1, ScriptVersion::PlutusV3,),
        Some(vec![(ContextField::Value, None)]),
    );
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::IntervalBoundType, 0, ScriptVersion::PlutusV3,),
        None,
    );
}

/// Pin the V3 `GovernanceAction` arity table (Plutus V3 `GovernanceAction`,
/// stdlib `cardano/governance`). Every constructor's Data arity
/// equals its surface arity, so all 7 tags are tabled; pre-V3 `None`.
#[test]
fn sum_type_constructor_fields_typed_covers_governance_action_v3() {
    use ContextField as F;
    let v3 = ScriptVersion::PlutusV3;
    let g = SumTypeId::GovernanceAction;
    // ProtocolParameters — 3 fields.
    assert_eq!(
        sum_type_constructor_fields(g, 0, v3),
        Some(vec![
            (F::Ancestor, None),
            (F::NewParameters, None),
            (F::Guardrails, None),
        ]),
    );
    // HardFork — 2 fields.
    assert_eq!(
        sum_type_constructor_fields(g, 1, v3),
        Some(vec![
            (F::Ancestor, None),
            (
                F::NewVersion,
                Some(FieldTypeRef::Context(ContextType::ProtocolVersion))
            ),
        ]),
    );
    // TreasuryWithdrawal — 2 fields. beneficiaries is a Map(Credential,Int);
    // `FieldTypeRef` cannot express a map, so it stays `None`.
    assert_eq!(
        sum_type_constructor_fields(g, 2, v3),
        Some(vec![(F::Beneficiaries, None), (F::Guardrails, None)]),
    );
    // NoConfidence — 1 field.
    assert_eq!(
        sum_type_constructor_fields(g, 3, v3),
        Some(vec![(F::Ancestor, None)]),
    );
    // ConstitutionalCommittee — 4 fields.
    assert_eq!(
        sum_type_constructor_fields(g, 4, v3),
        Some(vec![
            (F::Ancestor, None),
            (F::EvictedMembers, None),
            (F::AddedMembers, None),
            (
                F::Quorum,
                Some(FieldTypeRef::Context(ContextType::RationalNumber))
            ),
        ]),
    );
    // NewConstitution — 2 fields.
    assert_eq!(
        sum_type_constructor_fields(g, 5, v3),
        Some(vec![
            (F::Ancestor, None),
            (
                F::Constitution,
                Some(FieldTypeRef::Context(ContextType::Constitution))
            ),
        ]),
    );
    // NicePoll — nullary (Some(vec![]), NOT None).
    assert_eq!(sum_type_constructor_fields(g, 6, v3), Some(vec![]));
    // Tag past the constructor list → None.
    assert_eq!(sum_type_constructor_fields(g, 7, v3), None);
    // Arities match the names table length (7 constructors).
    let names = sum_type_constructor_names(g, v3).expect("V3 names present");
    assert_eq!(names.len(), 7);
    // Pre-V3 the sum is absent.
    assert_eq!(
        sum_type_constructor_fields(g, 0, ScriptVersion::PlutusV1),
        None
    );
    assert_eq!(
        sum_type_constructor_fields(g, 0, ScriptVersion::PlutusV2),
        None
    );
}

/// Sum-keyed map fields: withdrawals (Credential V3 / StakeCredential V2),
/// votes (Voter V3). The key sum is chainable via the entry's `.1st`.
#[test]
fn sum_keyed_map_field_refs() {
    use CardanoTypeRef as R;
    assert_eq!(
        context_field_type_full(ContextField::Withdrawals, ScriptVersion::PlutusV3),
        Some(R::MapKeyedBySum(SumTypeId::Credential)),
    );
    assert_eq!(
        context_field_type_full(ContextField::Withdrawals, ScriptVersion::PlutusV2),
        Some(R::MapKeyedBySum(SumTypeId::StakeCredential)),
        "V2: withdrawals is a Data map keyed by an Inline-wrapped StakeCredential",
    );
    // V1 `withdrawals` is `[(StakingCredential, Integer)]` — a LIST of
    // `Constr 0 [key, amount]`, not a map. It must NOT claim a map (there is no
    // builtin pair for `.1st` to project); it is a list of record entries whose
    // key sits at `.fields[0]`.
    assert_eq!(
        context_field_type_full(ContextField::Withdrawals, ScriptVersion::PlutusV1),
        Some(R::ListOfRecords(ContextType::WithdrawalEntry)),
    );
    assert_eq!(
        context_field_type_full(ContextField::Votes, ScriptVersion::PlutusV3),
        Some(R::MapKeyedBySum(SumTypeId::Voter)),
    );
    assert_eq!(
        context_field_type_full(ContextField::Votes, ScriptVersion::PlutusV1),
        None
    );
    // The map element is a key-sum pair; `.1st` projects the key sum.
    assert_eq!(
        R::MapKeyedBySum(SumTypeId::Credential).element_type(),
        Some(R::SumKeyedPair(SumTypeId::Credential)),
    );
    assert_eq!(
        R::SumKeyedPair(SumTypeId::Credential).pair_first_sum(),
        Some(SumTypeId::Credential),
    );
    assert_eq!(R::Sum(SumTypeId::Credential).pair_first_sum(), None);
    // The rendered names keep their map/pair prefix.
    assert_eq!(
        R::MapKeyedBySum(SumTypeId::Voter).display_name(),
        "map<voter>"
    );
    assert_eq!(
        R::SumKeyedPair(SumTypeId::Credential).display_name(),
        "pair<credential>"
    );
}

/// `stake_credential` is `Option<StakeCredential>`: typed via
/// `context_field_type_full` as `OptionOfSum(StakeCredential)`, and not via
/// `context_field_type` — `FieldTypeRef` cannot carry an Option.
#[test]
fn stake_credential_is_option_typed() {
    let v3 = ScriptVersion::PlutusV3;
    assert_eq!(
        context_field_type(ContextField::StakeCredential, v3),
        None,
        "stake_credential must NOT type as a bare FieldTypeRef (it is Option-wrapped)",
    );
    assert_eq!(
        context_field_type_full(ContextField::StakeCredential, v3),
        Some(CardanoTypeRef::OptionOfSum(SumTypeId::StakeCredential)),
    );
    // payment_credential stays a plain Credential.
    assert_eq!(
        context_field_type_full(ContextField::PaymentCredential, v3),
        Some(CardanoTypeRef::Sum(SumTypeId::Credential)),
    );
}

/// ABI PIN — the `StakeCredential` (Referenced) field table: Inline chains to
/// Credential; Pointer is 3 Int leaves. Version-invariant.
#[test]
fn sum_type_constructor_fields_typed_stake_credential() {
    use ContextField as F;
    for v in [
        ScriptVersion::PlutusV1,
        ScriptVersion::PlutusV2,
        ScriptVersion::PlutusV3,
    ] {
        assert_eq!(
            sum_type_constructor_fields(SumTypeId::StakeCredential, 0, v),
            Some(vec![(
                F::Credential,
                Some(FieldTypeRef::Sum(SumTypeId::Credential))
            )]),
            "{v:?}: Inline → Credential",
        );
        assert_eq!(
            sum_type_constructor_fields(SumTypeId::StakeCredential, 1, v),
            Some(vec![
                (F::SlotNumber, None),
                (F::TransactionIndex, None),
                (F::CertificateIndex, None),
            ]),
            "{v:?}: Pointer → 3 Int leaves",
        );
        assert_eq!(
            sum_type_constructor_fields(SumTypeId::StakeCredential, 2, v),
            None
        );
    }
}

/// V1/V2 Purpose.Rewarding + Certificate.delegator chain to the
/// Inline-wrapped StakeCredential sum, not a bare Credential (wrong depth).
#[test]
fn v1_v2_wrapped_credential_chains_to_stake_credential() {
    let sc = Some(FieldTypeRef::Sum(SumTypeId::StakeCredential));
    for v in [ScriptVersion::PlutusV1, ScriptVersion::PlutusV2] {
        assert_eq!(
            sum_type_constructor_fields(SumTypeId::Purpose, 2, v),
            Some(vec![(ContextField::Credential, sc)]),
            "{v:?}: Rewarding → StakeCredential",
        );
        assert_eq!(
            sum_type_constructor_fields(SumTypeId::Certificate, 0, v),
            Some(vec![(ContextField::Delegator, sc)]),
        );
        assert_eq!(
            sum_type_constructor_fields(SumTypeId::Certificate, 2, v),
            Some(vec![
                (ContextField::Delegator, sc),
                (ContextField::Delegatee, None)
            ]),
        );
    }
}

/// ABI PIN — the `OutputDatum` field table (NoDatum nullary / DatumHash /
/// InlineDatum), V2/V3-only. NoDatum MUST be `Some(vec![])` (arity 0), not
/// `None`, so `known_ctor_arity` reports a true nullary.
#[test]
fn sum_type_constructor_fields_typed_output_datum() {
    use ContextField as F;
    for v in [ScriptVersion::PlutusV2, ScriptVersion::PlutusV3] {
        assert_eq!(
            sum_type_constructor_fields(SumTypeId::OutputDatum, 0, v),
            Some(vec![])
        );
        assert_eq!(
            sum_type_constructor_fields(SumTypeId::OutputDatum, 1, v),
            Some(vec![(F::Hash, None)]),
        );
        assert_eq!(
            sum_type_constructor_fields(SumTypeId::OutputDatum, 2, v),
            Some(vec![(F::Datum, None)]),
        );
        assert_eq!(
            sum_type_constructor_fields(SumTypeId::OutputDatum, 3, v),
            None
        );
    }
    // V1 has no OutputDatum sum.
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::OutputDatum, 0, ScriptVersion::PlutusV1),
        None,
    );
}

/// ABI PIN — the V3 `Voter` field table (CC member / DRep → Credential; pool
/// → bare hash leaf). V3-only.
#[test]
fn sum_type_constructor_fields_typed_voter_v3() {
    use ContextField as F;
    let v3 = ScriptVersion::PlutusV3;
    let cred = Some(FieldTypeRef::Sum(SumTypeId::Credential));
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::Voter, 0, v3),
        Some(vec![(F::Credential, cred)]),
    );
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::Voter, 1, v3),
        Some(vec![(F::Credential, cred)]),
    );
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::Voter, 2, v3),
        Some(vec![(F::PoolId, None)]),
    );
    assert_eq!(sum_type_constructor_fields(SumTypeId::Voter, 3, v3), None);
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::Voter, 0, ScriptVersion::PlutusV1),
        None
    );
}

/// ScriptInfo (V3) payload chaining refs: Rewarding→Credential,
/// Voting→Voter. Certifying is an idx-0 Int index + an idx-1 certificate,
/// both untyped.
#[test]
fn script_info_v3_chaining_refs() {
    use ContextField as F;
    let v3 = ScriptVersion::PlutusV3;
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::ScriptInfo, 2, v3),
        Some(vec![(
            F::Credential,
            Some(FieldTypeRef::Sum(SumTypeId::Credential))
        )]),
    );
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::ScriptInfo, 3, v3),
        Some(vec![(F::Index, None), (F::Certificate, None)]),
        "Certifying: index is idx 0 (Int); the V3 certificate (idx 1) is left \
         UNTYPED — V3 TxCerts are un-nameable (Never-skew), and typing it would \
         leak into the early control_flow naming path (no arity gate there)",
    );
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::ScriptInfo, 4, v3),
        Some(vec![(F::Voter, Some(FieldTypeRef::Sum(SumTypeId::Voter)))]),
    );
}

/// The V3 governance RECORD field tables (ProtocolVersion / RationalNumber /
/// Constitution / GovActionId), all V3-only, all leaf fields.
#[test]
fn context_field_at_typed_governance_records_v3() {
    use ContextField as F;
    let v3 = ScriptVersion::PlutusV3;
    assert_eq!(
        context_field_at(ContextType::ProtocolVersion, 0, v3),
        Some(F::Major)
    );
    assert_eq!(
        context_field_at(ContextType::ProtocolVersion, 1, v3),
        Some(F::Minor)
    );
    assert_eq!(context_field_at(ContextType::ProtocolVersion, 2, v3), None);
    assert_eq!(
        context_field_at(ContextType::RationalNumber, 0, v3),
        Some(F::Numerator)
    );
    assert_eq!(
        context_field_at(ContextType::RationalNumber, 1, v3),
        Some(F::Denominator)
    );
    assert_eq!(
        context_field_at(ContextType::Constitution, 0, v3),
        Some(F::Guardrails)
    );
    assert_eq!(
        context_field_at(ContextType::GovActionId, 0, v3),
        Some(F::Id)
    );
    assert_eq!(
        context_field_at(ContextType::GovActionId, 1, v3),
        Some(F::Index)
    );
    // All V3-only.
    for ct in [
        ContextType::ProtocolVersion,
        ContextType::RationalNumber,
        ContextType::Constitution,
        ContextType::GovActionId,
    ] {
        assert_eq!(context_field_at(ct, 0, ScriptVersion::PlutusV1), None);
        assert_eq!(context_field_at(ct, 0, ScriptVersion::PlutusV2), None);
    }
}

/// `TxOut.datum` chains to OutputDatum; `TxInfo.proposal_procedures` is a
/// list of ProposalProcedure.
#[test]
fn context_field_chaining_datum_and_proposal_procedures() {
    let v3 = ScriptVersion::PlutusV3;
    assert_eq!(
        context_field_type_full(ContextField::Datum, v3),
        Some(CardanoTypeRef::Sum(SumTypeId::OutputDatum)),
    );
    assert_eq!(
        context_field_type_full(ContextField::ProposalProcedures, v3),
        Some(CardanoTypeRef::ListOfRecords(
            ContextType::ProposalProcedure
        )),
    );
}

/// ABI PIN — `ProposalProcedure` field order
/// `[deposit(0), return_address(1), governance_action(2)]`, mirroring
/// stdlib `cardano/governance.ProposalProcedure`. The
/// render-stage Cardano type-env types `proposal_procedure.fields[2]` as
/// `GovernanceAction`, so a wrong order would put that name on `deposit`,
/// an Int — a valid-looking wrong name. V3-only.
#[test]
fn context_field_at_typed_proposal_procedure_field_order_v3_pin() {
    use ContextField as F;
    let v3 = ScriptVersion::PlutusV3;
    let pp = ContextType::ProposalProcedure;
    assert_eq!(context_field_at(pp, 0, v3), Some(F::Deposit));
    assert_eq!(context_field_at(pp, 1, v3), Some(F::ReturnAddress));
    assert_eq!(
        context_field_at(pp, 2, v3),
        Some(F::GovernanceAction),
        "ABI PIN: ProposalProcedure.fields[2] must be governance_action",
    );
    // The script projection drops the on-chain `anchor` (index 3).
    assert_eq!(context_field_at(pp, 3, v3), None);
    // The field-2 label types as the GovernanceAction sum; the sibling
    // scalar/credential fields stay untyped (fail-closed).
    assert_eq!(
        context_field_type_full(F::GovernanceAction, v3),
        Some(CardanoTypeRef::Sum(SumTypeId::GovernanceAction)),
    );
    assert_eq!(context_field_type_full(F::Deposit, v3), None);
    assert_eq!(context_field_type_full(F::ReturnAddress, v3), None);
    // V3-only: ProposalProcedure has no fields at V1/V2.
    assert_eq!(context_field_at(pp, 0, ScriptVersion::PlutusV1), None);
    assert_eq!(context_field_at(pp, 0, ScriptVersion::PlutusV2), None);
}

/// `ScriptInfo::Proposing` (tag 5) field 1 points at the
/// `ProposalProcedure` record, so the type-env can chain
/// `proposal_procedure.fields[2] → GovernanceAction`.
#[test]
fn sum_type_constructor_fields_typed_proposing_field1_is_proposal_procedure() {
    use ContextField as F;
    let v3 = ScriptVersion::PlutusV3;
    assert_eq!(
        sum_type_constructor_fields(SumTypeId::ScriptInfo, 5, v3),
        Some(vec![
            (F::Index, None),
            (
                F::ProposalProcedure,
                Some(FieldTypeRef::Context(ContextType::ProposalProcedure)),
            ),
        ]),
    );
}

/// V1/V2 wrap every transaction id in a one-field `Constr 0 [ByteArray]`
/// newtype; V3 stores the bytes bare. Both id-carrying fields must follow that,
/// so `transaction_id.fields[0]` names as `.hash` at V1/V2 and stays a leaf at V3.
#[test]
fn transaction_id_is_a_wrapper_record_before_v3() {
    use ScriptVersion::{PlutusV1, PlutusV2, PlutusV3};
    for version in [PlutusV1, PlutusV2] {
        for field in [ContextField::TxId, ContextField::Id] {
            assert_eq!(
                context_field_type(field, version),
                Some(FieldTypeRef::Context(ContextType::TransactionId)),
                "{field:?} at {version:?} is the wrapped TxId newtype",
            );
        }
        assert_eq!(
            context_field_at(ContextType::TransactionId, 0, version),
            Some(ContextField::Hash),
        );
        assert_eq!(
            context_field_at(ContextType::TransactionId, 1, version),
            None,
            "the wrapper holds exactly one field",
        );
    }
    // V3 dropped the wrapper: bare bytes, nothing to index into.
    for field in [ContextField::TxId, ContextField::Id] {
        assert_eq!(context_field_type(field, PlutusV3), None);
    }
    assert_eq!(
        context_field_at(ContextType::TransactionId, 0, PlutusV3),
        None
    );
}

/// V1 stores `withdrawals` and `datums` as Haskell lists of tuples, so each
/// entry is a `Constr`, reached with `.fields[N]` — not a builtin pair. V2
/// changed both to `Map`s, where the entries ARE pairs, so the record shape
/// must not leak past V1.
#[test]
fn v1_list_of_tuple_entries_are_records() {
    use CardanoTypeRef as R;
    use ScriptVersion::{PlutusV1, PlutusV2, PlutusV3};
    assert_eq!(
        context_field_type_full(ContextField::Data, PlutusV1),
        Some(R::ListOfRecords(ContextType::DatumEntry)),
    );
    // `withdrawals[i].delegator` chains on to the Inline/Pointer sum; the
    // amount is an Int leaf. `datums[i]` is two leaves — a hash and raw Data.
    assert_eq!(
        context_field_at(ContextType::WithdrawalEntry, 0, PlutusV1),
        Some(ContextField::Delegator),
    );
    assert_eq!(
        context_field_type_full(ContextField::Delegator, PlutusV1),
        Some(R::Sum(SumTypeId::StakeCredential)),
        "the V1 withdrawal key is Inline-wrapped, so a bare Credential would \
         name tag 0 `VerificationKey` instead of `Inline`",
    );
    assert_eq!(
        context_field_at(ContextType::DatumEntry, 1, PlutusV1),
        Some(ContextField::Datum),
    );
    assert_eq!(context_field_type_full(ContextField::Datum, PlutusV1), None);
    // Not V2/V3: there the same fields are maps.
    for version in [PlutusV2, PlutusV3] {
        assert_eq!(
            context_field_at(ContextType::WithdrawalEntry, 0, version),
            None
        );
        assert_eq!(context_field_at(ContextType::DatumEntry, 0, version), None);
        assert_eq!(context_field_type_full(ContextField::Data, version), None);
    }
}
