use std::collections::HashMap;

use super::context_schema::{CardanoTypeRef, ContextField, ContextType, FieldTypeRef, SumTypeId};
use crate::decompile::ScriptVersion;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};
use crate::pseudo::walker::WalkVisitor;

/// Look up the semantic field at `index` for a typed [`ContextType`] under
/// the given Plutus version.
///
/// Sum types (purpose, script_info, …) are intentionally absent — they
/// expose constructors, not positional fields. Use
/// [`sum_type_constructor_fields`] for those.
pub(crate) fn context_field_at(
    parent: ContextType,
    index: usize,
    version: ScriptVersion,
) -> Option<ContextField> {
    use ContextField as F;
    let fields: &[ContextField] = match parent {
        ContextType::ScriptContext => match version {
            ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => &[F::TxInfo, F::Purpose],
            ScriptVersion::PlutusV3 => &[F::TxInfo, F::Redeemer, F::ScriptInfo],
        },
        ContextType::TxInfo => match version {
            ScriptVersion::PlutusV1 => &[
                F::Inputs,
                F::Outputs,
                F::Fee,
                F::Mint,
                F::Certificates,
                F::Withdrawals,
                F::ValidRange,
                F::Signatories,
                F::Data,
                F::Id,
            ],
            ScriptVersion::PlutusV2 => &[
                F::Inputs,
                F::ReferenceInputs,
                F::Outputs,
                F::Fee,
                F::Mint,
                F::Certificates,
                F::Withdrawals,
                F::ValidRange,
                F::Signatories,
                F::Redeemers,
                F::Data,
                F::Id,
            ],
            ScriptVersion::PlutusV3 => &[
                F::Inputs,
                F::ReferenceInputs,
                F::Outputs,
                F::Fee,
                F::Mint,
                F::Certificates,
                F::Withdrawals,
                F::ValidRange,
                F::Signatories,
                F::Redeemers,
                F::Data,
                F::Id,
                F::Votes,
                F::ProposalProcedures,
                F::CurrentTreasuryAmount,
                F::TreasuryDonation,
            ],
        },
        ContextType::TxInInfo => &[F::OutRef, F::Resolved],
        ContextType::TxOut => match version {
            ScriptVersion::PlutusV1 => &[F::Address, F::Value, F::DatumHash],
            ScriptVersion::PlutusV2 | ScriptVersion::PlutusV3 => {
                &[F::Address, F::Value, F::Datum, F::ReferenceScript]
            }
        },
        ContextType::TxOutRef => &[F::TxId, F::OutputIndex],
        ContextType::Address => &[F::PaymentCredential, F::StakeCredential],
        ContextType::Interval => &[F::LowerBound, F::UpperBound],
        ContextType::LowerBound | ContextType::UpperBound => &[F::BoundType, F::IsInclusive],
        // V3 `ProposalProcedure` (`cardano/governance`): the field order
        // is ABI-pinned as `[deposit(0), return_address(1),
        // governance_action(2)]`. The on-chain Plutus `Data` carries a trailing
        // `anchor` field that the surface projection drops, so index 3 is absent.
        ContextType::ProposalProcedure => match version {
            ScriptVersion::PlutusV3 => &[F::Deposit, F::ReturnAddress, F::GovernanceAction],
            _ => return None,
        },
        // V3 governance records (all V3-only; unreachable from a V1/V2
        // ScriptContext, so a versionless lookup correctly returns None).
        ContextType::ProtocolVersion => match version {
            ScriptVersion::PlutusV3 => &[F::Major, F::Minor],
            _ => return None,
        },
        ContextType::RationalNumber => match version {
            ScriptVersion::PlutusV3 => &[F::Numerator, F::Denominator],
            _ => return None,
        },
        ContextType::Constitution => match version {
            ScriptVersion::PlutusV3 => &[F::Guardrails],
            _ => return None,
        },
        // `TxId` — V1/V2 wrap a transaction id in a one-field `Constr 0 [bytes]`
        // newtype (`WithWrappedTransactionId` in the ledger's encoder); V3 stores
        // the bytes bare, so there is no record to index into there.
        ContextType::TransactionId => match version {
            ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => &[F::Hash],
            ScriptVersion::PlutusV3 => return None,
        },
        // V1 list-of-tuple entries. Both fields are positional in a `Constr`,
        // NOT a builtin pair — `.1st` does not apply, `.fields[N]` does.
        ContextType::WithdrawalEntry => match version {
            ScriptVersion::PlutusV1 => &[F::Delegator, F::Value],
            _ => return None,
        },
        ContextType::DatumEntry => match version {
            ScriptVersion::PlutusV1 => &[F::DatumHash, F::Datum],
            _ => return None,
        },
        // GovActionId { transaction (ByteArray), index (Int) } — both leaves.
        ContextType::GovActionId => match version {
            ScriptVersion::PlutusV3 => &[F::Id, F::Index],
            _ => return None,
        },
    };
    fields.get(index).copied()
}

/// Bridge a legacy stringly field/type name to a typed [`FieldTypeRef`].
///
/// Callers hold a name string (e.g. from `selector.as_pretty_name()` or
/// `HashMap<String, String>` state). The `tx_in_info`/`tx_out`/`tx_out_ref`
/// echo arm exists because `cardano_context_naming` re-feeds a field's
/// resolved type name back through here.
pub(crate) fn context_field_type_from_display_name(
    name: &str,
    version: ScriptVersion,
) -> Option<FieldTypeRef> {
    if let Some(field) = ContextField::from_display_name(name)
        && let Some(ftype) = context_field_type(field, version)
    {
        return Some(ftype);
    }
    if matches!(name, "tx_in_info" | "tx_out" | "tx_out_ref") {
        return ContextType::from_display_name(name).map(FieldTypeRef::Context);
    }
    None
}

/// Look up the static type of a [`ContextField`] as a typed
/// [`FieldTypeRef`].
///
/// Returns `None` for fields that don't have a known static schema type
/// at the typed layer (e.g. scalar fields like `fee`, `id`), and for
/// fields that do not EXIST at `version` — a field the schema cannot
/// reach at this version must not answer with a type, or the by-name
/// entry point ([`context_field_type_from_display_name`]) hands out a
/// type for a slot that is not there.
pub(crate) fn context_field_type(
    field: ContextField,
    version: ScriptVersion,
) -> Option<FieldTypeRef> {
    use ContextField as F;
    use ContextType as T;
    use ScriptVersion::{PlutusV1, PlutusV2, PlutusV3};
    Some(match field {
        F::Inputs => FieldTypeRef::Context(T::TxInInfo),
        // `reference_inputs` is a V2 addition; a V1 `TxInfo` has no such slot.
        F::ReferenceInputs => match version {
            PlutusV2 | PlutusV3 => FieldTypeRef::Context(T::TxInInfo),
            PlutusV1 => return None,
        },
        F::Outputs => FieldTypeRef::Context(T::TxOut),
        F::ValidRange => FieldTypeRef::Context(T::Interval),
        F::OutRef => FieldTypeRef::Context(T::TxOutRef),
        F::Resolved => FieldTypeRef::Context(T::TxOut),
        F::OutputReference => FieldTypeRef::Context(T::TxOutRef),
        F::Address => FieldTypeRef::Context(T::Address),
        F::LowerBound => FieldTypeRef::Context(T::LowerBound),
        F::UpperBound => FieldTypeRef::Context(T::UpperBound),
        // `payment_credential` and the V3 cert/voter `credential` payloads are a
        // PLAIN Credential. `stake_credential` is NOT here: it is
        // `Option<StakeCredential>`, two levels (Option, Inline) deeper and
        // beyond `FieldTypeRef`, so `context_field_type_full` types it
        // `OptionOfSum(StakeCredential)`; bare `Credential` would be a
        // wrong-depth mislabel.
        //
        // `F::Credential` stays version-INVARIANT on purpose. At V1/V2 the name
        // covers two different depths — `Purpose::Rewarding(credential)` is an
        // Inline-wrapped StakeCredential, while `StakeCredential::Inline`'s own
        // payload is a plain Credential — so the depth follows the PARENT, not
        // the version. `sum_type_constructor_fields` resolves both positionally;
        // gating this arm by version would just pick the wrong one of the two.
        F::PaymentCredential | F::Credential => FieldTypeRef::Sum(SumTypeId::Credential),
        F::BoundType => FieldTypeRef::Sum(SumTypeId::IntervalBoundType),
        // V3 replaced `ScriptContext.purpose : ScriptPurpose` with
        // `script_info : ScriptInfo`; neither name exists at the other versions.
        F::Purpose => match version {
            PlutusV1 | PlutusV2 => FieldTypeRef::Sum(SumTypeId::Purpose),
            PlutusV3 => return None,
        },
        F::ScriptInfo => match version {
            PlutusV3 => FieldTypeRef::Sum(SumTypeId::ScriptInfo),
            PlutusV1 | PlutusV2 => return None,
        },
        F::TxInfo => FieldTypeRef::Context(T::TxInfo),
        // `TxInfo.transaction_id` and `TxOutRef.tx_id` are a wrapped `TxId`
        // record at V1/V2 and bare bytes at V3 — a leaf there, with no field to
        // name. `F::Id` also serves V3's `GovActionId.transaction_id`, which is
        // likewise bare, so the V3 arm is right for both of its parents.
        // The V1/V2 certificate and withdrawal `delegator` payload is an
        // Inline-wrapped StakeCredential (`Constr 0 [Credential]`) — the sum with
        // Inline/Pointer tags, NOT a bare Credential, which would name tag 0
        // `VerificationKey` instead of `Inline`. V3 has no tabled certificate.
        F::Delegator => match version {
            PlutusV1 | PlutusV2 => FieldTypeRef::Sum(SumTypeId::StakeCredential),
            PlutusV3 => return None,
        },
        F::TxId | F::Id => match version {
            PlutusV1 | PlutusV2 => FieldTypeRef::Context(T::TransactionId),
            PlutusV3 => return None,
        },
        // `TxOut.datum : OutputDatum` — V2 and up. A V1 `TxOut` carries
        // `F::DatumHash` (`Option<ByteArray>`) and V1 has no `OutputDatum` sum
        // at all, so the name must not resolve there.
        F::Datum => match version {
            PlutusV2 | PlutusV3 => FieldTypeRef::Sum(SumTypeId::OutputDatum),
            PlutusV1 => return None,
        },
        // `ProposalProcedure.governance_action : GovernanceAction` — the
        // field-2 sum V3 governance validators dispatch on, and V3-only. The
        // siblings stay `None`: `deposit` is a scalar Int, and `return_address`
        // is a `Credential` that would need the merged-stub gate, so it fails
        // closed here.
        F::GovernanceAction => match version {
            PlutusV3 => FieldTypeRef::Sum(SumTypeId::GovernanceAction),
            PlutusV1 | PlutusV2 => return None,
        },
        _ => return None,
    })
}

/// Look up the static type of a [`ContextField`] as a [`CardanoTypeRef`].
///
/// Mirrors [`context_field_type`] but returns `ListOfRecords` /
/// `ListOfSums` / `MapKeyedBySum` for collection fields, so callers can
/// track a list binding's element type through `List.head`, `inputs[0]`,
/// slicing, etc.
///
/// Returns `None` for fields no `CardanoTypeRef` expresses (e.g. scalar
/// `Int`, `ByteArray`, or a map with a non-sum key).
pub(crate) fn context_field_type_full(
    field: ContextField,
    version: ScriptVersion,
) -> Option<CardanoTypeRef> {
    use ContextField as F;
    Some(match field {
        // List-of-record fields ---
        F::Inputs | F::ReferenceInputs => CardanoTypeRef::ListOfRecords(ContextType::TxInInfo),
        F::Outputs => CardanoTypeRef::ListOfRecords(ContextType::TxOut),
        // List-of-sum fields ---
        F::Certificates => CardanoTypeRef::ListOfSums(SumTypeId::Certificate),
        // `TxInfo.proposal_procedures : List<ProposalProcedure>` (V3). Lets
        // `proposal_procedures[i].governance_action` chain to GovernanceAction.
        F::ProposalProcedures => CardanoTypeRef::ListOfRecords(ContextType::ProposalProcedure),
        // `Address.stake_credential : Option<StakeCredential>` (Referenced).
        // After `Some(c)`, `c : StakeCredential` (Inline/Pointer); after
        // `Inline(cred)`, `cred : Credential`. Not in
        // `context_field_type` — `FieldTypeRef` cannot carry Option.
        F::StakeCredential => CardanoTypeRef::OptionOfSum(SumTypeId::StakeCredential),
        // Sum-keyed maps — iterating yields key-value pairs whose `.1st` is the
        // (chainable) key sum.
        //
        // `TxInfo.withdrawals` is a real `Data` MAP only from V2 on; the key is
        // an Inline-wrapped StakeCredential at V2 and a plain Credential at V3.
        // At V1 the field is a Haskell `[(StakingCredential, Integer)]`, which
        // encodes as a LIST of `Constr 0 [key, amount]` — no builtin pair, so
        // the `.1st` projection this variant promises never applies. No variant
        // models a list of constr-pairs, so V1 fails closed.
        F::Withdrawals => match version {
            ScriptVersion::PlutusV3 => CardanoTypeRef::MapKeyedBySum(SumTypeId::Credential),
            ScriptVersion::PlutusV2 => CardanoTypeRef::MapKeyedBySum(SumTypeId::StakeCredential),
            // V1 is a list of `Constr` entries, so it is a plain list-of-records
            // whose element carries the key at `.fields[0]`.
            ScriptVersion::PlutusV1 => CardanoTypeRef::ListOfRecords(ContextType::WithdrawalEntry),
        },
        // `datums` splits the same way: a V1 list of `Constr 0 [hash, datum]`
        // entries, a `Map` from V2 on. The V2/V3 map key is a plain hash, not a
        // sum, so `MapKeyedBySum` cannot express it and it stays untyped there.
        F::Data => match version {
            ScriptVersion::PlutusV1 => CardanoTypeRef::ListOfRecords(ContextType::DatumEntry),
            ScriptVersion::PlutusV2 | ScriptVersion::PlutusV3 => return None,
        },
        // `TxInfo.votes : Pairs<Voter, Pairs<GovActionId, Vote>>` (V3 only) —
        // key = Voter. (The value's inner map is not tracked.)
        F::Votes => match version {
            ScriptVersion::PlutusV3 => CardanoTypeRef::MapKeyedBySum(SumTypeId::Voter),
            _ => return None,
        },
        // All other fields fall back to the scalar table. ---
        _ => match context_field_type(field, version)? {
            FieldTypeRef::Context(ct) => CardanoTypeRef::Record(ct),
            FieldTypeRef::Sum(st) => CardanoTypeRef::Sum(st),
        },
    })
}

/// Resolve the Cardano-aware return type of a known builtin from the
/// (statically-inferred) Cardano types of its arguments.
///
/// Returns `None` for unmodelled builtins and when the argument types
/// are not enough to refine the result.
pub(crate) fn builtin_cardano_return(
    builtin: crate::BuiltinId,
    arg_types: &[Option<CardanoTypeRef>],
) -> Option<CardanoTypeRef> {
    use crate::BuiltinId;
    match builtin {
        // `un_map_data` / `un_list_data` reinterpret the raw `Data` of a typed
        // collection field as its list/map view — type passthrough. A key-sum
        // map stays `MapKeyedBySum` (so `[entry, ..]` / `Pair.first` chain to
        // the key); a list-of-T stays the list. Only collection types pass.
        BuiltinId::DataUnMap | BuiltinId::DataUnList => {
            match arg_types.first().copied().flatten()? {
                ty @ (CardanoTypeRef::MapKeyedBySum(_)
                | CardanoTypeRef::ListOfRecords(_)
                | CardanoTypeRef::ListOfSums(_)) => Some(ty),
                _ => None,
            }
        }
        // List.head(xs: List<T>) -> T
        BuiltinId::ListHead => arg_types
            .first()
            .copied()
            .flatten()
            .and_then(|ty| ty.element_type()),
        // List.tail(xs: List<T>) -> List<T>
        BuiltinId::ListTail => {
            let ty = arg_types.first().copied().flatten()?;
            matches!(
                ty,
                CardanoTypeRef::ListOfRecords(_) | CardanoTypeRef::ListOfSums(_)
            )
            .then_some(ty)
        }
        // When the arg is a known Cardano record-of-pairs,
        // project field 0 / 1. TxInInfo (out_ref, resolved) is
        // the pair-shaped record the schema models.
        BuiltinId::PairFirst => {
            let ty = arg_types.first().copied().flatten()?;
            let record = ty.record()?;
            // For TxInInfo: fst = out_ref (TxOutRef), snd = resolved (TxOut).
            match record {
                ContextType::TxInInfo => Some(CardanoTypeRef::Record(ContextType::TxOutRef)),
                _ => None,
            }
        }
        BuiltinId::PairSecond => {
            let ty = arg_types.first().copied().flatten()?;
            let record = ty.record()?;
            match record {
                ContextType::TxInInfo => Some(CardanoTypeRef::Record(ContextType::TxOut)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Shape of a known list-combinator call: where the list lives in the
/// outer call's `args` slice, where the callback lambda lives, and which
/// positional parameter of that lambda receives the element type.
///
/// `cardano_context_naming` binds that parameter at the moment the call
/// site is folded, so `find(inputs, fn(input) { ... })` has
/// `input: TxInInfo` in scope before the generic `enter_lambda` hook
/// fires.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ListCombinatorShape {
    pub list_arg_index: usize,
    pub callback_arg_index: usize,
    pub element_param_index: usize,
}

/// Map a list-combinator name — as it appears after
/// `analyze_function_binding` has renamed recursive helpers — to its
/// callback shape.
///
/// stdlib puts the element at param 0 and the accumulator at param
/// 1 of a `foldl`/`foldr` callback; every other combinator takes a
/// single-param callback. Unknown names return `None`, so the caller
/// falls through to the generic walk.
pub(crate) fn list_combinator_element_param_index(name: &str) -> Option<ListCombinatorShape> {
    let (callback_arg_index, element_param_index) = match name {
        "find" | "map" | "filter" | "any" | "exists" | "all" | "partition" => (1, 0),
        "foldl" | "foldr" => (2, 0),
        _ => return None,
    };
    Some(ListCombinatorShape {
        list_arg_index: 0,
        callback_arg_index,
        element_param_index,
    })
}

/// Pick the singular parameter-style alias for a list-typed context
/// field, used to name a binder like `let input = inputs[0]`.
pub(crate) fn singular_of_list_field(field: ContextField) -> Option<&'static str> {
    use ContextField as F;
    Some(match field {
        F::Inputs | F::ReferenceInputs => "input",
        F::Outputs => "output",
        F::Certificates => "certificate",
        F::Signatories => "signatory",
        _ => return None,
    })
}

/// Pick the singular parameter-style alias for the named element-bearing
/// record type.
pub(crate) fn context_element_type_name(elem: ContextType) -> Option<&'static str> {
    Some(match elem {
        ContextType::TxInInfo => "input",
        ContextType::TxOut => "output",
        _ => return None,
    })
}

/// List the constructor names of a typed [`SumTypeId`] under the given
/// Plutus version.
pub(crate) fn sum_type_constructor_names(
    type_name: SumTypeId,
    version: ScriptVersion,
) -> Option<&'static [&'static str]> {
    use SumTypeId as S;
    match type_name {
        S::Purpose => match version {
            ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => {
                Some(&["Minting", "Spending", "Rewarding", "Certifying"] as &[&str])
            }
            ScriptVersion::PlutusV3 => None,
        },
        S::ScriptInfo => match version {
            ScriptVersion::PlutusV3 => Some(&[
                "Minting",
                "Spending",
                "Rewarding",
                "Certifying",
                "Voting",
                "Proposing",
            ] as &[&str]),
            _ => None,
        },
        S::Credential => Some(&["VerificationKey", "Script"]),
        S::OutputDatum => match version {
            ScriptVersion::PlutusV2 | ScriptVersion::PlutusV3 => {
                Some(&["NoDatum", "DatumHash", "InlineDatum"])
            }
            ScriptVersion::PlutusV1 => None,
        },
        S::IntervalBoundType => Some(&["NegativeInfinity", "Finite", "PositiveInfinity"]),
        S::Certificate => match version {
            // V1/V2 `DCert` (surface `transaction/certificate`), Constr
            // tags 0-6.
            ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => Some(&[
                "CredentialRegistration",
                "CredentialDeregistration",
                "CredentialDelegation",
                "PoolRegistration",
                "PoolDeregistration",
                "Governance",
                "TreasuryMovement",
            ]),
            ScriptVersion::PlutusV3 => Some(&[
                "RegisterCredential",
                "UnregisterCredential",
                "DelegateCredential",
                "RegisterAndDelegateCredential",
                "RegisterDelegateRepresentative",
                "UpdateDelegateRepresentative",
                "UnregisterDelegateRepresentative",
                "RegisterStakePool",
                "RetireStakePool",
                "AuthorizeConstitutionalCommitteeProxy",
                "RetireFromConstitutionalCommittee",
            ]),
        },
        S::Voter => match version {
            ScriptVersion::PlutusV3 => Some(&[
                "ConstitutionalCommitteeMember",
                "DelegateRepresentative",
                "StakePool",
            ]),
            _ => None,
        },
        S::DRep => match version {
            ScriptVersion::PlutusV3 => Some(&["Registered", "AlwaysAbstain", "AlwaysNoConfidence"]),
            _ => None,
        },
        S::GovernanceAction => match version {
            // `cardano/governance` renames Plutus `ParameterChange`
            // to `ProtocolParameters` (tag 0).
            ScriptVersion::PlutusV3 => Some(&[
                "ProtocolParameters",
                "HardFork",
                "TreasuryWithdrawal",
                "NoConfidence",
                "ConstitutionalCommittee",
                "NewConstitution",
                "NicePoll",
            ]),
            _ => None,
        },
        S::Vote => match version {
            ScriptVersion::PlutusV3 => Some(&["No", "Yes", "Abstain"]),
            _ => None,
        },
        S::Bool => Some(&["False", "True"]),
        // `Referenced<Credential>`  — version-invariant. Inline wraps a
        // Credential; Pointer carries (slot, tx_index, cert_index).
        S::StakeCredential => Some(&["Inline", "Pointer"]),
    }
}

/// List the fields of a [`SumTypeId`]'s `tag`-th constructor as
/// `(ContextField, Option<FieldTypeRef>)` pairs.
pub(crate) fn sum_type_constructor_fields(
    parent: SumTypeId,
    tag: usize,
    version: ScriptVersion,
) -> Option<Vec<(ContextField, Option<FieldTypeRef>)>> {
    use ContextField as F;
    use ContextType as T;
    let out_ref_type = || Some(FieldTypeRef::Context(T::TxOutRef));
    match parent {
        SumTypeId::Purpose => match version {
            ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => match tag {
                0 => Some(vec![(F::PolicyId, None)]),
                1 => Some(vec![(F::OutputReference, out_ref_type())]),
                // Rewarding(credential): the V1/V2 payload is an Inline-wrapped
                // StakeCredential (`Constr 0 [Credential]`), so it chains to the
                // StakeCredential sum (Inline→Credential); a bare Credential
                // would be a wrong-depth mislabel.
                2 => Some(vec![(
                    F::Credential,
                    Some(FieldTypeRef::Sum(SumTypeId::StakeCredential)),
                )]),
                3 => Some(vec![(
                    F::Certificate,
                    Some(FieldTypeRef::Sum(SumTypeId::Certificate)),
                )]),
                _ => None,
            },
            ScriptVersion::PlutusV3 => None,
        },
        SumTypeId::ScriptInfo => match version {
            ScriptVersion::PlutusV3 => match tag {
                0 => Some(vec![(F::PolicyId, None)]),
                1 => Some(vec![(F::OutputReference, out_ref_type()), (F::Datum, None)]),
                // Rewarding(credential): the V3 credential is a PLAIN
                // Credential, not the V1/V2 Inline-wrapped StakeCredential,
                // so bind it directly.
                2 => Some(vec![(
                    F::Credential,
                    Some(FieldTypeRef::Sum(SumTypeId::Credential)),
                )]),
                // Certifying(index, certificate): the certificate payload is left
                // UNTYPED on purpose. A V3 TxCert is un-nameable (its tag-0/1
                // `Never` deposit skews Data arity against surface arity), so the
                // render-stage `known_ctor_arity` declines it; typing it here
                // would yield no nameable `when certificate is …` and would feed
                // the sum-type-ref into the EARLY control_flow naming path, which
                // names from the ctor-NAMES table with no arity gate and would
                // mis-name the cert.
                3 => Some(vec![(F::Index, None), (F::Certificate, None)]),
                // Voting(voter).
                4 => Some(vec![(F::Voter, Some(FieldTypeRef::Sum(SumTypeId::Voter)))]),
                // Proposing { index, proposal_procedure }. Field 1 carries a
                // type-ref because the render-stage Cardano type-env needs it to
                // type the payload binder as `ProposalProcedure`, so
                // `proposal_procedure.fields[2]` resolves to `GovernanceAction`
                // and the inner governance `when` gets named.
                5 => Some(vec![
                    (F::Index, None),
                    (
                        F::ProposalProcedure,
                        Some(FieldTypeRef::Context(T::ProposalProcedure)),
                    ),
                ]),
                _ => None,
            },
            _ => None,
        },
        SumTypeId::Credential => match tag {
            0 | 1 => Some(vec![(F::Hash, None)]),
            _ => None,
        },
        SumTypeId::IntervalBoundType => match tag {
            // ContextField has no IntervalBoundType-specific Value variant;
            // `Value` is reused because both legacy names are the literal
            // "value", which keeps the `.display_name()` round-trip exact.
            1 => Some(vec![(F::Value, None)]),
            _ => None,
        },
        // V1/V2 `DCert` (surface `transaction/certificate`). Nullary
        // constructors return `Some(vec![])`, NOT `None`, so the
        // arity-from-table path in `known_ctor_arity` tells a true nullary
        // from an untrusted type. V3 `TxCert` is deliberately absent: its
        // tag-0/1 carry a `Never` deposit/refund present in the on-chain
        // `Data` (arity 2) but erased in surface syntax (arity 1), so
        // naming it would emit an arity-mismatched (invalid) surface pattern.
        SumTypeId::Certificate => match version {
            // delegator is an Inline-wrapped StakeCredential (`Constr 0
            // [Credential]`), so it chains to the StakeCredential sum, NOT bare
            // Credential (wrong depth). delegatee is a PoolId hash leaf.
            ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => match tag {
                // CredentialRegistration
                0 => Some(vec![(
                    F::Delegator,
                    Some(FieldTypeRef::Sum(SumTypeId::StakeCredential)),
                )]),
                // CredentialDeregistration
                1 => Some(vec![(
                    F::Delegator,
                    Some(FieldTypeRef::Sum(SumTypeId::StakeCredential)),
                )]),
                // CredentialDelegation
                2 => Some(vec![
                    (
                        F::Delegator,
                        Some(FieldTypeRef::Sum(SumTypeId::StakeCredential)),
                    ),
                    (F::Delegatee, None),
                ]),
                3 => Some(vec![(F::PoolId, None), (F::Vrf, None)]), // PoolRegistration
                4 => Some(vec![(F::PoolId, None), (F::Epoch, None)]), // PoolDeregistration
                5 => Some(vec![]),                                  // Governance — nullary
                6 => Some(vec![]),                                  // TreasuryMovement — nullary
                _ => None,
            },
            ScriptVersion::PlutusV3 => None,
        },
        // V3 `GovernanceAction` (`cardano/governance`). Arities mirror
        // Plutus V3 `PlutusLedgerApi.V3.Contexts.GovernanceAction` field for
        // field. Unlike V3 `TxCert` it has NO surface/Data arity skew (no
        // erased `Never`-style field), so every tag 0-6 is certain and tabled.
        // Field type-refs stay `None`: the payload types (protocol-parameter
        // update, Pairs<...>, Rational, Constitution, …) are not modeled in the
        // ContextType/SumTypeId schema, and `name_cardano_sum_arms` needs only
        // the arity + field labels to stamp a valid surface pattern.
        SumTypeId::GovernanceAction => match version {
            ScriptVersion::PlutusV3 => match tag {
                // ProtocolParameters { ancestor, new_parameters, guardrails }
                0 => Some(vec![
                    (F::Ancestor, None),
                    (F::NewParameters, None),
                    (F::Guardrails, None),
                ]),
                // HardFork { ancestor, new_version }. new_version chains to the
                // ProtocolVersion record; ancestor is an Option(GovActionId),
                // which `FieldTypeRef` cannot express.
                1 => Some(vec![
                    (F::Ancestor, None),
                    (
                        F::NewVersion,
                        Some(FieldTypeRef::Context(T::ProtocolVersion)),
                    ),
                ]),
                // TreasuryWithdrawal { beneficiaries, guardrails }. beneficiaries
                // is a Map(Credential, Int), which `FieldTypeRef` cannot key-chain,
                // so it stays `None`; guardrails is an Option(ByteArray) leaf.
                2 => Some(vec![(F::Beneficiaries, None), (F::Guardrails, None)]),
                // NoConfidence { ancestor } — ancestor is an
                // Option(GovActionId).
                3 => Some(vec![(F::Ancestor, None)]),
                // ConstitutionalCommittee { ancestor, evicted_members,
                // added_members, quorum }: quorum chains to RationalNumber;
                // ancestor is an Option(GovActionId), evicted/added_members are
                // List/Map of Credential — none expressible as a `FieldTypeRef`.
                4 => Some(vec![
                    (F::Ancestor, None),
                    (F::EvictedMembers, None),
                    (F::AddedMembers, None),
                    (F::Quorum, Some(FieldTypeRef::Context(T::RationalNumber))),
                ]),
                // NewConstitution { ancestor, constitution }. constitution chains
                // to the Constitution record; ancestor is an Option(GovActionId).
                5 => Some(vec![
                    (F::Ancestor, None),
                    (
                        F::Constitution,
                        Some(FieldTypeRef::Context(T::Constitution)),
                    ),
                ]),
                // NicePoll — nullary
                6 => Some(vec![]),
                _ => None,
            },
            _ => None,
        },
        // V2/V3 `OutputDatum` (`cardano/transaction.{Datum}` /
        // `transaction.Datum`). NoDatum is a genuine nullary
        // (`Some(vec![])`, NOT `None`) so `known_ctor_arity` reports arity 0.
        // V1 has no OutputDatum: its `TxOut` carries a plain
        // `Option<DatumHash>`.
        SumTypeId::OutputDatum => match version {
            ScriptVersion::PlutusV2 | ScriptVersion::PlutusV3 => match tag {
                0 => Some(vec![]),                 // NoDatum
                1 => Some(vec![(F::Hash, None)]),  // DatumHash(hash: ByteArray)
                2 => Some(vec![(F::Datum, None)]), // InlineDatum(data: Data) — leaf
                _ => None,
            },
            ScriptVersion::PlutusV1 => None,
        },
        // V3 `Voter` (`cardano/governance.{Voter}`). Tags 0/1 carry a
        // Credential; tag 2 (StakePool) carries a bare pool-key-hash ByteArray
        // (leaf).
        SumTypeId::Voter => match version {
            ScriptVersion::PlutusV3 => match tag {
                0 => Some(vec![(
                    F::Credential,
                    Some(FieldTypeRef::Sum(SumTypeId::Credential)),
                )]),
                1 => Some(vec![(
                    F::Credential,
                    Some(FieldTypeRef::Sum(SumTypeId::Credential)),
                )]),
                2 => Some(vec![(F::PoolId, None)]),
                _ => None,
            },
            _ => None,
        },
        // `Referenced<Credential>` (StakeCredential), version-invariant. Inline
        // chains to Credential; Pointer carries 3 Int leaves and is a
        // deprecated address form, tabled only for completeness.
        SumTypeId::StakeCredential => match tag {
            0 => Some(vec![(
                F::Credential,
                Some(FieldTypeRef::Sum(SumTypeId::Credential)),
            )]),
            1 => Some(vec![
                (F::SlotNumber, None),
                (F::TransactionIndex, None),
                (F::CertificateIndex, None),
            ]),
            _ => None,
        },
        _ => None,
    }
}

/// Seed context field names by identifying top-level lambda params.
pub(crate) fn seed_context_field_names(
    expr: &PseudoExpr,
    version: ScriptVersion,
    names: &mut std::collections::HashMap<String, String>,
) {
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Lambda { params, body, .. } => {
                let mut all_params: Vec<&str> = params.iter().map(|s| s.as_str()).collect();
                let mut inner = body.as_ref();
                while all_params.len() < 3 {
                    if let PseudoExpr::Lambda {
                        params: ip,
                        body: ib,
                        ..
                    } = inner
                    {
                        all_params.extend(ip.iter().map(|s| s.as_str()));
                        inner = ib.as_ref();
                    } else {
                        break;
                    }
                }

                // Mirror `simplify::rename::validator::expected_validator_params`:
                // at V3 the last param is always `script_context`, with any number
                // of leading user params; V1/V2 arities are fixed.
                let trailing: &[&str] = match (version, all_params.len()) {
                    (ScriptVersion::PlutusV3, n) if n >= 1 => &["script_context"],
                    (ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2, 2) => {
                        &["redeemer", "script_context"]
                    }
                    (ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2, 3) => {
                        &["datum", "redeemer", "script_context"]
                    }
                    _ => return,
                };
                let leading = all_params.len() - trailing.len();
                for (param, semantic) in all_params[leading..].iter().zip(trailing.iter()) {
                    if *param != "_" {
                        names.insert(param.to_string(), semantic.to_string());
                    }
                }
                return;
            }
            PseudoExpr::Let { body, .. }
            | PseudoExpr::Delay(body)
            | PseudoExpr::RecFn { body, .. } => {
                current = body.as_ref();
            }
            _ => return,
        }
    }
}

fn is_fail_expr(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Error { .. } => return true,
            PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::Error => {
                return true;
            }
            PseudoExpr::Trace { value, .. } => pending.push(value),
            _ => {}
        }
    }
    false
}

/// Pre-scan the simplified AST to detect expect/when patterns on purpose/script_info.
pub(crate) fn detect_sum_type_overrides(
    expr: &PseudoExpr,
    version: ScriptVersion,
    context_names: &std::collections::HashMap<String, String>,
    context_field_names_by_id: &std::collections::HashMap<VarId, String>,
) -> std::collections::HashMap<String, Vec<String>> {
    struct SumTypeOverrideDetector<'a> {
        version: ScriptVersion,
        context_names: &'a HashMap<String, String>,
        context_field_names_by_id: &'a HashMap<VarId, String>,
        overrides: HashMap<String, Vec<String>>,
    }

    impl SumTypeOverrideDetector<'_> {
        fn resolve_ctx_name<'a>(&self, subject: &'a PseudoExpr) -> Option<&'a str> {
            match subject {
                PseudoExpr::Var { name, id, .. } => {
                    let by_id = id
                        .get()
                        .and_then(|vid| self.context_field_names_by_id.get(&vid))
                        .map(|s| s.as_str());
                    let by_name = self.context_names.get(name).map(|s| s.as_str());
                    let resolved = by_id.or(by_name);
                    match resolved {
                        Some("purpose") => Some("purpose"),
                        Some("script_info") => Some("script_info"),
                        _ => {
                            if name == "purpose" || name == "script_info" {
                                Some(name.as_str())
                            } else {
                                None
                            }
                        }
                    }
                }
                PseudoExpr::FieldAccess { selector, .. } => match selector.as_pretty_name() {
                    "purpose" => Some("purpose"),
                    "script_info" => Some("script_info"),
                    _ => None,
                },
                _ => None,
            }
        }

        fn detect_constructor_tag(&self, clauses: &[WhenClause]) -> Option<usize> {
            let mut non_fail_constructors: Vec<usize> = Vec::new();
            for clause in clauses {
                if let WhenPattern::Constructor { tag, .. } = &clause.pattern {
                    if !is_fail_expr(&clause.body) {
                        non_fail_constructors.push(*tag);
                    }
                } else if let WhenPattern::Wildcard = &clause.pattern
                    && !is_fail_expr(&clause.body)
                {
                    non_fail_constructors.clear();
                    break;
                }
            }

            (non_fail_constructors.len() == 1).then(|| non_fail_constructors[0])
        }
    }

    impl WalkVisitor for SumTypeOverrideDetector<'_> {
        fn visit_when(
            &mut self,
            subject: &PseudoExpr,
            _subject_name: Option<&crate::pseudo::ast::Binder>,
            clauses: &[WhenClause],
        ) {
            let Some(ctx) = self.resolve_ctx_name(subject) else {
                return;
            };
            if self.overrides.contains_key(ctx) {
                return;
            }
            let Some(tag) = self.detect_constructor_tag(clauses) else {
                return;
            };
            if let Some(fields) = SumTypeId::from_display_name(ctx)
                .and_then(|id| sum_type_constructor_fields(id, tag, self.version))
            {
                let field_names = fields
                    .into_iter()
                    .map(|(name, _)| name.display_name().to_string())
                    .collect();
                self.overrides.insert(ctx.to_string(), field_names);
            }
        }
    }

    let mut detector = SumTypeOverrideDetector {
        version,
        context_names,
        context_field_names_by_id,
        overrides: HashMap::new(),
    };
    detector.walk(expr);
    detector.overrides
}

#[cfg(test)]
mod tests;
