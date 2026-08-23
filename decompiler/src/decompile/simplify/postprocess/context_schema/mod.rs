//! Typed identifiers for the Cardano `ScriptContext` schema, in place
//! of stringly and magic-number ones: [`ContextType`] (records with
//! positional fields), [`SumTypeId`] (sums with constructor tags),
//! [`ContextField`] (fields reachable from a `ScriptContext`), and
//! the [`FieldTypeRef`] / [`CardanoTypeRef`] unions of the two.
//!
//! Self-contained by design: it depends on neither the AST graph nor
//! `ScriptVersion`, so helpers and tests can use it without pulling
//! in `pseudo::ast`. The version-dependent tables (fields-per-type,
//! constructors-per-sum-type) live with their consumers in
//! `postprocess::context`.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};

/// Named record types in the Cardano `ScriptContext` schema — types
/// that expose positional fields. Sum types (with constructor tags)
/// live separately in [`SumTypeId`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum ContextType {
    /// `ScriptContext` — the top-level record passed to every
    /// validator.
    ScriptContext,
    /// `TxInfo` — transaction information (inputs, outputs, fee, etc.).
    TxInfo,
    /// `TxInInfo` — a resolved transaction input (`out_ref` + `resolved`).
    TxInInfo,
    /// `TxOut` — a transaction output (`address`, `value`, `datum`, …).
    TxOut,
    /// `TxOutRef` — a reference to a transaction output
    /// (`tx_id`, `output_index`).
    TxOutRef,
    /// `Address` — `payment_credential` + optional `stake_credential`.
    Address,
    /// `Interval` — a validity-range interval (`lower_bound`,
    /// `upper_bound`).
    Interval,
    /// `Interval.lower_bound` — the lower bound record
    /// (`bound_type`, `is_inclusive`). Distinct from [`Self::UpperBound`]
    /// because the rendered schema addresses the two endpoints
    /// by separate parent-type names.
    LowerBound,
    /// `Interval.upper_bound` — the upper bound record. See
    /// [`Self::LowerBound`] for why this is a separate variant.
    UpperBound,
    /// `ProposalProcedure` (V3) — `deposit`, `return_address`, and
    /// `governance_action`, the [`SumTypeId::GovernanceAction`] sum.
    /// The record projected from `ScriptInfo::Proposing`'s field 1.
    ProposalProcedure,
    /// `ProtocolVersion` (V3) — `major` + `minor` (the
    /// `GovernanceAction::HardFork` `new_version` payload). Two `Int` leaves.
    ProtocolVersion,
    /// `RationalNumber` (`Rational`, V3) — `numerator` +
    /// `denominator` (the `ConstitutionalCommittee` `quorum` payload). Two
    /// `Int` leaves.
    RationalNumber,
    /// `Constitution` (V3) — the `NewConstitution` payload. One field
    /// (`guardrails : Option<ScriptHash>`, a leaf).
    Constitution,
    /// `GovActionId` (`GovernanceActionId`, V3) — `transaction_id`
    /// (ByteArray) + `index` (Int). The Option-wrapped `ancestor` payload
    /// of several `GovernanceAction` constructors; both fields are leaves.
    GovActionId,
    /// `TxId` (V1/V2 only) — the one-field `Constr 0 [ByteArray]` newtype that
    /// V1/V2 wrap every transaction id in (`TxInfo.transaction_id`,
    /// `TxOutRef.tx_id`). V3 dropped the wrapper and stores the bytes bare, so
    /// at V3 this record does not exist and the lookups fail closed.
    TransactionId,
    /// One entry of V1's `withdrawals` — `Constr 0 [StakingCredential, Integer]`.
    /// V1 types the field `[(StakingCredential, Integer)]`, a Haskell LIST of
    /// tuples, and a tuple encodes as a `Constr`; V2 changed it to a `Map`, whose
    /// entries are builtin pairs instead. V2/V3 therefore use
    /// [`CardanoTypeRef::MapKeyedBySum`] and this record does not exist there.
    WithdrawalEntry,
    /// One entry of V1's `datums` — `Constr 0 [DatumHash, Datum]`, for the same
    /// reason: V1 types it `[(DatumHash, Datum)]` and V2 changed it to a `Map`.
    DatumEntry,
}

impl ContextType {
    /// Parse a rendered parent-type name back into a typed
    /// [`ContextType`]. Returns `None` outside the record-type set —
    /// callers that also accept sum-type names fall through to
    /// [`SumTypeId::from_display_name`].
    pub(crate) fn from_display_name(name: &str) -> Option<Self> {
        Some(match name {
            "script_context" => Self::ScriptContext,
            "tx_info" => Self::TxInfo,
            "tx_in_info" => Self::TxInInfo,
            "tx_out" => Self::TxOut,
            "tx_out_ref" => Self::TxOutRef,
            "address" => Self::Address,
            "interval" => Self::Interval,
            "lower_bound" => Self::LowerBound,
            "upper_bound" => Self::UpperBound,
            "proposal_procedure" => Self::ProposalProcedure,
            "protocol_version" => Self::ProtocolVersion,
            "rational" => Self::RationalNumber,
            "constitution" => Self::Constitution,
            "gov_action_id" => Self::GovActionId,
            "transaction_id" => Self::TransactionId,
            "withdrawal" => Self::WithdrawalEntry,
            "datum_entry" => Self::DatumEntry,
            _ => return None,
        })
    }

    /// How this type is NAMED in the rendered output — the inverse of
    /// [`Self::from_display_name`]. Always round-trips.
    pub(crate) fn display_name(self) -> &'static str {
        match self {
            Self::ScriptContext => "script_context",
            Self::TxInfo => "tx_info",
            Self::TxInInfo => "tx_in_info",
            Self::TxOut => "tx_out",
            Self::TxOutRef => "tx_out_ref",
            Self::Address => "address",
            Self::Interval => "interval",
            Self::LowerBound => "lower_bound",
            Self::UpperBound => "upper_bound",
            Self::ProposalProcedure => "proposal_procedure",
            Self::ProtocolVersion => "protocol_version",
            Self::RationalNumber => "rational",
            Self::Constitution => "constitution",
            Self::GovActionId => "gov_action_id",
            Self::TransactionId => "transaction_id",
            Self::WithdrawalEntry => "withdrawal",
            Self::DatumEntry => "datum_entry",
        }
    }
}

/// Named sum types in the Cardano schema — types with constructor
/// tags. Records with positional fields live in [`ContextType`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum SumTypeId {
    /// `Purpose` (V1/V2) — `Minting`, `Spending`, `Rewarding`,
    /// `Certifying`.
    Purpose,
    /// `ScriptInfo` (V3) — `Minting`, `Spending`, `Rewarding`,
    /// `Certifying`, `Voting`, `Proposing`.
    ScriptInfo,
    /// `Credential` — `VerificationKey`, `Script`.
    Credential,
    /// `OutputDatum` (V2/V3) — `NoDatum`, `DatumHash`, `InlineDatum`.
    OutputDatum,
    /// `IntervalBoundType` — `NegativeInfinity`, `Finite`,
    /// `PositiveInfinity`.
    IntervalBoundType,
    /// `Certificate` — 7 variants at V1/V2 (`DCert`), 11 at V3 (`TxCert`).
    Certificate,
    /// `Voter` (V3) — `ConstitutionalCommitteeMember`,
    /// `DelegateRepresentative`, `StakePool`.
    Voter,
    /// `DRep` (V3) — `Registered`, `AlwaysAbstain`, `AlwaysNoConfidence`.
    DRep,
    /// `GovernanceAction` (V3) — `ProtocolParameters`, `HardFork`, …
    GovernanceAction,
    /// `StakeCredential` (`Referenced<Credential>`) — `Inline` /
    /// `Pointer` over a [`Self::Credential`]; version-invariant. Its display
    /// name is `"staking_credential"`, NOT `"stake_credential"`: that is the
    /// [`ContextField`] name, and a binder called `stake_credential` holds an
    /// `Option<StakeCredential>`, so it must not resolve to this sum by name.
    StakeCredential,
    /// `Vote` (V3) — `No`, `Yes`, `Abstain`.
    Vote,
    /// `Bool` — `False`, `True`.
    Bool,
}

impl SumTypeId {
    /// Parse a rendered sum-type name back into a [`SumTypeId`].
    /// Returns `None` for names outside the sum-type set.
    pub(crate) fn from_display_name(name: &str) -> Option<Self> {
        Some(match name {
            "purpose" => Self::Purpose,
            "script_info" => Self::ScriptInfo,
            "credential" => Self::Credential,
            "output_datum" => Self::OutputDatum,
            "interval_bound_type" => Self::IntervalBoundType,
            "certificate" => Self::Certificate,
            "voter" => Self::Voter,
            "drep" => Self::DRep,
            "governance_action" => Self::GovernanceAction,
            "vote" => Self::Vote,
            "bool" => Self::Bool,
            "staking_credential" => Self::StakeCredential,
            _ => return None,
        })
    }

    /// Legacy stringly sum-type name — the inverse of
    /// [`Self::from_display_name`]. Always round-trips.
    pub(crate) fn display_name(self) -> &'static str {
        match self {
            Self::Purpose => "purpose",
            Self::ScriptInfo => "script_info",
            Self::Credential => "credential",
            Self::OutputDatum => "output_datum",
            Self::IntervalBoundType => "interval_bound_type",
            Self::Certificate => "certificate",
            Self::Voter => "voter",
            Self::DRep => "drep",
            Self::GovernanceAction => "governance_action",
            Self::Vote => "vote",
            Self::Bool => "bool",
            Self::StakeCredential => "staking_credential",
        }
    }
}

/// Tagged reference to either a record type ([`ContextType`]) or a sum
/// type ([`SumTypeId`]), as returned by `context_field_type`: a
/// field's static type may be either kind (`inputs : List<TxInInfo>` →
/// [`ContextType::TxInInfo`], `purpose : Purpose` →
/// [`SumTypeId::Purpose`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum FieldTypeRef {
    /// The field's static type is a record type with positional fields.
    Context(ContextType),
    /// The field's static type is a sum type with named constructors.
    Sum(SumTypeId),
}

impl FieldTypeRef {
    /// Parse a rendered type name back into a [`FieldTypeRef`].
    /// `None` for a name in neither enum.
    pub(crate) fn from_display_name(name: &str) -> Option<Self> {
        if let Some(ctx) = ContextType::from_display_name(name) {
            return Some(Self::Context(ctx));
        }
        SumTypeId::from_display_name(name).map(Self::Sum)
    }

    /// Legacy stringly name from the inner enum — always
    /// round-trips through [`Self::from_display_name`].
    pub(crate) fn display_name(self) -> &'static str {
        match self {
            Self::Context(ct) => ct.display_name(),
            Self::Sum(st) => st.display_name(),
        }
    }
}

/// Cardano type reference that distinguishes scalar record/sum
/// references from list, option, and sum-keyed-map ones, so the
/// cardano-context naming propagator can track a binding's element
/// type through list combinators (`List.head`, indexing, slicing) and
/// pair projections.
///
/// Carried around typed; [`Self::display_name`] is only for the
/// rendered surface (`VarKind::CardanoContext`, hint ids), where a
/// scalar variant matches its [`FieldTypeRef`] display name and a
/// compound one wraps it in a `list`/`option`/`map`/`pair` prefix.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum CardanoTypeRef {
    /// Scalar record type (e.g. `TxInInfo`).
    Record(ContextType),
    /// `List<T>` where `T` is a record type.
    ListOfRecords(ContextType),
    /// Scalar sum type (e.g. `Purpose`).
    Sum(SumTypeId),
    /// `List<T>` where `T` is a sum type (e.g. `List<Certificate>`).
    ListOfSums(SumTypeId),
    /// `Option<T>` where `T` is a record type; after `Some(x)`,
    /// `x : Record(T)`. Flat, not nested: the reachable graph never nests
    /// `Option<Option>` or `Option<List>`, so this stays `Copy`.
    OptionOfRecord(ContextType),
    /// `Option<T>` where `T` is a sum type (e.g.
    /// `Address.stake_credential : Option<StakeCredential>`). After `Some(x)`,
    /// `x : Sum(T)`.
    OptionOfSum(SumTypeId),
    /// A `Map`/`Pairs` whose KEY is the sum type `S`, e.g.
    /// `TxInfo.withdrawals : Pairs<Credential, _>`. After
    /// `builtin.un_map_data` it is a list of key-value pairs, so iterating
    /// it yields a [`Self::SumKeyedPair`]. Only the chainable key is
    /// tracked, not the value type.
    MapKeyedBySum(SumTypeId),
    /// One entry of a [`Self::MapKeyedBySum`] — a `Pair<S, _>` whose first
    /// component (`.1st` / `Pair.first`) is `Sum(S)`. The second is untracked.
    SumKeyedPair(SumTypeId),
}

impl CardanoTypeRef {
    /// Render for the surface that still needs a name: scalar variants
    /// match [`FieldTypeRef::display_name`], compound ones wrap that
    /// name in their `list`/`option`/`map`/`pair` prefix.
    pub(crate) fn display_name(self) -> String {
        match self {
            Self::Record(ct) => ct.display_name().to_string(),
            Self::Sum(st) => st.display_name().to_string(),
            Self::ListOfRecords(ct) => format!("list<{}>", ct.display_name()),
            Self::ListOfSums(st) => format!("list<{}>", st.display_name()),
            Self::OptionOfRecord(ct) => format!("option<{}>", ct.display_name()),
            Self::OptionOfSum(st) => format!("option<{}>", st.display_name()),
            Self::MapKeyedBySum(st) => format!("map<{}>", st.display_name()),
            Self::SumKeyedPair(st) => format!("pair<{}>", st.display_name()),
        }
    }

    /// If `self` is a [`Self::SumKeyedPair`], the key sum its `.1st` /
    /// `Pair.first` projects. `None` otherwise.
    pub(crate) fn pair_first_sum(self) -> Option<SumTypeId> {
        match self {
            Self::SumKeyedPair(st) => Some(st),
            _ => None,
        }
    }

    /// For an `Option<T>` variant, the unwrapped `T` — the type of the
    /// `Some(x)` payload. `None` for non-Option variants.
    pub(crate) fn option_inner(self) -> Option<Self> {
        match self {
            Self::OptionOfRecord(ct) => Some(Self::Record(ct)),
            Self::OptionOfSum(st) => Some(Self::Sum(st)),
            _ => None,
        }
    }

    /// If `self` is a list variant, return the element type. Returns
    /// `None` for scalar variants.
    pub(crate) fn element_type(self) -> Option<Self> {
        match self {
            Self::ListOfRecords(ct) => Some(Self::Record(ct)),
            Self::ListOfSums(st) => Some(Self::Sum(st)),
            // A key-sum map, after `un_map_data`, is a list whose element is a
            // key-sum pair (`[entry, ..]` / `map[i]` / `List.head`).
            Self::MapKeyedBySum(st) => Some(Self::SumKeyedPair(st)),
            _ => None,
        }
    }

    /// If `self` is `Record(ct)`, return `ct`. Otherwise `None`.
    pub(crate) fn record(self) -> Option<ContextType> {
        match self {
            Self::Record(ct) => Some(ct),
            _ => None,
        }
    }

    /// If `self` is `Sum(st)`, return `st`. Otherwise `None`.
    pub(crate) fn sum(self) -> Option<SumTypeId> {
        match self {
            Self::Sum(st) => Some(st),
            _ => None,
        }
    }

    /// Convert from a [`FieldTypeRef`] (no list-variant info).
    pub(crate) fn from_field_type_ref(ftr: FieldTypeRef) -> Self {
        match ftr {
            FieldTypeRef::Context(ct) => Self::Record(ct),
            FieldTypeRef::Sum(st) => Self::Sum(st),
        }
    }
}

/// Field identifiers reachable from a Cardano `ScriptContext`.
///
/// A name shared with a [`ContextType`] or [`SumTypeId`] (`tx_info`,
/// `credential`, `certificate`, …) means the FIELD here, not the type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum ContextField {
    // ScriptContext direct fields ---
    /// `tx_info` — transaction information (all versions).
    TxInfo,
    /// `purpose` — validator purpose (V1/V2 only).
    Purpose,
    /// `redeemer` — raw redeemer data (V3 only).
    Redeemer,
    /// `script_info` — script-info record (V3 only).
    ScriptInfo,
    // TxInfo top-level fields ---
    /// `inputs` — `List<TxInInfo>`.
    Inputs,
    /// `reference_inputs` — `List<TxInInfo>` (V2/V3 only).
    ReferenceInputs,
    /// `outputs` — `List<TxOut>`.
    Outputs,
    /// `fee` — transaction fee.
    Fee,
    /// `mint` — minted value.
    Mint,
    /// `certificates` — `List<Certificate>`.
    Certificates,
    /// `withdrawals` — staking withdrawals.
    Withdrawals,
    /// `valid_range` — validity `Interval`.
    ValidRange,
    /// `signatories` — extra required signatories.
    Signatories,
    /// `redeemers` — per-purpose redeemer map (V2/V3 only).
    Redeemers,
    /// `data` — datum-hash → datum map.
    Data,
    /// `id` — transaction id.
    Id,
    /// `votes` — governance votes (V3 only).
    Votes,
    /// `proposal_procedures` — governance proposals (V3 only).
    ProposalProcedures,
    /// `current_treasury_amount` (V3 only).
    CurrentTreasuryAmount,
    /// `treasury_donation` (V3 only).
    TreasuryDonation,
    // TxInInfo fields ---
    /// `out_ref` — the output reference being consumed.
    OutRef,
    /// `resolved` — the `TxOut` being consumed.
    Resolved,
    // TxOut fields ---
    /// `address` — the payment address.
    Address,
    /// `value` — the output value.
    Value,
    /// `datum_hash` — V1 legacy datum-hash field.
    DatumHash,
    /// `datum` — `OutputDatum` (V2/V3).
    Datum,
    /// `reference_script` — optional reference-script hash (V2/V3).
    ReferenceScript,
    // TxOutRef fields ---
    /// `tx_id` — transaction id.
    TxId,
    /// `output_index` — zero-based output index.
    OutputIndex,
    // Address fields ---
    /// `payment_credential` — spending credential.
    PaymentCredential,
    /// `stake_credential` — optional stake credential.
    StakeCredential,
    // Interval fields ---
    /// `lower_bound` — the interval's lower endpoint.
    LowerBound,
    /// `upper_bound` — the interval's upper endpoint.
    UpperBound,
    // Interval bound fields ---
    /// `bound_type` — `IntervalBoundType` sum.
    BoundType,
    /// `is_inclusive` — `Bool`.
    IsInclusive,
    // Context-field-type fallbacks ---
    /// `credential` — used as a field name on purpose/script-info
    /// constructors (Rewarding, Certifying).
    Credential,
    /// `output_reference` — used as a field name on purpose/script-info
    /// constructors (Spending).
    OutputReference,
    // Constructor-introduced fields ---
    /// `policy_id` — `Minting` purpose field.
    PolicyId,
    /// `index` — `Certifying`/`Proposing` constructor index.
    Index,
    /// `certificate` — `Certifying` field.
    Certificate,
    /// `voter` — `Voting` field.
    Voter,
    /// `proposal_procedure` — `Proposing` field.
    ProposalProcedure,
    /// `hash` — `Credential` payload.
    Hash,
    // ProposalProcedure (V3) field labels (surface
    // `cardano/governance.ProposalProcedure`).
    /// `deposit` — proposal deposit (Int lovelace).
    Deposit,
    /// `return_address` — credential the deposit is returned to.
    ReturnAddress,
    /// `governance_action` — the proposed [`SumTypeId::GovernanceAction`].
    /// A field LABEL, distinct from the `SumTypeId` of the same name.
    GovernanceAction,
    /// `major` — `ProtocolVersion` major (Int).
    Major,
    /// `minor` — `ProtocolVersion` minor (Int).
    Minor,
    /// `numerator` — `RationalNumber` numerator (Int).
    Numerator,
    /// `denominator` — `RationalNumber` denominator (Int).
    Denominator,
    // `StakeCredential::Pointer` fields (deprecated pointer addresses).
    /// `slot_number` — Pointer slot (Int).
    SlotNumber,
    /// `transaction_index` — Pointer tx index (Int).
    TransactionIndex,
    /// `certificate_index` — Pointer cert index (Int).
    CertificateIndex,
    // V1/V2 `DCert` (Certificate) payload field labels (surface
    // `transaction/certificate`).
    /// `delegator` — staking credential being (de)registered/delegated.
    Delegator,
    /// `delegatee` — the pool a stake credential delegates to.
    Delegatee,
    /// `pool_id` — stake-pool identifier.
    PoolId,
    /// `vrf` — pool VRF key hash.
    Vrf,
    /// `epoch` — retirement epoch.
    Epoch,
    // V3 `GovernanceAction` payload field labels, taken verbatim from
    // stdlib v2.2.0 `cardano/governance`.
    /// `ancestor` — last governance action of the same kind (chain link).
    Ancestor,
    /// `new_parameters` — proposed protocol-parameter update.
    NewParameters,
    /// `guardrails` — optional constitution guardrails script hash.
    Guardrails,
    /// `new_version` — proposed protocol version (hard fork).
    NewVersion,
    /// `beneficiaries` — treasury-withdrawal recipients.
    Beneficiaries,
    /// `evicted_members` — constitutional-committee members to remove.
    EvictedMembers,
    /// `added_members` — constitutional-committee members to add.
    AddedMembers,
    /// `quorum` — constitutional-committee quorum ratio.
    Quorum,
    /// `constitution` — proposed new constitution.
    Constitution,
}

impl ContextField {
    /// Parse a rendered field name back into a [`ContextField`].
    /// `None` for names outside the Cardano-schema field set.
    pub(crate) fn from_display_name(name: &str) -> Option<Self> {
        Some(match name {
            "tx_info" => Self::TxInfo,
            "purpose" => Self::Purpose,
            "redeemer" => Self::Redeemer,
            "script_info" => Self::ScriptInfo,
            "inputs" => Self::Inputs,
            "reference_inputs" => Self::ReferenceInputs,
            "outputs" => Self::Outputs,
            "fee" => Self::Fee,
            "mint" => Self::Mint,
            "certificates" => Self::Certificates,
            "withdrawals" => Self::Withdrawals,
            "valid_range" => Self::ValidRange,
            "signatories" => Self::Signatories,
            "redeemers" => Self::Redeemers,
            // Ledger name `data`, rendered as `datums` — the field is a
            // `DatumHash -> Datum` map, and `un_map_data(data)` reads as
            // if `data` were the `Data` type. Both spellings parse.
            "data" | "datums" => Self::Data,
            // The ledger calls this field `id` (`uplc`'s `TxInfo`
            // serialises it as the last slot of V1/V2 and slot 11 of V3);
            // the render says `transaction_id`, which is the same field
            // spelled so it cannot be read as a generic identifier. Both
            // spellings parse.
            "id" | "transaction_id" => Self::Id,
            "votes" => Self::Votes,
            "proposal_procedures" => Self::ProposalProcedures,
            "current_treasury_amount" => Self::CurrentTreasuryAmount,
            "treasury_donation" => Self::TreasuryDonation,
            "out_ref" => Self::OutRef,
            "resolved" => Self::Resolved,
            "address" => Self::Address,
            "value" => Self::Value,
            "datum_hash" => Self::DatumHash,
            "datum" => Self::Datum,
            "reference_script" => Self::ReferenceScript,
            "tx_id" => Self::TxId,
            "output_index" => Self::OutputIndex,
            "payment_credential" => Self::PaymentCredential,
            "stake_credential" => Self::StakeCredential,
            "lower_bound" => Self::LowerBound,
            "upper_bound" => Self::UpperBound,
            "bound_type" => Self::BoundType,
            "is_inclusive" => Self::IsInclusive,
            "credential" => Self::Credential,
            "output_reference" => Self::OutputReference,
            "policy_id" => Self::PolicyId,
            "index" => Self::Index,
            "certificate" => Self::Certificate,
            "voter" => Self::Voter,
            "proposal_procedure" => Self::ProposalProcedure,
            "hash" => Self::Hash,
            "deposit" => Self::Deposit,
            "return_address" => Self::ReturnAddress,
            "governance_action" => Self::GovernanceAction,
            "major" => Self::Major,
            "minor" => Self::Minor,
            "numerator" => Self::Numerator,
            "denominator" => Self::Denominator,
            "slot_number" => Self::SlotNumber,
            "transaction_index" => Self::TransactionIndex,
            "certificate_index" => Self::CertificateIndex,
            "delegator" => Self::Delegator,
            "delegatee" => Self::Delegatee,
            "pool_id" => Self::PoolId,
            "vrf" => Self::Vrf,
            "epoch" => Self::Epoch,
            "ancestor" => Self::Ancestor,
            "new_parameters" => Self::NewParameters,
            "guardrails" => Self::Guardrails,
            "new_version" => Self::NewVersion,
            "beneficiaries" => Self::Beneficiaries,
            "evicted_members" => Self::EvictedMembers,
            "added_members" => Self::AddedMembers,
            "quorum" => Self::Quorum,
            "constitution" => Self::Constitution,
            _ => return None,
        })
    }

    /// How this field is NAMED in the rendered output — the inverse of
    /// [`Self::from_display_name`]. Always round-trips.
    pub(crate) fn display_name(self) -> &'static str {
        match self {
            Self::TxInfo => "tx_info",
            Self::Purpose => "purpose",
            Self::Redeemer => "redeemer",
            Self::ScriptInfo => "script_info",
            Self::Inputs => "inputs",
            Self::ReferenceInputs => "reference_inputs",
            Self::Outputs => "outputs",
            Self::Fee => "fee",
            Self::Mint => "mint",
            Self::Certificates => "certificates",
            Self::Withdrawals => "withdrawals",
            Self::ValidRange => "valid_range",
            Self::Signatories => "signatories",
            Self::Redeemers => "redeemers",
            Self::Data => "datums",
            Self::Id => "transaction_id",
            Self::Votes => "votes",
            Self::ProposalProcedures => "proposal_procedures",
            Self::CurrentTreasuryAmount => "current_treasury_amount",
            Self::TreasuryDonation => "treasury_donation",
            Self::OutRef => "out_ref",
            Self::Resolved => "resolved",
            Self::Address => "address",
            Self::Value => "value",
            Self::DatumHash => "datum_hash",
            Self::Datum => "datum",
            Self::ReferenceScript => "reference_script",
            Self::TxId => "tx_id",
            Self::OutputIndex => "output_index",
            Self::PaymentCredential => "payment_credential",
            Self::StakeCredential => "stake_credential",
            Self::LowerBound => "lower_bound",
            Self::UpperBound => "upper_bound",
            Self::BoundType => "bound_type",
            Self::IsInclusive => "is_inclusive",
            Self::Credential => "credential",
            Self::OutputReference => "output_reference",
            Self::PolicyId => "policy_id",
            Self::Index => "index",
            Self::Certificate => "certificate",
            Self::Voter => "voter",
            Self::ProposalProcedure => "proposal_procedure",
            Self::Hash => "hash",
            Self::Deposit => "deposit",
            Self::ReturnAddress => "return_address",
            Self::GovernanceAction => "governance_action",
            Self::Major => "major",
            Self::Minor => "minor",
            Self::Numerator => "numerator",
            Self::Denominator => "denominator",
            Self::SlotNumber => "slot_number",
            Self::TransactionIndex => "transaction_index",
            Self::CertificateIndex => "certificate_index",
            Self::Delegator => "delegator",
            Self::Delegatee => "delegatee",
            Self::PoolId => "pool_id",
            Self::Vrf => "vrf",
            Self::Epoch => "epoch",
            Self::Ancestor => "ancestor",
            Self::NewParameters => "new_parameters",
            Self::Guardrails => "guardrails",
            Self::NewVersion => "new_version",
            Self::Beneficiaries => "beneficiaries",
            Self::EvictedMembers => "evicted_members",
            Self::AddedMembers => "added_members",
            Self::Quorum => "quorum",
            Self::Constitution => "constitution",
        }
    }
}

#[cfg(test)]
mod tests;
