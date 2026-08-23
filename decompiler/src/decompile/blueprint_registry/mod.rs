//! Render-time registry for constructor display names.
//!
//! Two namespaces of blueprint hints:
//!
//! **Cardano-schema entries** keyed by [`SumTypeId`] + tag, seeded at
//!   pipeline startup with the canonical Cardano sum-type constructor
//!   names so late passes never re-derive them from string compares.
//! **User-ADT entries** keyed by [`TypeHintId`] + tag, populated from
//!   `BlueprintHints` (extracted from `plutus.json`) so a project's own
//!   ADT constructor names survive into rendering.

use std::collections::HashMap;
use std::rc::Rc;

use crate::decompile::ScriptVersion;
use crate::decompile::simplify::postprocess::{SumTypeId, sum_type_constructor_names};
use crate::pseudo::constructor::ConstructorShape;
pub(crate) use crate::pseudo::type_hint::TypeHintId;

/// Canonical V1/V2 [`SumTypeId::Purpose`] constructor names,
/// indexed by Plutus `Constr` tag.
const PURPOSE_V1_V2_NAMES: &[&str] = &["Minting", "Spending", "Rewarding", "Certifying"];

/// Canonical V3 [`SumTypeId::ScriptInfo`] constructor names,
/// indexed by Plutus `Constr` tag — the V1/V2 layout plus
/// `Voting` and `Proposing`.
const SCRIPT_INFO_V3_NAMES: &[&str] = &[
    "Minting",
    "Spending",
    "Rewarding",
    "Certifying",
    "Voting",
    "Proposing",
];

/// Version-INDEPENDENT sum types, seeded under their `SumTypeId`
/// legacy-name `TypeHintId` so `name_cardano_sum_arms` can stamp the
/// hint on a `when <subject> is { … }` pattern and have
/// [`Self::resolve`] return the constructor name.
///
/// Fixed by the Plutus ledger ABI and identical across V1/V2/V3, so
/// they need no version; keep them in sync with
/// `simplify::postprocess::context::sum_type_constructor_names`.
/// Version-DEPENDENT sum types are seeded only where the version is
/// known — see the gated arms of `with_cardano_seed`.
const INTERVAL_BOUND_TYPE_NAMES: &[&str] = &["NegativeInfinity", "Finite", "PositiveInfinity"];
const CREDENTIAL_NAMES: &[&str] = &["VerificationKey", "Script"];

/// Canonical Plutus `Data` variant names by tag, keyed under
/// [`TypeHintId`]`::new("Data")`.
///
/// Lets `data_resolution::resolve_data_case` (the V3 `Data.case`
/// handler) render its patterns from the registry instead of stamping
/// names onto the per-AST-node `display_name` field.
const DATA_VARIANT_NAMES: &[&str] = &["Constr", "Map", "List", "Int", "ByteString"];

/// Canonical stdlib `Option` constructor names by tag under the
/// [`TypeHintId`]`::new("Option")` namespace.
///
/// Late passes that emit arity-inconsistent `Some`/`None` placeholders
/// (e.g. `rename_option_pattern`'s empty-fields `Some`) tag the pattern
/// with `type_hint` and recover the display name here at render time.
const OPTION_NAMES: &[&str] = &["Some", "None"];

/// Well-known [`TypeHintId`] for the Plutus `Data` variant namespace —
/// see [`DATA_VARIANT_NAMES`].
pub(crate) const DATA_TYPE_HINT_NAME: &str = "Data";

/// Well-known [`TypeHintId`] for the stdlib `Option` namespace — see
/// [`OPTION_NAMES`].
pub(crate) const OPTION_TYPE_HINT_NAME: &str = "Option";

/// Render-time hint registry for constructor display names.
///
/// Seed with [`Self::with_cardano_seed`]; query at render time with
/// [`Self::resolve`] (user namespace) or [`Self::resolve_cardano`]
/// (Cardano-schema namespace).
#[derive(Debug, Clone, Default)]
pub(crate) struct BlueprintHintRegistry {
    /// Cardano-schema sum-type constructors keyed by `(sum_type, tag)`.
    entries: HashMap<(SumTypeId, usize), Rc<str>>,
    /// User-defined ADT constructors keyed by `(type_hint, tag)`.
    user_entries: HashMap<(TypeHintId, usize), Rc<str>>,
}

impl BlueprintHintRegistry {
    /// Build an empty registry.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Build a registry pre-populated with the canonical Cardano-schema
    /// constructor names.
    ///
    /// Seeds [`SumTypeId::Purpose`] (V1/V2 `ScriptPurpose`) and
    /// [`SumTypeId::ScriptInfo`] (V3) into the Cardano namespace, the
    /// version-independent sum types into the user namespace, and the
    /// version-gated ones `version` makes unambiguous.
    pub(crate) fn with_cardano_seed(version: Option<ScriptVersion>) -> Self {
        let mut reg = Self::new();
        for (tag, name) in PURPOSE_V1_V2_NAMES.iter().enumerate() {
            reg.register_cardano(SumTypeId::Purpose, tag, name);
        }
        for (tag, name) in SCRIPT_INFO_V3_NAMES.iter().enumerate() {
            reg.register_cardano(SumTypeId::ScriptInfo, tag, name);
        }
        let data_hint = TypeHintId::new(DATA_TYPE_HINT_NAME);
        for (tag, name) in DATA_VARIANT_NAMES.iter().enumerate() {
            reg.register_user(data_hint.clone(), tag, *name);
        }
        let option_hint = TypeHintId::new(OPTION_TYPE_HINT_NAME);
        for (tag, name) in OPTION_NAMES.iter().enumerate() {
            reg.register_user(option_hint.clone(), tag, *name);
        }
        // Version-independent sum types, keyed under their `SumTypeId`
        // legacy name; inert until a pattern carries the hint.
        let ibt_hint = TypeHintId::new(SumTypeId::IntervalBoundType.display_name());
        for (tag, name) in INTERVAL_BOUND_TYPE_NAMES.iter().enumerate() {
            reg.register_user(ibt_hint.clone(), tag, *name);
        }
        let credential_hint = TypeHintId::new(SumTypeId::Credential.display_name());
        for (tag, name) in CREDENTIAL_NAMES.iter().enumerate() {
            reg.register_user(credential_hint.clone(), tag, *name);
        }
        // `Referenced<Credential>` (StakeCredential) — same `Inline`/`Pointer`
        // shape in V1/V2/V3, so seed it unconditionally; resolves the
        // `"staking_credential"` hint `name_cardano_sum_arms` stamps.
        let staking_credential_hint = TypeHintId::new(SumTypeId::StakeCredential.display_name());
        for (tag, name) in ["Inline", "Pointer"].iter().enumerate() {
            reg.register_user(staking_credential_hint.clone(), tag, *name);
        }
        // Version-gated sum types. Certificate's ctor names DIFFER between
        // V1/V2 (`DCert`, 7 ctors) and V3 (`TxCert`, 11 ctors) under the
        // SAME `"certificate"` hint key, so an unknown version (`None`) must
        // seed NEITHER — else a wrong-version name renders. V3 is skipped
        // too: `name_cardano_sum_arms` does not name V3 certificates (the
        // Conway `Never` deposit/refund makes their arity unnameable).
        match version {
            Some(v @ (ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2)) => {
                reg.seed_sum_user(SumTypeId::Certificate, v);
                // Purpose is already in the cardano `entries`, but `resolve`
                // only consults `user_entries` — the same gap the V3
                // `ScriptInfo` arm below closes. Without this a `when purpose
                // is { … }` that `name_cardano_sum_arms` stamped renders its
                // arms as raw `Constr<3>(certificate)`: the payload named from
                // the schema, the constructor not. V1/V2-gated because the V3
                // ScriptPurpose is `ScriptInfo`, with two more constructors.
                reg.seed_sum_user(SumTypeId::Purpose, v);
            }
            // V3 `GovernanceAction` (Conway, 7 ctors). `name_cardano_sum_arms`
            // stamps the `"governance_action"` hint only under explicit V3, and
            // without these entries such an arm renders as a raw `Constr<tag>`.
            Some(v @ ScriptVersion::PlutusV3) => {
                reg.seed_sum_user(SumTypeId::GovernanceAction, v);
                // ScriptInfo is already in the cardano `entries`, but `resolve` only
                // consults `user_entries` — seed it under the `"script_info"` hint
                // too, or a stamped ScriptInfo arm renders as `Constr<5>`.
                reg.seed_sum_user(SumTypeId::ScriptInfo, v);
                // V3 `Voter` (ConstitutionalCommitteeMember / DelegateRepresentative
                // / StakePool) — V3-only; resolves its stamped `"voter"` hint.
                reg.seed_sum_user(SumTypeId::Voter, v);
            }
            None => {}
        }
        // `OutputDatum` (NoDatum / DatumHash / InlineDatum) exists only in
        // V2/V3, so a stamped `"output_datum"` hint from a
        // `when output.datum is { … }` resolves under those versions only.
        if let Some(v @ (ScriptVersion::PlutusV2 | ScriptVersion::PlutusV3)) = version {
            reg.seed_sum_user(SumTypeId::OutputDatum, v);
        }
        reg
    }

    /// Register every constructor name of `sum` at `version` into the user
    /// namespace under the `SumTypeId` legacy-name `TypeHintId`, so
    /// [`Self::resolve`] answers a stamped sum-type hint. Names come from
    /// `sum_type_constructor_names`.
    fn seed_sum_user(&mut self, sum: SumTypeId, version: ScriptVersion) {
        if let Some(names) = sum_type_constructor_names(sum, version) {
            let hint = TypeHintId::new(sum.display_name());
            for (tag, name) in names.iter().enumerate() {
                self.register_user(hint.clone(), tag, *name);
            }
        }
    }

    /// Resolve a constructor's display name for rendering.
    ///
    /// Lookup order:
    ///
    /// 1. A `Some` `type_hint` hits the user-ADT table at
    ///    `(hint, shape.tag())`.
    /// 2. On miss, a [`ConstructorShape::Known`] shape yields its
    ///    [`KnownConstructor::pretty_name`] — the closed set is the
    ///    source of truth for built-in shapes regardless of registry
    ///    state.
    /// 3. Otherwise `None`, leaving the caller to fall back to the
    ///    `display_name` the AST node carries.
    ///
    /// This never consults the Cardano-schema namespace; a caller that
    /// knows the surrounding dispatch's [`SumTypeId`] uses
    /// [`Self::resolve_cardano`].
    pub(crate) fn resolve(
        &self,
        shape: ConstructorShape,
        type_hint: Option<&TypeHintId>,
    ) -> Option<Rc<str>> {
        let tag = shape.tag();
        if let Some(hint) = type_hint
            && let Some(name) = self.user_entries.get(&(hint.clone(), tag))
        {
            return Some(name.clone());
        }
        shape.pretty_name().map(Rc::from)
    }

    /// Resolve a Cardano-schema constructor by its sum-type id and tag,
    /// or `None` when `(sum_type, tag)` was never registered. Seeded by
    /// [`Self::with_cardano_seed`] at pipeline startup.
    pub(crate) fn resolve_cardano(&self, sum_type: SumTypeId, tag: usize) -> Option<Rc<str>> {
        self.entries.get(&(sum_type, tag)).cloned()
    }

    /// Register a Cardano-schema constructor name, overwriting any
    /// previous entry for `(sum_type, tag)`. Takes `&'static str`:
    /// Cardano-schema names are compile-time constants from
    /// `simplify::postprocess::context`.
    pub(crate) fn register_cardano(&mut self, sum_type: SumTypeId, tag: usize, name: &'static str) {
        self.entries.insert((sum_type, tag), Rc::from(name));
    }

    /// Register a constructor for the V1/V2 [`SumTypeId::Purpose`] sum type.
    pub(crate) fn register_cardano_purpose(&mut self, tag: usize, name: &'static str) {
        self.register_cardano(SumTypeId::Purpose, tag, name);
    }

    /// Register a user ADT constructor name, overwriting any previous
    /// entry for `(hint, tag)`. Takes `impl Into<Rc<str>>` because
    /// user-ADT names arrive as borrowed slices from blueprint JSON.
    pub(crate) fn register_user(&mut self, hint: TypeHintId, tag: usize, name: impl Into<Rc<str>>) {
        self.user_entries.insert((hint, tag), name.into());
    }

    /// `true` when no entries have been registered.
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty() && self.user_entries.is_empty()
    }

    /// Total number of registered entries across both namespaces.
    pub(crate) fn len(&self) -> usize {
        self.entries.len() + self.user_entries.len()
    }
}

#[cfg(test)]
mod tests;
