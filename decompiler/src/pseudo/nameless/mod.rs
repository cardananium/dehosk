//! Nameless intermediate representation for the simplifier.
//!
//! `NamelessExpr` mirrors `PseudoExpr`, but variables carry only
//! `VarId`, never a `String` name. The dispatch information the
//! simplifier otherwise sniffs out of names lives in
//! [`VarTable`], keyed by `VarId`.
//!
//! The pipeline bridges through `PseudoExpr` before and after the
//! nameless segment.

use std::collections::HashMap;

use num_bigint::BigInt;

use super::ast::{BinaryOp, HelperIntrinsic, PseudoData, UnaryOp};
use super::constructor::ConstructorShape;
use super::field_selector::FieldSelector;
use super::var_id::VarId;
use crate::builtins::BuiltinId;

// =============================================================
// NamelessExpr
// =============================================================

/// Pseudo-IR with names erased from variable references.
///
/// Mirrors [`super::ast::PseudoExpr`] structurally, except that
/// [`NamelessExpr::Var`], every [`Binder`](super::ast::Binder)
/// position, and `When` subject names are bare [`VarId`].
/// Patterns mirror this.
///
/// Build through the converters in this module
/// (`pseudo_to_nameless`); a hand-built `NamelessExpr` must keep
/// every `VarId` either referencing an in-scope binder or
/// appearing in the entry-lambda parameter set.
#[derive(Debug, Clone)]
pub(crate) enum NamelessExpr {
    // ===== Literals =====
    Int(BigInt),
    ByteArray(Vec<u8>),
    String(String),
    Bool(bool),
    Unit,

    // ===== Variables =====
    /// Variable reference. The `VarId` is the only identity —
    /// names live in [`VarTable`].
    Var(VarId),

    // ===== Functions =====
    Lambda {
        params: Vec<VarId>,
        body: Box<NamelessExpr>,
    },
    RecFn {
        name: VarId,
        params: Vec<VarId>,
        body: Box<NamelessExpr>,
    },
    Apply {
        function: Box<NamelessExpr>,
        args: Vec<NamelessExpr>,
    },

    // ===== Bindings =====
    Let {
        binder: VarId,
        value: Box<NamelessExpr>,
        body: Box<NamelessExpr>,
    },

    // ===== Control Flow =====
    If {
        condition: Box<NamelessExpr>,
        then_branch: Box<NamelessExpr>,
        else_branch: Box<NamelessExpr>,
    },
    When {
        subject: Box<NamelessExpr>,
        subject_name: Option<VarId>,
        clauses: Vec<NamelessClause>,
    },

    // ===== Data Structures =====
    List {
        elements: Vec<NamelessExpr>,
        tail: Option<Box<NamelessExpr>>,
    },
    Tuple(Vec<NamelessExpr>),
    Pair(Box<NamelessExpr>, Box<NamelessExpr>),
    Constr {
        type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
        tag: usize,
        fields: Vec<NamelessExpr>,
        shape: ConstructorShape,
    },

    // ===== Field / Index Access =====
    FieldAccess {
        record: Box<NamelessExpr>,
        selector: FieldSelector,
    },
    IndexAccess {
        collection: Box<NamelessExpr>,
        index: usize,
    },

    // ===== Operators =====
    BinOp {
        op: BinaryOp,
        left: Box<NamelessExpr>,
        right: Box<NamelessExpr>,
    },
    UnOp {
        op: UnaryOp,
        operand: Box<NamelessExpr>,
    },
    BuiltinCall {
        name: BuiltinId,
        args: Vec<NamelessExpr>,
    },

    // ===== Special =====
    Error {
        message: Option<String>,
    },
    Delay(Box<NamelessExpr>),
    Force(Box<NamelessExpr>),
    Trace {
        message: Box<NamelessExpr>,
        value: Box<NamelessExpr>,
    },
    Raw {
        uplc: String,
        reason: String,
    },

    // ===== Cardano-specific =====
    Data(Box<PseudoData>),

    // ===== Intrinsic markers =====
    HelperSymbol(HelperIntrinsic),
}

/// Pattern-matching clause in nameless form.
#[derive(Debug, Clone)]
pub(crate) struct NamelessClause {
    pub pattern: NamelessPattern,
    pub guard: Option<NamelessExpr>,
    pub body: NamelessExpr,
}

/// When-pattern in nameless form. All binders are bare `VarId`.
#[derive(Debug, Clone)]
pub(crate) enum NamelessPattern {
    Wildcard,
    Var(VarId),
    Literal(NamelessExpr),
    Constructor {
        type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
        tag: usize,
        fields: Vec<VarId>,
        shape: ConstructorShape,
    },
    List {
        elements: Vec<VarId>,
        tail: Option<VarId>,
    },
    Tuple(Vec<VarId>),
    Pair(VarId, VarId),
}

// =============================================================
// VarTable + VarMetadata
// =============================================================

/// Side table mapping `VarId` → metadata.
///
/// Single source of truth for what the simplifier would otherwise
/// sniff out of variable names: schema-derived field kinds
/// (`FieldIndexAlias`), Cardano-context types, call-result hints.
#[derive(Debug, Clone, Default)]
pub(crate) struct VarTable {
    metadata: HashMap<VarId, VarMetadata>,
}

impl VarTable {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn insert(&mut self, id: VarId, metadata: VarMetadata) {
        self.metadata.insert(id, metadata);
    }

    pub(crate) fn get(&self, id: VarId) -> Option<&VarMetadata> {
        self.metadata.get(&id)
    }

    pub(crate) fn get_mut(&mut self, id: VarId) -> Option<&mut VarMetadata> {
        self.metadata.get_mut(&id)
    }

    pub(crate) fn contains(&self, id: VarId) -> bool {
        self.metadata.contains_key(&id)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&VarId, &VarMetadata)> {
        self.metadata.iter()
    }

    pub(crate) fn len(&self) -> usize {
        self.metadata.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.metadata.is_empty()
    }
}

/// Per-VarId metadata threading through the nameless IR.
#[derive(Debug, Clone)]
pub(crate) struct VarMetadata {
    /// Where this `VarId` was minted in the pipeline.
    pub origin: VarOrigin,

    /// Human-readable source/semantic name hint attached at mint time
    /// (typically the original UPLC variable name or a readability-rewrite
    /// suggestion). Pure annotation — never a dispatch source.
    pub name_hint: Option<String>,

    /// Final display-name override assigned by the late nameless naming
    /// owner. Raising back to `PseudoExpr` prefers it over `name_hint`,
    /// so `assign_names` leaves the original hint intact.
    pub display_name_hint: Option<String>,

    /// Type / role tag, used by Cardano-context naming and other
    /// dispatch passes WITHOUT relying on string names.
    pub kind: VarKind,
}

impl VarMetadata {
    /// Construct a "user binder" metadata entry — the default for
    /// vars whose origin is the original UPLC source.
    pub(crate) fn user(name_hint: impl Into<Option<String>>) -> Self {
        Self {
            origin: VarOrigin::UserBinder,
            name_hint: name_hint.into(),
            display_name_hint: None,
            kind: VarKind::User,
        }
    }

    /// Construct a synthetic-pass metadata entry.
    pub(crate) fn synthetic(producer: &'static str, hint: impl Into<Option<String>>) -> Self {
        Self {
            origin: VarOrigin::Synthetic {
                producer_pass: producer,
            },
            name_hint: hint.into(),
            display_name_hint: None,
            kind: VarKind::Synthetic,
        }
    }

    /// Name used when raising nameless IR for rendering.
    ///
    /// Skips empty-string hints in either slot so a stray `Some("")`
    /// doesn't shadow a meaningful fallback. Mirrors the
    /// `is_some_and(|n| !n.is_empty())` policy in
    /// `assign_names::candidate_name`.
    pub(crate) fn render_name_hint(&self) -> Option<&str> {
        self.display_name_hint
            .as_deref()
            .filter(|n| !n.is_empty())
            .or_else(|| self.name_hint.as_deref().filter(|n| !n.is_empty()))
    }
}

/// Where a `VarId` was introduced.
#[derive(Debug, Clone)]
pub(crate) enum VarOrigin {
    /// A binder from the original UPLC source (DeBruijn-named or
    /// MIR-lowered from a user lambda / let).
    UserBinder,
    /// A lambda parameter introduced by simplifier rewrites.
    LambdaParam,
    /// A let-binder introduced by simplifier rewrites.
    LetBinder,
    /// A binder minted by a specific simplifier pass.
    Synthetic { producer_pass: &'static str },
}

/// Type / role classification for a `VarId`. Each variant stands
/// in for a name-pattern dispatch site in the simplifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum VarKind {
    /// User-level binder — no special handling.
    User,

    /// Generic synthetic alias — no specific kind information.
    /// Use sparingly; prefer a specific variant.
    Synthetic,

    /// Synthetic alias for `parent.fields[index]`. Replaces the
    /// `field_N` name-pattern dispatch in
    /// `simplify::let_binding::aliases::introduce_field_index_aliases`.
    FieldIndexAlias { parent: VarId, index: usize },

    /// Synthetic alias for `parent[start..]` (List.tail chain).
    /// Replaces the textual `[N..]` chain detection in
    /// `simplify::transform::tail_chain_offsets`.
    SliceTailAlias { parent: VarId, depth: usize },

    /// Result of a function application. Replaces the
    /// `{fn}_result` name-pattern dispatch in
    /// `simplify::helpers::naming::suggest_generated_binding_name`.
    CallResult { callee: VarId },

    /// Hoisted large data literal. Replaces the
    /// `data_literal_N` name-pattern dispatch in
    /// `simplify::apply::hoist::hoist_large_data_literals_from_apply_args`.
    DataLiteralHoist,

    /// Cardano-context-typed binder (script_context, tx_info,
    /// redeemer, script_info). Replaces the string match in
    /// `cardano_context_naming::resolve_cardano_field_names`.
    /// `context_type` is a stringly tag, keeping
    /// `pseudo::nameless` decoupled from `decompile::simplify`'s
    /// internal `ContextType`.
    CardanoContext { context_type: String },

    /// Constr-payload binder — the K-th binder in a Constr<N> pattern
    /// at `pattern_id`. Minted by
    /// `pipeline::sync_late_constr_payload_kind_annotations`, consumed
    /// by `assign_names` to canonicalise unnamed constructor-pattern
    /// binders to `item_{index}`; a binder that already carries a
    /// meaningful name hint keeps it.
    ///
    /// `dangling_field_alias::repair_dangling_constr_payload_binders`
    /// is a name-level orphan-recovery pass over stray reference names
    /// and does NOT consume this kind.
    ConstrPayload { pattern_id: usize, index: usize },

    /// User-ADT field binder named from blueprint metadata. Distinct
    /// from `CardanoContext` so the Cardano-schema field-name lookup
    /// (`record_cardano_context_kind` in `cardano_context_naming.rs`)
    /// doesn't false-hit on user type names.
    ///
    /// Populated by `propagate_types_and_name_constructors` when a
    /// `WhenPattern::Constructor` carries a `TypeHintId` matching a
    /// user-ADT in `BlueprintHints::types`. Consumed by
    /// `assign_names::candidate_name`, which renders the binder as
    /// `field_name` instead of `field_N` / `item_N`.
    UserAdtField {
        type_name: String,
        field_name: String,
    },

    /// Validator entry point — the outermost Lambda after
    /// `hoist_local_helpers` has lifted top-level helpers into a Let
    /// chain. Render-prep wraps it in a synthetic `Let { name:
    /// "decompiled", kind: ValidatorEntry, value: <entry-Lambda>,
    /// body: <rest-of-chain> }`. The name is `decompiled` because
    /// `validator` collides with the keyword and renders as
    /// `validator_`. The kind lets the renderer find the entry
    /// without a name pattern, emit it as
    /// `fn decompiled(args) { ... }` instead of
    /// `let decompiled = fn(args) { ... }`, and place it first in the
    /// top-level output instead of last.
    ///
    /// the surface allows forward references between top-level declarations,
    /// so promoting the entry above its helpers keeps the rendered
    /// output well-scoped.
    ValidatorEntry,

    /// A validator-entry ROLE parameter (`datum` / `redeemer`) named by
    /// a validator-param rename. `param_name` is the role name; the
    /// trailing position is enforced at stamp time so a blueprint-named
    /// leading user param (even if coincidentally `datum`/`redeemer`) is
    /// never marked.
    ///
    ///   - `authoritative: true` — stamped by the LATE (post-uncurry)
    ///     rename, which the reverse-walk selector uses to pick the TRUE
    ///     entry. In `assign_names` it CLAIMS its bare role name.
    ///   - `authoritative: false` — stamped by the EARLY (pre-uncurry)
    ///     rename, which can name a NON-entry helper. Such a param
    ///     YIELDS its role name (gets suffixed) when an authoritative
    ///     param claims the same name; otherwise it keeps its name, the
    ///     fallback when the late rename found no entry.
    ///
    /// The marker — not VarId or fold order — is the entry-vs-helper
    /// discriminator. VarId ordering is NOT sound: a true entry's
    /// redeemer can carry a HIGHER VarId than a helper's, and in another
    /// script a LOWER VarId than a same-named body binder, so any VarId
    /// rule fixes one and regresses the other. Matching competitors by
    /// the (non-authoritative) marker — never by a broad name match —
    /// keeps genuine user `let redeemer = ...` binders (kind `User`)
    /// untouched.
    ///
    /// `script_context` is intentionally NOT marked: it carries
    /// `CardanoContext` (one kind per VarId) and is resolved by the
    /// descending-VarId "live binder wins" path in `candidate_name`.
    ValidatorEntryParam {
        param_name: String,
        authoritative: bool,
    },
}

impl VarKind {
    /// True for any kind the simplifier or pipeline mints itself
    /// rather than receiving from user code.
    pub(crate) fn is_generated_synthetic(&self) -> bool {
        matches!(
            self,
            Self::Synthetic
                | Self::FieldIndexAlias { .. }
                | Self::SliceTailAlias { .. }
                | Self::CallResult { .. }
                | Self::DataLiteralHoist
                | Self::ConstrPayload { .. }
                | Self::UserAdtField { .. }
        )
    }
}

// =============================================================
// Tests
// =============================================================

#[cfg(test)]
mod tests;

pub mod convert;
pub mod fold;
pub mod invariants;
