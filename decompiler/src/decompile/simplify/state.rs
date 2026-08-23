use std::collections::{BTreeMap, HashMap, HashSet};

use crate::builtins::BuiltinId;
use crate::decompile::ScriptVersion;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

/// Binding-indexed set keyed only by stable VarId.
#[derive(Clone, Default)]
pub(crate) struct BindingVarSet {
    ids: HashSet<VarId>,
}

impl BindingVarSet {
    pub(crate) fn contains(&self, id: VarId) -> bool {
        self.ids.contains(&id)
    }

    pub(crate) fn insert_binding(&mut self, _name: impl Into<String>, id: Option<VarId>) -> bool {
        id.is_some_and(|vid| self.insert(vid))
    }

    pub(crate) fn insert(&mut self, id: VarId) -> bool {
        self.ids.insert(id)
    }

    pub(crate) fn remove(&mut self, id: VarId) -> bool {
        self.ids.remove(&id)
    }
}

/// Binding-indexed map keyed only by stable VarId.
///
/// Ordered by `VarId`, not hashed: call sites SCAN this map for the first
/// entry matching a predicate (`destructure_when_fields` picks the
/// `<subject>.fields` alias to destructure against), and the same subject
/// can be aliased by several bindings. Under a `HashMap` the per-process
/// hash seed would decide that winner and the decompilation would differ
/// across runs; binding-id order picks the earliest-allocated alias.
#[derive(Clone)]
pub(crate) struct BindingVarMap<T> {
    by_id: BTreeMap<VarId, T>,
}

impl<T> BindingVarMap<T> {
    pub(crate) fn get(&self, id: VarId) -> Option<&T> {
        self.by_id.get(&id)
    }

    pub(crate) fn insert_binding(
        &mut self,
        _name: impl Into<String>,
        id: Option<VarId>,
        value: T,
    ) -> Option<T> {
        id.and_then(|vid| self.insert(vid, value))
    }

    pub(crate) fn insert(&mut self, id: VarId, value: T) -> Option<T> {
        self.by_id.insert(id, value)
    }

    pub(crate) fn remove(&mut self, id: VarId) -> Option<T> {
        self.by_id.remove(&id)
    }

    pub(crate) fn values(&self) -> std::collections::btree_map::Values<'_, VarId, T> {
        self.by_id.values()
    }

    /// Ascending `VarId` order — predicate scans over this iterator decide
    /// rewrites, so the order is part of the contract.
    pub(crate) fn iter(&self) -> std::collections::btree_map::Iter<'_, VarId, T> {
        self.by_id.iter()
    }
}

impl<T: Clone> BindingVarMap<T> {
    pub(crate) fn extend_from(&mut self, other: &Self) {
        self.by_id
            .extend(other.by_id.iter().map(|(k, v)| (*k, v.clone())));
    }
}

impl<T> Default for BindingVarMap<T> {
    fn default() -> Self {
        Self {
            by_id: BTreeMap::new(),
        }
    }
}

/// Output from a simplification pass, carrying context data needed for post-processing.
pub(crate) struct SimplifyOutput {
    /// The simplified expression.
    pub expr: PseudoExpr,
    /// Maps variable name → semantic name (e.g. "y_25" → "script_context").
    pub context_field_names: HashMap<String, String>,
    /// Maps variable name → type name (e.g. "inputs" → "tx_in_info").
    pub context_var_types: HashMap<String, String>,
    /// VarId-based context field names (authoritative, no collision).
    pub context_field_names_by_id: HashMap<VarId, String>,
    /// VarId-based context variable types (authoritative, no collision).
    pub context_var_types_by_id: HashMap<VarId, String>,
}

#[derive(Default, Clone)]
pub(crate) struct SimplifyBooleanState {
    /// Boolean helper vars accumulate across passes so later passes can
    /// convert `force(and_fn(a, delay(b)))` → `a && b` even when the and/or
    /// pattern was only recognized in a previous pass.
    pub(crate) and_vars: BindingVarSet,
    pub(crate) or_vars: BindingVarSet,
    pub(crate) partial_if_then_vals: BindingVarMap<PseudoExpr>,
}

impl SimplifyBooleanState {
    pub(crate) fn seed_tracking(&self, tracking: &mut BooleanTracking) {
        tracking.and_vars = self.and_vars.clone();
        tracking.or_vars = self.or_vars.clone();
        tracking.partial_if_then_vals = self.partial_if_then_vals.clone();
    }

    pub(crate) fn harvest_from_tracking(&mut self, tracking: BooleanTracking) {
        self.and_vars = tracking.and_vars;
        self.or_vars = tracking.or_vars;
        self.partial_if_then_vals = tracking.partial_if_then_vals;
    }
}

#[derive(Default, Clone)]
pub(crate) struct SimplifyRecursionState {
    /// Recursive helper vars persist across simplify passes, while
    /// `RecursionTracking::delayed_rec_vars` is deliberately pass-local because
    /// it stores source subtrees that become stale after rewriting.
    pub(crate) rec_vars: BindingVarSet,
}

impl SimplifyRecursionState {
    pub(crate) fn seed_tracking(&self, tracking: &mut RecursionTracking) {
        tracking.rec_vars = self.rec_vars.clone();
    }

    pub(crate) fn harvest_from_tracking(&mut self, tracking: RecursionTracking) {
        self.rec_vars = tracking.rec_vars;
    }
}

#[derive(Default, Clone)]
pub(crate) struct SimplifyNamingState {
    /// Builtin aliases can be pre-seeded from MIR or discovered during
    /// simplification, then reused by later passes to route Vars as builtins.
    pub(crate) builtin_aliases: BindingVarMap<BuiltinId>,
    /// Bindings whose semantic names were already committed in an earlier
    /// pass. Keeps fixed-point naming stable across repeated simplification.
    pub(crate) renamed_binding_ids: HashSet<VarId>,
}

impl SimplifyNamingState {
    pub(crate) fn seed_tracking(&self, tracking: &mut NamingTracking) {
        tracking.builtin_aliases.extend_from(&self.builtin_aliases);
        tracking.renamed_binding_ids = self.renamed_binding_ids.clone();
    }

    pub(crate) fn harvest_from_tracking(&mut self, tracking: NamingTracking) {
        self.builtin_aliases = tracking.builtin_aliases;
        self.renamed_binding_ids = tracking.renamed_binding_ids;
    }
}

#[derive(Default, Clone)]
pub(crate) struct SimplifyHelperSeedState {
    /// User-declared helpers (Let-bound lambdas with a MIR-registered
    /// concrete FnSignature) that must survive the small-function inlining
    /// heuristic in `let_binding.rs`. Seeded by `build_pipeline_seed` and
    /// copied into each `Simplifier`, never harvested back.
    pub(crate) preserved_helper_ids: HashSet<VarId>,
}

impl SimplifyHelperSeedState {
    pub(crate) fn seed_tracking(&self, tracking: &mut HelperPreservationTracking) {
        tracking.preserved_helper_ids = self.preserved_helper_ids.clone();
    }
}

#[derive(Default, Clone)]
pub(crate) struct SimplifyConstructorSeedState {
    /// Pre-seeded constructor unpack subjects from MIR analysis. Copied into
    /// each pass but not harvested back, because per-pass constructor tracking
    /// can contain rewritten source subtrees.
    pub(crate) constr_unpack_subjects: BindingVarMap<PseudoExpr>,
}

impl SimplifyConstructorSeedState {
    pub(crate) fn seed_tracking(&self, tracking: &mut ConstructorTracking) {
        tracking
            .constr_unpack_subjects
            .extend_from(&self.constr_unpack_subjects);
    }
}

#[derive(Default, Clone)]
pub(crate) struct SimplifyIdentityState {
    /// Next synthetic VarId to allocate across simplify calls. Persisting it
    /// across fixed-point iterations avoids rescanning old outputs to keep
    /// synthetic ids unique.
    pub(crate) next_synthetic_var_id: u32,
}

impl SimplifyIdentityState {
    pub(crate) fn seed_tracking(&self, tracking: &mut IdentityTracking, input_next_id: u32) {
        tracking.next_synthetic_var_id = self.next_synthetic_var_id.max(input_next_id);
    }

    pub(crate) fn harvest_from_tracking(&mut self, tracking: IdentityTracking) {
        self.next_synthetic_var_id = tracking.next_synthetic_var_id;
    }
}

#[derive(Default, Clone)]
pub(crate) struct SimplifyVarKindState {
    /// Mint-site VarKind annotations: a pass that creates a
    /// synthetic binder records its [`VarKind`] (e.g.
    /// `FieldIndexAlias`, `SliceTailAlias`) here. Downstream
    /// consumers (nameless post-pipeline, render_prep,
    /// `kind_inference` as verifier) read the authoritative kind
    /// by VarId instead of re-inferring it from shape + name.
    pub(crate) kind_annotations: HashMap<VarId, VarKind>,
}

impl SimplifyVarKindState {
    pub(crate) fn seed_tracking(&self, tracking: &mut VarKindTracking) {
        tracking.kind_annotations = self.kind_annotations.clone();
    }

    pub(crate) fn harvest_from_tracking(&mut self, tracking: VarKindTracking) {
        self.kind_annotations = tracking.kind_annotations;
    }
}

/// Persistent state carried across simplification passes.
#[derive(Default, Clone)]
pub(crate) struct SimplifyState {
    /// The program's church-bool convention, detected ONCE on the
    /// freshly-lowered seed and seeded into every `Simplifier` from here
    /// (`is_true`/`is_false` read it). `Cip` — the default — is what a
    /// caller that never ran detection gets, which is the fail-safe.
    pub(crate) church_polarity: crate::decompile::church_polarity::ChurchPolarity,
    pub(crate) booleans: SimplifyBooleanState,
    pub(crate) recursion: SimplifyRecursionState,
    pub(crate) naming: SimplifyNamingState,
    pub(crate) helpers: SimplifyHelperSeedState,
    pub(crate) constructors: SimplifyConstructorSeedState,
    pub(crate) identity: SimplifyIdentityState,
    pub(crate) var_kinds: SimplifyVarKindState,
}

// ===== Sub-struct groupings for Simplifier =====

#[derive(Default)]
pub(crate) struct BooleanTracking {
    pub and_vars: BindingVarSet,
    pub or_vars: BindingVarSet,
    pub partial_if_conds: BindingVarMap<PseudoExpr>,
    pub partial_if_then_vals: BindingVarMap<PseudoExpr>,
}

#[derive(Default)]
pub(crate) struct RecursionTracking {
    pub rec_vars: BindingVarSet,
    pub delayed_rec_vars: BindingVarMap<(u8, PseudoExpr)>,
}

#[derive(Default)]
pub(crate) struct SelectorTracking {
    pub delayed_fst_selectors: BindingVarSet,
    pub delayed_snd_selectors: BindingVarSet,
    pub single_delayed_fst_params: BindingVarSet,
    pub single_delayed_snd_params: BindingVarSet,
    // determinism: BTreeMap (not HashMap) so iteration order is sorted
    // by `(param_count, selected_idx)`. HashMap order would let the
    // per-process hash seed put `(2, 0)` before or after `(2, 1)`,
    // drifting which selector is picked.
    pub selector_vars: std::collections::BTreeMap<(usize, usize), SelectorBinding>,
    pub non_thunk_vars: BindingVarSet,
}

#[derive(Clone)]
pub(crate) struct SelectorBinding {
    pub name: String,
    pub id: Option<VarId>,
}

impl SelectorBinding {
    pub(crate) fn new(name: String, id: Option<VarId>) -> Self {
        Self { name, id }
    }

    pub(crate) fn matches_resolved_ref(&self, _name: &str, id: Option<VarId>) -> bool {
        crate::decompile::var_match::ids_match_strict(self.id, id)
    }
}

#[derive(Default)]
pub(crate) struct ConstructorTracking {
    pub constr_unpack_subjects: BindingVarMap<PseudoExpr>,
    pub constr_tag_subjects: BindingVarMap<PseudoExpr>,
    pub constr_pack_tags: BindingVarMap<PseudoExpr>,
    pub data_constr_bindings: BindingVarMap<PseudoExpr>,
    pub fields_bindings: BindingVarMap<PseudoExpr>,
    pub tail_chain_offsets: BindingVarMap<(PseudoExpr, usize)>,
}

#[derive(Default)]
pub(crate) struct ContextTracking {
    pub context_field_names: HashMap<String, String>,
    pub context_var_types: HashMap<String, String>,
    pub context_field_names_by_id: HashMap<VarId, String>,
    pub context_var_types_by_id: HashMap<VarId, String>,
    pub sum_type_field_overrides: HashMap<String, Vec<(String, Option<String>)>>,
}

#[derive(Default)]
pub(crate) struct NamingTracking {
    pub renames: BindingVarMap<String>,
    pub builtin_aliases: BindingVarMap<BuiltinId>,
    /// Bindings whose semantic name is already committed across fixed-point
    /// iterations. Prevents repeated `_partial_` and generated-name rewrites
    /// from drifting dedup suffixes on later passes.
    pub(crate) renamed_binding_ids: HashSet<VarId>,
    /// Name → VarId mapping for Var construction with proper identity.
    pub name_to_id: HashMap<String, VarId>,
}

#[derive(Default)]
pub(crate) struct DelayTracking {
    pub delayed_value_depths: BindingVarMap<u8>,
    pub partial_apps: BindingVarMap<(BinaryOp, PseudoExpr, bool)>,
    pub partial_choose_list_subjects: BindingVarMap<PseudoExpr>,
}

/// Rollback list captured before a `ContinueLoop` re-entry: each entry is
/// `(param_name, param_id, previous_depth)` so that the caller can restore
/// the delayed-value depth it overwrote.
pub(crate) type DelayRestoreList = Vec<(String, Option<VarId>, Option<u8>)>;

#[derive(Default)]
pub(crate) struct DethunkTracking {
    /// function VarId -> set of param indices where delay/force can be stripped
    pub dethunk_params: BindingVarMap<HashSet<usize>>,
}

#[derive(Default)]
pub(crate) struct VarKindTracking {
    pub(crate) kind_annotations: HashMap<VarId, VarKind>,
}

#[derive(Default)]
pub(crate) struct IdentityTracking {
    /// Fresh synthetic VarIds used for legacy/synthetic AST nodes that enter
    /// simplify without stable identity.
    pub(crate) next_synthetic_var_id: u32,
}

#[derive(Default)]
pub(crate) struct HelperPreservationTracking {
    /// Per-simplify-call copy of
    /// `SimplifyState::helpers.preserved_helper_ids`, consulted by the
    /// small-function inlining guard in `let_binding.rs` to skip
    /// user-declared helper bindings.
    pub(crate) preserved_helper_ids: HashSet<VarId>,
}

#[derive(Default, Clone)]
pub(crate) struct LexicalNameShadow {
    pub var_id: Option<VarId>,
}

/// Simplifier state. Fields grouped by logical concern.
pub(crate) struct Simplifier {
    pub(crate) safe_mode: bool,
    /// opt-in to VarKind-based recovery dispatch in simplifier
    /// passes (`single_field_collapse`). Mirrors
    /// `DecompileOptions::use_varkind_recovery`; set during pipeline
    /// configuration.
    pub(crate) use_varkind_recovery: bool,
    pub(crate) script_version: Option<ScriptVersion>,
    /// The program's church-bool convention, seeded from
    /// [`SimplifyState::church_polarity`]. Read by `is_true`/`is_false`
    /// for nullary `Constr` leaves that carry no `church_true` witness.
    pub(crate) church_polarity: crate::decompile::church_polarity::ChurchPolarity,
    pub(crate) booleans: BooleanTracking,
    pub(crate) recursion: RecursionTracking,
    pub(crate) selectors: SelectorTracking,
    pub(crate) constructors: ConstructorTracking,
    pub(crate) context: ContextTracking,
    pub(crate) naming: NamingTracking,
    pub(crate) delays: DelayTracking,
    pub(crate) dethunk: DethunkTracking,
    /// Recursion depth for simplify_let to prevent infinite recursion
    pub(crate) let_depth: u32,
    /// Global set of semantic names used across all simplify scopes.
    /// Prevents cross-closure naming collisions (e.g. two Data.un_int → "int").
    pub(crate) global_used_names: HashSet<String>,
    pub(crate) identity: IdentityTracking,
    pub(crate) helpers: HelperPreservationTracking,
    /// per-simplify-call VarKind metadata. Mint sites
    /// (e.g. `introduce_field_index_aliases`) insert here; the
    /// state copy syncs back out at end of `simplify_with_state`.
    pub(crate) var_kinds: VarKindTracking,
    /// Per-Let stack for Walker-driven Let traversal (`pre_let` →
    /// `enter_let` → `post_let`), parallel to the CPS task queue's
    /// `LetAfterValue` / `LetAfterBody` / `LetBailout` frames; empty
    /// when not mid-Let on the Walker path.
    pub(super) let_walker_states: Vec<super::let_binding::LetWalkerPhase>,
}

impl Simplifier {
    pub(crate) fn with_safe_mode(safe_mode: bool) -> Self {
        Self {
            safe_mode,
            use_varkind_recovery: false,
            script_version: None,
            church_polarity: crate::decompile::church_polarity::ChurchPolarity::Cip,
            let_depth: 0,
            global_used_names: HashSet::new(),
            booleans: BooleanTracking::default(),
            recursion: RecursionTracking::default(),
            selectors: SelectorTracking::default(),
            constructors: ConstructorTracking::default(),
            context: ContextTracking::default(),
            naming: NamingTracking::default(),
            delays: DelayTracking::default(),
            dethunk: DethunkTracking::default(),
            identity: IdentityTracking::default(),
            helpers: HelperPreservationTracking::default(),
            var_kinds: VarKindTracking::default(),
            let_walker_states: Vec::new(),
        }
    }

    pub(crate) fn shadow_lexical_name(
        &mut self,
        name: &str,
        current_id: Option<VarId>,
    ) -> LexicalNameShadow {
        let shadow = LexicalNameShadow {
            var_id: self.naming.name_to_id.remove(name),
        };
        if let Some(vid) = current_id {
            self.naming.name_to_id.insert(name.to_string(), vid);
        }
        shadow
    }

    pub(crate) fn restore_lexical_name(&mut self, name: &str, shadow: LexicalNameShadow) {
        self.naming.name_to_id.remove(name);
        if let Some(vid) = shadow.var_id {
            self.naming.name_to_id.insert(name.to_string(), vid);
        }
    }
}
