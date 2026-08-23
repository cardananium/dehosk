//! Per-`(TypeHintId, tag, field_idx)` field-kind inference for stub-ADT fields.
//!
//! Stub-ADT (`Unknown_S_*`/`Unknown_E_*`) fields are erased to `Data`,
//! so a downstream pass cannot tell a nested Scott value
//! (eliminator-callable) from native `Data` or a genuine function.
//! Recovers the kind from construction sites: classify each
//! `fields[j]` at a synthetic-stub `Constr`, then join across sites.
//!
//! Soundness (Plutus `Data` cannot contain functions): a field from a
//! recognized Scott constructor was built in-validator, never an
//! externally supplied HOF. Per site: stub `Constr` with a complete
//! ≥2-variant arity catalog → `Scott(arities)`; `Lambda` → `Fn`;
//! `un_*_data`/`un_constr_data` → `Native`; any other observed value
//! → `Opaque`; no site → absent. Unequal kinds join to `Conflict`.
//!
//! `Opaque` is not lattice bottom: `join(Scott, Opaque) = Conflict`,
//! so a key is `Scott` iff every observed site is a stub Scott value
//! with those exact arities. Only that verdict enables a rewrite.
//!
//! Fencing: both the outer constructor hint (the table key) and the
//! inner nested-ctor hint must be synthetic stubs (`is_stub_hint`).
//! `ConstructorShape::Unknown` alone is not enough — user / blueprint
//! ADTs are also `Unknown`-shaped with a real `TypeHintId`.
//!
//! Pure side-analysis: builds tables, rewrites nothing. Not every
//! entry point has an in-tree consumer, hence the `allow(dead_code)`.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use crate::builtins::BuiltinId;
use crate::decompile::TypeHintId;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

/// Per-variant arity signature of a (nested) Scott type.
pub(crate) type ScottArities = Vec<usize>;

/// Per-`(tag → arity)` record for one type hint. `None` for a tag means two
/// construction sites disagreed on that variant's arity (uncertain).
type TagArities = HashMap<usize, Option<usize>>;

/// `TypeHintId` → its per-variant arity record.
pub(super) type ArityCatalog = HashMap<TypeHintId, TagArities>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FieldKind {
    /// Lattice bottom: no information (no observed site contributed this).
    Unknown,
    /// Proven nested Scott value with the given per-variant arities.
    Scott(ScottArities),
    /// Proven native `Data` value (came out of a `un_*_data` builtin).
    Native,
    /// Proven function value (a `Lambda` at the construction site).
    Fn,
    /// Observed at a construction site but not provably any of the above
    /// (bare `Var`, `Apply`, literal, non-stub/1-variant ctor, …). DEFEATS
    /// `Scott` under join.
    Opaque,
    /// Lattice top: observed sites carry incompatible kinds.
    Conflict,
}

impl FieldKind {
    /// Flat lattice join: `Unknown` is bottom (identity); the four observed
    /// kinds (`Scott`, `Native`, `Fn`, `Opaque`) are mutually incomparable
    /// peers; unequal peers join to `Conflict` (top). Idempotent, commutative,
    /// associative ⇒ the single collection pass is order-independent.
    pub(super) fn join(self, other: FieldKind) -> FieldKind {
        match (self, other) {
            (FieldKind::Unknown, x) | (x, FieldKind::Unknown) => x,
            (FieldKind::Conflict, _) | (_, FieldKind::Conflict) => FieldKind::Conflict,
            (a, b) if a == b => a,
            _ => FieldKind::Conflict,
        }
    }
}

/// `(TypeHintId, tag, field_idx)` → inferred field kind.
pub(crate) type FieldKindTable = HashMap<(TypeHintId, usize, usize), FieldKind>;

/// True iff `th` names a synthetic stub ADT, following the codebase's own
/// stub-identity convention (see `stub_adt::extract_unknown_s_ord`): a stub is
/// `Unknown_S_<N>` (optional `_A<M>` shard suffix) or `Unknown_E_<N>`, `<N>`
/// being the generated integer ordinal/arity. The numeric-suffix check rejects
/// user/blueprint types that merely share the prefix (e.g. `Unknown_S_Foo`).
///
/// A user/blueprint type named *exactly* `Unknown_S_<int>` / `Unknown_E_<int>`
/// would alias the stub namespace, so this is a necessary, not a sufficient,
/// signal.
fn is_stub_hint(th: &TypeHintId) -> bool {
    let s = th.as_str();
    for prefix in ["Unknown_S_", "Unknown_E_"] {
        if let Some(rest) = s.strip_prefix(prefix) {
            let head = rest.split_once('_').map(|(h, _)| h).unwrap_or(rest);
            return head.parse::<usize>().is_ok();
        }
    }
    false
}

/// Gather per-variant arities for every synthetic-stub `Constr` node.
/// Disagreeing arities for the same `(hint, tag)` are recorded as `None`
/// (uncertain) rather than silently max-collapsed.
pub(super) fn build_arity_catalog(expr: &PseudoExpr) -> ArityCatalog {
    let mut catalog = ArityCatalog::new();
    collect_arities(expr, &mut catalog);
    catalog
}

fn collect_arities(expr: &PseudoExpr, catalog: &mut ArityCatalog) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if let PseudoExpr::Constr {
            shape: ConstructorShape::Unknown { arity, .. },
            type_hint: Some(th),
            tag,
            ..
        } = expr
        {
            if is_stub_hint(th) {
                let by_tag = catalog.entry(th.clone()).or_default();
                by_tag
                    .entry(*tag)
                    .and_modify(|slot| {
                        // Conflict (`None`) is sticky; otherwise demote on disagreement.
                        if *slot != Some(*arity) {
                            *slot = None;
                        }
                    })
                    .or_insert(Some(*arity));
            }
        }
        pending.extend(children(expr).into_iter().rev());
    }
}

/// The contiguous per-variant arity signature for a hint, or `None` if its tag
/// set is non-contiguous OR any variant's arity was uncertain (conflicting).
fn arities_for_hint(th: &TypeHintId, catalog: &ArityCatalog) -> Option<ScottArities> {
    let by_tag = catalog.get(th)?;
    let n = by_tag.len();
    (0..n).map(|t| by_tag.get(&t).copied().flatten()).collect()
}

/// Classify a single expression by what kind of value it constructs — the
/// per-site classifier shared with the inter-procedural provenance analysis.
pub(super) fn seed_from_field_expr(field_expr: &PseudoExpr, catalog: &ArityCatalog) -> FieldKind {
    match field_expr {
        // A nested SYNTHETIC-STUB constructor with a complete >=2-variant arity
        // catalog is a Scott-encoded sum value. (1-variant = record, not an
        // eliminator; non-stub ctor = user/blueprint data, not Scott.)
        PseudoExpr::Constr {
            shape: ConstructorShape::Unknown { .. },
            type_hint: Some(inner_th),
            ..
        } if is_stub_hint(inner_th) => match arities_for_hint(inner_th, catalog) {
            Some(arities) if arities.len() >= 2 => FieldKind::Scott(arities),
            _ => FieldKind::Opaque,
        },
        PseudoExpr::Lambda { .. } => FieldKind::Fn,
        PseudoExpr::BuiltinCall { name, .. }
            if matches!(
                name,
                BuiltinId::DataUnInt
                    | BuiltinId::DataUnByteArray
                    | BuiltinId::DataUnList
                    | BuiltinId::DataUnMap
                    | BuiltinId::DataUnConstr
            ) =>
        {
            FieldKind::Native
        }
        // Observed but unprovable — defeats Scott under join.
        _ => FieldKind::Opaque,
    }
}

fn collect_field_kinds(expr: &PseudoExpr, table: &mut FieldKindTable, catalog: &ArityCatalog) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if let PseudoExpr::Constr {
            shape: ConstructorShape::Unknown { .. },
            type_hint: Some(th),
            tag,
            fields,
        } = expr
        {
            // Only synthetic-stub constructors define keys in the table.
            if is_stub_hint(th) {
                for (j, field_expr) in fields.iter().enumerate() {
                    // Every observed site contributes (Opaque included), so an
                    // unprovable site fails the key closed instead of being ignored.
                    let kind = seed_from_field_expr(field_expr, catalog);
                    let key = (th.clone(), *tag, j);
                    let prev = table.remove(&key).unwrap_or(FieldKind::Unknown);
                    table.insert(key, prev.join(kind));
                }
            }
        }
        pending.extend(children(expr).into_iter().rev());
    }
}

/// Infer the field-kind table for `expr` (construction-site seed only).
pub(crate) fn infer_field_kinds(expr: &PseudoExpr) -> FieldKindTable {
    let catalog = build_arity_catalog(expr);
    let mut table = FieldKindTable::new();
    collect_field_kinds(expr, &mut table, &catalog);
    table
}

// ===========================================================================
// ELIMINATION-SITE scalar-kind analysis
//
// `FieldKind` above collapses `un_b_data` and `un_i_data` into one `Native`
// (construction sites only need Scott-vs-data-vs-fn), but the Credential /
// StakingCredential gate consuming THIS table must tell a `ByteArray` field
// from an `Int` one, so `ScalarKind` keys off ELIMINATION sites — how each
// stub-ADT pattern-field BINDER is decoded inside the `when` arm. Widening
// `FieldKind` itself is not an option: `interproc_provenance` depends on its
// exact lattice.
// ===========================================================================

/// Flat-lattice classification of a stub-ADT field's *scalar* decode kind,
/// observed at elimination sites. Distinguishes `ByteArray` from `Int`, which
/// `FieldKind::Native` cannot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScalarKind {
    /// Lattice bottom: no elimination site contributed (identity for join).
    Unknown,
    /// Decoded via `un_b_data` — a `ByteArray`.
    ByteArray,
    /// Decoded via `un_i_data` — an `Int`.
    Int,
    /// Decoded via `un_list_data` / `un_map_data` — structured `Data`
    /// (not a scalar; recorded so it cannot be mistaken for a scalar peer).
    OtherData,
    /// Observed at an elimination site but not provably any of the above
    /// (passed into another stub-typed position, matched as a stub, or used
    /// in any other way). DEFEATS the scalar peers under join.
    Opaque,
    /// Lattice top: elimination sites carry incompatible kinds.
    Conflict,
}

impl ScalarKind {
    /// Flat lattice join, mirroring [`FieldKind::join`]: `Unknown` is bottom
    /// (identity); `ByteArray`/`Int`/`OtherData`/`Opaque` are mutually
    /// incomparable peers; unequal peers join to `Conflict` (top). Idempotent,
    /// commutative, associative ⇒ join order does not affect the result.
    pub(crate) fn join(self, other: ScalarKind) -> ScalarKind {
        match (self, other) {
            (ScalarKind::Unknown, x) | (x, ScalarKind::Unknown) => x,
            (ScalarKind::Conflict, _) | (_, ScalarKind::Conflict) => ScalarKind::Conflict,
            (a, b) if a == b => a,
            _ => ScalarKind::Conflict,
        }
    }
}

/// `(TypeHintId, tag, field_idx)` → inferred scalar decode kind.
pub(crate) type ScalarKindTable = HashMap<(TypeHintId, usize, usize), ScalarKind>;

/// Walk `expr`, collecting `VarId → (hint, tag, field_idx)` for every binder
/// introduced by a stub-typed `when`-arm CONSTRUCTOR pattern. VarIds are
/// globally unique, so a flat map (rather than a scoped env) is correct.
fn collect_stub_arm_binders(
    expr: &PseudoExpr,
    binders: &mut HashMap<VarId, (TypeHintId, usize, usize)>,
) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if let PseudoExpr::When { clauses, .. } = expr {
            for clause in clauses {
                if let crate::pseudo::ast::WhenPattern::Constructor {
                    type_hint: Some(th),
                    tag,
                    fields,
                    ..
                } = &clause.pattern
                    && is_stub_hint(th)
                {
                    for (field_idx, binder) in fields.iter().enumerate() {
                        binders.insert(binder.var_id(), (th.clone(), *tag, field_idx));
                    }
                }
            }
        }
        pending.extend(children(expr).into_iter().rev());
    }
}

/// If `parent` is a 1-arg builtin applied to a bare tracked-binder `Var`,
/// return `Some((vid, kind))` for that binder — the scalar kind its decode
/// proves, or `Opaque` for a builtin that proves no scalar.
///
/// The returned binder lets the caller skip that occurrence while counting
/// every OTHER occurrence of a tracked binder (helper-call arg, stub ctor
/// field, stub `when` subject, …) as `Opaque` — fail-closed, so an
/// unrecognized flow cannot evade `Conflict`.
fn recognized_scalar_decode(
    parent: &PseudoExpr,
    is_tracked: &impl Fn(VarId) -> bool,
) -> Option<(VarId, ScalarKind)> {
    if let PseudoExpr::BuiltinCall { name, args } = parent
        && args.len() == 1
        && let PseudoExpr::Var { id: Some(v), .. } = &args[0]
        && is_tracked(*v)
    {
        let kind = match name {
            BuiltinId::DataUnByteArray => ScalarKind::ByteArray,
            BuiltinId::DataUnInt => ScalarKind::Int,
            BuiltinId::DataUnList | BuiltinId::DataUnMap => ScalarKind::OtherData,
            // un_constr_data / anything else: observed but not a scalar.
            _ => ScalarKind::Opaque,
        };
        return Some((*v, kind));
    }
    None
}

/// Walk `expr`, joining EVERY occurrence of a tracked binder into `table`
/// under that binder's `(hint, tag, field_idx)` key, recording in `observed`
/// which binders were seen at all.
///
/// Site-COMPLETE (the soundness lever): every occurrence contributes — a
/// recognized `un_*_data(Var)` decode its scalar kind, every other one
/// `Opaque` — so a binder used as both `un_b_data(f)` and `extract_int(f)`
/// joins to `Conflict` and no unrecognized flow evades the verdict.
fn collect_scalar_uses(
    expr: &PseudoExpr,
    binders: &HashMap<VarId, (TypeHintId, usize, usize)>,
    table: &mut ScalarKindTable,
    observed: &mut HashSet<VarId>,
) {
    let is_tracked = |v: VarId| binders.contains_key(&v);
    let mut join_use = |vid: VarId, kind: ScalarKind, table: &mut ScalarKindTable| {
        let key = binders[&vid].clone();
        observed.insert(vid);
        let prev = table.remove(&key).unwrap_or(ScalarKind::Unknown);
        table.insert(key, prev.join(kind));
    };

    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        // (a) A recognized scalar decode consumes ONE tracked-binder `Var`
        //     operand; record its scalar kind and remember which occurrence it
        //     consumed so it is not double-counted as an `Opaque` use below.
        let consumed = recognized_scalar_decode(expr, &is_tracked);
        if let Some((vid, kind)) = consumed {
            join_use(vid, kind, table);
        }

        // (b) Every OTHER direct-child `Var` occurrence of a tracked binder is
        //     an unrecognized flow ⇒ `Opaque`; the recognized decode's own
        //     operand is skipped, being the immediate child of THIS
        //     `BuiltinCall` node. The skip is by `VarId` and is position-safe
        //     ONLY because `recognized_scalar_decode` matches a UNARY builtin
        //     over one bare `Var` (`args.len() == 1`), making the consumed
        //     operand the sole direct-child `Var`. A multi-arg shape where the
        //     same binder appears twice would need a child-position skip, so a
        //     second occurrence still counts `Opaque`.
        let kids = children(expr);
        for child in &kids {
            if let PseudoExpr::Var { id: Some(v), .. } = child
                && is_tracked(*v)
            {
                let is_consumed_operand = matches!(consumed, Some((cv, _)) if cv == *v)
                    && matches!(expr, PseudoExpr::BuiltinCall { .. });
                if !is_consumed_operand {
                    join_use(*v, ScalarKind::Opaque, table);
                }
            }
        }

        pending.extend(kids.into_iter().rev());
    }
}

/// Infer the per-`(TypeHintId, tag, field_idx)` scalar decode kind for every
/// stub-ADT `when`-arm pattern field in `expr`, joined across all elimination
/// sites. A tracked field with NO observed decode/use site defaults to
/// `Opaque` — an undecoded field is never assumed `ByteArray`/`Int`.
pub(crate) fn infer_arm_field_scalars(expr: &PseudoExpr) -> ScalarKindTable {
    let mut binders: HashMap<VarId, (TypeHintId, usize, usize)> = HashMap::new();
    collect_stub_arm_binders(expr, &mut binders);

    let mut table = ScalarKindTable::new();
    let mut observed: HashSet<VarId> = HashSet::new();
    collect_scalar_uses(expr, &binders, &mut table, &mut observed);

    // Fail-closed default — PER BINDER, not merely per key. A merged stub's
    // `TypeHintId` is shared by all its sites, so two binders for the same arm
    // field can map to the SAME key: joining `Opaque` for every un-observed
    // binder forces `Conflict` rather than letting one decoded site
    // (`un_b_data` ⇒ ByteArray) speak for a sibling that flowed somewhere
    // unrecognized — which is how the Credential gate sees the conflation.
    for (vid, key) in binders {
        if !observed.contains(&vid) {
            let prev = table.remove(&key).unwrap_or(ScalarKind::Unknown);
            table.insert(key, prev.join(ScalarKind::Opaque));
        }
    }

    if crate::debug_env::scalar_kind() {
        let mut rows: Vec<_> = table.iter().collect();
        rows.sort_by(|a, b| (a.0.0.as_str(), a.0.1, a.0.2).cmp(&(b.0.0.as_str(), b.0.1, b.0.2)));
        eprintln!("=== DEHOSK_SCALARKIND: arm-field scalar kinds ===");
        for ((th, tag, field_idx), kind) in rows {
            eprintln!("  {}[tag {tag}].{field_idx} -> {kind:?}", th.as_str());
        }
    }

    table
}

#[cfg(test)]
mod tests;
