//! Centralized matching helpers for `Var` ↔ `Binder` correspondence.
//!
//! The helpers take `Option<VarId>`; for a `Var` that is
//! `var_id.get()`, which is `None` for a compat-placeholder id.
//! Callsites asking "does this ref correspond to that binder or
//! target?" go through here so the id-versus-name fallback stays
//! consistent rather than being re-hand-rolled per site.
//!
//! Plain `let Some(x) = id.get() else { ... }` destructuring,
//! single `id.get() == Some(target)` equalities, and matches gated
//! on scope-tracking state (`exact_blocked`, `fallback_shadowed`)
//! stay inline — a helper would add nothing or lose the gates.
//!
//! `Binder.id` is a concrete `VarId`, never an `Option`, so helpers
//! that compare against a binder take `&Binder` and read
//! `binder.id.get()` themselves.

use crate::pseudo::ast::Binder;
use crate::pseudo::var_id::VarId;

/// Check whether a `Var { name, id }` reference matches `binder`.
///
/// `ref_id` is the ref's `var_id.get()`: `Some` when
/// authoritative, `None` for a compat-placeholder. When both it
/// and `binder.id.get()` are `Some`, id identity decides and the
/// name is ignored; if either is `None`, the names are compared.
pub(crate) fn ref_matches_binder(ref_name: &str, ref_id: Option<VarId>, binder: &Binder) -> bool {
    refs_match(ref_name, ref_id, binder.as_str(), binder.id.get())
}

/// Check whether two `Var`-style references (name, id) refer to the
/// same variable: both ids `Some` → id equality decides (name
/// ignored); either id `None` → name comparison.
pub(crate) fn refs_match(
    a_name: &str,
    a_id: Option<VarId>,
    b_name: &str,
    b_id: Option<VarId>,
) -> bool {
    match (a_id, b_id) {
        (Some(x), Some(y)) => x == y,
        _ => a_name == b_name,
    }
}

/// Strict id-only match: `true` iff both ids are `Some` and equal.
///
/// Use where name-fallback is unsafe — retargeting passes must not
/// collapse two different binders that share a name.
pub(crate) fn ids_match_strict(a_id: Option<VarId>, b_id: Option<VarId>) -> bool {
    matches!((a_id, b_id), (Some(x), Some(y)) if x == y)
}

/// `true` unless the ids actively disagree: both `Some` must be
/// equal, either `None` is no evidence.
///
/// Use after the caller has already matched on name:
/// `name_eq && ids_compatible(a.id, b.id)`.
pub(crate) fn ids_compatible(a_id: Option<VarId>, b_id: Option<VarId>) -> bool {
    match (a_id, b_id) {
        (Some(x), Some(y)) => x == y,
        _ => true,
    }
}

/// `true` iff both ids are `Some` and equal, or both are `None`
/// and the names match. Unlike [`refs_match`], a mixed `Some`/
/// `None` pair is `false`, not a name comparison — use it to
/// require that two refs share a resolution state before treating
/// them as the same variable.
// No caller today: the strict counterpart to [`refs_match`], kept
// because the pair of them is the module's contract — `refs_match` says
// "same variable, falling back to the name when an id is missing", and
// this one says "same variable AND the same resolution state". A pass
// that must not treat a resolved and an unresolved ref as equal wants
// this one, and its tests below pin that difference.
#[allow(dead_code)]
pub(crate) fn refs_match_paired(
    a_name: &str,
    a_id: Option<VarId>,
    b_name: &str,
    b_id: Option<VarId>,
) -> bool {
    match (a_id, b_id) {
        (Some(x), Some(y)) => x == y,
        (None, None) => a_name == b_name,
        _ => false,
    }
}

/// Asymmetric variant: the name fallback fires only when
/// `target_id` is `None`. A `Some` target requires strict id
/// equality — a disagreeing ref id does NOT fall back to name.
///
/// Use when the target is the known binder and the ref is being
/// classified as "same variable or not": a stale placeholder ref
/// must not be conflated with a different-id concrete binder that
/// happens to share its name.
pub(crate) fn ref_matches_resolved_target(
    ref_name: &str,
    ref_id: Option<VarId>,
    target_name: &str,
    target_id: Option<VarId>,
) -> bool {
    match target_id {
        Some(t) => ref_id == Some(t),
        None => ref_name == target_name,
    }
}

#[cfg(test)]
mod tests;
