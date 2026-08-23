//! Resolve an ordinal/numeric projection of a let-bound tuple literal to the
//! projected element.
//!
//! A church-pack-N decodes to a let-bound tuple of pure components; pack
//! eliminations survive as positional projections (`w6.2nd` is
//! `FieldAccess { record: Var(w6), selector: NamedField(idx) }`). Because
//! `w6`'s value is an inline `Tuple` of binder-free leaves (`is_inlinable`),
//! projecting one element is exactly that element — no evaluation-order
//! effect on discarded siblings. `w6` then has no remaining references and
//! is dropped by `drop_dead_pure_lets`.
//!
//! Soundness is local: the binding is a tuple literal of pure elements, not
//! an opaque/function value, which is why this is provable where a
//! Scott-eliminator (head of unknown origin) is not. `is_inlinable` admits
//! only binder-free leaves — `is_pure_value` would duplicate `Lambda`/`RecFn`
//! binders with identical `VarId`s on a multi-site projection.
//!
//! Index parse handles both the pre-`normalize_tuple_field_ordinals` numeric
//! form (`NamedField("1")` = 0-based index) and the post-normalize ordinal
//! form (`NamedField("2nd")` = 1-based ordinal → index 1). The pass runs
//! just before `normalize_tuple_field_ordinals`, so it normally sees the
//! numeric form.

use std::collections::HashMap;

use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

pub(super) fn resolve_pack_ordinal_projection(expr: PseudoExpr) -> PseudoExpr {
    let mut packs: HashMap<VarId, Vec<PseudoExpr>> = HashMap::new();
    collect_pure_tuple_lets(&expr, &mut packs);
    if packs.is_empty() {
        return expr;
    }
    rewrite(expr, &packs)
}

/// Collect `let id = (e0, e1, …)` bindings whose value is a `Tuple` literal with
/// every element INLINABLE (a binder-free leaf — see `is_inlinable`), keyed by
/// the binder id.
fn collect_pure_tuple_lets(expr: &PseudoExpr, out: &mut HashMap<VarId, Vec<PseudoExpr>>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(binder_id),
            value,
            ..
        } = current
            && let PseudoExpr::Tuple(elems) = value.as_ref()
            && elems.iter().all(is_inlinable)
        {
            out.insert(*binder_id, (elems.clone()).into_vec());
        }
        pending.extend(children(current));
    }
}

/// A pack element safe to inline at (possibly multiple) projection sites: a
/// reference or a literal, with NO internal binders. (`is_pure_value` would be
/// broader — it admits `Lambda`/`RecFn`/aggregates whose binders would be
/// DUPLICATED with identical `VarId`s on a multi-site projection, breaking the
/// global VarId-uniqueness invariant.)
fn is_inlinable(e: &PseudoExpr) -> bool {
    matches!(
        e,
        PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_)
    )
}

struct PackProjectionRewriter<'a> {
    packs: &'a HashMap<VarId, Vec<PseudoExpr>>,
}

impl ExprFolder for PackProjectionRewriter<'_> {
    fn post_expr(&mut self, expr: PseudoExpr) -> PseudoExpr {
        if let PseudoExpr::FieldAccess {
            record,
            selector: FieldSelector::NamedField(n),
        } = &expr
            && let PseudoExpr::Var { id: Some(v), .. } = record.as_ref()
            && let Some(elems) = self.packs.get(v)
            && let Some(idx) = parse_index(n)
            && idx < elems.len()
        {
            return elems[idx].clone();
        }
        expr
    }

    // `map_children` never recursed into a `when` clause's literal
    // pattern expression (only subject/guard/body) — match that exactly
    // rather than the default's descent into `WhenPattern::Literal`.
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }
}

fn rewrite(expr: PseudoExpr, packs: &HashMap<VarId, Vec<PseudoExpr>>) -> PseudoExpr {
    PackProjectionRewriter { packs }.fold(expr)
}

/// Map a tuple selector string to a 0-based element index. Accepts the numeric
/// form (`"1"` → 1, pre-normalize) and the ordinal form (`"2nd"`/`"8th"` →
/// 1/7, post-normalize: `ordinal n` → index `n - 1`). Returns `None` for any
/// non-tuple selector (`"fields"`, …) or a malformed string.
fn parse_index(n: &str) -> Option<usize> {
    if !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()) {
        // Numeric selector — already a 0-based tuple index.
        return n.parse().ok();
    }
    // Ordinal selector "<n>st|nd|rd|th" — 1-based; index = n - 1. The part after
    // the leading digits MUST be exactly a valid ordinal suffix (so a malformed
    // `"2foo"` is rejected, not silently read as index 1).
    let suffix_start = n.find(|c: char| !c.is_ascii_digit())?;
    let (digits, suffix) = n.split_at(suffix_start);
    if digits.is_empty() || !matches!(suffix, "st" | "nd" | "rd" | "th") {
        return None;
    }
    digits.parse::<usize>().ok()?.checked_sub(1)
}

#[cfg(test)]
mod tests;
