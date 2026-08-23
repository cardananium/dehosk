//! Rename a synthetic `let <syn> = <X>.<cardano_field>` binder to the
//! schema field it projects, so a following `when <syn> is { … }`
//! reads by the Cardano name (`let w = <X>.governance_action` →
//! `let governance_action = …`).
//!
//! After `resolve_cardano_field_indices`, which turns positional
//! `.fields[N]` into the named accessor this pass keys off. Value-shape
//! driven (trailing selector is a known Cardano [`ContextField`]); no
//! type-env needed.
//!
//! Display rename, rewired by `VarId`. Fail-closed drop-on-collision:
//! a target already used as some other binder/var, or wanted by two
//! distinct synthetic binders, is dropped and those binders keep their
//! original name. Only an unambiguous synthetic→field mapping is
//! renamed — three `bound_type` projections in disjoint scopes stay
//! untouched.
//!
//! Version-gated: inert when neither channel is set — a versionless
//! render never ran `resolve_cardano_field_indices` /
//! `resolve_tx_info_field_indices`, so there are no `.<cardano_field>`
//! accessors. Under V1/V2 ambiguity the strict channel is `None` but
//! the ScriptContext-level channel still named the V1/V2-invariant
//! `.purpose`/`.tx_info` accessors, so this pass must still rename
//! their synthetic binders (`let field_1 = script_context.purpose`
//! → `purpose`).

use std::collections::{HashMap, HashSet};

use crate::decompile::simplify::postprocess::ContextField;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

use super::ctx::RenderCtx;
use super::rename_hygiene::{apply_renames, collect_used_names};
use super::rename_synthetic_field_let_binders::is_synthetic_field_name;
use super::scope_recurse::children;

pub(super) fn rename_let_to_cardano_field(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    if !ctx.any_version_set() {
        return expr;
    }
    let mut candidates: Vec<(VarId, &'static str)> = Vec::new();
    collect(&expr, &mut candidates);
    if candidates.is_empty() {
        return expr;
    }
    // Drop-on-collision: a target already used as a binder/var anywhere, or
    // wanted by ≥2 distinct binders, would shadow or be ambiguous — only
    // unambiguous, non-colliding renames survive.
    let mut used: HashSet<String> = HashSet::new();
    collect_used_names(&expr, &mut used);
    let mut counts: HashMap<&str, usize> = HashMap::new();
    for (_, n) in &candidates {
        *counts.entry(*n).or_insert(0) += 1;
    }
    let renames: HashMap<VarId, String> = candidates
        .iter()
        .filter(|(_, n)| counts[*n] == 1 && !used.contains(*n))
        .map(|(id, n)| (*id, n.to_string()))
        .collect();
    if renames.is_empty() {
        return expr;
    }
    apply_renames(expr, &renames)
}

/// The trailing Cardano [`ContextField`] legacy name of a `<X>.<field>` value,
/// excluding the structural accessors (`fields`/`tag`/`fst`/`snd`/`head`).
fn cardano_field_projection(value: &PseudoExpr) -> Option<&'static str> {
    let PseudoExpr::FieldAccess { selector, .. } = value else {
        return None;
    };
    let name = match selector {
        FieldSelector::NamedField(n) | FieldSelector::ContextField(n) => n.as_str(),
        _ => return None,
    };
    // Canonicalize to the schema-owned `&'static str`, which also confirms the
    // selector IS a Cardano field.
    ContextField::from_display_name(name).map(ContextField::display_name)
}

/// A decompiler-minted placeholder binder — the rename candidates:
/// `field_N`/`fields_N` (via `is_synthetic_field_name`), single letters (`w`),
/// letter+digits (`q7`), and `letter_digits…` (`w_2`, `x_3_4`). A name that is
/// itself a Cardano field is already meaningful, never a placeholder.
fn is_synthetic_let_name(n: &str) -> bool {
    if ContextField::from_display_name(n).is_some() {
        return false;
    }
    if is_synthetic_field_name(n) {
        return true;
    }
    let bytes = n.as_bytes();
    if bytes.is_empty() || !bytes[0].is_ascii_lowercase() {
        return false;
    }
    let rest = &n[1..];
    rest.is_empty()
        || rest.bytes().all(|b| b.is_ascii_digit())
        || (rest.starts_with('_') && rest[1..].bytes().all(|b| b.is_ascii_digit() || b == b'_'))
}

fn collect<'a>(expr: &'a PseudoExpr, out: &mut Vec<(VarId, &'static str)>) {
    let mut pending: Vec<&'a PseudoExpr> = vec![expr];
    while let Some(expr) = pending.pop() {
        if let PseudoExpr::Let {
            name,
            id: Some(bid),
            value,
            ..
        } = expr
            && is_synthetic_let_name(name)
            && let Some(field) = cardano_field_projection(value)
            && field != name
        {
            out.push((*bid, field));
        }
        for child in children(expr).into_iter().rev() {
            pending.push(child);
        }
    }
}

#[cfg(test)]
mod tests;
