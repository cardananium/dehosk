//! Lower raw-`Constr` sugar `record.tag` / `record.fields` to
//! `builtin.un_constr_data(record).1st` / `.2nd`.
//!
//! Those selectors are reserved codebase-wide, but a blueprint record
//! can literally title a field `tag` or `fields`. Rewriting that would
//! look valid and be wrong. Fire only when the record is not a concrete
//! non-stub `Named` type (`Unknown`, `Data`, or `Unknown_S_*`/`Unknown_E_*`).
//! Fail-closed: unsure → leave untouched.
//!
//! Primary basis is the convention (`kind_inference`, `stub_adt`,
//! `inline_pattern_field_access`, …); `gate_b_allows` is a second check.
//! No fresh `VarId`s. Bottom-up so a rewritten record can feed an outer
//! `.tag`/`.fields`.

use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, PseudoType};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;

use super::ctx::RenderCtx;

pub(super) fn lower_constr_field_sugar(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    // OPT-IN: emits the compilable `builtin.un_constr_data(X).1st`/`.2nd`
    // surface; with the toggle OFF the render keeps the readable pseudo
    // `X.tag`/`X.fields`, which is not valid surface syntax. The printer
    // reads the SAME flag off the ctx, so the two halves cannot disagree.
    if !ctx.compilable_data_access() {
        return expr;
    }
    LowerConstrFieldSugar.fold(expr)
}

struct LowerConstrFieldSugar;

impl ExprFolder for LowerConstrFieldSugar {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    // Runs after `record` is already folded (bottom-up), same as the old
    // post-order `map_children` call — a rewritten record can feed an
    // outer `.tag`/`.fields`.
    fn post_field_access(&mut self, record: PseudoExpr, selector: FieldSelector) -> PseudoExpr {
        if let FieldSelector::NamedField(name) = &selector
            && (name == "tag" || name == "fields")
            && gate_b_allows(&record)
        {
            let pair_selector = if name == "tag" {
                FieldSelector::PairFst
            } else {
                FieldSelector::PairSnd
            };
            let unpacked = PseudoExpr::BuiltinCall {
                name: BuiltinId::DataUnConstr,
                args: vec![record].into(),
            };
            return PseudoExpr::FieldAccess {
                record: PBox::new(unpacked),
                selector: pair_selector,
            };
        }
        PseudoExpr::field_access_typed(record, selector)
    }
}

/// GATE B: `true` when the `.tag`/`.fields` rewrite is safe — the record is
/// not a concrete, non-stub blueprint `Named` type. See the module docs.
fn gate_b_allows(record: &PseudoExpr) -> bool {
    match record.type_resolution().as_deref() {
        // Concrete blueprint record type: a genuine `tag`/`fields` field is
        // possible. SKIP unless the name is a synthetic stub.
        Some(PseudoType::Named(n)) => is_stub_type_name(n),
        // `Data`, or no type known: the raw-Constr spine. FIRE.
        _ => true,
    }
}

/// Synthetic stub type name minted by `stub_adt` (`Unknown_S_<…>` /
/// `Unknown_E_<…>`): an unresolved-type placeholder, never a real blueprint
/// title, matching `is_stub_type_hint` in `name_cardano_sum_arms`.
fn is_stub_type_name(name: &str) -> bool {
    name.starts_with("Unknown_S_") || name.starts_with("Unknown_E_")
}

#[cfg(test)]
mod tests;
