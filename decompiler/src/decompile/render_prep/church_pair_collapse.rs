//! Collapse the church-pair-eliminator AST shape
//! `FieldAccess { record: Force(Lambda(x, Apply(Var(x), [a, b]))),
//!  selector: PairFst|PairSnd }` to `a` (PairFst) or `b` (PairSnd).
//!
//! The replacement is sound because:
//! 1. VarId identity: the `Var` applied must carry the same id as
//!    `Lambda::params[0]`, proving it is the lambda's parameter.
//! 2. Shape lock: `Force(Lambda(x, x(a, b)))` is the standard
//!    church-encoding lowering of a Pair; `.fst` extracts the first
//!    component, `.snd` the second.
//! 3. Purity guard: the discarded side (`b` for fst, `a` for
//!    snd) must be a pure UPLC value — literals, vars, `Constr`/
//!    `Pair`/`Tuple`/`List` with pure elements, `Lambda`s as values.
//!    Anything that evaluates (`Apply`, `BuiltinCall`, `Force`,
//!    `Trace`, `Let`, `If`, `When`, `FieldAccess`, `IndexAccess`,
//!    `BinOp`, `UnOp`) blocks the collapse — Plutus's strict
//!    evaluation cannot skip it.

use super::purity::is_pure_value;
use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;

/// Walk the AST and collapse safe church-pair-eliminator shapes.
pub(super) fn collapse_church_pair_eliminator_ast(expr: PseudoExpr) -> PseudoExpr {
    struct ChurchPairCollapser;

    impl ExprFolder for ChurchPairCollapser {
        fn post_field_access(&mut self, record: PseudoExpr, selector: FieldSelector) -> PseudoExpr {
            // Recognise the church-pair shape ONLY at PairFst/PairSnd
            // (`.tag` or a named field here is not a projector).
            if matches!(selector, FieldSelector::PairFst | FieldSelector::PairSnd) {
                if let Some((a, b)) = match_church_pair(&record) {
                    let (keep, discard) = match selector {
                        FieldSelector::PairFst => (a, b), // (keep, discard)
                        FieldSelector::PairSnd => (b, a),
                        _ => unreachable!(),
                    };
                    if is_pure_value(discard) {
                        return keep.clone();
                    }
                }
                // Native `Pair(a, b)` literal: `.fst -> a`, `.snd -> b` when the
                // discarded side is pure. Mirrors the simplify-layer Pair-projection
                // fold, which never sees Pair nodes built during render_prep
                // (`decode_church_to_native` / pack inlining).
                if let PseudoExpr::Pair(pa, pb) = &record {
                    let (keep, discard): (&PseudoExpr, &PseudoExpr) = match selector {
                        FieldSelector::PairFst => (pa, pb),
                        FieldSelector::PairSnd => (pb, pa),
                        _ => unreachable!(),
                    };
                    if is_pure_value(discard) {
                        return keep.clone();
                    }
                }
            }
            PseudoExpr::field_access_typed(record, selector)
        }

        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            pattern
        }
    }

    ChurchPairCollapser.fold(expr)
}

/// Match `Force(Lambda(x, Apply(Var(x), [a, b])))`, returning
/// `Some((a, b))`. The `Var`-to-`Lambda`-param link is checked
/// by `VarId`, not by name, so a shadowed binding sharing the
/// surface name cannot match.
fn match_church_pair(expr: &PseudoExpr) -> Option<(&PseudoExpr, &PseudoExpr)> {
    let PseudoExpr::Force(inner) = expr else {
        return None;
    };
    let PseudoExpr::Lambda { params, body } = inner.as_ref() else {
        return None;
    };
    if params.len() != 1 {
        return None;
    }
    let param_id = params[0].id;
    // Body must be Apply(Var(param), [a, b]).
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let PseudoExpr::Var { id: var_id, .. } = function.as_ref() else {
        return None;
    };
    if (*var_id)? != param_id {
        return None;
    }
    Some((&args[0], &args[1]))
}

// `is_pure_value` lives in `super::purity` so this pass and
// `slice_chain` share one definition, keeping the
// `expect!`-sentinel exception consistent.

#[cfg(test)]
mod tests;
