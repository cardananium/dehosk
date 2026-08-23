//! Collapse an identity `list.map` that rebuilds each Pair element from its own
//! components:
//!   `list.map(xs, fn(e) { Pair(e.fst, e.snd) })`  →  `xs`
//!
//! For a `Pair` element `e`, `Pair(e.fst, e.snd)` is structurally `e`, so the
//! map is the identity; Pair construction is pure, so dropping the traversal
//! loses no effect. Gated by VarId: both projections must read the lambda's own
//! parameter, so unrelated `x.fst`/`y.snd` never match.
//!
//! Runs right after `rewrite_native_list_map`, which emits the synthetic
//! `Var("list.map")` call this matches.

use crate::builtins::BuiltinId;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn fold_identity_pair_map(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_fold)
}

fn try_fold(expr: PseudoExpr) -> PseudoExpr {
    match expr {
        PseudoExpr::Apply { function, args } if is_identity_pair_map(&function, &args) => {
            // args[0] is `xs`; the map is the identity, so return it.
            args.into_iter().next().expect("checked args.len() == 2")
        }
        PseudoExpr::Apply { function, args } => PseudoExpr::Apply { function, args },
        other => other,
    }
}

fn is_identity_pair_map(function: &PseudoExpr, args: &[PseudoExpr]) -> bool {
    if !matches!(function, PseudoExpr::Var { name, .. } if name == "list.map") {
        return false;
    }
    if args.len() != 2 {
        return false;
    }
    let PseudoExpr::Lambda { params, body } = &args[1] else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let eid = params[0].id;
    matches!(
        body.as_ref(),
        PseudoExpr::BuiltinCall { name: BuiltinId::PairNew, args: pargs }
            if pargs.len() == 2
                && is_pair_proj(&pargs[0], eid, FieldSelector::PairFst)
                && is_pair_proj(&pargs[1], eid, FieldSelector::PairSnd)
    )
}

/// `<var with id `eid`>.<fst|snd>` for the given selector.
fn is_pair_proj(e: &PseudoExpr, eid: VarId, want: FieldSelector) -> bool {
    matches!(
        e,
        PseudoExpr::FieldAccess { record, selector }
            if *selector == want
                && matches!(record.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == eid)
    )
}

#[cfg(test)]
mod tests;
