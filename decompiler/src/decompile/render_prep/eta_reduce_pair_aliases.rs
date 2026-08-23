//! Eta-reduce `Pair(fn(a, b) { p.fst(a, b) }, p.snd)` to `p`.
//!
//! After the church-pair sentinel-call decoder rewrites
//! `pair_var(e, x, y)` → `pair_var.fst(x, y)`, callers that
//! reconstruct a pair from another pair's projections produce
//! eta-equivalent values — `p` itself in eta-expanded form.
//!
//! The Lambda must have exactly 2 params. The record Var must have
//! the same id in the `.fst` call and the `.snd` selector. The
//! `.fst` Apply's args must be exactly `[Var(a), Var(b)]` in that
//! order — no arg swap, no extras. Force wrappers around the Lambda
//! body and around the `.fst` function are peeled.

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::field_selector::FieldSelector;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn eta_reduce_pair_aliases(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_rewrite)
}

fn try_rewrite(expr: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::Pair(fst_box, snd_box) = expr else {
        return expr;
    };
    // .fst position: must be `Lambda { [a, b], Apply(FieldAccess(p,
    // PairFst), [Var(a), Var(b)]) }`.
    let PseudoExpr::Lambda { params, body } = fst_box.as_ref() else {
        return PseudoExpr::Pair(fst_box, snd_box);
    };
    if params.len() != 2 {
        return PseudoExpr::Pair(fst_box, snd_box);
    }
    let body_inner = strip_force(body.as_ref());
    let PseudoExpr::Apply { function, args } = body_inner else {
        return PseudoExpr::Pair(fst_box, snd_box);
    };
    if args.len() != 2 {
        return PseudoExpr::Pair(fst_box, snd_box);
    }
    // args must be Var(params[0]) and Var(params[1]) in that order.
    let arg0_ok = matches!(&args[0], PseudoExpr::Var { id: Some(v), .. } if *v == params[0].id);
    let arg1_ok = matches!(&args[1], PseudoExpr::Var { id: Some(v), .. } if *v == params[1].id);
    if !(arg0_ok && arg1_ok) {
        return PseudoExpr::Pair(fst_box, snd_box);
    }
    // function must be FieldAccess(p, PairFst).
    let function_inner = strip_force(function.as_ref());
    let PseudoExpr::FieldAccess {
        record: fst_record,
        selector: fst_sel,
    } = function_inner
    else {
        return PseudoExpr::Pair(fst_box, snd_box);
    };
    if !matches!(fst_sel, FieldSelector::PairFst) {
        return PseudoExpr::Pair(fst_box, snd_box);
    }
    let PseudoExpr::Var {
        name: p_name,
        id: Some(p_id),
    } = fst_record.as_ref()
    else {
        return PseudoExpr::Pair(fst_box, snd_box);
    };
    // .snd position: must be FieldAccess(SAME p, PairSnd).
    let PseudoExpr::FieldAccess {
        record: snd_record,
        selector: snd_sel,
    } = snd_box.as_ref()
    else {
        return PseudoExpr::Pair(fst_box, snd_box);
    };
    if !matches!(snd_sel, FieldSelector::PairSnd) {
        return PseudoExpr::Pair(fst_box, snd_box);
    }
    let PseudoExpr::Var {
        id: Some(p_id_snd), ..
    } = snd_record.as_ref()
    else {
        return PseudoExpr::Pair(fst_box, snd_box);
    };
    if p_id_snd != p_id {
        return PseudoExpr::Pair(fst_box, snd_box);
    }
    // All checks passed — collapse to just `Var(p)`.
    PseudoExpr::Var {
        name: p_name.clone(),
        id: Some(*p_id),
    }
}

fn strip_force(expr: &PseudoExpr) -> &PseudoExpr {
    let mut cur = expr;
    while let PseudoExpr::Force(inner) = cur {
        cur = inner.as_ref();
    }
    cur
}

#[cfg(test)]
mod tests;
