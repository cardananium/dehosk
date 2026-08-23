//! Flatten `rec fn name(unused_self) { fn(p1, …, pN) { body } }`
//! to `rec fn name(p1, …, pN) { body }` when the outer self-param
//! is never referenced.
//!
//! V1 scripts produce Y-combinator-decoded rec-fns where the outer
//! `Lambda` (the Y-fix self-receiver) survives with an unused param.
//! After Y-fix the runtime arity is the inner `Lambda`'s: the outer
//! param is consumed during fix-point construction, so the curried
//! 1+N form only obscures the real arity.
//!
//! Fire only when every outer `RecFn` param is unused in the body
//! and the body is exactly a `Lambda` — the flattened params and
//! body are that Lambda's. Every self-reference inside must already
//! be an `Apply` carrying at least the inner arity; flattening drops
//! the written arity by the outer-param count, so a bare or
//! under-applied reference would break.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn flatten_recfn_unused_self(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_rewrite)
}

fn try_rewrite(expr: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::RecFn { name, params, body } = expr else {
        return expr;
    };
    // Outer params must be unused — that's what makes the outer
    // Lambda pure Y-comb residue.
    for p in &params {
        if contains_var_id(&body, p.id) {
            return PseudoExpr::RecFn { name, params, body };
        }
    }
    // Body must be exactly a single `Lambda` whose arity is the
    // post-flatten arity.
    let unboxed = body.into_inner();
    let PseudoExpr::Lambda {
        params: inner_params,
        body: inner_body,
    } = unboxed
    else {
        // Body isn't a Lambda: dropping the outer wrapper would
        // change the rec-fn's arity and shift Apply-chain semantics.
        return PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(unboxed),
        };
    };
    // Soundness gate: every self-reference in the body must sit in
    // `Apply.function` position with at least the inner arity —
    // flattening drops the runtime arity by the outer-param count,
    // so a partial-application call site would break.
    if !all_self_refs_fully_applied(&inner_body, name.id, inner_params.len()) {
        // Reconstruct original — flatten not safe.
        return PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(PseudoExpr::Lambda {
                params: inner_params,
                body: inner_body,
            }),
        };
    }
    PseudoExpr::RecFn {
        name,
        params: inner_params,
        body: inner_body,
    }
}

/// Return false if any reference to `self_id` inside `expr` is NOT
/// the `function` field of an `Apply` with `args.len() >= min_arity`.
fn all_self_refs_fully_applied(expr: &PseudoExpr, self_id: VarId, min_arity: usize) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            // Apply where the function is exactly `Var(self_id)`: arity
            // check on this site, and descend into args only — `function`
            // is deliberately NOT pushed, since it's the self-reference
            // this Apply legitimately consumes.
            PseudoExpr::Apply { function, args } => {
                if let PseudoExpr::Var { id: Some(v), .. } = function.as_ref()
                    && *v == self_id
                {
                    if args.len() < min_arity {
                        return false;
                    }
                    // Args still need to be self-clean.
                    pending.extend(args.iter());
                    continue;
                }
                // Non-self Apply — descend into both.
                pending.push(function);
                pending.extend(args.iter());
            }
            // Bare reference to self: under-applied → unsafe.
            PseudoExpr::Var { id: Some(v), .. } if *v == self_id => return false,
            _ => pending.extend(super::scope_recurse::children(current)),
        }
    }
    true
}

fn contains_var_id(expr: &PseudoExpr, target: VarId) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Var { id: Some(v), .. } if *v == target => return true,
            _ => pending.extend(super::scope_recurse::children(current)),
        }
    }
    false
}

#[cfg(test)]
mod tests;
