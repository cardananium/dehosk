//! Reduce a Church-pair-pack that is built and immediately consumed.
//!
//! A Church pair packs two fields into `fn(x) { x(a, b) }`. Applying
//! that pack to its consumer is a pure round-trip: `consumer(a, b)`.
//! Left alone, `hoist_church_pair_pack` (which runs next) lifts the
//! inline pack to a named `pair_pack` helper, leaving the opaque
//! `pair_pack(a, b)(consumer)` that `beta_reduce` can no longer
//! simplify — its callee is a helper call, not a lambda.
//!
//! Rewrite `Apply(fn(x) { x(a, b) }, [consumer])` to
//! `Apply(consumer, [a, b])` — a single beta step (`x` occurs once,
//! as the call head). When `consumer` is a 2-arg lambda, the
//! subsequent `beta_reduce_lambda_apply` turns `consumer(a, b)` into
//! a `let`-chain binding the fields.
//!
//! Runs before `hoist_church_pair_pack`, so genuine (non-applied)
//! pair values still hoist while the round-trips are gone. Only the
//! immediately-applied form (pack in function position of an `Apply`
//! with exactly one argument) is matched. The result is an ordinary
//! application, valid in any position, so no function-position guard
//! is needed. Evaluation order is preserved: `a`/`b` are evaluated
//! at the same call in both forms, never moved across a
//! lambda/thunk boundary.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{children, rewrite_bottom_up};

/// Bottom-up: [`try_reduce`] runs on each node after its children, which is where ran
/// it.
pub(super) fn reduce_applied_church_pair_pack(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_reduce)
}

/// The node's own rewrite, lifted out of the walk unchanged.
fn try_reduce(expr: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::Apply { function, args } = &expr else {
        return expr;
    };
    if args.len() != 1 {
        return expr;
    }
    let PseudoExpr::Lambda { params, body } = function.as_ref() else {
        return expr;
    };
    if params.len() != 1 {
        return expr;
    }
    // body must be exactly `param(a, b)`.
    let PseudoExpr::Apply {
        function: body_fn,
        args: body_args,
    } = body.as_ref()
    else {
        return expr;
    };
    if body_args.len() != 2 {
        return expr;
    }
    let PseudoExpr::Var {
        id: Some(head_id), ..
    } = body_fn.as_ref()
    else {
        return expr;
    };
    if *head_id != params[0].id {
        return expr;
    }
    // The parameter must occur ONLY as the call head — a genuine pair's
    // fields never reference the consumer slot. If `x` also appears in
    // `a`/`b` (e.g. `fn(x) { x(x, b) }`), lifting the args verbatim
    // would leave `x` free; that needs a full substitution, so leave it
    // for the general `beta_reduce_lambda_apply`.
    if mentions_var_id(&body_args[0], params[0].id) || mentions_var_id(&body_args[1], params[0].id)
    {
        return expr;
    }

    // Match — rebuild as `consumer(a, b)`.
    let PseudoExpr::Apply { function, mut args } = expr else {
        unreachable!("just matched Apply above");
    };
    let consumer = args.pop().expect("len checked == 1");
    let PseudoExpr::Lambda { body, .. } = function.into_inner() else {
        unreachable!("just matched Lambda above");
    };
    let PseudoExpr::Apply {
        args: field_args, ..
    } = body.into_inner()
    else {
        unreachable!("just matched Apply body above");
    };
    PseudoExpr::Apply {
        function: PBox::new(consumer),
        args: field_args,
    }
}

fn mentions_var_id(expr: &PseudoExpr, target: VarId) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::Var { id: Some(v), .. } = current
            && *v == target
        {
            return true;
        }
        // `scope_recurse::children` does not descend into
        // `WhenPattern::Literal` expressions; a missed occurrence would
        // wrongly allow the reduction, so scan them explicitly.
        if let PseudoExpr::When { clauses, .. } = current {
            for c in clauses {
                if let WhenPattern::Literal(lit) = &c.pattern {
                    pending.push(lit);
                }
            }
        }
        pending.extend(children(current));
    }
    false
}

#[cfg(test)]
mod tests;
