//! Eta-saturate a recursion knot whose visible parameter is a dead strictness
//! thunk and whose body under-applies a known callee by exactly one argument.
//!
//! PlutusTx list decoders are Y-combinator knots. The decompiler lowers the
//! knot's dummy strictness-thunk parameter into the rec fn's own parameter and
//! renders the body as the partial `force(knot)` value, dropping the wiring
//! that applies the real list argument at each call site. Every use is
//! `o(list)` and the result is consumed as a list, but as rendered
//! `o(list) = helper(nil, cons)` is a 2-of-3 partial — a function, not a
//! list. The knot's real meaning is `o(z) = helper(nil, cons, z)`.
//!
//! So a `rec fn f(p) { callee(a1, …, ak) }` where `p` is dead in the body,
//! the body is a direct application of a callee of known arity, and that
//! arity is exactly `k + 1`, becomes `rec fn f(p) { callee(a1, …, ak, p) }`:
//! the dead parameter is the missing trailing argument, renamed to the
//! callee's own trailing parameter name. Self-calls `f(tail)` then correctly
//! mean `callee(…, tail)`.
//!
//! Fail-closed:
//! - Only a `RecFn` (a genuine fixpoint — a non-recursive constant function
//!   returning a partial would not be rendered `rec fn`).
//! - Exactly one parameter, dead in the body, so nothing that currently
//!   reads it is disturbed.
//! - The callee's arity must be known (a let-bound Lambda/RecFn) and equal
//!   to `args + 1`, so appending one argument saturates it exactly and
//!   never over-applies.
//!   Adding the arithmetically-required final argument cannot change a
//!   well-formed program's meaning.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::decompile::simplify::Simplifier;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

pub(super) fn saturate_dead_param_knot(expr: PseudoExpr) -> PseudoExpr {
    let mut params = HashMap::new();
    collect_fn_params(&expr, &mut params);
    rewrite(expr, &params)
}

/// Map every let-bound `Lambda`/`RecFn` (and standalone `RecFn`) VarId to its
/// parameter binders, so a callee's arity + trailing-param name are known.
fn collect_fn_params(expr: &PseudoExpr, out: &mut HashMap<VarId, Vec<Binder>>) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            PseudoExpr::Let {
                id: Some(v), value, ..
            } => match value.as_ref() {
                PseudoExpr::Lambda { params, .. } | PseudoExpr::RecFn { params, .. } => {
                    out.insert(*v, params.clone());
                }
                _ => {}
            },
            PseudoExpr::RecFn { name, params, .. } => {
                out.insert(name.id, params.clone());
            }
            _ => {}
        }
        pending.extend(children(expr).into_iter().rev());
    }
}

fn rewrite(expr: PseudoExpr, params: &HashMap<VarId, Vec<Binder>>) -> PseudoExpr {
    struct Saturate<'a> {
        params: &'a HashMap<VarId, Vec<Binder>>,
    }

    impl ExprFolder for Saturate<'_> {
        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            pattern
        }

        fn post_recfn(
            &mut self,
            name: Binder,
            params: Vec<Binder>,
            body: PseudoExpr,
        ) -> PseudoExpr {
            if let Some((saturated_params, saturated_body)) =
                try_saturate(&params, &body, self.params)
            {
                PseudoExpr::RecFn {
                    name,
                    params: saturated_params,
                    body: PBox::new(saturated_body),
                }
            } else {
                PseudoExpr::RecFn {
                    name,
                    params,
                    body: PBox::new(body),
                }
            }
        }
    }

    Saturate { params }.fold(expr)
}

/// If `fn_params` is a single DEAD parameter and `body` under-applies a known
/// callee by exactly one, return the (renamed param, saturated body).
fn try_saturate(
    fn_params: &[Binder],
    body: &PseudoExpr,
    params: &HashMap<VarId, Vec<Binder>>,
) -> Option<(Vec<Binder>, PseudoExpr)> {
    let [p] = fn_params else {
        return None;
    };
    // The parameter must be unused in the body (it's the dummy thunk slot).
    if Simplifier::count_var_uses_by_id(body, &p.name, Some(p.id)) != 0 {
        return None;
    }
    let PseudoExpr::Apply { function, args } = body else {
        return None;
    };
    let PseudoExpr::Var {
        id: Some(callee), ..
    } = function.as_ref()
    else {
        return None;
    };
    let callee_params = params.get(callee)?;
    // Appending the one parameter must saturate the callee exactly.
    if callee_params.len() != args.len() + 1 {
        return None;
    }
    // Rename the (formerly dead) parameter to the callee's trailing parameter
    // name for readability; keep its VarId so references stay linked.
    let trailing_name = callee_params
        .last()
        .map(|b| b.name.clone())
        .unwrap_or_else(|| p.name.clone());
    let renamed = Binder::new(trailing_name.clone(), p.id);
    let mut new_args = args.clone();
    new_args.push(PseudoExpr::var_with_id(trailing_name, p.id));
    let saturated_body = PseudoExpr::Apply {
        function: function.clone(),
        args: new_args,
    };
    Some((vec![renamed], saturated_body))
}

#[cfg(test)]
mod tests;
