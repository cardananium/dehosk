//! Strip a stray empty `()` applied to a call whose result is non-callable.
//!
//! Delay/Force cancellation upstream can leave a trailing empty apply on a
//! fully-applied named function. `<call>()` is
//! `Apply { function: Apply { Var(fn), args }, args: [] }`. When `fn`'s
//! body always returns a non-callable literal (`List` / `Pair` / `Tuple` /
//! `Constr`), `fn(args)` is not a function — applying `()` to it is an
//! ill-typed UPLC application the original program never executed. Dropping
//! that stray Force residue is a semantic no-op; downstream `.fst`/`==` then
//! projects the real List/Pair value.
//!
//! Soundness rests on the callee's return shape alone — a local, observable
//! fact. The gate (`all_tails_non_callable`) is conservative: every tail of
//! the body must be a non-callable literal or `fail` (a divergence that
//! returns nothing); anything that could be, or return, a function (`Var`,
//! `Apply`, `Lambda`, `BuiltinCall`, `Force`, …) fails it, so a legitimate
//! 0-arity call is never dropped.

use std::collections::HashMap;

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

pub(super) fn strip_void_apply_on_noncallable_result(expr: PseudoExpr) -> PseudoExpr {
    // fn binder id → arity. Only a FULL application (`args.len() == arity`) is
    // stripped: a partial one returns the curried remainder, which is callable,
    // so its trailing `()` is a real argument.
    let mut candidates: HashMap<VarId, (usize, &PseudoExpr)> = HashMap::new();
    collect_fn_bodies(&expr, &mut candidates);
    let non_callable = solve_non_callable(&candidates);
    if non_callable.is_empty() {
        return expr;
    }
    rewrite(expr, &non_callable)
}

/// Which of `candidates` provably never return a function.
///
/// A GREATEST fixpoint: assume every named function is non-callable, then
/// drop the ones whose tails contradict it, until nothing changes. The
/// optimistic start is what admits mutual recursion — `b` returns
/// `a(..)` and `a` returns `b(..)`, so a least fixpoint would prove
/// neither, though neither can return a function: every tail that is not
/// such a call is a scalar.
///
/// Deliberately uncapped. Each non-final round removes at least one
/// entry from a finite set, so it terminates in at most
/// `candidates.len()` rounds. A round cap would be UNSOUND in the wrong
/// direction: cutting the loop short leaves entries still ASSUMED
/// non-callable that a further round would have removed, so a helper
/// chain longer than the cap would have its `()` stripped off a call
/// that really can return a function.
fn solve_non_callable(candidates: &HashMap<VarId, (usize, &PseudoExpr)>) -> HashMap<VarId, usize> {
    let mut assumed: HashMap<VarId, usize> = candidates
        .iter()
        .map(|(id, (arity, _))| (*id, *arity))
        .collect();
    loop {
        let violators: Vec<VarId> = assumed
            .keys()
            .copied()
            .filter(|id| {
                let (_, body) = candidates[id];
                !all_tails_non_callable(body, &assumed)
            })
            .collect();
        if violators.is_empty() {
            return assumed;
        }
        for id in violators {
            assumed.remove(&id);
        }
    }
}

/// Collect `binder id → (arity, body)` for every named `fn`/`rec fn`
/// definition. Covers both representations: a `Let` bound to a
/// `Lambda`/`RecFn` (keyed by the `Let` id), and a `RecFn` (keyed by its own
/// `name.id`, which recursive/self references carry). The non-callable
/// question is answered later, by [`solve_non_callable`].
fn collect_fn_bodies<'a>(expr: &'a PseudoExpr, out: &mut HashMap<VarId, (usize, &'a PseudoExpr)>) {
    let mut pending: Vec<&'a PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Let { id, value, .. } => {
                let fn_info = match value.as_ref() {
                    PseudoExpr::Lambda { params, body } => Some((params.len(), body.as_ref())),
                    PseudoExpr::RecFn { params, body, .. } => Some((params.len(), body.as_ref())),
                    _ => None,
                };
                if let (Some(binder_id), Some((arity, body))) = (id, fn_info) {
                    out.insert(*binder_id, (arity, body));
                }
                if let PseudoExpr::RecFn {
                    name, params, body, ..
                } = value.as_ref()
                {
                    out.insert(name.id, (params.len(), body.as_ref()));
                }
            }
            PseudoExpr::RecFn {
                name, params, body, ..
            } => {
                out.insert(name.id, (params.len(), body.as_ref()));
            }
            _ => {}
        }
        pending.extend(children(current).into_iter().rev());
    }
}

/// True iff EVERY tail-position expression of `body` is a non-callable literal
/// (`List`/`Pair`/`Tuple`/`Constr`) or `fail` (an `Error` divergence never
/// returns a callable), recursing through the control-flow tails
/// (`If`/`When`/`Let`/`Trace`). Any other tail shape is possibly-callable.
fn all_tails_non_callable(body: &PseudoExpr, assumed: &HashMap<VarId, usize>) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![body];
    while let Some(current) = pending.pop() {
        match current {
            // A SATURATED call to a function that is itself non-callable.
            // Under-applying one leaves the curried remainder, which is.
            PseudoExpr::Apply { function, args } => {
                let ok = matches!(function.as_ref(), PseudoExpr::Var { id: Some(v), .. }
                    if assumed.get(v) == Some(&args.len()));
                if !ok {
                    return false;
                }
            }
            PseudoExpr::List { .. }
            | PseudoExpr::Pair(..)
            | PseudoExpr::Tuple(_)
            | PseudoExpr::Constr { .. }
            | PseudoExpr::Error { .. } => {}
            // An operator's result is a scalar — `Int`, `Bool`, `ByteArray` —
            // and a literal is itself. Neither can be applied, so a trailing
            // `()` on a function that returns one is the same Force residue
            // the literal cases cover. This is what leaves `-> Bool` helpers
            // rendering as `helper(a, b)()`, an application of a boolean.
            PseudoExpr::BinOp { .. }
            | PseudoExpr::UnOp { .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit => {}
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::When { clauses, .. } => {
                pending.extend(clauses.iter().map(|c| &c.body));
            }
            PseudoExpr::Let { body, .. } => pending.push(body),
            PseudoExpr::Trace { value, .. } => pending.push(value),
            _ => return false,
        }
    }
    true
}

fn rewrite(expr: PseudoExpr, non_callable: &HashMap<VarId, usize>) -> PseudoExpr {
    struct Rewriter<'a> {
        non_callable: &'a HashMap<VarId, usize>,
    }

    impl ExprFolder for Rewriter<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_expr(&mut self, expr: PseudoExpr) -> PseudoExpr {
            match expr {
                // `<fn(args)>()` where `fn` returns a non-callable → drop the stray
                // `()`, which is either an empty `Apply` or a `Force` (both render
                // as `x()`).
                PseudoExpr::Apply { function, args }
                    if args.is_empty()
                        && is_full_noncallable_call(&function, self.non_callable) =>
                {
                    function.into_inner()
                }
                PseudoExpr::Force(inner) if is_full_noncallable_call(&inner, self.non_callable) => {
                    inner.into_inner()
                }
                other => other,
            }
        }
    }

    Rewriter { non_callable }.fold(expr)
}

/// `f` is `Apply { function: Var(id), args }` where `id` is a collected
/// non-callable-returning fn AND `args.len()` equals its arity — a FULL
/// application whose result is provably not a function. A partial application
/// returns the curried remainder, which is callable, so it must NOT match.
fn is_full_noncallable_call(f: &PseudoExpr, non_callable: &HashMap<VarId, usize>) -> bool {
    let PseudoExpr::Apply { function, args } = f else {
        return false;
    };
    let PseudoExpr::Var { id: Some(v), .. } = function.as_ref() else {
        return false;
    };
    non_callable.get(v) == Some(&args.len())
}

#[cfg(test)]
mod tests;
