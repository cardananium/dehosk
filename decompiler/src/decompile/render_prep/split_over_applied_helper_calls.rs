//! Surface currying at over-applied helper call sites.
//!
//! MID translate collapses every chained UPLC application
//! `f(a)(b)(c)` into one n-ary `Apply` without consulting the callee's
//! arity. A call to a 2-param helper that returns a function and then
//! applies that result becomes a single 3-arg `Apply`, rendered
//! `helper(a, b, c)` — a wrong-arity, non-compilable call.
//!
//! Inverse of that flatten: for `Apply { Var(helper), [a1..a_{N+K}] }`
//! where `helper` is a Let-bound N-param function whose body returns a
//! K-param function and the call supplies exactly `N + K` args,
//! re-associate to `helper(a, b)(c)`.
//!
//! `Apply { f, [a1..am] }` denotes the left-associated curried spine
//! translate built. Splitting at any index is the identical term:
//! same subterms, same order, no drop/dup, same strict evaluation.
//! The returns-a-function gate only chooses the honest split point.
//!
//! Fail-closed: def is `Let { id: Some, value: Lambda }` whose body
//! tail structurally returns a function (bare `Lambda`/`RecFn`, or a
//! `Var` resolving to a body-local `Let` of one) and `K >= 1`; split
//! only at exactly `N + K` args (never a partial, never `m > N+K`,
//! never saturated `m == N`); callee is `Var { id: Some }`.
//! VarId-keyed — `alpha_uniquify` guarantees binder-id uniqueness.
//! Idempotent: after the split the outer function is an `Apply` and
//! the inner call has exactly `N` args.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

/// `VarId -> (N defined params, K returned-function arity)`.
type Candidates = HashMap<VarId, (usize, usize)>;

pub(super) fn split_over_applied_helper_calls(expr: PseudoExpr) -> PseudoExpr {
    let mut candidates = Candidates::new();
    collect(&expr, &mut candidates);
    if candidates.is_empty() {
        return expr;
    }
    rewrite(expr, &candidates)
}

/// Collect `Let`-bound N-param helpers whose body returns a
/// K-param function.
fn collect<'a>(expr: &'a PseudoExpr, out: &mut Candidates) {
    let mut pending: Vec<&'a PseudoExpr> = vec![expr];
    while let Some(expr) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            ..
        } = expr
            && let PseudoExpr::Lambda { params, body } = value.as_ref()
            && let Some(k) = returned_fn_arity(body, &mut HashMap::new())
            && k >= 1
        {
            out.insert(*vid, (params.len(), k));
        }
        for child in children(expr).into_iter().rev() {
            pending.push(child);
        }
    }
}

/// The arity of the function this expression STRUCTURALLY evaluates to:
/// a bare `Lambda`/`RecFn`, or a `Var` resolving (through the body-local
/// `Let` chain recorded in `locals`) to one. `None` for anything else
/// (When/If/Apply/outer-scope Var/BinOp/…) — fail closed.
fn returned_fn_arity<'a>(
    expr: &'a PseudoExpr,
    locals: &mut HashMap<VarId, &'a PseudoExpr>,
) -> Option<usize> {
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Lambda { params, .. } => return Some(params.len()),
            PseudoExpr::RecFn { params, .. } => return Some(params.len()),
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                if let Some(vid) = id {
                    locals.insert(*vid, value.as_ref());
                }
                current = body;
            }
            PseudoExpr::Var { id: Some(vid), .. } => {
                return match locals.get(vid)? {
                    PseudoExpr::Lambda { params, .. } => Some(params.len()),
                    PseudoExpr::RecFn { params, .. } => Some(params.len()),
                    _ => None,
                };
            }
            _ => return None,
        }
    }
}

/// Bottom-up call-site split.
///
/// The split test runs BOTTOM-UP, so it belongs after the node's children have
/// been rewritten (so an over-applied call nested in an arg splits too) —
/// exactly where [`rewrite_bottom_up`] calls back. It also fires on leaves,
/// which costs nothing: a leaf can never match the `Apply` shape.
fn rewrite(expr: PseudoExpr, candidates: &Candidates) -> PseudoExpr {
    rewrite_bottom_up(expr, |expr| split_call_site(expr, candidates))
}

/// The node-local work, run on each node once its children are rewritten.
fn split_call_site(expr: PseudoExpr, candidates: &Candidates) -> PseudoExpr {
    if let PseudoExpr::Apply { function, args } = &expr
        && let PseudoExpr::Var { id: Some(vid), .. } = function.as_ref()
        && let Some(&(n, k)) = candidates.get(vid)
        && args.len() == n + k
    {
        let PseudoExpr::Apply { function, mut args } = expr else {
            unreachable!("matched Apply above");
        };
        let rest = args.split_off(n);
        return PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Apply { function, args }),
            args: rest.into(),
        };
    }
    expr
}

/// Direct children (read-only walk for `collect`). [`rewrite_bottom_up`]
/// already covers the rewrite traversal; this mirrors it for the scan.
fn children(expr: &PseudoExpr) -> Vec<&PseudoExpr> {
    match expr {
        PseudoExpr::Apply { function, args } => {
            let mut c = vec![function.as_ref()];
            c.extend(args.iter());
            c
        }
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => vec![body.as_ref()],
        PseudoExpr::Let { value, body, .. } => vec![value.as_ref(), body.as_ref()],
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => vec![condition, then_branch, else_branch],
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            let mut c = vec![subject.as_ref()];
            for clause in clauses {
                if let Some(g) = &clause.guard {
                    c.push(g);
                }
                c.push(&clause.body);
            }
            c
        }
        PseudoExpr::List { elements, tail } => {
            let mut c: Vec<&PseudoExpr> = elements.iter().collect();
            c.extend(tail.iter().map(|t| t.as_ref()));
            c
        }
        PseudoExpr::Tuple(items) => items.iter().collect(),
        PseudoExpr::Pair(a, b) => vec![a, b],
        PseudoExpr::Constr { fields, .. } => fields.iter().collect(),
        PseudoExpr::FieldAccess { record, .. } => vec![record],
        PseudoExpr::IndexAccess { collection, .. } => vec![collection],
        PseudoExpr::BinOp { left, right, .. } => vec![left, right],
        PseudoExpr::UnOp { operand, .. } => vec![operand],
        PseudoExpr::BuiltinCall { args, .. } => args.iter().collect(),
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => vec![inner],
        PseudoExpr::Trace { message, value } => vec![message, value],
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests;
