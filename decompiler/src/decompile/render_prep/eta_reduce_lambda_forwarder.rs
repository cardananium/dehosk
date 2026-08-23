//! Eta-reduce `fn(p1, …, pN) { F(p1, …, pN) }` → `F`.
//!
//! After other render-prep passes (notably the `inline_pack_call_use_sites`
//! sentinel decoder), V1 scripts carry inline forwarder lambdas. The lambda
//! forwards its args verbatim to a closed function expression, which in a
//! call-by-value language with pure semantics (UPLC) is eta-equivalent to
//! that function value itself.
//!
//! The body must be `Apply { function: F, args: [Var(p1), …, Var(pN)] }`
//! with each arg the `Var` of the corresponding param, exactly once each
//! in declared order. Arg swap, partial application, extras — no eta.
//! `F` must not reference any param (capture safety). `F` must be a
//! `Var`, a `FieldAccess` over a closed record, or an `IndexAccess` over
//! a closed collection. Other shapes (`Apply`, `Lambda`, `RecFn`,
//! `Constr`, …) could have side effects, or change evaluation order once
//! the lambda wrapper is gone. Force wrappers around the body are peeled
//! before matching the `Apply`.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn eta_reduce_lambda_forwarder(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_rewrite)
}

fn try_rewrite(expr: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::Lambda { params, body } = expr else {
        return expr;
    };
    if params.is_empty() {
        return PseudoExpr::Lambda { params, body };
    }
    // Body must be `Apply(F, args)` with args = the params in order.
    let body_inner = strip_force(body.into_inner());
    let PseudoExpr::Apply { function, args } = body_inner else {
        return rebuild(params, body_inner);
    };
    if args.len() != params.len() {
        return rebuild(params, PseudoExpr::Apply { function, args });
    }
    // Each arg must be `Var(id == params[i].id)`.
    for (i, a) in args.iter().enumerate() {
        let ok = matches!(a, PseudoExpr::Var { id: Some(v), .. } if *v == params[i].id);
        if !ok {
            return rebuild(params, PseudoExpr::Apply { function, args });
        }
    }
    // F must not reference any of the params (capture safety).
    for p in &params {
        if contains_var_id(function.as_ref(), p.id) {
            return rebuild(params, PseudoExpr::Apply { function, args });
        }
    }
    // F must be a "safely eta-reducible" shape: Var, FieldAccess,
    // IndexAccess. Other shapes risk changing semantics.
    if !is_safe_to_eta_reduce(function.as_ref()) {
        return rebuild(params, PseudoExpr::Apply { function, args });
    }
    // All checks passed — return F.
    function.into_inner()
}

fn rebuild(params: Vec<crate::pseudo::ast::Binder>, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Lambda {
        params,
        body: PBox::new(body),
    }
}

fn strip_force(mut expr: PseudoExpr) -> PseudoExpr {
    while let PseudoExpr::Force(inner) = expr {
        expr = inner.into_inner();
    }
    expr
}

/// Shapes safe to expose in place of the lambda: `Var`, or a
/// function-valued `FieldAccess` (`pair_value.fst`) / `IndexAccess`
/// (`tuple[3]`). Excluded: `Apply`, `Lambda`, `RecFn`, `Constr`,
/// `BuiltinCall` — they may carry side effects or runtime behaviour
/// the surrounding Lambda wrapper was preserving.
fn is_safe_to_eta_reduce(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Var { .. } | PseudoExpr::FieldAccess { .. } | PseudoExpr::IndexAccess { .. }
    )
}

fn contains_var_id(expr: &PseudoExpr, target: VarId) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        let kids: Vec<&PseudoExpr> = match expr {
            PseudoExpr::Var { id: Some(v), .. } => {
                if *v == target {
                    return true;
                }
                vec![]
            }
            PseudoExpr::Let { value, body, .. } => vec![value, body],
            PseudoExpr::Lambda { body, .. } => vec![body],
            PseudoExpr::RecFn { body, .. } => vec![body],
            PseudoExpr::Apply { function, args } => {
                let mut v = vec![function.as_ref()];
                v.extend(args.iter());
                v
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => vec![condition, then_branch, else_branch],
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                let mut v = vec![subject.as_ref()];
                for c in clauses {
                    if let Some(g) = &c.guard {
                        v.push(g);
                    }
                    v.push(&c.body);
                }
                v
            }
            PseudoExpr::FieldAccess { record, .. } => vec![record],
            PseudoExpr::IndexAccess { collection, .. } => vec![collection],
            PseudoExpr::BinOp { left, right, .. } => vec![left, right],
            PseudoExpr::UnOp { operand, .. } => vec![operand],
            PseudoExpr::Constr { fields, .. } => fields.iter().collect(),
            PseudoExpr::BuiltinCall { args, .. } => args.iter().collect(),
            PseudoExpr::List { elements, tail } => {
                let mut v: Vec<&PseudoExpr> = elements.iter().collect();
                if let Some(t) = tail.as_deref() {
                    v.push(t);
                }
                v
            }
            PseudoExpr::Tuple(items) => items.iter().collect(),
            PseudoExpr::Pair(a, b) => vec![a, b],
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => vec![inner],
            PseudoExpr::Trace { message, value } => vec![message, value],
            _ => vec![],
        };
        pending.extend(kids.into_iter().rev());
    }
    false
}

#[cfg(test)]
mod tests;
