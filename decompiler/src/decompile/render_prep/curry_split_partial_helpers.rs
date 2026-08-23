//! Curry-split helpers that are only ever called at one partial arity
//! below their full param count.
//!
//! The Plutus `fn(p_0, ..., p_{n-1}) { p_{n-1}(p_0, ..., p_{n-2}) }`
//! shape — a Church-pair-pack / Scott-encoded constructor — arrives with
//! its full n-param signature but is called at partial arity K < n: the
//! K captured args are the constructor payload, the remaining params the
//! consumer interface. Rendered literally, that is a type error.
//!
//! A let-bound helper of that shape whose call sites all use the same K
//! is rewritten so the outer lambda takes the K payload params and
//! returns an inner lambda of the remaining n−K consumer params with
//! the original body. The K-arg call now returns the inner Lambda, and
//! applying that to `(_, k)` still yields `k(x, y)`.
//!
//! Shape recognition, as in `is_y_comb_defining_lambda` /
//! `is_church_cons_shape`: the outer body is `Apply { function:
//! Var(last param), args: [Var(some prefix of params)] }`, and K is the
//! number of args it passes to the continuation.
//!
//! - The helper must be let-bound, so the rewrite has a clear scope.
//! - Every call site must pass exactly K args; one call at a different
//!   arity leaves the helper untouched, since the split would break it.
//! - The body args must be exactly `Var(p_0), ..., Var(p_{K-1})` in
//!   order, with nothing else interleaved — the captured-payload shape.
//! - K must be strictly less than n; at K == n the helper is already
//!   used at full arity.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, children, plain_children, rebuild_plain, take};

pub(super) fn curry_split_partial_helpers(expr: PseudoExpr) -> PseudoExpr {
    let mut helpers: HashMap<VarId, HelperShape> = HashMap::new();
    collect_helpers(&expr, &mut helpers);
    if helpers.is_empty() {
        return expr;
    }
    // Splittable: the helper has at least one call site and every
    // call passes exactly K args.
    let mut call_arities: HashMap<VarId, Vec<usize>> = HashMap::new();
    collect_call_arities(&expr, &helpers, &mut call_arities);
    let splittable: HashMap<VarId, HelperShape> = helpers
        .into_iter()
        .filter(|(vid, shape)| {
            let Some(arities) = call_arities.get(vid) else {
                return false; // No calls → no split needed.
            };
            !arities.is_empty() && arities.iter().all(|&a| a == shape.split_k)
        })
        .collect();
    if splittable.is_empty() {
        return expr;
    }
    rewrite_let_values(expr, &splittable)
}

#[derive(Clone, Copy)]
struct HelperShape {
    /// Full param count of the outer Lambda.
    n: usize,
    /// Number of payload positions the body passes to the continuation.
    /// The curry split point: outer takes K params, inner takes (n - K).
    split_k: usize,
}

/// Match `Lambda(p_0, ..., p_{n-1}) -> Apply(Var(p_{n-1}), [Var(p_0),
/// ..., Var(p_{K-1})])` where K < n and the args are exactly the
/// initial K param Vars in order.
fn try_match_church_pair_shape(value: &PseudoExpr) -> Option<HelperShape> {
    let PseudoExpr::Lambda { params, body } = value else {
        return None;
    };
    let n = params.len();
    if n < 3 {
        // A split needs 1 payload + 1 continuation + 1 further
        // param; below 3 the helper is already minimal-arity.
        return None;
    }
    let last_param_id = params[n - 1].var_id();
    // Body may be wrapped in Force(...) — peel as in church-list.
    let mut body_inner = body.as_ref();
    while let PseudoExpr::Force(inner) = body_inner {
        body_inner = inner;
    }
    let PseudoExpr::Apply { function, args } = body_inner else {
        return None;
    };
    // Function head: Var(last param) (with any Force-peel).
    let mut fn_inner = function.as_ref();
    while let PseudoExpr::Force(inner) = fn_inner {
        fn_inner = inner;
    }
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = fn_inner
    else {
        return None;
    };
    if *fn_id != last_param_id {
        return None;
    }
    let k = args.len();
    if k == 0 || k >= n {
        return None;
    }
    // Each arg must be Var(p_i) in order.
    for (i, arg) in args.iter().enumerate() {
        let PseudoExpr::Var {
            id: Some(arg_id), ..
        } = arg
        else {
            return None;
        };
        if *arg_id != params[i].var_id() {
            return None;
        }
    }
    Some(HelperShape { n, split_k: k })
}

fn collect_helpers(expr: &PseudoExpr, out: &mut HashMap<VarId, HelperShape>) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if let PseudoExpr::Let { id, value, .. } = expr
            && let Some(binder_id) = id
            && let Some(shape) = try_match_church_pair_shape(value)
        {
            out.insert(*binder_id, shape);
        }
        for child in children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

fn collect_call_arities(
    expr: &PseudoExpr,
    helpers: &HashMap<VarId, HelperShape>,
    out: &mut HashMap<VarId, Vec<usize>>,
) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if let PseudoExpr::Apply { function, args } = expr {
            // Peel Force wrappers off the function head.
            let mut fn_inner = function.as_ref();
            while let PseudoExpr::Force(inner) = fn_inner {
                fn_inner = inner;
            }
            if let PseudoExpr::Var { id: Some(vid), .. } = fn_inner
                && helpers.contains_key(vid)
            {
                out.entry(*vid).or_default().push(args.len());
            }
        }
        for child in children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// One pending job of [`rewrite_let_values`]'s explicit stack: a node still to visit,
/// or rebuild after children.
enum SplitStep {
    Visit(PseudoExpr),
    Post(SplitPost),
}

enum SplitPost {
    Let {
        name: String,
        id: Option<VarId>,
    },
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    When {
        subject_name: Option<Binder>,
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Only the `Let` arm does anything but rebuild verbatim from rewritten children, so
/// every other kind goes through `plain_children` / `rebuild_plain`. A splittable let's
/// VALUE is curry-split in place and never descended into — — so it goes straight onto
/// `done` in the slot the value occupies, and only the body is visited.
fn rewrite_let_values(expr: PseudoExpr, splittable: &HashMap<VarId, HelperShape>) -> PseudoExpr {
    let mut steps: Vec<SplitStep> = vec![SplitStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            SplitStep::Visit(expr) => match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    let split = id.and_then(|binder_id| splittable.get(&binder_id).copied());
                    steps.push(SplitStep::Post(SplitPost::Let { name, id }));
                    match split {
                        Some(shape) => {
                            done.push(curry_split_value(value.into_inner(), shape).into_inner());
                            steps.push(SplitStep::Visit(body.into_inner()));
                        }
                        None => {
                            // Reversed so they pop — and so land on `done` — in order.
                            steps.push(SplitStep::Visit(body.into_inner()));
                            steps.push(SplitStep::Visit(value.into_inner()));
                        }
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(SplitStep::Post(SplitPost::Lambda { params }));
                    steps.push(SplitStep::Visit(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(SplitStep::Post(SplitPost::RecFn { name, params }));
                    steps.push(SplitStep::Visit(body.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut clause_children = Vec::new();
                    for c in clauses {
                        clause_meta.push((c.pattern, c.guard.is_some()));
                        if let Some(g) = c.guard {
                            clause_children.push(g);
                        }
                        clause_children.push(c.body);
                    }
                    steps.push(SplitStep::Post(SplitPost::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(SplitStep::Visit(c));
                    }
                    steps.push(SplitStep::Visit(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(SplitStep::Post(SplitPost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(SplitStep::Visit(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            SplitStep::Post(post) => {
                let rebuilt = match post {
                    SplitPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    SplitPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    SplitPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    SplitPost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = take(&mut done, total).into_iter();
                        let subject = parts.next().expect("when subject");
                        let clauses = clause_meta
                            .into_iter()
                            .map(|(pattern, has_guard)| WhenClause {
                                pattern,
                                guard: has_guard.then(|| parts.next().expect("when guard")),
                                body: parts.next().expect("when clause body"),
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    SplitPost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite_let_values must leave one result");
    done.pop().expect("rewrite_let_values result")
}

/// Curry-split the value `Lambda(p_0, ..., p_{n-1}) { body }` at
/// position K into `Lambda(p_0, ..., p_{K-1}) { Lambda(p_K, ..., p_{n-1}) { body } }`.
fn curry_split_value(value: PseudoExpr, shape: HelperShape) -> PBox {
    let PseudoExpr::Lambda { params, body } = value else {
        // `helpers` was built from this exact node, so a non-Lambda
        // cannot reach here; the fallback drops the value.
        return PBox::new(PseudoExpr::Unit);
    };
    let n = shape.n;
    let k = shape.split_k;
    debug_assert_eq!(params.len(), n);
    debug_assert!(k < n);
    let mut outer_params: Vec<Binder> = Vec::with_capacity(k);
    let mut inner_params: Vec<Binder> = Vec::with_capacity(n - k);
    for (i, p) in params.into_iter().enumerate() {
        if i < k {
            outer_params.push(p);
        } else {
            inner_params.push(p);
        }
    }
    let inner_lambda = PseudoExpr::Lambda {
        params: inner_params,
        body,
    };
    PBox::new(PseudoExpr::Lambda {
        params: outer_params,
        body: PBox::new(inner_lambda),
    })
}

#[cfg(test)]
mod tests;
