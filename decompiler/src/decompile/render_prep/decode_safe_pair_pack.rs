//! Decode safe Church-pair constructions to native `Pair(a, b)`.
//!
//! V1/V2 scripts construct 2-tuples as Church pairs, and
//! `hoist_church_pair_pack` names the constructor
//! `fn pair_pack(a, b) { fn(x) { x(a, b) } }`. The consumer side is
//! already native `expect Pair(p, q)` (from
//! `collapse_eta_pair_selector_when_subjects`); construction stays
//! Church — `decode_church_to_native` is opt-in and off by default.
//! Native destructures fed by Church `pair_pack(...)` values do not
//! compile.
//!
//! Native `Pair(a, b)` re-encodes the Church pair for every *data*
//! use: construction matches, projection is identical, and
//! `expect Pair(x,y) = Pair(a,b)` binds `x=a, y=b`. They differ only
//! when the value is applied as a function: converting one yields
//! `Pair(a, b)(selector)`, a type error since a `Pair` is not
//! callable. A mis-classified conversion is honestly invalid, never
//! silently wrong.
//!
//! For readability, not soundness, a Scott-style accumulator — a
//! construction with a `Lambda`/`RecFn` component, or one whose
//! value is applied as a function — stays Church `pair_pack(...)`
//! rather than an obvious `Pair(fn…)(…)` break.
//!
//! After `inline_constructor_helpers` and the dead-let cleanup, so
//! the `pair_pack` helper drops once no Church site references it.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, children, plain_children, rebuild_plain, take};

pub(super) fn decode_safe_pair_pack(expr: PseudoExpr) -> PseudoExpr {
    // Map each Church pack helper's binder id to its arity N
    // (`fn(a1..aN){ fn(x){ x(a1..aN) } }`).
    let mut pack_arities: HashMap<VarId, usize> = HashMap::new();
    collect_pack_helper_arities(&expr, &mut pack_arities);
    if pack_arities.is_empty() {
        return expr;
    }
    let mut applied_vars: HashSet<VarId> = HashSet::new();
    collect_applied_vars(&expr, &mut applied_vars);
    let rewritten = rewrite(expr, &pack_arities, &applied_vars, true);

    // Drop any pack helper left unreferenced once its construction
    // sites converted; the value is a pure lambda, so removing the
    // binding is sound. The generic dead-let cleanup has already run.
    let dead: HashSet<VarId> = pack_arities
        .keys()
        .copied()
        .filter(|id| !references_var(&rewritten, *id))
        .collect();
    if dead.is_empty() {
        rewritten
    } else {
        drop_helper_lets(rewritten, &dead)
    }
}

/// Does `expr` reference `target` as a `Var` anywhere (excluding the
/// helper's own binder occurrence)?
fn references_var(expr: &PseudoExpr, target: VarId) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if matches!(current, PseudoExpr::Var { id: Some(v), .. } if *v == target) {
            return true;
        }
        pending.extend(children(current));
    }
    false
}

/// Replace `let <dead helper> = <pure lambda> in body` with `body`.
///
/// A dead `let` is dropped by visiting its BODY in the node's own slot (no
/// `Post` step, no value descent). This
/// walk has no conversion gate, so every job carries `true`.
fn drop_helper_lets(expr: PseudoExpr, dead: &HashSet<VarId>) -> PseudoExpr {
    let mut steps: Vec<PackStep> = vec![PackStep::Visit(expr, true)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            PackStep::Visit(expr, _) => match expr {
                PseudoExpr::Let {
                    id: Some(bid),
                    body,
                    ..
                } if dead.contains(&bid) => steps.push(PackStep::Visit(body.into_inner(), true)),
                other => push_map_children(other, true, &mut steps, &mut done),
            },
            PackStep::Post(post) => {
                let rebuilt = rebuild_step(post, &mut done);
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "drop_helper_lets must leave one result");
    done.pop().expect("drop_helper_lets result")
}

/// A job on the two walks below. `Visit` carries [`rewrite`]'s `enabled` conversion
/// gate, which passed as an argument — it must travel with the node, not with the walk.
enum PackStep {
    Visit(PseudoExpr, bool),
    Post(PackPost),
}

enum PackPost {
    /// A construction applied as a function: the head `Var` of the inner
    /// (constructor) `Apply` is never descended into, so it rides here.
    PackApplied {
        ctor_fn: PBox,
        ctor_argc: usize,
        argc: usize,
    },
    /// A construction site. The decision between Church and native is taken
    /// AFTER the components are converted, so the gate rides here too.
    PackConstruction {
        function: PBox,
        argc: usize,
        enabled: bool,
    },
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

/// `map_children(node, |c| <walk>(c, enabled))` expressed as jobs: push the
/// node's reconstruction, then its children in REVERSE so they pop — and so
/// land on `done` — in source order. Leaves are finished on the spot, matching
/// `map_children`'s `other => other`.
fn push_map_children(
    node: PseudoExpr,
    enabled: bool,
    steps: &mut Vec<PackStep>,
    done: &mut Vec<PseudoExpr>,
) {
    match node {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            steps.push(PackStep::Post(PackPost::Let { name, id }));
            steps.push(PackStep::Visit(body.into_inner(), enabled));
            steps.push(PackStep::Visit(value.into_inner(), enabled));
        }
        PseudoExpr::Lambda { params, body } => {
            steps.push(PackStep::Post(PackPost::Lambda { params }));
            steps.push(PackStep::Visit(body.into_inner(), enabled));
        }
        PseudoExpr::RecFn { name, params, body } => {
            steps.push(PackStep::Post(PackPost::RecFn { name, params }));
            steps.push(PackStep::Visit(body.into_inner(), enabled));
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
            steps.push(PackStep::Post(PackPost::When {
                subject_name,
                clause_meta,
            }));
            for c in clause_children.into_iter().rev() {
                steps.push(PackStep::Visit(c, enabled));
            }
            steps.push(PackStep::Visit(subject.into_inner(), enabled));
        }
        other => match plain_children(other) {
            Ok((kind, children)) => {
                steps.push(PackStep::Post(PackPost::Plain(kind)));
                for c in children.into_iter().rev() {
                    steps.push(PackStep::Visit(c, enabled));
                }
            }
            Err(leaf) => done.push(leaf),
        },
    }
}

/// Reassemble one node from the already-rewritten children on `done`.
fn rebuild_step(post: PackPost, done: &mut Vec<PseudoExpr>) -> PseudoExpr {
    match post {
        PackPost::PackApplied {
            ctor_fn,
            ctor_argc,
            argc,
        } => {
            let args = take(done, argc);
            let ctor_args = take(done, ctor_argc);
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Apply {
                    function: ctor_fn,
                    args: ctor_args.into(),
                }),
                args: args.into(),
            }
        }
        PackPost::PackConstruction {
            function,
            argc,
            enabled,
        } => {
            let converted = take(done, argc);
            // Keep Church when conversion is disabled (inside an applied
            // binding's value) or when ANY component is a function (Scott
            // accumulator).
            if !enabled || converted.iter().any(is_lambda_like) {
                return PseudoExpr::Apply {
                    function,
                    args: converted.into(),
                };
            }
            // N==2 -> native `Pair(a, b)`; N>=3 -> native tuple.
            if converted.len() == 2 {
                let mut it = converted.into_iter();
                PseudoExpr::Pair(PBox::new(it.next().unwrap()), PBox::new(it.next().unwrap()))
            } else {
                PseudoExpr::Tuple(converted.into())
            }
        }
        PackPost::Let { name, id } => {
            let body = done.pop().expect("let body");
            let value = done.pop().expect("let value");
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
        PackPost::Lambda { params } => PseudoExpr::Lambda {
            params,
            body: PBox::new(done.pop().expect("lambda body")),
        },
        PackPost::RecFn { name, params } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(done.pop().expect("recfn body")),
        },
        PackPost::When {
            subject_name,
            clause_meta,
        } => {
            let total = 1 + clause_meta
                .iter()
                .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                .sum::<usize>();
            let mut parts = take(done, total).into_iter();
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
        PackPost::Plain(kind) => rebuild_plain(kind, done),
    }
}

/// A Church pack helper is, by SHAPE (name-independent), a binding whose
/// value is `fn(a1, …, aN) { fn(x) { x(a1, …, aN) } }` (N >= 2).
fn collect_pack_helper_arities(expr: &PseudoExpr, out: &mut HashMap<VarId, usize>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(bid),
            value,
            ..
        } = current
            && let Some(n) = pack_helper_arity(value)
        {
            out.insert(*bid, n);
        }
        pending.extend(children(current));
    }
}

/// If `value` is `fn(a1, …, aN) { fn(x) { x(a1, …, aN) } }` — the inner
/// args matching the outer params by VarId, in order — return N (>= 2).
fn pack_helper_arity(value: &PseudoExpr) -> Option<usize> {
    let PseudoExpr::Lambda { params, body } = value else {
        return None;
    };
    let n = params.len();
    if n < 2 {
        return None;
    }
    let PseudoExpr::Lambda {
        params: inner,
        body: inner_body,
    } = body.as_ref()
    else {
        return None;
    };
    if inner.len() != 1 {
        return None;
    }
    let x = inner[0].id;
    let PseudoExpr::Apply { function, args } = inner_body.as_ref() else {
        return None;
    };
    let ok = matches!(function.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == x)
        && args.len() == n
        && args
            .iter()
            .zip(params.iter())
            .all(|(arg, p)| matches!(arg, PseudoExpr::Var { id: Some(v), .. } if *v == p.id));
    ok.then_some(n)
}

/// Collect every VarId that appears in `Apply.function` position (used as
/// a function). A `pair_pack` binding in this set is applied as a Church
/// pair and is left un-decoded for readability.
fn collect_applied_vars(expr: &PseudoExpr, out: &mut HashSet<VarId>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::Apply { function, .. } = current
            && let PseudoExpr::Var { id: Some(v), .. } = function.as_ref()
        {
            out.insert(*v);
        }
        pending.extend(children(current));
    }
}

/// A construction `pack(v1, …, vN)` — an Apply of a pack-helper Var to
/// exactly its arity-many args.
fn is_pack_construction(expr: &PseudoExpr, pack_arities: &HashMap<VarId, usize>) -> bool {
    matches!(
        expr,
        PseudoExpr::Apply { function, args }
            if matches!(function.as_ref(), PseudoExpr::Var { id: Some(v), .. } if pack_arities.get(v) == Some(&args.len()))
    )
}

fn is_lambda_like(expr: &PseudoExpr) -> bool {
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => return true,
            PseudoExpr::Force(inner) => current = inner,
            _ => return false,
        }
    }
}

/// `enabled` is the conversion gate. It is OFF for the TAIL/result of a
/// binding applied as a function: that value IS the function, so a Church
/// pair in its result position is a selector being applied, and converting
/// it would create a `Pair(..)(..)` mismatch. This is the escape guard for
/// the Scott accumulator `let acc = when c { _ -> pair_pack(a,b) };
/// acc(sel)`.
///
/// The gate RESETS to enabled inside a `Lambda`/`RecFn` body: that body is
/// a separate function scope, so a pair built there — e.g. in a helper
/// `fn f(x){ … pair_pack(a,b) … }` that is itself applied as `f(arg)` — is
/// the helper's own DATA, not affected by the helper value being
/// function-typed. Without the reset, every pair inside every applied
/// helper would be suppressed.
///
/// `enabled` was a recursion ARGUMENT, so it travels on each [`PackStep::Visit`]
/// job rather than in a walk-wide variable: a `Let` value job carries
/// `value_enabled` while its body job carries the inherited `enabled`, and a
/// `Lambda`/`RecFn` body job carries the reset `true` — exactly the values the
/// recursive calls passed at those same points. The Church/native decision for
/// a construction site runs AFTER its components are converted, so it is its
/// own `Post` step, carrying the gate that applied at that node.
fn rewrite(
    expr: PseudoExpr,
    pack_arities: &HashMap<VarId, usize>,
    applied_vars: &HashSet<VarId>,
    enabled: bool,
) -> PseudoExpr {
    let mut steps: Vec<PackStep> = vec![PackStep::Visit(expr, enabled)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            PackStep::Visit(expr, enabled) => match expr {
                // A construction APPLIED as a function `pack(v1..vN)(…)` is a
                // selector being taken: keep it Church, but recurse both arg lists.
                PseudoExpr::Apply { function, args }
                    if is_pack_construction(&function, pack_arities) =>
                {
                    let PseudoExpr::Apply {
                        function: ctor_fn,
                        args: ctor_args,
                    } = function.into_inner()
                    else {
                        unreachable!("is_pack_construction guarantees an Apply");
                    };
                    steps.push(PackStep::Post(PackPost::PackApplied {
                        ctor_fn,
                        ctor_argc: ctor_args.len(),
                        argc: args.len(),
                    }));
                    // Reversed so the two lists pop in source order: every
                    // `ctor_args` element first, then every `args` element.
                    for a in args.into_iter().rev() {
                        steps.push(PackStep::Visit(a, enabled));
                    }
                    for a in ctor_args.into_iter().rev() {
                        steps.push(PackStep::Visit(a, enabled));
                    }
                }
                // A construction site `pack(v1, …, vN)`.
                PseudoExpr::Apply { function, args }
                    if is_pack_construction_parts(&function, &args, pack_arities) =>
                {
                    steps.push(PackStep::Post(PackPost::PackConstruction {
                        function,
                        argc: args.len(),
                        enabled,
                    }));
                    for a in args.into_iter().rev() {
                        steps.push(PackStep::Visit(a, enabled));
                    }
                }
                // Disable conversion in a binding's VALUE when the binder is
                // applied as a function anywhere; the Lambda/RecFn arms
                // re-enable it.
                PseudoExpr::Let {
                    name,
                    id: Some(bid),
                    value,
                    body,
                } => {
                    let value_enabled = enabled && !applied_vars.contains(&bid);
                    steps.push(PackStep::Post(PackPost::Let {
                        name,
                        id: Some(bid),
                    }));
                    steps.push(PackStep::Visit(body.into_inner(), enabled));
                    steps.push(PackStep::Visit(value.into_inner(), value_enabled));
                }
                // A nested function scope: pairs in its body are the
                // function's own data — RESET the gate.
                PseudoExpr::Lambda { params, body } => {
                    steps.push(PackStep::Post(PackPost::Lambda { params }));
                    steps.push(PackStep::Visit(body.into_inner(), true));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(PackStep::Post(PackPost::RecFn { name, params }));
                    steps.push(PackStep::Visit(body.into_inner(), true));
                }
                other => push_map_children(other, enabled, &mut steps, &mut done),
            },
            PackStep::Post(post) => {
                let rebuilt = rebuild_step(post, &mut done);
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

/// `function(args)` is a construction of a pack helper applied to exactly
/// its arity-many args.
fn is_pack_construction_parts(
    function: &PseudoExpr,
    args: &[PseudoExpr],
    pack_arities: &HashMap<VarId, usize>,
) -> bool {
    matches!(function, PseudoExpr::Var { id: Some(v), .. } if pack_arities.get(v) == Some(&args.len()))
}

#[cfg(test)]
mod tests;
