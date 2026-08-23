//! Strip stray zero-arg wrappers around non-callable expressions.
//!
//! Two AST shapes both render as a trailing `}()`: an explicit
//! `Apply { function: When { ... }, args: [] }`, and a `Force { inner:
//! When { ... } }` — the renderer turns a standalone `Force(x)` into
//! `x()` (`pseudo/pretty/mod.rs` "Standalone Force(x) → x()").
//!
//! For any structurally non-callable `e` (`When` / `If` / `Trace` /
//! `Let`), both `(e())` and `force(e)` are semantic no-ops: the
//! `()` / `force` are UPLC thunk artifacts left uncancelled
//! upstream. Unwrap to just `e`. `Var`, `RecFn`, `BuiltinCall` and a
//! zero-param `Lambda` can legitimately be 0-arity calls and are
//! left alone.
//!
//! A delay/force U-combinator also lowers into an n-param `RecFn`
//! that absorbed its interior `delay` into the param list, but the
//! matching outer UPLC `force` survives; once
//! `simplify_force_through_wrappers` sinks it onto the body the
//! residue is `Force(Apply{Var(rec_fn), [driver]})`, printed as
//! `rec_fn(driver)()`. A partial application of an n-param function
//! is a lambda value (never a `Delay`/thunk), so the `Force` is a
//! no-op. Stripping is gated on a collision-poisoned arity witness
//! (`is_provable_partial_recfn_apply`) and on the `Force` being in
//! standalone (not function) position — in function position it
//! renders transparently, so there is nothing to strip.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PVec;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

/// Arity of every rec-fn binder, keyed by `VarId`. A `None` value is a
/// POISONED id (recorded with conflicting arities, or also bound by a
/// non-rec-fn binder) — the witness never fires on it (fail closed).
type RecFnArities = HashMap<VarId, Option<usize>>;

pub(super) fn strip_stray_thunk_wrappers(expr: PseudoExpr) -> PseudoExpr {
    let arities = collect_recfn_arities(&expr);
    strip(expr, &arities, false)
}

/// `in_fn_position` rides on each `Visit` job: the head of an `Apply` gets
/// `true` and every other child `false`. The two arms that decide on their
/// already-stripped child — a zero-arg `Apply` and a `Force` — keep that
/// decision in their own `Post` step.
fn strip(expr: PseudoExpr, arities: &RecFnArities, in_fn_position: bool) -> PseudoExpr {
    let mut steps: Vec<StripStep> = vec![StripStep::Visit(expr, in_fn_position)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            StripStep::Visit(expr, in_fn_position) => match expr {
                PseudoExpr::Apply { function, args } if args.is_empty() => {
                    // `f()` is identity for ANY `f`, so the partial-rec-fn witness
                    // needs no `in_fn_position` gate here, unlike the `Force` arm.
                    steps.push(StripStep::Post(StripPost::EmptyApply));
                    steps.push(StripStep::Visit(function.into_inner(), true));
                }
                PseudoExpr::Apply { function, args } => {
                    let argc = args.len();
                    steps.push(StripStep::Post(StripPost::Plain(PlainPost::Apply { argc })));
                    // Reversed so they pop — and so land on `done` — in order.
                    for a in args.into_vec().into_iter().rev() {
                        steps.push(StripStep::Visit(a, false));
                    }
                    steps.push(StripStep::Visit(function.into_inner(), true));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(StripStep::Post(StripPost::Lambda { params }));
                    steps.push(StripStep::Visit(body.into_inner(), false));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(StripStep::Post(StripPost::RecFn { name, params }));
                    steps.push(StripStep::Visit(body.into_inner(), false));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(StripStep::Post(StripPost::Let { name, id }));
                    steps.push(StripStep::Visit(body.into_inner(), false));
                    steps.push(StripStep::Visit(value.into_inner(), false));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut clause_children = Vec::new();
                    for clause in clauses {
                        clause_meta.push((clause.pattern, clause.guard.is_some()));
                        if let Some(g) = clause.guard {
                            clause_children.push(g);
                        }
                        clause_children.push(clause.body);
                    }
                    steps.push(StripStep::Post(StripPost::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(StripStep::Visit(c, false));
                    }
                    steps.push(StripStep::Visit(subject.into_inner(), false));
                }
                PseudoExpr::Force(inner) => {
                    steps.push(StripStep::Post(StripPost::Force { in_fn_position }));
                    steps.push(StripStep::Visit(inner.into_inner(), false));
                }
                // Every remaining non-leaf kind rebuilds verbatim with each child
                // stripped at `in_fn_position: false`, which is exactly
                // `plain_children` / `rebuild_plain`; the leaves fall through `Err`
                // untouched.
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(StripStep::Post(StripPost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(StripStep::Visit(c, false));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            StripStep::Post(post) => {
                let rebuilt = match post {
                    StripPost::EmptyApply => {
                        let unwrapped_function = done.pop().expect("apply function");
                        if is_unwrappable(&unwrapped_function)
                            || is_provable_partial_recfn_apply(&unwrapped_function, arities)
                        {
                            // The trailing `()` is stray — return just the inner expression.
                            unwrapped_function
                        } else {
                            PseudoExpr::Apply {
                                function: PBox::new(unwrapped_function),
                                args: PVec::new(),
                            }
                        }
                    }
                    StripPost::Force { in_fn_position } => {
                        let inner = done.pop().expect("force inner");
                        // A standalone `Force(x)` renders as `x()` (pretty/mod.rs ~1298).
                        // Strip when `x` is non-callable (When/If/Trace/Let) or a provable
                        // PARTIAL rec-fn application — a lambda value, so forcing is a
                        // no-op. The `!in_fn_position` gate spares a `Force` in function
                        // position, which renders transparently and leaves no stray `()`.
                        if is_unwrappable(&inner)
                            || (!in_fn_position && is_provable_partial_recfn_apply(&inner, arities))
                        {
                            inner
                        } else {
                            PseudoExpr::Force(PBox::new(inner))
                        }
                    }
                    StripPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    StripPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    StripPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    StripPost::When {
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
                    StripPost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "strip must leave one result");
    done.pop().expect("strip result")
}

/// A job on [`strip`]'s stack. `Visit` carries the `in_fn_position` flag;
/// the `Post` variants run after that node's children.
enum StripStep {
    Visit(PseudoExpr, bool),
    Post(StripPost),
}

enum StripPost {
    /// `Apply { args: [] }` — decides whether the trailing `()` is stray.
    EmptyApply,
    /// `Force` — decides whether the `force` is stray; needs the flag the
    /// enclosing `Visit` was handed.
    Force {
        in_fn_position: bool,
    },
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    Let {
        name: String,
        id: Option<VarId>,
    },
    When {
        subject_name: Option<Binder>,
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Pre-scan the tree, mapping each rec-fn binder `VarId` to its param
/// arity, POISONING (`None`) any id recorded with two different arities
/// or ALSO bound by a non-rec-fn binder (lambda/recfn params,
/// when-pattern binders, non-rec-fn lets). alpha_uniquify makes
/// cross-kind id reuse unlikely, not impossible, so the map fails closed.
fn collect_recfn_arities(expr: &PseudoExpr) -> RecFnArities {
    let mut recfn: HashMap<VarId, usize> = HashMap::new();
    let mut conflicts: HashSet<VarId> = HashSet::new();
    let mut other_binders: HashSet<VarId> = HashSet::new();
    scan(expr, &mut recfn, &mut conflicts, &mut other_binders);
    recfn
        .into_iter()
        .map(|(id, arity)| {
            let poisoned = conflicts.contains(&id) || other_binders.contains(&id);
            (id, if poisoned { None } else { Some(arity) })
        })
        .collect()
}

/// Record one rec-fn binder's arity, poisoning the id on a conflict. Was a
/// closure inside `scan`; hoisted out because the iterative form borrows
/// `recfn`/`conflicts` for the whole loop.
fn record_recfn(
    recfn: &mut HashMap<VarId, usize>,
    conflicts: &mut HashSet<VarId>,
    id: VarId,
    arity: usize,
) {
    match recfn.get(&id) {
        Some(prev) if *prev != arity => {
            conflicts.insert(id);
        }
        _ => {
            recfn.insert(id, arity);
        }
    }
}

/// A pure pre-order visitor with nothing to do after a child, so it needs no
/// `Post` step: every arm records its binders and then pushes its children in
/// REVERSE, which pops them in source order.
fn scan(
    expr: &PseudoExpr,
    recfn: &mut HashMap<VarId, usize>,
    conflicts: &mut HashSet<VarId>,
    other: &mut HashSet<VarId>,
) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr {
            PseudoExpr::RecFn { name, params, body } => {
                record_recfn(recfn, conflicts, name.id, params.len());
                for p in params {
                    other.insert(p.id);
                }
                stack.push(body);
            }
            PseudoExpr::Lambda { params, body } => {
                for p in params {
                    other.insert(p.id);
                }
                stack.push(body);
            }
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                if let (Some(vid), PseudoExpr::RecFn { params, .. }) = (id, value.as_ref()) {
                    record_recfn(recfn, conflicts, *vid, params.len());
                } else if let Some(vid) = id {
                    other.insert(*vid);
                }
                stack.push(body);
                stack.push(value);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                // Record each clause's pattern binders before descending
                // into that clause. Nothing in this walk ever READS `other`
                // (the poison sets are consumed only after it finishes), so
                // recording them all up front here is the same computation.
                for clause in clauses {
                    for b in pattern_binders(&clause.pattern) {
                        other.insert(b);
                    }
                }
                for clause in clauses.iter().rev() {
                    stack.push(&clause.body);
                    if let Some(g) = &clause.guard {
                        stack.push(g);
                    }
                }
                stack.push(subject);
            }
            _ => {
                for child in expr_children(expr).into_iter().rev() {
                    stack.push(child);
                }
            }
        }
    }
}

fn pattern_binders(pattern: &WhenPattern) -> Vec<VarId> {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields.iter().map(|b| b.id).collect(),
        WhenPattern::List { elements, tail } => {
            elements.iter().chain(tail.iter()).map(|b| b.id).collect()
        }
        WhenPattern::Tuple(items) => items.iter().map(|b| b.id).collect(),
        WhenPattern::Pair(a, b) => vec![a.id, b.id],
        WhenPattern::Var(b) => vec![b.id],
        WhenPattern::Wildcard | WhenPattern::Literal(_) => Vec::new(),
    }
}

/// Direct (non-binding, non-when, non-lambda/recfn/let) children — for the
/// fall-through arm of `scan`. The structured arms above own
/// binder-introducing nodes.
fn expr_children(expr: &PseudoExpr) -> Vec<&PseudoExpr> {
    match expr {
        PseudoExpr::Apply { function, args } => {
            let mut c = vec![function.as_ref()];
            c.extend(args.iter());
            c
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => vec![condition, then_branch, else_branch],
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

/// Is `expr` a PROVABLE partial application of a rec fn — i.e. an `Apply`
/// spine `f(a1)(a2)…` whose head is `Var{id}` with a non-poisoned recorded
/// arity `n`, supplying `k` args with `1 <= k < n`? Such a value is a
/// lambda awaiting the remaining params — a function VALUE, so a wrapping
/// `Force`/zero-arg-apply is a no-op. Fail-closed: head not a Var, id None,
/// poisoned/unknown arity, `k == 0`, or `k >= n` → false.
fn is_provable_partial_recfn_apply(expr: &PseudoExpr, arities: &RecFnArities) -> bool {
    let mut supplied = 0usize;
    let mut cur = expr;
    loop {
        match cur {
            PseudoExpr::Apply { function, args } => {
                supplied += args.len();
                cur = function;
            }
            PseudoExpr::Var { id: Some(id), .. } => {
                return matches!(arities.get(id), Some(Some(n)) if supplied >= 1 && supplied < *n);
            }
            _ => return false,
        }
    }
}

/// True iff `Apply { function: e, args: [] }` should unwrap to `e`.
/// Only clearly non-callable shapes qualify: `Var`, `BuiltinCall`,
/// `FieldAccess`, nested `Apply` and `Constr` could legitimately
/// carry a 0-arity call; `When`, `If`, `Trace`, `Let` and a
/// parameterised `Lambda` cannot.
///
/// `fn(x){body}()` is a UPLC-level type error — a 1+-arg function
/// called with 0 args fails before the body runs. Such sites appear
/// in V1 scripts as wildcard when-branches: a
/// `force(delay(lambda))` whose `force` an upstream simplifier left
/// behind, which the pretty-printer renders as `()`. Treating the
/// empty apply as a no-op leaves a bare function value, valid surface syntax
/// for a when-arm result.
///
/// `RecFn` excluded — a top-level rec-fn used with trailing `()`
/// could legitimately be a forced thunk emitted upstream.
fn is_unwrappable(expr: &PseudoExpr) -> bool {
    match expr {
        PseudoExpr::When { .. }
        | PseudoExpr::If { .. }
        | PseudoExpr::Trace { .. }
        | PseudoExpr::Let { .. } => true,
        // `fn(){body}()` is a legitimate 0-arity thunk; preserve it.
        // `fn(<≥1 args>){body}()` is an arity error (body never
        // runs), so unwrap to a bare function value.
        PseudoExpr::Lambda { params, .. } => !params.is_empty(),
        _ => false,
    }
}

#[cfg(test)]
mod tests;
