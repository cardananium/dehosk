//! Drop the Z-combinator's dead identity self-receiver.
//!
//! V1/V2 recursion decodes to a `rec fn` with an unused leading slot
//! that every call fills with `fn d(x) { x }`. Identity into a dead
//! slot is a no-op, but two existing passes bounce off that extra arg:
//! - `flatten_recfn_unused_self` sees `self(d)` as under-applied, and
//!   cannot rewrite the external `n(d)` site.
//! - `clarify_rec_self_value_use` wants a bare `Var(self)`, not
//!   `Apply(Var(self), [d])`.
//!
//! When the dead slot is the only extra param, the body is a single
//! inner lambda, and every `self`/`alias` use applies a pure identity
//! first, drop the slot and rewrite `f(d, …)` → `f(…)` / `f(d)` → `f`.
//! Follow-up flatten and clarify then fire.
//!
//! Soundness: the slot is unused and every filler is a CBV value
//! (closed identity or a ref to one), so `(λs. M) v ≡ M`. All-or-nothing
//! per binding — any bare use or non-identity first arg leaves the
//! tree unchanged.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{
    PlainPost, children, plain_children, rebuild_plain, rewrite_bottom_up, take,
};

pub(super) fn collapse_identity_self_receiver(expr: PseudoExpr) -> PseudoExpr {
    let identity_ids = collect_identity_helper_ids(&expr);
    rewrite(expr, &identity_ids)
}

/// BOTTOM-UP, so a nested binding collapses before its parent — which is
/// exactly where [`rewrite_bottom_up`] calls back. `try_collapse` fires at
/// most once per node: its result is not fed back through the walk.
fn rewrite(expr: PseudoExpr, identity_ids: &HashSet<VarId>) -> PseudoExpr {
    rewrite_bottom_up(expr, |c| try_collapse(c, identity_ids))
}

fn try_collapse(expr: PseudoExpr, identity_ids: &HashSet<VarId>) -> PseudoExpr {
    let PseudoExpr::Let {
        name,
        id: Some(alias_id),
        value,
        body,
    } = expr
    else {
        return expr;
    };
    // Only a direct `rec fn` value binds the self-receiver and exposes
    // both call-site scopes: rec-fn body for self refs, let body for
    // external refs.
    let value = value.into_inner();
    let PseudoExpr::RecFn {
        name: self_binder,
        params,
        body: rec_body,
    } = value
    else {
        // Not a rec-fn binding — reconstruct unchanged.
        return PseudoExpr::Let {
            name,
            id: Some(alias_id),
            value: PBox::new(value),
            body,
        };
    };

    let reconstruct = |params, rec_body: PBox, body: PBox| PseudoExpr::Let {
        name: name.clone(),
        id: Some(alias_id),
        value: PBox::new(PseudoExpr::RecFn {
            name: self_binder.clone(),
            params,
            body: rec_body,
        }),
        body,
    };

    // Guard 1: exactly one leading param (the dead self-receiver slot),
    // and it is dead in the body. (`contains_var_id` traverses literal
    // patterns too, so a slot use hidden there still blocks the fire.)
    if params.len() != 1 {
        return reconstruct(params, rec_body, body);
    }
    let slot_id = params[0].id;
    if contains_var_id(&rec_body, slot_id) {
        return reconstruct(params, rec_body, body);
    }

    // Guard 2: the rec-fn body must be exactly one inner `Lambda` (the
    // real N-arg function) — the Z-combinator's curried shape, and what
    // `flatten_recfn_unused_self` lifts once the slot is gone, so the
    // post-collapse flatten is provable. Its arity is the floor every
    // self-call must meet for flatten to accept it.
    let PseudoExpr::Lambda {
        params: inner_params,
        ..
    } = rec_body.as_ref()
    else {
        return reconstruct(params, rec_body, body);
    };
    let inner_arity = inner_params.len();
    if inner_arity == 0 {
        return reconstruct(params, rec_body, body);
    }

    let self_id = self_binder.id;
    // INTERNAL refs: only the rec-fn's own self id is repairable downstream
    // (clarify + flatten both key on `name.id`). If the alias id differs
    // and is used INSIDE the body, downstream can't repair it — bail.
    if alias_id != self_id && contains_var_id(&rec_body, alias_id) {
        return reconstruct(params, rec_body, body);
    }
    let self_targets: HashSet<VarId> = std::iter::once(self_id).collect();
    // EXTERNAL refs: both ids (covers `mark_closure_recursive` aliasing
    // them to the same VarId, or to distinct ones).
    let mut ext_targets: HashSet<VarId> = HashSet::new();
    ext_targets.insert(self_id);
    ext_targets.insert(alias_id);

    // Guard 3a (INTERNAL, strict): every self reference in the rec-fn
    // body must collapse to a self-call with ≥ `inner_arity` args, so
    // `flatten_recfn_unused_self` provably fires. Anything else bails to
    // the honestly-invalid output.
    if !internal_refs_collapsible(&rec_body, &self_targets, identity_ids, inner_arity) {
        return reconstruct(params, rec_body, body);
    }
    // Guard 3b (EXTERNAL, lenient): every reference in the let body must
    // be first-applied to a pure identity. Rest-empty is fine — the alias
    // becomes the post-slot function value, which flatten makes denote
    // the original `n(d)` result. A bare value-use would mis-bind after
    // the arity change.
    if !external_refs_collapsible(&body, &ext_targets, identity_ids) {
        return reconstruct(params, rec_body, body);
    }

    // Fire: drop the dead param and the identity arg in both scopes.
    let new_params = params[1..].to_vec();
    let new_rec_body = strip_identity_first_arg(rec_body.into_inner(), &self_targets, identity_ids);
    let new_body = strip_identity_first_arg(body.into_inner(), &ext_targets, identity_ids);
    PseudoExpr::Let {
        name,
        id: Some(alias_id),
        value: PBox::new(PseudoExpr::RecFn {
            name: self_binder,
            params: new_params,
            body: PBox::new(new_rec_body),
        }),
        body: PBox::new(new_body),
    }
}

/// Is `expr` a bare `Var` to one of `targets`?
fn is_target_var(expr: &PseudoExpr, targets: &HashSet<VarId>) -> bool {
    matches!(expr, PseudoExpr::Var { id: Some(v), .. } if targets.contains(v))
}

fn internal_refs_collapsible(
    expr: &PseudoExpr,
    targets: &HashSet<VarId>,
    identity_ids: &HashSet<VarId>,
    inner_arity: usize,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                match subject.as_ref() {
                    // Rest-empty self-subject `self(identity)`: clarify
                    // reverts it to a call with one arg per clause, so
                    // require `>= inner_arity` clauses. clarify also DROPS
                    // the `subject_name` binder, so a clause referencing it
                    // would dangle — allow only when it is absent or unused.
                    PseudoExpr::Apply { function, args }
                        if is_target_var(function, targets)
                            && args.len() == 1
                            && is_identity_arg(&args[0], identity_ids) =>
                    {
                        let subj_ok = clarify_rewritable_arm_count(clauses)
                            .is_some_and(|n| n >= inner_arity)
                            && subject_name.as_ref().is_none_or(|sn| {
                                !clauses.iter().any(|c| {
                                    contains_var_id(&c.body, sn.id)
                                        || c.guard
                                            .as_ref()
                                            .is_some_and(|g| contains_var_id(g, sn.id))
                                })
                            });
                        if !subj_ok {
                            return false;
                        }
                    }
                    // Any other self-applied subject can't be repaired into
                    // a bare-Var self-subject that clarify recognises — bail.
                    PseudoExpr::Apply { function, .. } if is_target_var(function, targets) => {
                        return false;
                    }
                    other => pending.push(other),
                }
                for c in clauses {
                    // A target ref hidden in a literal pattern can't be
                    // stripped by the map_children rewrite — bail if present.
                    if literal_pattern_expr(&c.pattern)
                        .is_some_and(|e| contains_any_target(e, targets))
                    {
                        return false;
                    }
                    if let Some(g) = &c.guard {
                        pending.push(g);
                    }
                    pending.push(&c.body);
                }
            }
            PseudoExpr::Apply { function, args } => {
                if is_target_var(function, targets) {
                    // Single-apply self-call `self(identity, real…)`. After
                    // stripping the identity it has `args.len() - 1` real
                    // args; require `>= inner_arity` so flatten accepts it.
                    if args
                        .first()
                        .is_some_and(|a| is_identity_arg(a, identity_ids))
                        && args.len() > inner_arity
                    {
                        pending.extend(args.iter());
                        continue;
                    }
                    return false;
                }
                // One-level curried self-call `self(identity)(real…)`: the
                // inner rest-empty self-ref is fine because the outer apply
                // supplies the real args. Strip leaves `self(real…)`;
                // require `>= inner_arity`.
                if let PseudoExpr::Apply {
                    function: inner_fn,
                    args: inner_args,
                } = function.as_ref()
                    && is_target_var(inner_fn, targets)
                {
                    if inner_args.len() == 1
                        && is_identity_arg(&inner_args[0], identity_ids)
                        && args.len() >= inner_arity
                    {
                        pending.extend(args.iter());
                        continue;
                    }
                    return false;
                }
                pending.push(function);
                pending.extend(args.iter());
            }
            PseudoExpr::Var { id: Some(v), .. } if targets.contains(v) => return false,
            other => pending.extend(children(other)),
        }
    }
    true
}

/// If `clauses` is exactly what `clarify_rec_self_value_use` rewrites — a
/// complete consecutive zero-field, no-guard constructor tag sequence
/// `0, 1, …, n-1` with `n >= 2` — return `n` (the rewritten call's arg
/// count). Mirrors `clarify_rec_self_value_use::try_extract_complete_tag_args`.
fn clarify_rewritable_arm_count(clauses: &[crate::pseudo::ast::WhenClause]) -> Option<usize> {
    let n = clauses.len();
    if n < 2 {
        return None;
    }
    let mut tags: Vec<usize> = Vec::with_capacity(n);
    for c in clauses {
        if c.guard.is_some() {
            return None;
        }
        let crate::pseudo::ast::WhenPattern::Constructor { tag, fields, .. } = &c.pattern else {
            return None;
        };
        if !fields.is_empty() {
            return None;
        }
        tags.push(*tag);
    }
    tags.sort_unstable();
    tags.dedup();
    if tags.len() != n {
        return None; // duplicate tag
    }
    if tags.iter().enumerate().all(|(i, &t)| t == i) {
        Some(n)
    } else {
        None
    }
}

/// EXTERNAL (let body), lenient. Every self/alias reference must be in
/// `Apply.function` position with a pure-identity first arg (rest-empty
/// ok — the alias becomes the post-slot function value). A bare
/// value-use, or a target ref inside a literal pattern => not collapsible.
fn external_refs_collapsible(
    expr: &PseudoExpr,
    targets: &HashSet<VarId>,
    identity_ids: &HashSet<VarId>,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Apply { function, args } => {
                if is_target_var(function, targets) {
                    if args.is_empty() || !is_identity_arg(&args[0], identity_ids) {
                        return false;
                    }
                    pending.extend(args.iter());
                    continue;
                }
                pending.push(function);
                pending.extend(args.iter());
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for c in clauses {
                    if literal_pattern_expr(&c.pattern)
                        .is_some_and(|e| contains_any_target(e, targets))
                    {
                        return false;
                    }
                    if let Some(g) = &c.guard {
                        pending.push(g);
                    }
                    pending.push(&c.body);
                }
            }
            PseudoExpr::Var { id: Some(v), .. } if targets.contains(v) => return false,
            other => pending.extend(children(other)),
        }
    }
    true
}

/// The inner expression of a `WhenPattern::Literal`, if any.
fn literal_pattern_expr(p: &crate::pseudo::ast::WhenPattern) -> Option<&PseudoExpr> {
    match p {
        crate::pseudo::ast::WhenPattern::Literal(e) => Some(e),
        _ => None,
    }
}

/// Does `expr` reference any of `targets` (traversing literal patterns)?
fn contains_any_target(expr: &PseudoExpr, targets: &HashSet<VarId>) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::Var { id: Some(v), .. } = current
            && targets.contains(v)
        {
            return true;
        }
        if let PseudoExpr::When { clauses, .. } = current {
            for c in clauses {
                if let Some(e) = literal_pattern_expr(&c.pattern) {
                    pending.push(e);
                }
            }
        }
        pending.extend(children(current));
    }
    false
}

/// One pending step of [`strip_identity_first_arg`]'s explicit stack.
enum StripStep {
    Enter(PseudoExpr),
    Post(StripPost),
}

enum StripPost {
    /// `Apply(Var(target), [identity, rest…])` — the identity arg has already
    /// been dropped, and `function` is the target `Var` UNTOUCHED: the
    /// recursion never re-stripped the head of this arm, so it must not be
    /// pushed as a child here either.
    TargetApply {
        function: PBox,
        rest_len: usize,
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

/// Rewrite every `Apply(Var(target), [identity, rest…])` to
/// `Apply(Var(target), [rest…])` — bare `Var(target)` if `rest` empty.
///
/// TOP-DOWN, and that matters: the target test looks at
/// the ORIGINAL `function`/`args[0]`, before either is stripped. Doing it
/// bottom-up would re-test an `Apply` whose head had just collapsed from
/// `self(identity)` to `Var(self)` and strip a second argument the walk
/// left alone. Children are pushed in REVERSE so they pop in source order.
fn strip_identity_first_arg(
    expr: PseudoExpr,
    targets: &HashSet<VarId>,
    identity_ids: &HashSet<VarId>,
) -> PseudoExpr {
    let mut steps: Vec<StripStep> = vec![StripStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            StripStep::Enter(expr) => match expr {
                PseudoExpr::Apply { function, args } => {
                    let is_target_with_identity = matches!(
                        function.as_ref(),
                        PseudoExpr::Var { id: Some(v), .. } if targets.contains(v)
                    ) && !args.is_empty()
                        && is_identity_arg(&args[0], identity_ids);
                    if is_target_with_identity {
                        let rest: Vec<PseudoExpr> = args.into_iter().skip(1).collect();
                        steps.push(StripStep::Post(StripPost::TargetApply {
                            function,
                            rest_len: rest.len(),
                        }));
                        for a in rest.into_iter().rev() {
                            steps.push(StripStep::Enter(a));
                        }
                    } else {
                        let argc = args.len();
                        steps.push(StripStep::Post(StripPost::Plain(PlainPost::Apply { argc })));
                        for a in args.into_vec().into_iter().rev() {
                            steps.push(StripStep::Enter(a));
                        }
                        steps.push(StripStep::Enter(function.into_inner()));
                    }
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(StripStep::Post(StripPost::Let { name, id }));
                    steps.push(StripStep::Enter(body.into_inner()));
                    steps.push(StripStep::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(StripStep::Post(StripPost::Lambda { params }));
                    steps.push(StripStep::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(StripStep::Post(StripPost::RecFn { name, params }));
                    steps.push(StripStep::Enter(body.into_inner()));
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
                    steps.push(StripStep::Post(StripPost::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(StripStep::Enter(c));
                    }
                    steps.push(StripStep::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(StripStep::Post(StripPost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(StripStep::Enter(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            StripStep::Post(post) => {
                let rebuilt = match post {
                    StripPost::TargetApply { function, rest_len } => {
                        let rest = take(&mut done, rest_len);
                        if rest.is_empty() {
                            function.into_inner()
                        } else {
                            PseudoExpr::Apply {
                                function,
                                args: rest.into(),
                            }
                        }
                    }
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
                    StripPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    StripPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
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

    debug_assert_eq!(
        done.len(),
        1,
        "strip_identity_first_arg must leave one result"
    );
    done.pop().expect("strip_identity_first_arg result")
}

fn contains_var_id(expr: &PseudoExpr, target: VarId) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if matches!(current, PseudoExpr::Var { id: Some(v), .. } if *v == target) {
            return true;
        }
        if let PseudoExpr::When { clauses, .. } = current {
            for c in clauses {
                if let Some(e) = literal_pattern_expr(&c.pattern) {
                    pending.push(e);
                }
            }
        }
        pending.extend(children(current));
    }
    false
}

/// Is `expr` a pure identity argument — an inline `fn(x){x}` or a `Var`
/// to a program-wide identity helper (matched by `VarId`)?
fn is_identity_arg(expr: &PseudoExpr, identity_ids: &HashSet<VarId>) -> bool {
    if is_identity_lambda(expr) {
        return true;
    }
    matches!(expr, PseudoExpr::Var { id: Some(v), .. } if identity_ids.contains(v))
}

/// Collect `VarId`s of every let-binding whose value is an identity
/// lambda `fn(p){p}`.
fn collect_identity_helper_ids(expr: &PseudoExpr) -> HashSet<VarId> {
    struct Collector {
        ids: HashSet<VarId>,
    }
    impl ExprVisitor for Collector {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, value: &PseudoExpr) {
            if let Some(vid) = id
                && is_identity_lambda(value)
            {
                self.ids.insert(*vid);
            }
        }
    }
    let mut c = Collector {
        ids: HashSet::new(),
    };
    c.walk(expr);
    c.ids
}

/// Is `expr` an identity Lambda `fn(x){x}`? Exactly one param, body a
/// `Var` whose id (or name, as fallback) matches the param.
fn is_identity_lambda(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let param = &params[0];
    let PseudoExpr::Var {
        name: body_name,
        id: body_id,
    } = body.as_ref()
    else {
        return false;
    };
    match body_id {
        Some(body_var_id) => *body_var_id == param.id,
        None => body_name == &param.name,
    }
}

#[cfg(test)]
mod tests;
