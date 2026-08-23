//! Relabel raw / mislabeled Option arguments at call sites whose callee
//! parameter is already consumed as Option — the argument dual of
//! `relabel_option_producer_leaves`.
//!
//! `Ok` and `Some` are the same `Constr` tag-0 arity-1, so the rename
//! is display-only. A nullary tag-1 `None` clause (`Constr 1 []`)
//! disproves Result (`Error` is unary), so the position is decidably
//! Option. Tag-faithful to the Plutus convention the consuming `when`
//! already carries.
//!
//! Fail-closed:
//! 1. A `Let`-bound `Lambda`/`RecFn` has a param `P` that is the subject
//!    of `when P is { Known(Some), Known(None) }`.
//! 2. That None witness is nullary — a unary tag-1 (genuine Result)
//!    is never recorded.
//! 3. The argument is tag-0 arity-1 (`Ok` / `Unknown`) → `Some`, or
//!    tag-1 arity-0 → `None`. Anything else is left alone.
//! 4. Call head peels to that exact fn `VarId`. Collided ids are dropped.
//!
//! Rewrites call-site argument values, never the callee body. A genuine
//! `Result` helper is never recorded. After
//! `relabel_option_producer_leaves`; both need `unfold_y_comb_helper_apply`.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

pub(super) fn relabel_option_consumer_args(expr: PseudoExpr) -> PseudoExpr {
    if !super::drop_dead_pure_lets::contains_decompiled_marker(&expr) {
        return expr;
    }
    let multiply_bound = collect_multiply_bound_ids(&expr);
    let consuming = collect_option_consuming_params(&expr, &multiply_bound);
    if consuming.is_empty() {
        return expr;
    }
    rewrite(expr, &consuming)
}

/// Argument that is `Constr` tag-0 arity-1 with shape `Known(Ok)` or raw
/// `Unknown`. `Known(Some)` is excluded so the pass is idempotent.
fn is_relabelable_some_arg(e: &PseudoExpr) -> bool {
    matches!(
        e,
        PseudoExpr::Constr {
            tag: 0,
            fields,
            shape: ConstructorShape::Known(KnownConstructor::Ok)
                | ConstructorShape::Unknown { .. },
            ..
        } if fields.len() == 1
    )
}

/// Argument value that is `Constr` tag-1 arity-0 (`Known(Error)` cannot be
/// this — `Error` is unary — so only raw `Unknown` nullary tag-1 qualifies).
fn is_relabelable_none_arg(e: &PseudoExpr) -> bool {
    matches!(
        e,
        PseudoExpr::Constr {
            tag: 1,
            fields,
            shape: ConstructorShape::Unknown { .. },
            ..
        } if fields.is_empty()
    )
}

/// Every binder id that appears more than once program-wide (VarId
/// collisions). Fn identities in this set are never used as relabel keys.
fn collect_multiply_bound_ids(expr: &PseudoExpr) -> HashSet<VarId> {
    use crate::pseudo::fold::ExprVisitor;
    struct Scan {
        counts: HashMap<VarId, usize>,
    }
    impl ExprVisitor for Scan {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, _value: &PseudoExpr) {
            if let Some(vid) = id {
                *self.counts.entry(*vid).or_insert(0) += 1;
            }
        }
        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for p in params {
                *self.counts.entry(p.var_id()).or_insert(0) += 1;
            }
        }
        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            *self.counts.entry(name.var_id()).or_insert(0) += 1;
            for p in params {
                *self.counts.entry(p.var_id()).or_insert(0) += 1;
            }
        }
        fn visit_when_clause_pre(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            if let Some(b) = subject_name {
                *self.counts.entry(b.var_id()).or_insert(0) += 1;
            }
            for id in clause.pattern.bound_ids() {
                *self.counts.entry(id).or_insert(0) += 1;
            }
        }
    }
    let mut scan = Scan {
        counts: HashMap::new(),
    };
    scan.walk(expr);
    scan.counts
        .into_iter()
        .filter(|(_, c)| *c > 1)
        .map(|(id, _)| id)
        .collect()
}

/// Map of fn-identity VarId → the parameter indices consumed as Option in
/// that fn's body: the body matches `when Var(param) is { … }` with BOTH a
/// `Known(Some)` and a `Known(None)` clause — the nullary tag-1 witness
/// that proves Option over Result. Colliding fn identities are skipped.
///
/// For a `Let`-bound `RecFn` both the Let binder id and the RecFn `name`
/// id map to the same param set, so an external call and a surviving
/// self-reference resolve alike.
fn collect_option_consuming_params(
    expr: &PseudoExpr,
    multiply_bound: &HashSet<VarId>,
) -> HashMap<VarId, HashSet<usize>> {
    let mut out: HashMap<VarId, HashSet<usize>> = HashMap::new();
    collect_at(expr, multiply_bound, &mut out);
    out
}

fn collect_at(
    expr: &PseudoExpr,
    multiply_bound: &HashSet<VarId>,
    out: &mut HashMap<VarId, HashSet<usize>>,
) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if let PseudoExpr::Let {
            id: Some(fid),
            value,
            ..
        } = expr
        {
            let fn_shape = match value.as_ref() {
                PseudoExpr::Lambda { params, body } => Some((*fid, None, params, body.as_ref())),
                PseudoExpr::RecFn { name, params, body } => {
                    Some((*fid, Some(name.var_id()), params, body.as_ref()))
                }
                _ => None,
            };
            if let Some((let_id, recfn_name_id, params, fn_body)) = fn_shape {
                let option_indices = option_consuming_param_indices(fn_body, params);
                if !option_indices.is_empty() {
                    // Register under the Let id (external call identity) and,
                    // for a RecFn, its self-name id — unless either collides.
                    if !multiply_bound.contains(&let_id) {
                        out.entry(let_id)
                            .or_default()
                            .extend(option_indices.iter().copied());
                    }
                    if let Some(name_id) = recfn_name_id {
                        if !multiply_bound.contains(&name_id) {
                            out.entry(name_id)
                                .or_default()
                                .extend(option_indices.iter().copied());
                        }
                    }
                }
            }
        }
        for child in super::scope_recurse::children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// Indices of `params` whose binder is the subject of a `when` anywhere in
/// `body` with both a native `Known(Some)` and a `Known(None)` clause.
fn option_consuming_param_indices(body: &PseudoExpr, params: &[Binder]) -> HashSet<usize> {
    let param_index: HashMap<VarId, usize> = params
        .iter()
        .enumerate()
        .map(|(i, p)| (p.var_id(), i))
        .collect();
    let mut hits: HashSet<usize> = HashSet::new();
    scan_option_whens(body, &param_index, &mut hits);
    hits
}

fn scan_option_whens(
    expr: &PseudoExpr,
    param_index: &HashMap<VarId, usize>,
    hits: &mut HashSet<usize>,
) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = expr
        {
            if let PseudoExpr::Var { id: Some(vid), .. } = subject.as_ref() {
                if let Some(idx) = param_index.get(vid) {
                    let has_some = clauses
                        .iter()
                        .any(|c| is_known_pattern(&c.pattern, KnownConstructor::Some));
                    let has_none = clauses
                        .iter()
                        .any(|c| is_known_pattern(&c.pattern, KnownConstructor::None));
                    if has_some && has_none {
                        hits.insert(*idx);
                    }
                }
            }
        }
        for child in super::scope_recurse::children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

fn is_known_pattern(pattern: &WhenPattern, kc: KnownConstructor) -> bool {
    matches!(
        pattern,
        WhenPattern::Constructor {
            shape: ConstructorShape::Known(k),
            ..
        } if *k == kc
    )
}

fn apply_head_and_args(
    function: &PseudoExpr,
    args: &[PseudoExpr],
) -> Option<(VarId, Vec<PseudoExpr>)> {
    let mut levels: Vec<&[PseudoExpr]> = vec![args];
    let mut current = function;
    let head_vid = loop {
        match current {
            PseudoExpr::Var { id: Some(vid), .. } => break *vid,
            PseudoExpr::Apply {
                function: inner_fn,
                args: inner_args,
            } => {
                levels.push(inner_args);
                current = inner_fn;
            }
            _ => return None,
        }
    };
    let mut acc: Vec<PseudoExpr> = Vec::new();
    for level in levels.into_iter().rev() {
        acc.extend(level.iter().cloned());
    }
    Some((head_vid, acc))
}

/// `rebuild_apply_with_relabel` is the [`RwPost::RelabelApply`] step: the
/// spine peel is itself a walk, so all that moves is the per-argument
/// `rewrite` — the head and then the flattened arguments (innermost
/// application first, left to right) become ordinary child jobs, and the
/// relabel-per-index runs on them at reassembly.
fn rewrite(expr: PseudoExpr, consuming: &HashMap<VarId, HashSet<usize>>) -> PseudoExpr {
    let mut steps: Vec<RwStep> = vec![RwStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RwStep::Visit(expr) => {
                // An `Apply` whose (possibly curried) head is a recorded fn
                // identity: relabel its Option-consuming argument slots
                // rather than folding it as a plain node.
                let relabel_head = match &expr {
                    PseudoExpr::Apply { function, args } => {
                        apply_head_and_args(function, args).map(|(head, _flat_args)| head)
                    }
                    _ => None,
                }
                .filter(|head| consuming.contains_key(head));
                if let Some(head) = relabel_head {
                    let mut spine: Vec<Vec<PseudoExpr>> = Vec::new();
                    let mut current = expr;
                    let head_expr = loop {
                        match current {
                            PseudoExpr::Apply { function, args } => {
                                spine.push(args.into_vec());
                                current = function.into_inner();
                            }
                            other => break other,
                        }
                    };
                    // `levels` is innermost-application-first, 's `for args in
                    // levels.into_iter().rev()`, so a slot's FLATTENED absolute index
                    // is recoverable.
                    let mut levels: Vec<usize> = Vec::with_capacity(spine.len());
                    let mut children: Vec<PseudoExpr> = Vec::new();
                    for args in spine.into_iter().rev() {
                        levels.push(args.len());
                        children.extend(args);
                    }
                    steps.push(RwStep::Post(RwPost::RelabelApply { head, levels }));
                    // Reversed so they pop in source order, the head first.
                    for c in children.into_iter().rev() {
                        steps.push(RwStep::Visit(c));
                    }
                    steps.push(RwStep::Visit(head_expr));
                    continue;
                }
                // Otherwise: `map_children`'s traversal, node kind by kind.
                match expr {
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        steps.push(RwStep::Post(RwPost::Let { name, id }));
                        steps.push(RwStep::Visit(body.into_inner()));
                        steps.push(RwStep::Visit(value.into_inner()));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        steps.push(RwStep::Post(RwPost::Lambda { params }));
                        steps.push(RwStep::Visit(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        steps.push(RwStep::Post(RwPost::RecFn { name, params }));
                        steps.push(RwStep::Visit(body.into_inner()));
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
                        steps.push(RwStep::Post(RwPost::When {
                            subject_name,
                            clause_meta,
                        }));
                        for c in clause_children.into_iter().rev() {
                            steps.push(RwStep::Visit(c));
                        }
                        steps.push(RwStep::Visit(subject.into_inner()));
                    }
                    other => match super::scope_recurse::plain_children(other) {
                        Ok((kind, children)) => {
                            steps.push(RwStep::Post(RwPost::Plain(kind)));
                            for c in children.into_iter().rev() {
                                steps.push(RwStep::Visit(c));
                            }
                        }
                        Err(leaf) => done.push(leaf),
                    },
                }
            }
            RwStep::Post(post) => {
                let rebuilt = match post {
                    RwPost::RelabelApply { head, levels } => {
                        let total = 1 + levels.iter().sum::<usize>();
                        let mut parts = super::scope_recurse::take(&mut done, total).into_iter();
                        let empty = HashSet::new();
                        let indices = consuming.get(&head).unwrap_or(&empty);
                        // The already-rewritten non-`Apply` head.
                        let mut result = parts.next().expect("apply head");
                        let mut acc = 0usize;
                        for count in levels {
                            let mut new_args = Vec::with_capacity(count);
                            for i in 0..count {
                                let abs = acc + i;
                                // Already recursed; relabel per index.
                                let recursed = parts.next().expect("apply arg");
                                let relabeled = if indices.contains(&abs) {
                                    relabel_option_arg(recursed)
                                } else {
                                    recursed
                                };
                                new_args.push(relabeled);
                            }
                            acc += new_args.len();
                            result = PseudoExpr::Apply {
                                function: PBox::new(result),
                                args: new_args.into(),
                            };
                        }
                        result
                    }
                    RwPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    RwPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    RwPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    RwPost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = super::scope_recurse::take(&mut done, total).into_iter();
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
                    RwPost::Plain(kind) => super::scope_recurse::rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

/// A job on [`rewrite`]'s stack. `RelabelApply` is the old
/// `rebuild_apply_with_relabel`: `levels` records how many arguments each
/// application level of the peeled spine contributed, innermost first, so the
/// flattened index each argument is relabelled at is recoverable.
enum RwStep {
    Visit(PseudoExpr),
    Post(RwPost),
}

enum RwPost {
    RelabelApply {
        head: VarId,
        levels: Vec<usize>,
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
    Plain(super::scope_recurse::PlainPost),
}

/// Display-only relabel of a gate-3 argument leaf: `Constr` tag-0 arity-1 →
/// `Some(payload)`, nullary `Constr` tag-1 → `None`. Anything else untouched.
fn relabel_option_arg(arg: PseudoExpr) -> PseudoExpr {
    if is_relabelable_some_arg(&arg) {
        let PseudoExpr::Constr { fields, .. } = arg else {
            unreachable!("shape checked");
        };
        PseudoExpr::constr_known(KnownConstructor::Some, fields.into_vec())
    } else if is_relabelable_none_arg(&arg) {
        PseudoExpr::constr_known(KnownConstructor::None, Vec::new())
    } else {
        arg
    }
}

#[cfg(test)]
mod tests;
