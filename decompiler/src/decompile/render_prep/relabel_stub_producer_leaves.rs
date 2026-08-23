//! Witness-gated producer-side unification of a stub-sum recovery — the
//! multi-variant generalization of [`super::relabel_option_producer_leaves`].
//!
//! The Option pass fixes the two-variant `Some`/`None` split; the same
//! defect occurs for an arbitrary stub sum (`Unknown_S_N`, 2+ variants, ≥1
//! field-bearing). Producer tails can mix `Nil` (list-nil recovery of raw
//! `Constr<0>`), `None` (Option recovery of raw `Constr<1>`), and an
//! arity-bucket stub (`Unknown_E_3_2` of raw `Constr<2>`) while the
//! exclusive consumer matches all three as one stub sum. `Nil`/`None` are
//! mislabels — the tag2-with-3-fields sibling disproves both List and
//! Option. Revert those leaves to raw `Constr<tag>` (Unknown shape, real
//! tag + arity) so the stub-ADT collector groups them under the consumer's
//! scrutinee class; [`super::stub_adt::attribute_producer_leaf_fns`]
//! attributes the leaf `Constr`s to that sum instead of the arity bucket.
//!
//! A producer fn is only touched when its result flows exclusively into
//! one `when Var(S) is { … }` whose clause patterns are the raw-Constr
//! stub sum. Exclusivity = `S` bound exactly once and referenced exactly
//! once (that when's subject), reached from `S`'s binding through a chain
//! of `if`/`let`/single-call hops. The target sum must have ≥2 distinct
//! tags with ≥1 field-bearing variant: a single nullary variant is
//! Bool/Void territory, and a genuine Option/List consumer presents
//! `Known(Some/None/Nil)` patterns rather than raw `Constr`. A leaf is
//! re-tagged only when its raw tag/arity matches a declared consumer
//! variant; a nullary `Known` leaf whose canonical tag is not in the
//! variant map is left alone. Genuine `None`s of other Option-typed
//! values live in fns with no flow into this `when`, so they are never
//! reached. Semantics never change: a `Constr<t>` is the same Plutus datum however it is displayed.

use crate::pseudo::ast::PBox;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

/// One producer→consumer stub-sum witness: the producer fn binders whose
/// return leaves flow exclusively into `when Var(scrutinee)`, plus the
/// consumer's declared variant map (`tag → arity`).
#[derive(Debug, Clone)]
pub(crate) struct StubProducerWitness {
    /// The `when` subject's VarId — the scrutinee class the producer
    /// leaves must join.
    pub scrutinee: VarId,
    /// Fn binder VarIds along the producer chain (e.g. `f_14`, `f_13`)
    /// whose bodies carry the return leaves.
    pub producer_fns: BTreeSet<VarId>,
    /// Consumer-declared variants: `tag → arity` (from the raw-Constr
    /// clause patterns).
    pub variants: BTreeMap<usize, usize>,
}

/// Depth cap on the single-call producer chain follow; fences
/// pathological cycles the unique-binding invariant already precludes.
const CHAIN_DEPTH_CAP: usize = 8;

/// Analyse `expr` for stub-sum producer/consumer splits and return one
/// [`StubProducerWitness`] per exclusive-flow site. Shared by this pass
/// (leaf relabel) and [`super::stub_adt`] (scrutinee attribution) so the
/// two never diverge.
pub(crate) fn collect_stub_producer_witnesses(expr: &PseudoExpr) -> Vec<StubProducerWitness> {
    let bindings = collect_unique_bindings(expr);
    let ref_counts = collect_var_ref_counts(expr);
    let mut out = Vec::new();
    collect_witnesses(expr, &bindings, &ref_counts, &mut out);
    out
}

/// Entry point for the leaf-relabel pass.
pub(crate) fn relabel_stub_producer_leaves(expr: PseudoExpr) -> PseudoExpr {
    if !super::drop_dead_pure_lets::contains_decompiled_marker(&expr) {
        return expr;
    }
    let witnesses = collect_stub_producer_witnesses(&expr);
    if witnesses.is_empty() {
        return expr;
    }
    // producer-fn VarId → the consumer variant map that governs its leaves.
    let mut fn_variants: HashMap<VarId, BTreeMap<usize, usize>> = HashMap::new();
    for w in &witnesses {
        for f in &w.producer_fns {
            // A producer fn feeding two distinct scrutinees with
            // conflicting variant maps is ambiguous — fail closed by
            // emptying its variant map, dropping it from the relabel set.
            match fn_variants.get(f) {
                Some(existing) if *existing != w.variants => {
                    fn_variants.insert(*f, BTreeMap::new());
                }
                Some(_) => {}
                None => {
                    fn_variants.insert(*f, w.variants.clone());
                }
            }
        }
    }
    rewrite(expr, &fn_variants)
}

/// Rewrite pass: at each `let F = <fn>` where `F` is a witnessed producer
/// fn, relabel that fn value's RETURN LEAVES to raw `Constr<tag>` matching
/// the consumer variant map.
///
/// The `Let` value's leaf relabel runs on the `Visit` arm, before descending
/// into the two children.
fn rewrite(expr: PseudoExpr, fn_variants: &HashMap<VarId, BTreeMap<usize, usize>>) -> PseudoExpr {
    let mut steps: Vec<RwStep> = vec![RwStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RwStep::Visit(expr) => match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    let value = match id {
                        Some(vid) if fn_variants.get(&vid).is_some_and(|v| !v.is_empty()) => {
                            let variants = &fn_variants[&vid];
                            relabel_fn_leaves(value.into_inner(), variants)
                        }
                        _ => value.into_inner(),
                    };
                    steps.push(RwStep::Post(RwPost::Let { name, id }));
                    steps.push(RwStep::Visit(body.into_inner()));
                    steps.push(RwStep::Visit(value));
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
                    // Reversed so they pop in source order.
                    for c in clause_children.into_iter().rev() {
                        steps.push(RwStep::Visit(c));
                    }
                    steps.push(RwStep::Visit(subject.into_inner()));
                }
                // `map_children`'s remaining (non-binding) variants.
                other => match super::scope_recurse::plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RwStep::Post(RwPost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(RwStep::Visit(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            RwStep::Post(post) => {
                let rebuilt = match post {
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

/// A job on [`rewrite`]'s stack.
enum RwStep {
    Visit(PseudoExpr),
    Post(RwPost),
}

enum RwPost {
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

/// Relabel the RETURN LEAVES of a producer fn value. The value is a
/// `Lambda`/`RecFn` (possibly curried); descend to its body's leaves.
fn relabel_fn_leaves(expr: PseudoExpr, variants: &BTreeMap<usize, usize>) -> PseudoExpr {
    match expr {
        PseudoExpr::Lambda { params, body } => PseudoExpr::Lambda {
            params,
            body: PBox::new(relabel_leaves(body.into_inner(), variants)),
        },
        PseudoExpr::RecFn { name, params, body } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(relabel_leaves(body.into_inner(), variants)),
        },
        // Non-fn value (shouldn't happen for a producer-fn binder) — leave.
        other => other,
    }
}

/// Walk return-leaf positions, relabelling each qualifying leaf.
///
/// Only LEAF positions are descended into, so each `Post` variant carries the
/// non-leaf parts of its node (a `let` value, an `if` condition, a clause
/// guard) verbatim rather than rebuilding them from `done`.
fn relabel_leaves(expr: PseudoExpr, variants: &BTreeMap<usize, usize>) -> PseudoExpr {
    let mut steps: Vec<LeafStep> = vec![LeafStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            LeafStep::Visit(expr) => match expr {
                // Known nullary constructor (Nil = Constr<0>, None = Constr<1>, …)
                // whose canonical tag is a nullary consumer variant → revert to raw
                // Constr so the collector stubs it under the scrutinee class.
                PseudoExpr::Constr {
                    shape: ConstructorShape::Known(kc),
                    fields,
                    ..
                } if fields.is_empty() && variants.get(&kc.expected_tag()) == Some(&0) => {
                    done.push(raw_constr(kc.expected_tag(), Vec::new()))
                }
                // Every other `Constr` leaf is left alone: raw ones the collector
                // already stubs, and `Known` leaves outside the variant map.
                e @ PseudoExpr::Constr { .. } => done.push(e),
                // Leaf-position structural descent (mirrors the Option pass).
                PseudoExpr::Lambda { params, body } => {
                    steps.push(LeafStep::Post(LeafPost::Lambda { params }));
                    steps.push(LeafStep::Visit(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(LeafStep::Post(LeafPost::RecFn { name, params }));
                    steps.push(LeafStep::Visit(body.into_inner()));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(LeafStep::Post(LeafPost::Let { name, id, value }));
                    steps.push(LeafStep::Visit(body.into_inner()));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(LeafStep::Post(LeafPost::If { condition }));
                    // Reversed so they pop in source order.
                    steps.push(LeafStep::Visit(else_branch.into_inner()));
                    steps.push(LeafStep::Visit(then_branch.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut bodies = Vec::with_capacity(clauses.len());
                    for c in clauses {
                        clause_meta.push((c.pattern, c.guard));
                        bodies.push(c.body);
                    }
                    steps.push(LeafStep::Post(LeafPost::When {
                        subject,
                        subject_name,
                        clause_meta,
                    }));
                    for b in bodies.into_iter().rev() {
                        steps.push(LeafStep::Visit(b));
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(LeafStep::Post(LeafPost::Trace { message }));
                    steps.push(LeafStep::Visit(value.into_inner()));
                }
                other => done.push(other),
            },
            LeafStep::Post(post) => {
                let rebuilt = match post {
                    LeafPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    LeafPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    LeafPost::Let { name, id, value } => PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body: PBox::new(done.pop().expect("let body")),
                    },
                    LeafPost::If { condition } => {
                        let else_branch = done.pop().expect("if else");
                        let then_branch = done.pop().expect("if then");
                        PseudoExpr::If {
                            condition,
                            then_branch: PBox::new(then_branch),
                            else_branch: PBox::new(else_branch),
                        }
                    }
                    LeafPost::When {
                        subject,
                        subject_name,
                        clause_meta,
                    } => {
                        let mut parts =
                            super::scope_recurse::take(&mut done, clause_meta.len()).into_iter();
                        PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses: clause_meta
                                .into_iter()
                                .map(|(pattern, guard)| WhenClause {
                                    pattern,
                                    guard,
                                    body: parts.next().expect("when clause body"),
                                })
                                .collect(),
                        }
                    }
                    LeafPost::Trace { message } => PseudoExpr::Trace {
                        message,
                        value: PBox::new(done.pop().expect("trace value")),
                    },
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "relabel_leaves must leave one result");
    done.pop().expect("relabel_leaves result")
}

/// A job on [`relabel_leaves`]'s stack.
enum LeafStep {
    Visit(PseudoExpr),
    Post(LeafPost),
}

enum LeafPost {
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    /// The `let` VALUE is not a leaf position — carried through untouched.
    Let {
        name: String,
        id: Option<VarId>,
        value: PBox,
    },
    /// Same for an `if` CONDITION.
    If {
        condition: PBox,
    },
    /// Same for a `when` SUBJECT and each clause GUARD.
    When {
        subject: PBox,
        subject_name: Option<Binder>,
        clause_meta: Vec<(WhenPattern, Option<PseudoExpr>)>,
    },
    /// Same for a `trace` MESSAGE.
    Trace {
        message: PBox,
    },
}

fn raw_constr(tag: usize, fields: Vec<PseudoExpr>) -> PseudoExpr {
    let arity = fields.len();
    PseudoExpr::Constr {
        type_hint: None,
        tag,
        fields: fields.into(),
        shape: ConstructorShape::unknown_data(tag, arity),
    }
}

// ===================== witness analysis (shared) =====================

/// Every `Let` binder id bound exactly once program-wide → its value.
/// Multiply-bound ids (VarId collisions) are dropped.
fn collect_unique_bindings(expr: &PseudoExpr) -> HashMap<VarId, PseudoExpr> {
    struct Scan {
        values: HashMap<VarId, PseudoExpr>,
        counts: HashMap<VarId, usize>,
    }
    impl ExprVisitor for Scan {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, value: &PseudoExpr) {
            if let Some(vid) = id {
                *self.counts.entry(*vid).or_insert(0) += 1;
                self.values.insert(*vid, value.clone());
            }
        }
    }
    let mut scan = Scan {
        values: HashMap::new(),
        counts: HashMap::new(),
    };
    scan.walk(expr);
    scan.values
        .into_iter()
        .filter(|(id, _)| scan.counts.get(id) == Some(&1))
        .collect()
}

/// Count `Var` reference occurrences per VarId (uses only, not bindings).
fn collect_var_ref_counts(expr: &PseudoExpr) -> HashMap<VarId, usize> {
    struct Scan {
        counts: HashMap<VarId, usize>,
    }
    impl ExprVisitor for Scan {
        fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
            if let Some(vid) = id {
                *self.counts.entry(*vid).or_insert(0) += 1;
            }
        }
    }
    let mut scan = Scan {
        counts: HashMap::new(),
    };
    scan.walk(expr);
    scan.counts
}

fn collect_witnesses<'a>(
    expr: &'a PseudoExpr,
    bindings: &'a HashMap<VarId, PseudoExpr>,
    ref_counts: &HashMap<VarId, usize>,
    out: &mut Vec<StubProducerWitness>,
) {
    let mut stack: Vec<&'a PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = expr
            && let Some(scrutinee) = subject_head_var(subject)
            && ref_counts.get(&scrutinee) == Some(&1)
            && bindings.contains_key(&scrutinee)
            && let Some(variants) = raw_stub_sum_variants(clauses)
        {
            let mut producer_fns = BTreeSet::new();
            // Count how many call sites of each producer fn the chain-follow
            // visits; a fn referenced more often than that escapes the chain.
            let mut in_chain_calls: HashMap<VarId, usize> = HashMap::new();
            follow_producer_chain(
                &bindings[&scrutinee],
                bindings,
                &mut producer_fns,
                &mut in_chain_calls,
                0,
            );
            // PRODUCER-EXCLUSIVITY (fail-closed): a producer fn whose GLOBAL
            // ref count exceeds the calls reachable inside this chain also
            // feeds some OTHER consumer — reverting its Nil/None leaves would
            // corrupt that consumer. Drop the whole witness in that case.
            let producer_exclusive = producer_fns.iter().all(|f| {
                let global = ref_counts.get(f).copied().unwrap_or(0);
                let in_chain = in_chain_calls.get(f).copied().unwrap_or(0);
                global == in_chain && global >= 1
            });
            if !producer_fns.is_empty() && producer_exclusive {
                out.push(StubProducerWitness {
                    scrutinee,
                    producer_fns,
                    variants,
                });
            }
        }
        for child in super::scope_recurse::children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// Peel the subject's Apply spine to its head `Var` id (a curried producer
/// call passes extra args). Returns `None` for non-Var heads.
fn subject_head_var(subject: &PseudoExpr) -> Option<VarId> {
    let mut cur = subject;
    loop {
        match cur {
            PseudoExpr::Var { id: Some(vid), .. } => return Some(*vid),
            PseudoExpr::Apply { function, .. } => cur = function,
            _ => return None,
        }
    }
}

/// If every clause pattern is a raw (`Unknown`, hint-less) `Constructor`
/// pattern and together they form a stub sum with ≥2 distinct tags and ≥1
/// field-bearing variant, return `tag → arity`. Else `None` (fail closed:
/// any `Known`/`Var`/`Wildcard`/`List`/`Literal`/… clause disqualifies).
fn raw_stub_sum_variants(clauses: &[WhenClause]) -> Option<BTreeMap<usize, usize>> {
    let mut variants: BTreeMap<usize, usize> = BTreeMap::new();
    for clause in clauses {
        match &clause.pattern {
            WhenPattern::Constructor {
                type_hint: None,
                tag,
                fields,
                shape,
            } if matches!(shape, ConstructorShape::Unknown { .. }) => {
                // Conflicting arity for a repeated tag → not a clean sum.
                if let Some(prev) = variants.insert(*tag, fields.len())
                    && prev != fields.len()
                {
                    return None;
                }
            }
            _ => return None,
        }
    }
    let has_field_bearing = variants.values().any(|a| *a >= 1);
    if variants.len() >= 2 && has_field_bearing {
        Some(variants)
    } else {
        None
    }
}

/// From a scrutinee's binding value, follow the dataflow to the producer
/// fn(s) whose bodies hold the return leaves, recording their binder ids.
///
/// Descends `if`/`let`-body/`Trace`; a call `Apply(Var(F), …)` where `F` is
/// a uniquely-bound fn is a producer — record `F` and follow F's body
/// leaves (an `f_14 → f_13` single-call chain).
///
/// The two mutually recursive walks (`follow_producer_chain` and
/// `follow_leaf_calls`, which differ only in the `When` arm) are the two
/// [`ChainJob`] variants of one driver, so a fn-body hop is just another job
/// pushed on top — the DFS order, and with it the `fns` / `in_chain_calls`
/// bookkeeping, is unchanged.
fn follow_producer_chain<'a>(
    value: &'a PseudoExpr,
    bindings: &'a HashMap<VarId, PseudoExpr>,
    fns: &mut BTreeSet<VarId>,
    in_chain_calls: &mut HashMap<VarId, usize>,
    depth: usize,
) {
    let mut jobs: Vec<ChainJob<'a>> = vec![ChainJob::Chain(value, depth)];

    while let Some(job) = jobs.pop() {
        match job {
            ChainJob::Chain(value, depth) => {
                if depth > CHAIN_DEPTH_CAP {
                    continue;
                }
                match value {
                    PseudoExpr::If {
                        then_branch,
                        else_branch,
                        ..
                    } => {
                        // Reversed so they pop in source order.
                        jobs.push(ChainJob::Chain(else_branch.as_ref(), depth));
                        jobs.push(ChainJob::Chain(then_branch.as_ref(), depth));
                    }
                    PseudoExpr::Let { body, .. } => {
                        jobs.push(ChainJob::Chain(body.as_ref(), depth))
                    }
                    PseudoExpr::Trace { value, .. } => {
                        jobs.push(ChainJob::Chain(value.as_ref(), depth))
                    }
                    PseudoExpr::Apply { function, .. } => {
                        if let Some(fid) = subject_head_var(function)
                            && let Some(fn_value) = bindings.get(&fid)
                            && is_fn_value(fn_value)
                        {
                            *in_chain_calls.entry(fid).or_insert(0) += 1;
                            if fns.insert(fid)
                                && let Some(body) = fn_value_body(fn_value)
                            {
                                jobs.push(ChainJob::Leaf(body, depth + 1));
                            }
                        }
                    }
                    _ => {}
                }
            }
            ChainJob::Leaf(expr, depth) => {
                if depth > CHAIN_DEPTH_CAP {
                    continue;
                }
                match expr {
                    PseudoExpr::If {
                        then_branch,
                        else_branch,
                        ..
                    } => {
                        jobs.push(ChainJob::Leaf(else_branch.as_ref(), depth));
                        jobs.push(ChainJob::Leaf(then_branch.as_ref(), depth));
                    }
                    PseudoExpr::Let { body, .. } => jobs.push(ChainJob::Leaf(body.as_ref(), depth)),
                    PseudoExpr::Trace { value, .. } => {
                        jobs.push(ChainJob::Leaf(value.as_ref(), depth))
                    }
                    PseudoExpr::When { clauses, .. } => {
                        for c in clauses.iter().rev() {
                            jobs.push(ChainJob::Leaf(&c.body, depth));
                        }
                    }
                    PseudoExpr::Apply { function, .. } => {
                        if let Some(fid) = subject_head_var(function)
                            && let Some(fn_value) = bindings.get(&fid)
                            && is_fn_value(fn_value)
                        {
                            *in_chain_calls.entry(fid).or_insert(0) += 1;
                            if fns.insert(fid)
                                && let Some(body) = fn_value_body(fn_value)
                            {
                                jobs.push(ChainJob::Leaf(body, depth + 1));
                            }
                        }
                    }
                    // A Constr leaf here is a genuine terminal — the enclosing fn IS a
                    // producer (already recorded by the caller). Nothing to chain.
                    _ => {}
                }
            }
        }
    }
}

/// A job on [`follow_producer_chain`]'s stack, carrying its own fn-hop depth.
/// `Chain` is the scrutinee-side descent; `Leaf` the RETURN-LEAF descent of a
/// producer fn body (the old `follow_leaf_calls`, which additionally follows
/// `when` clause bodies).
enum ChainJob<'a> {
    Chain(&'a PseudoExpr, usize),
    Leaf(&'a PseudoExpr, usize),
}

/// The body of a `Lambda`/`RecFn` producer value — the old
/// `follow_fn_body_leaves`' first half.
fn fn_value_body(fn_value: &PseudoExpr) -> Option<&PseudoExpr> {
    match fn_value {
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => Some(body.as_ref()),
        _ => None,
    }
}

fn is_fn_value(e: &PseudoExpr) -> bool {
    matches!(e, PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. })
}

#[cfg(test)]
mod tests;
