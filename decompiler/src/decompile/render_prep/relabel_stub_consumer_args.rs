//! Relabel a reconstructed stub `Unknown_E_*` payload back to the native
//! constructor it was extracted from — the Result/Pair sibling of
//! [`relabel_option_consumer_args`].
//!
//! Extraction alone is not enough: a `Result::Error` payload may be
//! re-packed into a different tag-1 arity-1 ADT, and `Unknown_E_1_1` is
//! also a genuine stub. Relabel only when the reconstruction flows to a
//! call argument that is destructured as the extraction's family.
//!
//! Rewrite `Constr{Unknown, tag, [Var(b)]}` → `Known(K)(b)` only when:
//! 1. `b` was extracted by a single-field `Known(K)(b)` (`expect Error(b)`);
//!    collided VarIds are skipped.
//! 2. The construction's tag equals `K.expected_tag()`, arity is 1, and
//!    the field is exactly `Var(b)` — so the change is display-only
//!    (`Error` and `Unknown_E_1_1` are the same `Constr(1, [v])`).
//! 3. That construction is a call argument (or a `Pair` component of one)
//!    whose callee parameter is consumed as K's family.
//!
//! On success the stub `type_hint` is dropped (`resolve` would otherwise
//! keep printing `Unknown_E_*`). Fail-closed: no witness, no rewrite.
//! Rewrites call-site argument values, never definitions. Idempotent:
//! a relabeled shape is no longer `Unknown`.
//!
//! After `relabel_option_consumer_args`; needs `unfold_y_comb_helper_apply`
//! so callee params and `when` subjects are visible.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

/// Pre-order walk over every node of `expr`, in the same order the recursive
/// `… ; for child in children(expr) { recurse }` shape visited them.
///
/// Children are pushed in REVERSE so they pop in source order.
fn walk_pre_order(expr: &PseudoExpr, mut visit: impl FnMut(&PseudoExpr)) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(node) = stack.pop() {
        visit(node);
        for child in super::scope_recurse::children(node).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// An ADT family whose unary member constructors may be reconstruction
/// targets. `Result = {Ok, Error}`; `Option`'s unary member is `Some` (its
/// `None` is nullary, handled by `relabel_option_consumer_args`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum AdtFamily {
    Result,
    Option,
}

/// The family a KnownConstructor belongs to, if it is a UNARY member (the
/// only members that can be a `Constr{tag, [Var(b)]}` reconstruction).
fn unary_family(kc: KnownConstructor) -> Option<AdtFamily> {
    match kc {
        KnownConstructor::Ok | KnownConstructor::Error => Some(AdtFamily::Result),
        KnownConstructor::Some => Some(AdtFamily::Option),
        _ => None,
    }
}

/// Whether a `when`-clause pattern matches a `Known` constructor of `family`.
fn clause_matches_family(pattern: &WhenPattern, family: AdtFamily) -> bool {
    let WhenPattern::Constructor {
        shape: ConstructorShape::Known(kc),
        ..
    } = pattern
    else {
        return false;
    };
    match family {
        AdtFamily::Result => matches!(kc, KnownConstructor::Ok | KnownConstructor::Error),
        AdtFamily::Option => matches!(kc, KnownConstructor::Some | KnownConstructor::None),
    }
}

/// The path within a call argument at which a parameter is consumed:
/// - `Direct`: the argument itself is the consumed value.
/// - `PairComponent(N)`: the argument is a `Pair(c0, c1)` and component N is
///   consumed (N ∈ {0, 1}).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ConsumePath {
    Direct,
    PairComponent(usize),
}

/// A recorded consumer position: at parameter index `param_index`, the value
/// reachable via `path` is destructured with `family`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ConsumerPosition {
    param_index: usize,
    path: ConsumePath,
    family: AdtFamily,
}

pub(super) fn relabel_stub_consumer_args(expr: PseudoExpr) -> PseudoExpr {
    if !super::drop_dead_pure_lets::contains_decompiled_marker(&expr) {
        return expr;
    }
    let multiply_bound = collect_multiply_bound_ids(&expr);
    // Gate 1: candidate ctor per provenance binder.
    let provenance = collect_binder_provenance(&expr, &multiply_bound);
    if provenance.is_empty() {
        return expr;
    }
    // Gate 3 (analysis): consumer positions per fn identity.
    let consuming = collect_family_consuming_params(&expr, &multiply_bound);
    if consuming.is_empty() {
        return expr;
    }
    rewrite(expr, &provenance, &consuming)
}

// ---------------------------------------------------------------------------
// Gate 1: binder provenance
// ---------------------------------------------------------------------------

/// Map of binder VarId → the UNARY `Known` constructor it was extracted with,
/// via a single-clause single-field `expect K(b) = …` (`When` with a lone
/// `Known(K)(binder)` clause). Multiply-bound binders are excluded so a binder
/// uniquely identifies one extraction.
fn collect_binder_provenance(
    expr: &PseudoExpr,
    multiply_bound: &HashSet<VarId>,
) -> HashMap<VarId, KnownConstructor> {
    let mut out: HashMap<VarId, KnownConstructor> = HashMap::new();
    collect_provenance_at(expr, multiply_bound, &mut out);
    out
}

fn collect_provenance_at(
    expr: &PseudoExpr,
    multiply_bound: &HashSet<VarId>,
    out: &mut HashMap<VarId, KnownConstructor>,
) {
    walk_pre_order(expr, |expr| {
        if let PseudoExpr::When { clauses, .. } = expr {
            for clause in clauses {
                if let WhenPattern::Constructor {
                    shape: ConstructorShape::Known(kc),
                    fields,
                    ..
                } = &clause.pattern
                {
                    if unary_family(*kc).is_some() && fields.len() == 1 {
                        let binder = &fields[0];
                        let vid = binder.var_id();
                        if !multiply_bound.contains(&vid) {
                            out.insert(vid, *kc);
                        }
                    }
                }
            }
        }
    })
}

// ---------------------------------------------------------------------------
// Gate 3 (analysis): consumer positions
// ---------------------------------------------------------------------------

/// Map of fn-identity VarId → the set of consumer positions in its body.
///
/// For a `Let`-bound `RecFn`, BOTH the Let binder id and the RecFn `name` id
/// map to the same position set. Colliding fn identities are skipped.
fn collect_family_consuming_params(
    expr: &PseudoExpr,
    multiply_bound: &HashSet<VarId>,
) -> HashMap<VarId, HashSet<ConsumerPosition>> {
    let mut out: HashMap<VarId, HashSet<ConsumerPosition>> = HashMap::new();
    collect_consumers_at(expr, multiply_bound, &mut out);
    out
}

fn collect_consumers_at(
    expr: &PseudoExpr,
    multiply_bound: &HashSet<VarId>,
    out: &mut HashMap<VarId, HashSet<ConsumerPosition>>,
) {
    walk_pre_order(expr, |expr| {
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
                let positions = family_consuming_positions(fn_body, params);
                if !positions.is_empty() {
                    if !multiply_bound.contains(&let_id) {
                        out.entry(let_id)
                            .or_default()
                            .extend(positions.iter().copied());
                    }
                    if let Some(name_id) = recfn_name_id {
                        if !multiply_bound.contains(&name_id) {
                            out.entry(name_id)
                                .or_default()
                                .extend(positions.iter().copied());
                        }
                    }
                }
            }
        }
    })
}

/// The consumer positions of `params` within `body`:
/// - DIRECT: a `when Var(param) is { … }` with a `Known` clause of a family.
/// - PAIR-NESTED: an `expect Pair(p0, p1) = param` (a lone Pair-destructuring
///   clause on subject `Var(param)` — see `pair_pattern_binders`) where a
///   component `p_N` is itself the subject of a family-matching `when`.
fn family_consuming_positions(body: &PseudoExpr, params: &[Binder]) -> HashSet<ConsumerPosition> {
    let param_index: HashMap<VarId, usize> = params
        .iter()
        .enumerate()
        .map(|(i, p)| (p.var_id(), i))
        .collect();
    // First pass: for every VarId, which family (if any) is it directly
    // matched against as a `when <var> is { Known(family) … }` subject.
    let mut family_of_subject: HashMap<VarId, AdtFamily> = HashMap::new();
    collect_family_subjects(body, &mut family_of_subject);
    // Second pass: for every `expect Pair(p0, p1) = <var>`, record the Pair
    // component binders that came out of which subject VarId.
    let mut pair_projections: HashMap<VarId, [Option<VarId>; 2]> = HashMap::new();
    collect_pair_projections(body, &mut pair_projections);
    let mut hits: HashSet<ConsumerPosition> = HashSet::new();
    for (subject_vid, &idx) in &param_index {
        // Direct consumption of the param itself.
        if let Some(family) = family_of_subject.get(subject_vid) {
            hits.insert(ConsumerPosition {
                param_index: idx,
                path: ConsumePath::Direct,
                family: *family,
            });
        }
        // Pair-nested: `expect Pair(p0, p1) = param`, then some `p_N` is
        // matched against a family.
        if let Some(components) = pair_projections.get(subject_vid) {
            for (n, comp) in components.iter().enumerate() {
                if let Some(comp_vid) = comp {
                    if let Some(family) = family_of_subject.get(comp_vid) {
                        hits.insert(ConsumerPosition {
                            param_index: idx,
                            path: ConsumePath::PairComponent(n),
                            family: *family,
                        });
                    }
                }
            }
        }
    }
    hits
}

/// For every `when <Var(vid)> is { … }` whose clauses include a `Known`
/// constructor of a family, record `vid → family`. (When a subject is matched
/// against more than one family — pathological — the last wins; harmless
/// because gate 2 additionally pins the exact tag.)
fn collect_family_subjects(expr: &PseudoExpr, out: &mut HashMap<VarId, AdtFamily>) {
    walk_pre_order(expr, |expr| {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = expr
        {
            if let PseudoExpr::Var { id: Some(vid), .. } = subject.as_ref() {
                for family in [AdtFamily::Result, AdtFamily::Option] {
                    if clauses
                        .iter()
                        .any(|c| clause_matches_family(&c.pattern, family))
                    {
                        out.insert(*vid, family);
                    }
                }
            }
        }
    })
}

/// The two component binder ids of a Pair-destructuring pattern, if the
/// clause pattern IS a Pair. Handles BOTH surface forms the pipeline emits:
/// the dedicated `WhenPattern::Pair(p0, p1)`, and the two-binder
/// `WhenPattern::Constructor { shape: Known(Pair), fields: [p0, p1] }` that
/// `expect Pair(a, b) = x` lowers to at this pass's point.
fn pair_pattern_binders(pattern: &WhenPattern) -> Option<(VarId, VarId)> {
    match pattern {
        WhenPattern::Pair(p0, p1) => Some((p0.var_id(), p1.var_id())),
        WhenPattern::Constructor {
            shape: ConstructorShape::Known(KnownConstructor::Pair),
            fields,
            ..
        } if fields.len() == 2 => Some((fields[0].var_id(), fields[1].var_id())),
        _ => None,
    }
}

/// For every `expect Pair(p0, p1) = <Var(vid)>` (a `When` whose subject is
/// `Var(vid)` and whose single clause is a Pair-destructuring pattern —
/// either `WhenPattern::Pair` or a `Known(Pair)` two-binder constructor),
/// record `vid → [p0.id, p1.id]`.
fn collect_pair_projections(expr: &PseudoExpr, out: &mut HashMap<VarId, [Option<VarId>; 2]>) {
    walk_pre_order(expr, |expr| {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = expr
        {
            if let PseudoExpr::Var { id: Some(vid), .. } = subject.as_ref() {
                if clauses.len() == 1 {
                    if let Some((p0, p1)) = pair_pattern_binders(&clauses[0].pattern) {
                        out.insert(*vid, [Some(p0), Some(p1)]);
                    }
                }
            }
        }
    })
}

// ---------------------------------------------------------------------------
// Multiply-bound ids
// ---------------------------------------------------------------------------

/// Every binder id that appears more than once program-wide (VarId
/// collisions). Both provenance binders and fn identities in this set are
/// excluded.
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

// ---------------------------------------------------------------------------
// Rewrite
// ---------------------------------------------------------------------------

/// `rebuild_apply_with_relabel` is the [`RwPost::RelabelApply`] step: the
/// spine peel is itself a walk, so all that moves is the per-argument
/// `rewrite` — the head and then the flattened arguments (innermost
/// application first, left to right) become ordinary child jobs, and the
/// relabel-per-position runs on them at reassembly.
fn rewrite(
    expr: PseudoExpr,
    provenance: &HashMap<VarId, KnownConstructor>,
    consuming: &HashMap<VarId, HashSet<ConsumerPosition>>,
) -> PseudoExpr {
    let mut steps: Vec<RwStep> = vec![RwStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RwStep::Visit(expr) => {
                // An `Apply` whose (possibly curried) head is a recorded fn
                // identity: relabel its argument leaves at the consumer
                // positions rather than folding it as a plain node.
                let relabel_head =
                    apply_head_and_args_head(&expr).filter(|h| consuming.contains_key(h));
                if let Some(head) = relabel_head {
                    let mut spine: Vec<crate::pseudo::ast::PVec> = Vec::new();
                    let mut current = expr;
                    while let PseudoExpr::Apply { function, args } = current {
                        spine.push(args);
                        current = function.into_inner();
                    }
                    // `current` is now the non-`Apply` head. `levels` is
                    // innermost-application-first, 's `for args in
                    // spine.into_iter().rev()`.
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
                    steps.push(RwStep::Visit(current));
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
                        let positions = consuming.get(&head).unwrap_or(&empty);
                        // The already-rewritten non-`Apply` head.
                        let mut acc = parts.next().expect("apply head");
                        let mut base = 0usize;
                        for count in levels {
                            let next_base = base;
                            let mut new_args = Vec::with_capacity(count);
                            for i in 0..count {
                                let abs = next_base + i;
                                // Already recursed; relabel per position.
                                let mut recursed = parts.next().expect("apply arg");
                                for pos in positions.iter().filter(|p| p.param_index == abs) {
                                    recursed =
                                        relabel_at_path(recursed, pos.path, pos.family, provenance);
                                }
                                new_args.push(recursed);
                            }
                            let consumed = new_args.len();
                            acc = PseudoExpr::Apply {
                                function: PBox::new(acc),
                                args: new_args.into(),
                            };
                            base = next_base + consumed;
                        }
                        acc
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
/// flattened parameter index each argument was relabelled at is recoverable.
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

/// The head VarId of a (possibly curried) `Apply`, without cloning args.
fn apply_head_and_args_head(expr: &PseudoExpr) -> Option<VarId> {
    let mut cur = expr;
    loop {
        let PseudoExpr::Apply { function, .. } = cur else {
            return None;
        };
        match function.as_ref() {
            PseudoExpr::Var { id: Some(vid), .. } => return Some(*vid),
            inner @ PseudoExpr::Apply { .. } => cur = inner,
            _ => return None,
        }
    }
}

/// Relabel the value reachable via `path` inside an argument, gated on 1+2 and
/// the family from gate 3.
fn relabel_at_path(
    arg: PseudoExpr,
    path: ConsumePath,
    family: AdtFamily,
    provenance: &HashMap<VarId, KnownConstructor>,
) -> PseudoExpr {
    match path {
        ConsumePath::Direct => relabel_construction(arg, family, provenance),
        ConsumePath::PairComponent(n) => match arg {
            // Dedicated Pair literal.
            PseudoExpr::Pair(a, b) => {
                let (a, b) = (a.into_inner(), b.into_inner());
                let (a, b) = if n == 0 {
                    (relabel_construction(a, family, provenance), b)
                } else {
                    (a, relabel_construction(b, family, provenance))
                };
                PseudoExpr::Pair(PBox::new(a), PBox::new(b))
            }
            // The `Constr { shape: Known(Pair), fields: [a, b] }` form that a
            // `Pair(a, b)` call-site argument lowers to at this pass's point —
            // a call passes this, not a `PseudoExpr::Pair`.
            PseudoExpr::Constr {
                type_hint,
                tag,
                mut fields,
                shape: shape @ ConstructorShape::Known(KnownConstructor::Pair),
            } if fields.len() == 2 => {
                let comp = std::mem::replace(&mut fields[n], PseudoExpr::Unit);
                fields[n] = relabel_construction(comp, family, provenance);
                PseudoExpr::Constr {
                    type_hint,
                    tag,
                    fields,
                    shape,
                }
            }
            other => other,
        },
    }
}

/// Gate 1+2: if `e` is `Constr{Unknown, tag, [Var(b)]}` where `b`'s provenance
/// ctor K is in `family` and `tag == K.expected_tag()`, relabel to `K(b)`;
/// otherwise return `e` verbatim, `shape`, `origin`/`church_true` metadata and
/// `type_hint` all preserved.
///
/// The candidacy check goes through a BORROW so a rejected construction is
/// never destructured and rebuilt; only the relabel path consumes `e`. That
/// keeps a non-target argument at a consumer position byte-identical.
///
/// The `type_hint` is DROPPED on relabel, and that is required rather than
/// stylistic: `rewrite_unresolved_constrs` (which runs before render-prep)
/// attaches the stub-ADT `TypeHintId` (`"Unknown_E_1"`), and the renderer's
/// `BlueprintHintRegistry::resolve` gives the stub name PRIORITY over the
/// shape's `pretty_name()` — a `Known(Error)` node carrying it would still
/// render `Unknown_E_1_1`. Dropping it lets `resolve` fall through to
/// `shape.pretty_name()` = `Error`.
fn relabel_construction(
    e: PseudoExpr,
    family: AdtFamily,
    provenance: &HashMap<VarId, KnownConstructor>,
) -> PseudoExpr {
    // Gates 1+2, decided through a borrow so a rejection returns `e` verbatim.
    let relabel_to = match &e {
        PseudoExpr::Constr {
            tag,
            fields,
            shape: ConstructorShape::Unknown { .. },
            ..
        } if fields.len() == 1 => match &fields[0] {
            // Sole field is a bare `Var(b)`; gate 1: b's provenance ctor is in
            // the witnessed family; gate 2: raw tag == that ctor's canonical tag.
            PseudoExpr::Var { id: Some(bid), .. } => provenance
                .get(bid)
                .copied()
                .filter(|kc| unary_family(*kc) == Some(family))
                .filter(|kc| *tag == kc.expected_tag()),
            _ => None,
        },
        _ => None,
    };
    match relabel_to {
        Some(kc) => {
            let PseudoExpr::Constr { tag, fields, .. } = e else {
                unreachable!("shape checked in the borrow above");
            };
            // type_hint dropped on relabel — see doc-comment above.
            PseudoExpr::Constr {
                type_hint: None,
                tag,
                fields,
                shape: ConstructorShape::Known(kc),
            }
        }
        // Verbatim: original shape / origin / church_true / type_hint intact.
        None => e,
    }
}

#[cfg(test)]
mod tests;
