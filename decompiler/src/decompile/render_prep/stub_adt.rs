//! Stub-ADT emission for unresolved `Constr<N>` constructors.
//!
//! The decompiler emits `Constr<N>(args)` when no blueprint type
//! maps to the constructor's `(parent_type, tag)`, and the surface
//! has no syntax for raw tags. This module synthesizes
//! `pub type Unknown_S_<ord> { Unknown_S_<ord>_<tag>(...), ... }`
//! for the module top and rewrites each unresolved `Constr` through
//! the [`BlueprintHintRegistry`] lookup chain.
//!
//! Grouping is by When-scrutinee identity — a `BTreeMap` keyed by
//! the canonical `Var.id` (see [`AliasAnalysis::canonical`]). Pattern
//! constructors inside `when X is { ... }` share `X`'s `VarId`, so
//! two `When`s on the same subject merge. Expression-position
//! constructors that reach no tracked scrutinee fall into a global
//! per-arity bucket.
//!
//! Def-use refinement (`build_alias_analysis` +
//! `promote_let_value_constrs`) also covers `let Y = X; when Y is`
//! (Y canonicalizes to X) and `let X = Constr<0>(...); when X is`
//! (the value-position `Constr` is attributed to `X`, then to `X`'s
//! class if scrutinized, else the arity bucket).
//! `rewrite_unresolved_constrs` mirrors that so pattern and value
//! get the same type-hint.
//!
//! Detection keys on `ConstructorShape::Unknown`, not
//! `type_hint.is_none()` — known constructors also lack type hints
//! and must not be stubbed. Rendered names use ordinals assigned
//! from sorted class representatives, never raw `VarId` fields,
//! whose thread-local counter does not reset between decompile
//! calls.

use crate::pseudo::ast::PBox;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::decompile::TypeHintId;
use crate::decompile::blueprint_registry::BlueprintHintRegistry;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

/// A `(tag, arity)` pair characterising one unresolved constructor
/// shape that needs a stub-ADT slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct StubVariant {
    pub tag: usize,
    pub arity: usize,
}

/// Analysis output — every unresolved constructor in the AST grouped
/// by its scrutinee class (for `When` patterns) or arity (for
/// expression-position fallbacks).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct StubAdtGroups {
    /// Shapes keyed by the **canonical** `VarId` —
    /// [`AliasAnalysis::canonical`] applied to the scrutinee's
    /// `Var.id`, so aliased subjects (`let Y = X; when Y is ...`)
    /// merge into `X`'s class.
    pub by_scrutinee: BTreeMap<VarId, BTreeSet<StubVariant>>,
    /// Expression-position fallback shapes, grouped by arity — for
    /// a `Constr<N>(...)` that reaches no tracked scrutinee (it
    /// flows into a call or list head without being matched).
    pub by_arity: BTreeMap<usize, BTreeSet<StubVariant>>,
}

impl StubAdtGroups {
    /// No unresolved constructors: the AST is blueprint-clean and
    /// stub emission is a no-op here.
    pub(crate) fn is_empty(&self) -> bool {
        self.by_scrutinee.is_empty() && self.by_arity.is_empty()
    }
}

/// Walk `expr` and collect all `ConstructorShape::Unknown` shapes
/// into a [`StubAdtGroups`] map. A `When`'s scrutinee identity is its
/// subject's `Var.id` when the subject is a bare variable; complex
/// subjects (`FieldAccess`, `Apply`, …) drop their unresolved
/// patterns into the arity-fallback bucket.
///
/// **Def-use refinement** reaches two cases naive grouping misses:
/// (a) aliased subjects (`let Y = X`) — `When` on `Y` groups under
///     `X`'s canonical class.
/// (b) a let-bound value-position constructor
///     (`let X = Constr<N>(..)`) attributes to `X`'s class when `X`
///     is later scrutinized, and to `by_arity` when it never is.
pub(crate) fn collect_unresolved_constr_shapes(expr: &PseudoExpr) -> StubAdtGroups {
    let analysis = build_alias_analysis(expr);
    let mut groups = StubAdtGroups::default();
    collect(expr, &mut groups, None, &analysis);
    promote_let_value_constrs(&mut groups, &analysis);
    groups
}

/// Pre-pass maps: aliases, let-bound `Constr` values, producer fns.
#[derive(Debug, Default)]
struct AliasAnalysis {
    /// `Y → X` for every `let Y = Var(X)` shape. Resolve to canonical
    /// via [`canonical`].
    aliases: BTreeMap<VarId, VarId>,
    /// `X → {variants}` for every `let X = Constr<tag>(...)` whose
    /// value is a top-level unresolved Constr.
    /// [`promote_let_value_constrs`] later routes them by whether
    /// `canonical(X)` is in `by_scrutinee`.
    let_value_constrs: BTreeMap<VarId, BTreeSet<StubVariant>>,
    /// `producer-fn VarId → (scrutinee VarId, consumer variants
    /// tag→arity)`. When a fn's return leaves flow EXCLUSIVELY into one
    /// `when Var(scrutinee)` stub sum, a return-leaf raw `Constr` whose
    /// `(tag, arity)` is a declared consumer variant attributes to the
    /// SCRUTINEE class rather than the arity fallback bucket. Built from
    /// [`super::relabel_stub_producer_leaves`]'s shared witness. Leaves NOT
    /// in the variant map stay with the arity fallback — fail-closed, never
    /// widen the sum.
    producer_leaf_fns: BTreeMap<VarId, (VarId, BTreeMap<usize, usize>)>,
}

impl AliasAnalysis {
    /// Resolve `id` to its canonical representative through the alias
    /// chain. The visited set is defensive: VarIds are globally
    /// unique per binding, so a well-formed program's alias edges
    /// form a DAG and cannot cycle.
    fn canonical(&self, id: VarId) -> VarId {
        let mut current = id;
        let mut visited = std::collections::BTreeSet::new();
        loop {
            if !visited.insert(current) {
                // Return the lowest VarId seen on the chain, so
                // attribution stays deterministic; a cycle means
                // malformed AST.
                return *visited.iter().next().unwrap_or(&current);
            }
            match self.aliases.get(&current) {
                Some(next) if *next != current => current = *next,
                _ => return current,
            }
        }
    }
}

/// Build the alias, let-value-`Constr` and producer-fn maps.
fn build_alias_analysis(expr: &PseudoExpr) -> AliasAnalysis {
    let mut analysis = AliasAnalysis::default();
    build_alias_inner(expr, &mut analysis);
    // A producer fn reachable from two distinct scrutinees is ambiguous
    // — poison it so its leaves fall back to the arity bucket.
    let mut poisoned: BTreeSet<VarId> = BTreeSet::new();
    for w in super::relabel_stub_producer_leaves::collect_stub_producer_witnesses(expr) {
        for f in &w.producer_fns {
            match analysis.producer_leaf_fns.get(f) {
                Some((existing, _)) if *existing != w.scrutinee => {
                    poisoned.insert(*f);
                }
                _ if poisoned.contains(f) => {}
                _ => {
                    analysis
                        .producer_leaf_fns
                        .insert(*f, (w.scrutinee, w.variants.clone()));
                }
            }
        }
    }
    for f in poisoned {
        analysis.producer_leaf_fns.remove(&f);
    }
    analysis
}

/// A pure pre-order visitor with nothing to do after a child, so it needs no
/// post step: each arm records its entries and then pushes its children in
/// REVERSE, which pops them in source order.
fn build_alias_inner(expr: &PseudoExpr, analysis: &mut AliasAnalysis) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            PseudoExpr::Let {
                id: Some(let_id),
                value,
                body,
                ..
            } => {
                // Alias case: `let Y = Var(X)` with both VarIds available.
                if let PseudoExpr::Var {
                    id: Some(var_id), ..
                } = value.as_ref()
                {
                    // Skip `let X = X`: an X→X entry is one
                    // `canonical()` short-circuits on anyway.
                    if let_id != var_id {
                        analysis.aliases.insert(*let_id, *var_id);
                    }
                }
                // Let-value case: `let X = Constr<tag>(...)`. Same
                // Unknown-shape detection as the main collect.
                if let PseudoExpr::Constr {
                    shape,
                    tag,
                    fields,
                    type_hint,
                } = value.as_ref()
                    && matches!(shape, ConstructorShape::Unknown { .. })
                    && type_hint.is_none()
                {
                    let variant = StubVariant {
                        tag: *tag,
                        arity: fields.len(),
                    };
                    analysis
                        .let_value_constrs
                        .entry(*let_id)
                        .or_default()
                        .insert(variant);
                }
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for clause in clauses.iter().rev() {
                    pending.push(&clause.body);
                    if let Some(guard) = &clause.guard {
                        pending.push(guard);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push(t);
                }
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Tuple(items) => {
                for i in items.iter().rev() {
                    pending.push(i);
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push(f);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
}

/// Route each let-value Constr variant to the scrutinee class when
/// `canonical(let_id)` is in `by_scrutinee`, else to the arity
/// bucket.
fn promote_let_value_constrs(groups: &mut StubAdtGroups, analysis: &AliasAnalysis) {
    for (let_id, variants) in &analysis.let_value_constrs {
        let canonical_id = analysis.canonical(*let_id);
        if groups.by_scrutinee.contains_key(&canonical_id) {
            groups
                .by_scrutinee
                .get_mut(&canonical_id)
                .unwrap()
                .extend(variants.iter().copied());
        } else {
            for variant in variants {
                groups
                    .by_arity
                    .entry(variant.arity)
                    .or_default()
                    .insert(*variant);
            }
        }
    }
}

/// One job on [`collect`]'s stack.
enum CollectJob<'a> {
    /// An expression, carrying the `current_scrutinee_id` passed as a call argument.
    Expr(&'a PseudoExpr, Option<VarId>),
    /// A `When` clause pattern, carrying the `scrutinee_id` handed to `collect_pattern`
    /// — THAT `When`'s subject class, not the outer context the clause bodies keep.
    Pattern(&'a WhenPattern, Option<VarId>),
}

/// Collector. Pattern positions group under their own `When` subject,
/// canonicalized through `analysis`'s alias map; expression positions fall
/// into the arity bucket.
///
/// A pure pre-order visitor: nothing runs after a child, so there is no post
/// step. The one thing computed BETWEEN a `When`'s subject and its clauses —
/// the scrutinee id — reads only the subject NODE, never the walk's result,
/// so it stays where it was, in the arm that pushes the clause jobs.
/// `collect_pattern`'s body became the `Pattern` job: it is a call the
/// recursion made mid-arm, and its `Literal` case descends back into
/// expression position.
fn collect(
    expr: &PseudoExpr,
    groups: &mut StubAdtGroups,
    current_scrutinee_id: Option<VarId>,
    analysis: &AliasAnalysis,
) {
    let mut pending: Vec<CollectJob<'_>> = vec![CollectJob::Expr(expr, current_scrutinee_id)];
    while let Some(job) = pending.pop() {
        let (expr, current_scrutinee_id) = match job {
            // Walk a `WhenPattern` for unresolved constructor shapes,
            // grouping under `scrutinee_id` when available, else under the
            // arity fallback. `WhenPattern::Literal` carries an arbitrary
            // `PseudoExpr`, so `Constr` shapes nested inside it must be
            // visited too.
            CollectJob::Pattern(pattern, scrutinee_id) => {
                match pattern {
                    WhenPattern::Constructor {
                        type_hint,
                        tag,
                        fields,
                        shape,
                    } => {
                        // Same rule as expression position:
                        // `ConstructorShape::Unknown` with no type hint.
                        if matches!(shape, ConstructorShape::Unknown { .. }) && type_hint.is_none()
                        {
                            let variant = StubVariant {
                                tag: *tag,
                                arity: fields.len(),
                            };
                            if let Some(sid) = scrutinee_id {
                                groups.by_scrutinee.entry(sid).or_default().insert(variant);
                            } else {
                                groups
                                    .by_arity
                                    .entry(variant.arity)
                                    .or_default()
                                    .insert(variant);
                            }
                        }
                    }
                    WhenPattern::Literal(inner) => {
                        // A `Constr` literal pattern lands here when the
                        // simplifier emits the constructor as a value-equality
                        // check. Treat its TOP-LEVEL Constr as pattern position
                        // so it groups under the current scrutinee; nested
                        // expressions go through the normal expression
                        // collector.
                        if let PseudoExpr::Constr {
                            shape,
                            tag,
                            fields,
                            type_hint,
                        } = inner
                        {
                            if matches!(shape, ConstructorShape::Unknown { .. })
                                && type_hint.is_none()
                            {
                                let variant = StubVariant {
                                    tag: *tag,
                                    arity: fields.len(),
                                };
                                if let Some(sid) = scrutinee_id {
                                    groups.by_scrutinee.entry(sid).or_default().insert(variant);
                                } else {
                                    groups
                                        .by_arity
                                        .entry(variant.arity)
                                        .or_default()
                                        .insert(variant);
                                }
                            }
                            // Fields are sub-expressions, not pattern positions
                            // — recurse with the outer scrutinee context.
                            for f in fields.iter().rev() {
                                pending.push(CollectJob::Expr(f, scrutinee_id));
                            }
                        } else {
                            // Non-Constr literal — just recurse normally.
                            pending.push(CollectJob::Expr(inner, scrutinee_id));
                        }
                    }
                    // List / Tuple / Pair / Wildcard / Var patterns only bind
                    // names; they carry no unresolved Constructor of their own.
                    WhenPattern::List { .. }
                    | WhenPattern::Tuple(_)
                    | WhenPattern::Pair(_, _)
                    | WhenPattern::Wildcard
                    | WhenPattern::Var(_) => {}
                }
                continue;
            }
            CollectJob::Expr(expr, current_scrutinee_id) => (expr, current_scrutinee_id),
        };
        match expr {
            PseudoExpr::When {
                subject,
                subject_name: _,
                clauses,
            } => {
                // Scrutinee identity for THIS When: the subject's
                // `Var.id`, else None. Canonicalizing through the alias
                // map groups a `When` on an aliased subject (`let Y = X;
                // when Y is ..`) with `X`'s class.
                let scrutinee_id = scrutinee_var_id(subject).map(|id| analysis.canonical(id));

                // Patterns group under `scrutinee_id`; clause bodies
                // keep the OUTER scrutinee context, since a body is no
                // longer in this `When`'s pattern position.
                for clause in clauses.iter().rev() {
                    pending.push(CollectJob::Expr(&clause.body, current_scrutinee_id));
                    if let Some(guard) = &clause.guard {
                        pending.push(CollectJob::Expr(guard, current_scrutinee_id));
                    }
                    pending.push(CollectJob::Pattern(&clause.pattern, scrutinee_id));
                }
                pending.push(CollectJob::Expr(subject, current_scrutinee_id));
            }
            PseudoExpr::Constr {
                shape,
                tag,
                fields,
                type_hint,
            } => {
                // Skip resolved constructors: non-Unknown shape, or a
                // type_hint already set. Shape is the source of truth,
                // type_hint alone is not.
                if matches!(shape, ConstructorShape::Unknown { .. }) && type_hint.is_none() {
                    let variant = StubVariant {
                        tag: *tag,
                        arity: fields.len(),
                    };
                    // Expression position — arity bucket. Pattern
                    // positions are caught by the `Pattern` job with
                    // their When scrutinee context; let-value positions
                    // are skipped at their `Let` parent and routed by
                    // `promote_let_value_constrs`.
                    groups
                        .by_arity
                        .entry(variant.arity)
                        .or_default()
                        .insert(variant);
                }
                // Recurse into fields so nested Constrs are also caught.
                for f in fields.iter().rev() {
                    pending.push(CollectJob::Expr(f, current_scrutinee_id));
                }
            }
            PseudoExpr::Let {
                id: Some(let_id),
                value,
                body,
                ..
            } if analysis.let_value_constrs.contains_key(let_id) => {
                // The pre-pass recorded this Let's top-level Constr
                // value. Skip emitting that constructor here — the
                // finalize step routes it — but RECURSE INTO THE FIELDS
                // so nested unresolved Constrs inside its arguments still
                // surface.
                pending.push(CollectJob::Expr(body, current_scrutinee_id));
                if let PseudoExpr::Constr { fields, .. } = value.as_ref() {
                    for f in fields.iter().rev() {
                        pending.push(CollectJob::Expr(f, current_scrutinee_id));
                    }
                } else {
                    // Defensive: pre-pass said this was a Constr, but the
                    // current AST shape isn't. Fall back to regular walk.
                    pending.push(CollectJob::Expr(value, current_scrutinee_id));
                }
            }
            PseudoExpr::Let {
                id: Some(let_id),
                value,
                body,
                ..
            } if analysis.producer_leaf_fns.contains_key(let_id) => {
                // A witnessed producer fn: attribute its RETURN-LEAF raw Constrs
                // to the consumer's canonicalized scrutinee class, so they group
                // as `Unknown_S_N`, not the arity fallback. Leaf attribution is
                // additive — non-leaf Constrs still collect in the walk below.
                let (raw_scrutinee, variants) = &analysis.producer_leaf_fns[let_id];
                let scrutinee = analysis.canonical(*raw_scrutinee);
                collect_producer_leaves(value, groups, scrutinee, variants);
                pending.push(CollectJob::Expr(body, current_scrutinee_id));
                pending.push(CollectJob::Expr(value, current_scrutinee_id));
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(CollectJob::Expr(body, current_scrutinee_id));
                pending.push(CollectJob::Expr(value, current_scrutinee_id));
            }
            PseudoExpr::Lambda { body, .. } => {
                pending.push(CollectJob::Expr(body, current_scrutinee_id))
            }
            PseudoExpr::RecFn { body, .. } => {
                pending.push(CollectJob::Expr(body, current_scrutinee_id))
            }
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(CollectJob::Expr(a, current_scrutinee_id));
                }
                pending.push(CollectJob::Expr(function, current_scrutinee_id));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(CollectJob::Expr(else_branch, current_scrutinee_id));
                pending.push(CollectJob::Expr(then_branch, current_scrutinee_id));
                pending.push(CollectJob::Expr(condition, current_scrutinee_id));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push(CollectJob::Expr(t, current_scrutinee_id));
                }
                for e in elements.iter().rev() {
                    pending.push(CollectJob::Expr(e, current_scrutinee_id));
                }
            }
            PseudoExpr::Tuple(items) => {
                for i in items.iter().rev() {
                    pending.push(CollectJob::Expr(i, current_scrutinee_id));
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(CollectJob::Expr(b, current_scrutinee_id));
                pending.push(CollectJob::Expr(a, current_scrutinee_id));
            }
            PseudoExpr::FieldAccess { record, .. } => {
                pending.push(CollectJob::Expr(record, current_scrutinee_id))
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                pending.push(CollectJob::Expr(collection, current_scrutinee_id))
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(CollectJob::Expr(right, current_scrutinee_id));
                pending.push(CollectJob::Expr(left, current_scrutinee_id));
            }
            PseudoExpr::UnOp { operand, .. } => {
                pending.push(CollectJob::Expr(operand, current_scrutinee_id))
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(CollectJob::Expr(a, current_scrutinee_id));
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                pending.push(CollectJob::Expr(inner, current_scrutinee_id))
            }
            PseudoExpr::Trace { message, value } => {
                pending.push(CollectJob::Expr(value, current_scrutinee_id));
                pending.push(CollectJob::Expr(message, current_scrutinee_id));
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
}

/// Attribute a producer fn's RETURN-LEAF raw `Constr`s to
/// `scrutinee`'s class. Descends the fn value (Lambda/RecFn) to its body
/// leaves through `if`/`let`-body/`when`-tail/`trace`, and adds each raw
/// (`Unknown`, hint-less) leaf `Constr`'s `(tag, arity)` to
/// `groups.by_scrutinee[scrutinee]`. Only leaf-position constructors are
/// attributed (mirrors [`super::relabel_stub_producer_leaves`]'s leaf walk);
/// nested/argument-position Constrs are left to the ordinary collector.
fn collect_producer_leaves(
    fn_value: &PseudoExpr,
    groups: &mut StubAdtGroups,
    scrutinee: VarId,
    variants: &BTreeMap<usize, usize>,
) {
    /// A pure pre-order visitor with nothing to do after a child, so it needs
    /// no post step; children go on in REVERSE so they pop in the order the
    /// recursion visited them.
    fn walk_body(
        expr: &PseudoExpr,
        groups: &mut StubAdtGroups,
        scrutinee: VarId,
        variants: &BTreeMap<usize, usize>,
    ) {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(expr) = pending.pop() {
            match expr {
                PseudoExpr::Constr {
                    shape,
                    tag,
                    fields,
                    type_hint,
                } if matches!(shape, ConstructorShape::Unknown { .. })
                    && type_hint.is_none()
                    // Fail-closed: only attribute a leaf whose (tag, arity) IS a
                    // declared consumer variant — never widen the sum.
                    && variants.get(tag) == Some(&fields.len()) =>
                {
                    let variant = StubVariant {
                        tag: *tag,
                        arity: fields.len(),
                    };
                    groups
                        .by_scrutinee
                        .entry(scrutinee)
                        .or_default()
                        .insert(variant);
                }
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(else_branch);
                    pending.push(then_branch);
                }
                PseudoExpr::Let { body, .. } => pending.push(body),
                PseudoExpr::Trace { value, .. } => pending.push(value),
                PseudoExpr::When { clauses, .. } => {
                    for c in clauses.iter().rev() {
                        pending.push(&c.body);
                    }
                }
                // A leaf call to another producer fn is handled when that callee's
                // own binder is visited.
                _ => {}
            }
        }
    }
    match fn_value {
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
            walk_body(body, groups, scrutinee, variants)
        }
        _ => {}
    }
}

/// Stable scrutinee identity for a `When`: the subject's `Var` id. A
/// non-Var subject has none, so its patterns drop into the
/// arity-fallback bucket.
fn scrutinee_var_id(expr: &PseudoExpr) -> Option<VarId> {
    match expr {
        PseudoExpr::Var { id: Some(id), .. } => Some(*id),
        _ => None,
    }
}

/// Map each class representative `VarId` in `groups.by_scrutinee` to
/// an ordinal (1, 2, 3, ...), ascending by `VarId` as `BTreeMap`
/// already orders them.
///
/// Ordinals keep rendered names like `Unknown_S_1` stable across
/// decompile runs, which raw `VarId`s would not:
/// `VarId::fresh_binding()` uses a thread-local counter that drifts.
pub(crate) fn assign_class_ordinals(groups: &StubAdtGroups) -> BTreeMap<VarId, usize> {
    groups
        .by_scrutinee
        .keys()
        .enumerate()
        .map(|(idx, vid)| (*vid, idx + 1))
        .collect()
}

/// Stub-ADT name minted for one scrutinee class or arity bucket.
///
/// The bucket name doubles as the [`TypeHintId`] in
/// [`BlueprintHintRegistry::register_user`], so the renderer's
/// `(type_hint, tag)` lookup chain in `pseudo/pretty` resolves
/// these synthetic entries with no new code path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StubAdtNames {
    /// Per-scrutinee class: VarId → its ADT shards. One `pub type
    /// Unknown_S_<ord>` covers the class, stored under every arity
    /// it was collected at so the arity-keyed rewrite lookup finds
    /// it.
    pub by_scrutinee: BTreeMap<VarId, StubAdtClass>,
    /// Per-arity fallback: arity → (type-hint, variant-name-per-tag).
    pub by_arity: BTreeMap<usize, StubAdtTypeNames>,
}

/// One scrutinee class. `shards` is keyed by the arities its
/// variants were collected at, so `shards[arity].type_hint`
/// resolves an unresolved Constr of that arity flowing into this
/// class; every key of a class maps to the same ADT.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct StubAdtClass {
    pub shards: BTreeMap<usize, StubAdtTypeNames>,
}

impl StubAdtClass {
    /// Iterate the shards for emission order (sorted by arity).
    pub(crate) fn shards_in_emission_order(&self) -> impl Iterator<Item = &StubAdtTypeNames> {
        self.shards.values()
    }
}

/// Names minted for one stub-ADT (one type hint + variant names
/// indexed by `(tag, arity)`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StubAdtTypeNames {
    pub type_hint: TypeHintId,
    pub type_name: String,
    /// Variant constructor names keyed by `(tag, arity)`.
    pub variant_names: BTreeMap<StubVariant, String>,
    /// Set when `override_cardano_stub_adt_names` renamed this class to
    /// a LEDGER record (`TxInfo`, `Address`, …). Such a type is part of
    /// the Cardano prelude, so `format_stub_adt_prefix` emits no
    /// declaration for it: `pub type ScriptContext { ScriptContext(Data,
    /// Data) }` redeclares a type the reader already has, under a shape
    /// (all-`Data` fields) that is less true than the real one.
    ///
    /// Recorded at the rename rather than re-derived from the name, so
    /// it cannot drift from `decl_names_for_context_type`.
    pub cardano_record: bool,
}

/// Mint deterministic stub-ADT names from the analysis output, and
/// register every `(type_hint, tag) → variant_name` into `registry`.
/// The renderer's existing lookup (`BlueprintHintRegistry::resolve`)
/// then maps unresolved `Constr` nodes to their synthetic variant
/// names — provided the AST rewrite sets `type_hint` on those nodes.
///
/// Returns the [`StubAdtNames`] map the AST rewrite consults for
/// which hint to set on each Constr.
pub(crate) fn register_stub_adts_in_registry(
    groups: &StubAdtGroups,
    ordinals: &BTreeMap<VarId, usize>,
    registry: &mut BlueprintHintRegistry,
) -> StubAdtNames {
    let mut by_scrutinee = BTreeMap::new();
    let mut by_arity = BTreeMap::new();

    // The `BlueprintHintRegistry`'s `(hint, tag) → name` lookup
    // table is arity-agnostic. Sharding a class by arity to work
    // around that over-splits ADTs whose variants legitimately
    // differ in arity at distinct tags (`None` arity 0 and
    // `Some(T)` arity 1 under one type).
    for (vid, variants) in &groups.by_scrutinee {
        let ord = ordinals
            .get(vid)
            .copied()
            .expect("every scrutinee key in groups must have an ordinal");
        // Emit ONE ADT per scrutinee class covering all its variants: a
        // tag seen at several collection arities just re-registers the
        // SAME name. The declared field count is reconciled later to the
        // uniform (overflow-expanded +
        // `unify_constructor_pattern_arity`-padded) arity by
        // `reconcile_declared_arities`, which also dedups the duplicate
        // same-tag/different-arity entries down to one variant per tag.
        //
        // (Splitting a multi-arity tag into `Unknown_S_<ord>_A<arity>`
        // types instead breaks a single Scott value's `when` across
        // several declared types — invalid surface syntax — and the multi-arity
        // observation is itself an artifact of per-site overflow
        // expansion, not genuinely distinct types.)
        let type_name = format!("Unknown_S_{ord}");
        let type_hint = TypeHintId::new(type_name.clone());
        let mut variant_names = BTreeMap::new();
        for variant in variants {
            let variant_name = format!("Unknown_S_{ord}_{}", variant.tag);
            registry.register_user(type_hint.clone(), variant.tag, variant_name.clone());
            variant_names.insert(*variant, variant_name);
        }
        // Register the single ADT under every collection-arity key so
        // the arity-keyed `rewrite_pattern` lookup finds it regardless
        // of which (pre-overflow) arity a given pattern was collected at.
        let single = StubAdtTypeNames {
            type_hint,
            type_name,
            variant_names,
            cardano_record: false,
        };
        let arities_seen: BTreeSet<usize> = variants.iter().map(|v| v.arity).collect();
        let class = by_scrutinee
            .entry(*vid)
            .or_insert_with(StubAdtClass::default);
        for arity in arities_seen {
            class.shards.insert(arity, single.clone());
        }
    }

    for (arity, variants) in &groups.by_arity {
        let type_name = format!("Unknown_E_{arity}");
        let type_hint = TypeHintId::new(type_name.clone());
        let mut variant_names = BTreeMap::new();
        for variant in variants {
            let variant_name = format!("Unknown_E_{arity}_{}", variant.tag);
            registry.register_user(type_hint.clone(), variant.tag, variant_name.clone());
            variant_names.insert(*variant, variant_name);
        }
        by_arity.insert(
            *arity,
            StubAdtTypeNames {
                type_hint,
                type_name,
                variant_names,
                cardano_record: false,
            },
        );
    }

    StubAdtNames {
        by_scrutinee,
        by_arity,
    }
}

/// Produce the textual `pub type Unknown_S_<ord> { ... }`
/// declarations for the minted stub-ADT names, suitable for
/// prepending to the rendered validator block.
///
/// Field types default to `Data` per slot: the underlying
/// constructors are blueprint-unresolved, so no refined per-slot
/// type is available.
///
/// Output format (deterministic — `BTreeMap` iteration sorts):
/// ```text
/// pub type Unknown_S_1 {
///   Unknown_S_1_0
///   Unknown_S_1_1(Data, Data)
/// }
///
/// pub type Unknown_E_2 {
///   Unknown_E_2_3(Data, Data)
/// }
///
/// ```
pub(crate) fn format_stub_adt_prefix(names: &StubAdtNames) -> String {
    let mut out = String::new();
    // A class with no tag-arity conflict registers the SAME
    // `StubAdtTypeNames` under every arity key it covers, so
    // iterating `shards` without deduping by `type_hint` emits
    // duplicate `pub type` blocks.
    let mut seen_hints: std::collections::HashSet<TypeHintId> = std::collections::HashSet::new();
    // Two DIFFERENT classes can carry the same Cardano-override name
    // and shape (both interval bounds override to `IntervalBound`),
    // which would emit the `pub type` block twice. Deduping on the
    // rendered text still emits distinct shapes that share a name.
    let mut seen_blocks: std::collections::HashSet<String> = std::collections::HashSet::new();
    for class in names.by_scrutinee.values() {
        for adt in class.shards_in_emission_order() {
            // A ledger record is prelude, not a synthesized ADT.
            if adt.cardano_record {
                continue;
            }
            if seen_hints.insert(adt.type_hint.clone()) {
                let mut block = String::new();
                format_stub_adt_block(adt, &mut block);
                if seen_blocks.insert(block.clone()) {
                    out.push_str(&block);
                }
            }
        }
    }
    // Arity fallback buckets — each has its own unique TypeHintId.
    for adt in names.by_arity.values() {
        format_stub_adt_block(adt, &mut out);
    }
    out
}

/// Bump each stub-constructor's DECLARED arity to the one the final
/// rendered AST's patterns bind. `register_stub_adts_in_registry`
/// froze the arity at collection time, before overflow expansion and
/// before `unify_constructor_pattern_arity` padded every
/// destructuring site of a `(type_hint, tag)` to a uniform max.
pub(crate) fn reconcile_declared_arities(names: &mut StubAdtNames, rendered: &PseudoExpr) {
    let mut max: HashMap<(TypeHintId, usize), usize> = HashMap::new();
    collect_rendered_pattern_arities(rendered, &mut max);
    if max.is_empty() {
        return;
    }
    for class in names.by_scrutinee.values_mut() {
        for adt in class.shards.values_mut() {
            bump_variant_arities(adt, &max);
        }
    }
    for adt in names.by_arity.values_mut() {
        bump_variant_arities(adt, &max);
    }
}

fn bump_variant_arities(adt: &mut StubAdtTypeNames, max: &HashMap<(TypeHintId, usize), usize>) {
    let old = std::mem::take(&mut adt.variant_names);
    for (variant, name) in old {
        let target = max
            .get(&(adt.type_hint.clone(), variant.tag))
            .copied()
            .unwrap_or(variant.arity)
            .max(variant.arity);
        adt.variant_names.insert(
            StubVariant {
                tag: variant.tag,
                arity: target,
            },
            name,
        );
    }
}

/// Max payload arity bound at each `(stub hint, tag)` in a PREPARED
/// tree — the evidence `merge_isomorphic_stub_adts` groups by.
///
/// Must be measured on a PRE-merge prepared view: after the merge the
/// classes share a hint, and the max collapses them all onto the widest
/// one, which is the very confusion the merge key is trying to avoid.
pub(crate) fn collect_stub_pattern_arities(
    prepared: &PseudoExpr,
) -> HashMap<(TypeHintId, usize), usize> {
    let mut out = HashMap::new();
    collect_rendered_pattern_arities(prepared, &mut out);
    out
}

fn collect_rendered_pattern_arities(
    expr: &PseudoExpr,
    max: &mut HashMap<(TypeHintId, usize), usize>,
) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = pending.pop() {
        if let PseudoExpr::When { clauses, .. } = expr {
            for clause in clauses {
                if let WhenPattern::Constructor {
                    type_hint: Some(hint),
                    tag,
                    fields,
                    shape,
                } = &clause.pattern
                    && matches!(shape, ConstructorShape::Unknown { .. })
                {
                    let entry = max.entry((hint.clone(), *tag)).or_insert(0);
                    *entry = (*entry).max(fields.len());
                }
            }
        }
        // Value-position constructions count too: an unpaddable `Constr`
        // value must not exceed the declared arity (mirrors the max folded
        // in by `unify_constructor_pattern_arity`).
        if let PseudoExpr::Constr {
            type_hint: Some(hint),
            tag,
            fields,
            shape,
        } = expr
            && matches!(shape, ConstructorShape::Unknown { .. })
        {
            let entry = max.entry((hint.clone(), *tag)).or_insert(0);
            *entry = (*entry).max(fields.len());
        }
        pending.extend(crate::decompile::render_prep::scope_recurse::children(expr));
    }
}

fn format_stub_adt_block(adt: &StubAdtTypeNames, out: &mut String) {
    // Compact single-variant ADTs onto one line:
    //   `pub type Foo { Foo_0 }`             (zero arity)
    //   `pub type Foo { Foo_0(Data, Data) }` (with payload)
    // Multi-variant types keep the vertical form.
    if adt.variant_names.len() == 1 {
        let (variant, variant_name) = adt.variant_names.iter().next().unwrap();
        out.push_str("pub type ");
        out.push_str(&adt.type_name);
        out.push_str(" { ");
        out.push_str(variant_name);
        if variant.arity > 0 {
            out.push('(');
            for i in 0..variant.arity {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str("Data");
            }
            out.push(')');
        }
        out.push_str(" }\n\n");
        return;
    }
    out.push_str("pub type ");
    out.push_str(&adt.type_name);
    out.push_str(" {\n");
    // Variants iterate in `BTreeMap` order (sorted by (tag, arity)).
    // Arity may VARY across variants of one block — a class with no
    // registry conflict is a single ADT (`None` arity 0 + `Some(T)`
    // arity 1), so each variant emits its own field count.
    for (variant, variant_name) in &adt.variant_names {
        out.push_str("  ");
        out.push_str(variant_name);
        if variant.arity > 0 {
            out.push('(');
            for i in 0..variant.arity {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str("Data");
            }
            out.push(')');
        }
        out.push('\n');
    }
    out.push_str("}\n\n");
}

/// Walk `expr` collecting every [`TypeHintId`] that appears on a
/// `Constr.type_hint` or `WhenPattern::Constructor.type_hint`. Used by
/// [`prune_unused_stub_adts`] to drop synthetic decls whose hint no
/// longer resolves — a later render-prep pass (church-Bool recovery,
/// constructor-helper inline) can erase every reference to a stub type
/// that [`collect_unresolved_constr_shapes`] recorded.
pub(crate) fn collect_referenced_type_hints(
    expr: &PseudoExpr,
) -> std::collections::HashSet<TypeHintId> {
    let mut out = std::collections::HashSet::new();
    collect_referenced_type_hints_inner(expr, &mut out);
    out
}

fn collect_referenced_type_hints_inner(
    expr: &PseudoExpr,
    out: &mut std::collections::HashSet<TypeHintId>,
) {
    enum Pending<'a> {
        Expr(&'a PseudoExpr),
        Pattern(&'a WhenPattern),
    }
    let mut pending = vec![Pending::Expr(expr)];
    while let Some(item) = pending.pop() {
        let expr = match item {
            Pending::Pattern(pattern) => {
                match pattern {
                    WhenPattern::Constructor { type_hint, .. } => {
                        if let Some(h) = type_hint {
                            out.insert(h.clone());
                        }
                    }
                    WhenPattern::Literal(expr) => pending.push(Pending::Expr(expr)),
                    _ => {}
                }
                continue;
            }
            Pending::Expr(expr) => expr,
        };
        match expr {
            PseudoExpr::Constr {
                type_hint, fields, ..
            } => {
                if let Some(h) = type_hint {
                    out.insert(h.clone());
                }
                for f in fields.iter().rev() {
                    pending.push(Pending::Expr(f));
                }
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for clause in clauses.iter().rev() {
                    pending.push(Pending::Expr(&clause.body));
                    if let Some(g) = &clause.guard {
                        pending.push(Pending::Expr(g));
                    }
                    pending.push(Pending::Pattern(&clause.pattern));
                }
                pending.push(Pending::Expr(subject));
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(Pending::Expr(body));
                pending.push(Pending::Expr(value));
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(Pending::Expr(body));
            }
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(Pending::Expr(a));
                }
                pending.push(Pending::Expr(function));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(Pending::Expr(else_branch));
                pending.push(Pending::Expr(then_branch));
                pending.push(Pending::Expr(condition));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push(Pending::Expr(t));
                }
                for e in elements.iter().rev() {
                    pending.push(Pending::Expr(e));
                }
            }
            PseudoExpr::Tuple(items) => {
                for i in items.iter().rev() {
                    pending.push(Pending::Expr(i));
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(Pending::Expr(b));
                pending.push(Pending::Expr(a));
            }
            PseudoExpr::FieldAccess { record, .. } => {
                pending.push(Pending::Expr(record));
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                pending.push(Pending::Expr(collection));
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(Pending::Expr(right));
                pending.push(Pending::Expr(left));
            }
            PseudoExpr::UnOp { operand, .. } => {
                pending.push(Pending::Expr(operand));
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(Pending::Expr(a));
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                pending.push(Pending::Expr(inner));
            }
            PseudoExpr::Trace { message, value } => {
                pending.push(Pending::Expr(value));
                pending.push(Pending::Expr(message));
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
}

/// Drop stub-ADT decls whose [`TypeHintId`] is not in `referenced`.
/// Cardano-canonical overrides (`TxInfo`, `ScriptContext`, …) survive:
/// [`override_cardano_stub_adt_names`] rewrites the type name but keeps
/// the hint, which still appears in the AST.
pub(crate) fn prune_unused_stub_adts(
    names: &mut StubAdtNames,
    referenced: &std::collections::HashSet<TypeHintId>,
) {
    names.by_scrutinee.retain(|_vid, class| {
        class
            .shards
            .retain(|_arity, adt| referenced.contains(&adt.type_hint));
        !class.shards.is_empty()
    });
    names
        .by_arity
        .retain(|_arity, adt| referenced.contains(&adt.type_hint));
}

/// Merge structurally-identical stub-ADT classes into one canonical
/// type. Distinct scrutinee classes often share a variant set (the
/// same `(tag, arity)` pairs) because the Plutus code reuses one ADT
/// across binders, and rendering each as its own `Unknown_S_NN` fills
/// the module header with isomorphic decls.
///
/// This pass:
/// 1. Groups stub-ADT shards by their variant-set `(tag, arity)` keys.
///    Only `Unknown_S_*` type names participate — Cardano-overridden
///    names (`TxInfo`, `ScriptContext`, …) are excluded.
/// 2. Picks a canonical hint per group (lowest ordinal).
/// 3. Rewrites every non-canonical `Constr.type_hint` /
///    `WhenPattern::Constructor.type_hint` in `expr` to the canonical
///    hint, so the renderer resolves them all to one name.
/// 4. Drops non-canonical entries from `names` so the prefix emits one
///    decl per equivalence class.
///
/// Returns `(rewritten_expr, merged_count)`. Safe to run after DCE.
pub(crate) fn merge_isomorphic_stub_adts(
    names: &mut StubAdtNames,
    expr: PseudoExpr,
    observed_arities: &HashMap<(TypeHintId, usize), usize>,
    cardano_sum_scrutinees: &std::collections::HashSet<VarId>,
) -> (PseudoExpr, usize) {
    use super::field_kind_inference::{ScalarKind, infer_arm_field_scalars};
    use std::collections::HashMap;
    // Per-class CONCRETE field-decode signatures from the PRE-merge
    // tree (every class still carries its own hint here). Two classes
    // whose same (tag, field) slot decodes as two DIFFERENT concrete
    // scalars (`un_b_data` at one class's arms, `un_i_data` at the
    // other's) are NOT one type — merging an Int-decoded record with a
    // ByteArray-decoded one declares a lie. Soft kinds (Unknown /
    // Opaque / Conflict — helper-call and pass-through sites) never
    // block a merge and never force a split: only concrete-vs-concrete
    // disagreement separates classes, fail-closed in both directions.
    let scalar_table = infer_arm_field_scalars(&expr);
    let mut signatures: HashMap<TypeHintId, HashMap<(usize, usize), ScalarKind>> = HashMap::new();
    for ((hint, tag, idx), kind) in &scalar_table {
        if matches!(
            kind,
            ScalarKind::ByteArray | ScalarKind::Int | ScalarKind::OtherData
        ) {
            signatures
                .entry(hint.clone())
                .or_default()
                .insert((*tag, *idx), *kind);
        }
    }
    // Per-class OBSERVED payload arities, measured by the caller on a
    // PREPARED pre-merge view of this tree (see
    // `collect_stub_pattern_arities`).
    //
    // Neither the variant key below nor this tree can supply them. In
    // the un-prepared AST the arms are still nullary — the binders are
    // materialized from `<subject>.fields[N]` accesses during prepare —
    // and `StubVariant::arity` is 0 for every destructuring class until
    // `reconcile_declared_arities` runs, much later. So without this the
    // key degenerates to "which TAGS does this class match", and every
    // two-variant `{0, 1}` class in a program looks isomorphic to every
    // other. In one V3 script that merged five unrelated types into a
    // single stub, among them the `ScriptInfo` (`Minting` 1 field,
    // `Spending` 2) and a record binding 3 ints at tag 1 — after which
    // `unify_constructor_pattern_arity` padded the spend arm to
    // `(_, _, _)` and the ScriptInfo naming, which checks each arm
    // against the ABI arity, correctly refused to name the whole `when`.
    //
    // Only POSITIVE counts are evidence. A site that binds no fields
    // says nothing — it may be a genuine nullary constructor or just an
    // undestructured match — so it stays compatible with anything, the
    // same fail-open direction the soft scalar kinds take. Two classes
    // separate only when both POSITIVELY bind a different number of
    // fields at the same tag, which no single type can do.
    let mut arities: HashMap<TypeHintId, HashMap<usize, usize>> = HashMap::new();
    for ((hint, tag), n) in observed_arities {
        if *n > 0 {
            arities.entry(hint.clone()).or_default().insert(*tag, *n);
        }
    }
    // Group shards by their variant key-set.
    let mut groups: HashMap<Vec<StubVariant>, Vec<TypeHintId>> = HashMap::new();
    // The classes are keyed by the alias-canonical representative of
    // their scrutinee, so put the caller's raw subject ids through the
    // same resolution before comparing — `let y = x; when y is …` is
    // filed under `x`, and a skip that silently fails to apply is worse
    // than no skip at all.
    let alias = build_alias_analysis(&expr);
    let cardano_classes: std::collections::HashSet<VarId> = cardano_sum_scrutinees
        .iter()
        .map(|id| alias.canonical(*id))
        .collect();
    for (vid, class) in &names.by_scrutinee {
        // A class whose `when` subject the context schema types as a
        // Cardano sum keeps its own identity: its constructors are named
        // from the ABI, not from this pool, and joining the pool only
        // exposes it to the arity padding that follows the merge — which
        // is what stopped a V3 `when script_info is { … }` from
        // rendering `Spending(..)`.
        if cardano_classes.contains(vid) {
            continue;
        }
        for adt in class.shards.values() {
            if !adt.type_name.starts_with("Unknown_S_") {
                continue;
            }
            let mut key: Vec<StubVariant> = adt.variant_names.keys().copied().collect();
            key.sort();
            groups.entry(key).or_default().push(adt.type_hint.clone());
        }
    }
    // Build redirect map (non-canonical → canonical) per group,
    // compat-partitioning each variant-key-set bucket by the concrete
    // signatures. Greedy first-fit in ordinal order (deterministic): a
    // class joins the first subgroup with no concrete disagreement and
    // contributes its concrete slots to the subgroup's accumulator.
    let mut redirect: HashMap<TypeHintId, TypeHintId> = HashMap::new();
    let mut merged = 0usize;
    for (_, mut hints) in groups {
        hints.sort_by_key(|h| extract_unknown_s_ord(h.as_str()).unwrap_or(usize::MAX));
        // Dedup (same hint registered under multiple arity keys in a
        // class — only keep the first occurrence).
        hints.dedup_by(|a, b| a == b);
        if hints.len() < 2 {
            continue;
        }
        type Subgroup = (
            Vec<TypeHintId>,
            HashMap<(usize, usize), ScalarKind>,
            HashMap<usize, usize>,
        );
        let mut subgroups: Vec<Subgroup> = Vec::new();
        'hints: for h in hints {
            let sig = signatures.get(&h).cloned().unwrap_or_default();
            let ar = arities.get(&h).cloned().unwrap_or_default();
            for (members, acc, acc_ar) in subgroups.iter_mut() {
                let compatible = sig
                    .iter()
                    .all(|(slot, kind)| acc.get(slot).is_none_or(|a| a == kind))
                    && ar
                        .iter()
                        .all(|(tag, n)| acc_ar.get(tag).is_none_or(|a| a == n));
                if compatible {
                    for (slot, kind) in sig {
                        acc.insert(slot, kind);
                    }
                    for (tag, n) in ar {
                        acc_ar.insert(tag, n);
                    }
                    members.push(h);
                    continue 'hints;
                }
            }
            subgroups.push((vec![h], sig, ar));
        }
        for (members, _, _) in subgroups {
            if members.len() < 2 {
                continue;
            }
            let canonical = members[0].clone();
            for h in &members[1..] {
                redirect.insert(h.clone(), canonical.clone());
                merged += 1;
            }
        }
    }
    if merged == 0 {
        return (expr, 0);
    }
    let new_expr = rewrite_type_hints(expr, &redirect);
    let drop_hints: std::collections::HashSet<TypeHintId> = redirect.keys().cloned().collect();
    names.by_scrutinee.retain(|_vid, class| {
        class
            .shards
            .retain(|_, adt| !drop_hints.contains(&adt.type_hint));
        !class.shards.is_empty()
    });
    (new_expr, merged)
}

/// Parse the numeric ordinal out of `Unknown_S_<N>` / `Unknown_S_<N>_A<M>`
/// so isomorphic-group canonical selection picks the lowest-ordinal
/// member deterministically (stable rendering).
fn extract_unknown_s_ord(name: &str) -> Option<usize> {
    let rest = name.strip_prefix("Unknown_S_")?;
    // Strip optional `_A<M>` shard suffix (conflict shard form).
    let head = rest.split_once('_').map(|(h, _)| h).unwrap_or(rest);
    head.parse().ok()
}

fn rewrite_type_hints(
    expr: PseudoExpr,
    redirect: &std::collections::HashMap<TypeHintId, TypeHintId>,
) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    struct Rewriter<'a> {
        redirect: &'a std::collections::HashMap<TypeHintId, TypeHintId>,
    }

    impl ExprFolder for Rewriter<'_> {
        fn post_constr(
            &mut self,
            type_hint: Option<TypeHintId>,
            tag: usize,
            fields: Vec<PseudoExpr>,
            shape: ConstructorShape,
        ) -> PseudoExpr {
            PseudoExpr::Constr {
                type_hint: type_hint.map(|h| self.redirect.get(&h).cloned().unwrap_or(h)),
                tag,
                fields: fields.into(),
                shape,
            }
        }

        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            match pattern {
                WhenPattern::Constructor {
                    type_hint,
                    tag,
                    fields,
                    shape,
                } => WhenPattern::Constructor {
                    type_hint: type_hint.map(|h| self.redirect.get(&h).cloned().unwrap_or(h)),
                    tag,
                    fields,
                    shape,
                },
                WhenPattern::Literal(expr) => WhenPattern::Literal(self.fold(expr)),
                other => other,
            }
        }
    }

    Rewriter { redirect }.fold(expr)
}

/// Rewrite every unresolved `Constr { shape: Unknown, type_hint: None,
/// .. }` node in `expr` to carry the minted synthetic `TypeHintId`, so
/// the renderer's lookup chain (`pseudo/pretty/mod.rs`) resolves each
/// Constr to its `Unknown_S_<ord>_<tag>` / `Unknown_E_<arity>_<tag>`
/// variant name.
///
/// Mirrors the collector: pattern-position `Constructor`s inside
/// `when X is { ... }` get the scrutinee class's hint; expression-
/// position `Constr`s get the arity bucket's hint.
pub(crate) fn rewrite_unresolved_constrs(expr: PseudoExpr, names: &StubAdtNames) -> PseudoExpr {
    // Build the same alias + let-value analysis the collector used
    // so the rewriter can canonicalize aliased `When` subjects AND
    // route let-bound value-position Constrs to the scrutinee class's
    // type-hint instead of the arity-bucket fallback.
    let analysis = build_alias_analysis(&expr);
    rewrite(expr, names, &analysis)
}

/// Map a known Cardano binder name + `Constr` arity to a canonical
/// type name, so `override_cardano_stub_adt_names` can rename
/// `Unknown_S_N` to `TxInfo` / `ScriptContext` when the scrutinee is
/// a recognized Cardano context binder. `None` when the pair pins no
/// canonical type.
///
/// The rendered `pub type X { X(Data, ..., Data) }` block uses
/// `type_name`; constructor sites use `variant_name`.
fn cardano_canonical_name_for_scrutinee(
    binder_name: &str,
    arity: usize,
) -> Option<(&'static str, &'static str)> {
    match (binder_name, arity) {
        // V1/V2 ScriptContext: (tx_info, purpose) — 2 fields
        ("script_context", 2) => Some(("ScriptContext", "ScriptContext")),
        // V3 ScriptContext: (tx_info, redeemer, script_info) — 3 fields
        ("script_context", 3) => Some(("ScriptContext", "ScriptContext")),
        // TxInfo: arity 10 (V1), 12 (V2), 16 (V3)
        ("tx_info", 10) | ("tx_info", 12) | ("tx_info", 16) => Some(("TxInfo", "TxInfo")),
        // Interval (valid_range field of TxInfo): (lower_bound, upper_bound)
        ("valid_range", 2) => Some(("Interval", "Interval")),
        // IntervalBound destructure (lower_bound or upper_bound):
        // (bound_type, is_inclusive)
        ("lower_bound", 2) | ("upper_bound", 2) => Some(("IntervalBound", "IntervalBound")),
        _ => None,
    }
}

/// Walk `expr` collecting VarIds of let-binders bound to
/// `script_context.fields.head` — these are tx_info-equivalent
/// for V1/V2 ScriptContext (where field 0 is the tx_info).
fn collect_tx_info_aliases(expr: &PseudoExpr) -> BTreeSet<VarId> {
    let mut out = BTreeSet::new();
    collect_tx_info_aliases_inner(expr, &mut out);
    out
}

fn collect_tx_info_aliases_inner(expr: &PseudoExpr, out: &mut BTreeSet<VarId>) {
    use crate::pseudo::field_selector::FieldSelector;
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(let_id),
            value,
            ..
        } = expr
        {
            // Recognize `let X = script_context.fields.head` and
            // `let X = script_context.fields[0]` — both resolve to
            // tx_info on V1/V2 ScriptContext.
            let is_sc_head = match value.as_ref() {
                PseudoExpr::FieldAccess { record, selector } => {
                    let head_match = matches!(selector, FieldSelector::ListHead);
                    let inner_fields_match = matches!(
                        record.as_ref(),
                        PseudoExpr::FieldAccess { record: r, selector: s }
                            if matches!(s, FieldSelector::NamedField(n) if n == "fields")
                                && matches!(
                                    r.as_ref(),
                                    PseudoExpr::Var { name, .. } if name == "script_context"
                                )
                    );
                    head_match && inner_fields_match
                }
                PseudoExpr::IndexAccess { collection, index } => {
                    *index == 0
                        && matches!(
                            collection.as_ref(),
                            PseudoExpr::FieldAccess { record, selector }
                                if matches!(selector, FieldSelector::NamedField(n) if n == "fields")
                                    && matches!(
                                        record.as_ref(),
                                        PseudoExpr::Var { name, .. } if name == "script_context"
                                    )
                        )
                }
                _ => false,
            };
            if is_sc_head {
                out.insert(*let_id);
            }
        }
        match expr {
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                    if let Some(g) = &c.guard {
                        pending.push(g);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push(f);
                }
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push(t);
                }
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Tuple(elements) => {
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            _ => {}
        }
    }
}

/// Walk `expr` collecting `VarId → name` for every binder.
fn collect_var_id_to_name(expr: &PseudoExpr) -> BTreeMap<VarId, String> {
    let mut map = BTreeMap::new();
    collect_var_id_to_name_inner(expr, &mut map);
    map
}

fn collect_var_id_to_name_inner(expr: &PseudoExpr, out: &mut BTreeMap<VarId, String>) {
    enum Pending<'a> {
        Expr(&'a PseudoExpr),
        ClausePatternFields(&'a WhenClause),
    }
    let mut pending = vec![Pending::Expr(expr)];
    while let Some(item) = pending.pop() {
        let expr = match item {
            Pending::ClausePatternFields(c) => {
                if let WhenPattern::Constructor { fields, .. } = &c.pattern {
                    for b in fields {
                        out.entry(b.var_id()).or_insert_with(|| b.to_string());
                    }
                }
                continue;
            }
            Pending::Expr(expr) => expr,
        };
        match expr {
            PseudoExpr::Let {
                name,
                id: Some(vid),
                value,
                body,
            } => {
                out.entry(*vid).or_insert_with(|| name.clone());
                pending.push(Pending::Expr(body));
                pending.push(Pending::Expr(value));
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(Pending::Expr(body));
                pending.push(Pending::Expr(value));
            }
            PseudoExpr::Lambda { params, body } => {
                for b in params {
                    out.entry(b.var_id()).or_insert_with(|| b.to_string());
                }
                pending.push(Pending::Expr(body));
            }
            PseudoExpr::RecFn { name, params, body } => {
                out.entry(name.var_id()).or_insert_with(|| name.to_string());
                for b in params {
                    out.entry(b.var_id()).or_insert_with(|| b.to_string());
                }
                pending.push(Pending::Expr(body));
            }
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(Pending::Expr(a));
                }
                pending.push(Pending::Expr(function));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(Pending::Expr(else_branch));
                pending.push(Pending::Expr(then_branch));
                pending.push(Pending::Expr(condition));
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push(Pending::Expr(&c.body));
                    if let Some(g) = &c.guard {
                        pending.push(Pending::Expr(g));
                    }
                    pending.push(Pending::ClausePatternFields(c));
                }
                pending.push(Pending::Expr(subject));
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(Pending::Expr(right));
                pending.push(Pending::Expr(left));
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(Pending::Expr(operand)),
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push(Pending::Expr(f));
                }
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(Pending::Expr(a));
                }
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push(Pending::Expr(t));
                }
                for e in elements.iter().rev() {
                    pending.push(Pending::Expr(e));
                }
            }
            PseudoExpr::Tuple(elements) => {
                for e in elements.iter().rev() {
                    pending.push(Pending::Expr(e));
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(Pending::Expr(b));
                pending.push(Pending::Expr(a));
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(Pending::Expr(record)),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(Pending::Expr(collection)),
            PseudoExpr::Trace { message, value } => {
                pending.push(Pending::Expr(value));
                pending.push(Pending::Expr(message));
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                pending.push(Pending::Expr(inner))
            }
            _ => {}
        }
    }
}

/// Override the synthesized `Unknown_S_<ord>` stub-ADT names with
/// canonical Cardano type names (`TxInfo`, `ScriptContext`, …)
/// when the scrutinee binder's name matches a recognized Cardano
/// context binder AND the Constr's arity matches that type's
/// canonical arity.
///
/// Mutates both:
/// - `names` — the class's `type_name` / `variant_names`, so
///   `format_stub_adt_prefix` declares `pub type TxInfo`.
/// - `registry` — the variant-name lookup, so the pretty printer
///   emits `TxInfo(...)` at pattern and constructor positions.
///
/// Runs AFTER `register_stub_adts_in_registry`, whose synthetic
/// names it overrides, and BEFORE `format_stub_adt_prefix`, which
/// reads `names`.
pub(crate) fn override_cardano_stub_adt_names(
    expr: &PseudoExpr,
    names: &mut StubAdtNames,
    registry: &mut BlueprintHintRegistry,
) -> Vec<(VarId, crate::decompile::simplify::postprocess::ContextType)> {
    use crate::decompile::simplify::postprocess::ContextType;

    let var_names = collect_var_id_to_name(expr);
    let alias_to_tx_info = collect_tx_info_aliases(expr);
    let mut updates: Vec<(VarId, &'static str, &'static str)> = Vec::new();
    // Schema-descent roots: classes overridden by NAME whose
    // `ContextType` layout the descent below can walk into.
    let mut work: Vec<(VarId, ContextType)> = Vec::new();
    let mut typed: std::collections::BTreeSet<VarId> = std::collections::BTreeSet::new();

    // NAME-seeded overrides. Only binder names minted by the
    // PIPELINE are reliable here (`script_context`, the `tx_info`
    // pattern binder / aliases). Names minted later inside
    // `prepare_for_render` (`valid_range`, `lower_bound`, …) do NOT
    // exist yet on this tree — those classes are reached by the
    // schema descent instead.
    for (vid, class) in &names.by_scrutinee {
        // Direct binder-name match OR alias resolution: `let head =
        // script_context.fields.head` makes `head` a tx_info-equivalent
        // binder at index 0 of the V1/V2 ScriptContext layout.
        let raw_name = var_names.get(vid).map(|s| s.as_str()).unwrap_or("");
        let binder_name = if alias_to_tx_info.contains(vid) {
            "tx_info"
        } else {
            raw_name
        };
        if binder_name.is_empty() {
            continue;
        }
        // Override only a SINGLE-variant shard whose arity matches a
        // canonical Cardano shape — multi-variant types (Bool) match
        // none.
        for (arity, adt) in &class.shards {
            if adt.variant_names.len() != 1 {
                continue;
            }
            let Some((type_name, variant_name)) =
                cardano_canonical_name_for_scrutinee(binder_name, *arity)
            else {
                continue;
            };
            updates.push((*vid, type_name, variant_name));
            if let Some(ct) = context_type_for_decl_name(type_name) {
                if typed.insert(*vid) {
                    work.push((*vid, ct));
                }
            }
        }
    }

    // The descent and updates application live in `run_schema_descent`
    // so `override_list_element_stub_adts` — the second pass, over the
    // PREPARED tree where rec-fn iteration shapes exist — reuses the
    // identical machinery.

    run_schema_descent(expr, expr, names, registry, updates, work, typed)
}

/// The Cardano override's schema-position descent and
/// the updates application. Shared by the pipeline-tree pass
/// (`override_cardano_stub_adt_names`) and the prepared-tree
/// list-element pass (`override_list_element_stub_adts`). Returns every
/// (scrutinee, ContextType) the run typed — seeds plus discoveries.
fn run_schema_descent(
    slots_expr: &PseudoExpr,
    flow_expr: &PseudoExpr,
    names: &mut StubAdtNames,
    registry: &mut BlueprintHintRegistry,
    mut updates: Vec<(VarId, &'static str, &'static str)>,
    mut work: Vec<(VarId, crate::decompile::simplify::postprocess::ContextType)>,
    mut typed: std::collections::BTreeSet<VarId>,
) -> Vec<(VarId, crate::decompile::simplify::postprocess::ContextType)> {
    use crate::decompile::simplify::postprocess::{
        FieldTypeRef, context_field_at, context_field_type,
    };
    let mut typed_pairs: Vec<(VarId, crate::decompile::simplify::postprocess::ContextType)> =
        work.clone();
    // SCHEMA-POSITION descent (name-independent). Binder `i` of a typed
    // `ContextType` record has child type `context_field_at(ct, i,
    // version)`; a class scrutinized on that binder (VarId-canonical)
    // whose single tag-0 variant matches the child layout's arity IS the
    // child record — override and recurse. The version is SELF-EVIDENT
    // from the observed arity (`version_for_record_arity`: TxInfo
    // 10/12/16, ScriptContext 2/3 discriminate; ties only where the
    // tying layouts are identical). Fail-closed at every step: unknown
    // field type, non-record child, arity with no unique layout,
    // multi-variant or non-tag-0 class — all skip.
    // Slot linkage (pattern binders / projections) comes from the SAME
    // tree the classes were collected on (`slots_expr` — class keys are
    // its canonical scrutinee ids); the list-element DATAFLOW index
    // reads `flow_expr`, which for the prepared-tree pass carries the
    // rec-fn iteration shapes the y-comb unfolds minted (binder ids are
    // shared between the trees; prepare re-mints only duplicates).
    let scrutinee_fields = collect_scrutinee_field_binders(slots_expr);
    let projection_aliases = collect_field_projection_aliases(slots_expr);
    let list_index = super::list_element_provenance::ListIterationIndex::build(flow_expr);
    // OUTER FIXPOINT (full-coverage): the list-element and union-param
    // links depend on what is already typed (an element claim for a
    // helper param may only appear after a sibling record types), so
    // the inner worklist drains repeatedly until the typed set stops
    // growing. Per-element-type list ROOTS accumulate across rounds —
    // sibling co-typed list fields (inputs + reference_inputs) must be
    // unioned BEFORE the member fixpoint or a shared iteration helper
    // never qualifies.
    use crate::decompile::simplify::postprocess::{CardanoTypeRef, sum_type_constructor_fields};
    let mut list_roots: Vec<(
        crate::decompile::simplify::postprocess::ContextType,
        std::collections::BTreeSet<VarId>,
    )> = Vec::new();
    // Record-typed SLOT binders, classed or not: a pattern binder like
    // TxInInfo's `resolved` (a TxOut) often flows STRAIGHT into a
    // helper without its own destructure — no class, but a perfectly
    // good union-claim for the param pass.
    let mut field_claims: std::collections::BTreeMap<
        VarId,
        crate::decompile::simplify::postprocess::ContextType,
    > = std::collections::BTreeMap::new();
    loop {
        let typed_before = typed.len();
        while let Some((vid, ctype)) = work.pop() {
            let Some(version) = names
                .by_scrutinee
                .get(&vid)
                .and_then(single_tag0_arity)
                .and_then(|arity| version_for_record_arity(ctype, arity))
            else {
                continue;
            };
            // Two linkage forms reach a child record's scrutinee: the
            // destructure PATTERN binder at field index i, and a
            // PROJECTION alias `let X = <scrutinee>.fields.head` /
            // `.fields[i]` (church residue re-projects fields
            // positionally instead of using the recovered binder).
            let mut child_slots: Vec<(usize, VarId)> = Vec::new();
            if let Some(arms) = scrutinee_fields.get(&vid) {
                for (tag, binders) in arms {
                    if *tag != 0 {
                        continue;
                    }
                    for (idx, binder) in binders.iter().enumerate() {
                        if let Some(b) = binder {
                            child_slots.push((idx, *b));
                        }
                    }
                }
            }
            if let Some(projected) = projection_aliases.get(&vid) {
                child_slots.extend(projected.iter().copied());
            }
            for (idx, binder) in child_slots {
                let Some(field) = context_field_at(ctype, idx, version) else {
                    continue;
                };
                match crate::decompile::simplify::postprocess::context_field_type_full(
                    field, version,
                ) {
                    // A LIST-typed field (outputs: List<TxOut>) — record
                    // the root; elements/params resolve after the drain,
                    // against the UNION of co-typed roots.
                    Some(CardanoTypeRef::ListOfRecords(elem_ct)) => {
                        if decl_names_for_context_type(elem_ct).is_some() {
                            match list_roots.iter_mut().find(|(ct, _)| *ct == elem_ct) {
                                Some((_, roots)) => {
                                    roots.insert(binder);
                                }
                                None => {
                                    let mut roots = std::collections::BTreeSet::new();
                                    roots.insert(binder);
                                    list_roots.push((elem_ct, roots));
                                }
                            }
                        }
                        continue;
                    }
                    // A SUM-typed field: the binder's `when` arms are
                    // schema constructors — their PAYLOAD binders carry
                    // ABI-fixed types (Spending(output_reference:
                    // TxOutRef), governance arms carrying ProtocolVersion /
                    // RationalNumber / Constitution / GovActionId).
                    // Per-arm: the tag must resolve in the sum's table
                    // and the payload arity must match; record-typed
                    // payloads qualify through the standard gates.
                    Some(CardanoTypeRef::Sum(sum_id)) => {
                        let Some(arms) = scrutinee_fields.get(&binder) else {
                            continue;
                        };
                        for (tag, payload_binders) in arms {
                            let Some(payload_fields) =
                                sum_type_constructor_fields(sum_id, *tag, version)
                            else {
                                continue;
                            };
                            if payload_fields.len() != payload_binders.len() {
                                continue;
                            }
                            for (pi, pb) in payload_binders.iter().enumerate() {
                                let Some(pb) = pb else { continue };
                                let Some((_, Some(FieldTypeRef::Context(payload_ct)))) =
                                    payload_fields.get(pi)
                                else {
                                    continue;
                                };
                                field_claims.insert(*pb, *payload_ct);
                                try_type_candidate(
                                    *pb,
                                    *payload_ct,
                                    names,
                                    &mut typed,
                                    &mut typed_pairs,
                                    &mut updates,
                                    &mut work,
                                );
                            }
                        }
                        continue;
                    }
                    _ => {}
                }
                let Some(FieldTypeRef::Context(child_ct)) = context_field_type(field, version)
                else {
                    continue;
                };
                field_claims.insert(binder, child_ct);
                try_type_candidate(
                    binder,
                    child_ct,
                    names,
                    &mut typed,
                    &mut typed_pairs,
                    &mut updates,
                    &mut work,
                );
            }
        }
        // List resolution: per element type, elements from the UNION of
        // roots; then helper params via UNION claims — a param types
        // when EVERY call site's slot arg is a proven element and all
        // claims agree on one element type (a helper fed TxOut at one
        // site and a TxInInfo at another never types).
        let mut element_claims: std::collections::BTreeMap<
            VarId,
            crate::decompile::simplify::postprocess::ContextType,
        > = std::collections::BTreeMap::new();
        // Conflict tombstones: an element claimed under two DIFFERENT
        // types never claims again. The cross-set membership gate makes
        // that unreachable; the tombstone makes the fail-closed promise
        // structural rather than incidental.
        let mut claim_tombstones: std::collections::BTreeSet<VarId> =
            std::collections::BTreeSet::new();
        let mut member_claims: std::collections::BTreeMap<
            VarId,
            crate::decompile::simplify::postprocess::ContextType,
        > = std::collections::BTreeMap::new();
        for (elem_ct, roots) in &list_roots {
            let elements = list_index.element_binders_of(roots);
            let members = list_index.members_of(roots);
            for e in &elements {
                if claim_tombstones.contains(e) {
                    continue;
                }
                match element_claims.entry(*e) {
                    std::collections::btree_map::Entry::Vacant(v) => {
                        v.insert(*elem_ct);
                    }
                    std::collections::btree_map::Entry::Occupied(o) => {
                        if *o.get() != *elem_ct {
                            // Conflicting element types — tombstone the
                            // element so neither claim survives.
                            element_claims.remove(e);
                            claim_tombstones.insert(*e);
                        }
                    }
                }
                if element_claims.contains_key(e) {
                    try_type_candidate(
                        *e,
                        *elem_ct,
                        names,
                        &mut typed,
                        &mut typed_pairs,
                        &mut updates,
                        &mut work,
                    );
                }
            }
            for m in &members {
                member_claims.insert(*m, *elem_ct);
            }
        }
        // typed-record + record-typed-slot claims: a binder already
        // typed as a record, OR a record-typed slot binder with no
        // class of its own (TxInInfo's `resolved` flowing straight
        // into a helper), is a valid element claim for params fed
        // from it — one helper can take the outputs cons-head at one
        // site and TxInInfo.resolved at the other, both TxOut.
        for (vid, ct) in &typed_pairs {
            if !claim_tombstones.contains(vid) {
                element_claims.entry(*vid).or_insert(*ct);
            }
        }
        for (vid, ct) in &field_claims {
            if !claim_tombstones.contains(vid) {
                element_claims.entry(*vid).or_insert(*ct);
            }
        }
        for (pid, p_ct) in list_index.params_with_agreed_claims(&element_claims, &member_claims) {
            try_type_candidate(
                pid,
                p_ct,
                names,
                &mut typed,
                &mut typed_pairs,
                &mut updates,
                &mut work,
            );
        }
        if typed.len() == typed_before && work.is_empty() {
            break;
        }
    }

    for (vid, new_type_name, new_variant_name) in updates {
        let Some(class) = names.by_scrutinee.get_mut(&vid) else {
            continue;
        };
        for adt in class.shards.values_mut() {
            // Override the type name shown at the `pub type X { ... }`
            // declaration site.
            adt.type_name = new_type_name.to_string();
            adt.cardano_record = true;
            // Override each variant's name (single variant in this path).
            for (variant, name) in adt.variant_names.iter_mut() {
                *name = new_variant_name.to_string();
                // Re-register so the renderer's resolve() returns the
                // canonical name at use sites.
                registry.register_user(
                    adt.type_hint.clone(),
                    variant.tag,
                    new_variant_name.to_string(),
                );
            }
        }
    }
    typed_pairs
}

/// Give the typed record destructures their SCHEMA field names.
/// `expect TxOut(field_0, map, variant) = x_123` reads positionally;
/// the schema says those fields are `address`, `value`, `datum_hash`.
/// Scoped to the types the prepare-time `rename_tx_info_binders` table
/// does NOT already cover, so the two renamers never disagree.
/// Display-only: binder ids kept, uses rewired by VarId;
/// already-schema-named binders are skipped (idempotent).
pub(crate) fn rename_typed_record_field_binders(
    expr: PseudoExpr,
    names: &StubAdtNames,
    typed: &[(VarId, crate::decompile::simplify::postprocess::ContextType)],
) -> PseudoExpr {
    use crate::decompile::simplify::postprocess::{ContextType as T, context_field_at};
    let mut renames: Vec<(VarId, VarId, Vec<Option<&'static str>>)> = Vec::new();
    for (vid, ctype) in typed {
        if !matches!(
            ctype,
            T::TxOut
                | T::Address
                | T::TxOutRef
                | T::TxInInfo
                | T::ProposalProcedure
                | T::ProtocolVersion
                | T::RationalNumber
                | T::Constitution
                | T::GovActionId
        ) {
            continue;
        }
        let Some(version) = names
            .by_scrutinee
            .get(vid)
            .and_then(single_tag0_arity)
            .and_then(|arity| version_for_record_arity(*ctype, arity))
        else {
            continue;
        };
        let arity = names
            .by_scrutinee
            .get(vid)
            .and_then(single_tag0_arity)
            .unwrap_or(0);
        let field_names: Vec<Option<&'static str>> = (0..arity)
            .map(|i| context_field_at(*ctype, i, version).map(|f| f.display_name()))
            .collect();
        renames.push((*vid, *vid, field_names));
    }
    if renames.is_empty() {
        return expr;
    }
    let analysis = build_alias_analysis(&expr);
    let by_subject: std::collections::BTreeMap<VarId, Vec<Option<&'static str>>> = renames
        .into_iter()
        .map(|(vid, _, fields)| (vid, fields))
        .collect();
    rename_fields_walk(expr, &by_subject, &analysis)
}

/// One job on [`rename_fields_walk`]'s stack.
enum RenameStep {
    Visit(PseudoExpr),
    Post(RenamePost),
}

enum RenamePost {
    /// Each clause carries the pattern already rewritten at Visit time (it reads the
    /// UN-walked subject, ) plus the binder renames to substitute into THAT clause's
    /// body and guard — after the clause's own descent
    /// returned.
    When {
        subject_name: Option<crate::pseudo::ast::Binder>,
        clause_meta: Vec<(WhenPattern, Vec<(VarId, String)>, bool)>,
    },
    Let {
        name: String,
        id: Option<VarId>,
    },
    Lambda {
        params: Vec<crate::pseudo::ast::Binder>,
    },
    RecFn {
        name: crate::pseudo::ast::Binder,
        params: Vec<crate::pseudo::ast::Binder>,
    },
    Plain(PlainPost),
}

/// The per-clause use-site substitution runs BETWEEN the clause's descent and the
/// `When`'s rebuild, so each clause's rename list rides on the post step and is applied
/// there. The pattern rewrite itself needs no walked child, so it stays in the visit
/// arm.
fn rename_fields_walk(
    expr: PseudoExpr,
    by_subject: &std::collections::BTreeMap<VarId, Vec<Option<&'static str>>>,
    analysis: &AliasAnalysis,
) -> PseudoExpr {
    use crate::pseudo::ast::WhenClause;
    let mut steps: Vec<RenameStep> = vec![RenameStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RenameStep::Visit(expr) => match expr {
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let subject_key = scrutinee_var_id(&subject).map(|id| analysis.canonical(id));
                    let field_names = subject_key.and_then(|k| by_subject.get(&k));
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut clause_children = Vec::new();
                    for clause in clauses {
                        let (pattern, renamed) = match (&field_names, clause.pattern) {
                            (
                                Some(fields),
                                WhenPattern::Constructor {
                                    type_hint,
                                    tag: 0,
                                    fields: binders,
                                    shape,
                                },
                            ) => {
                                let mut renamed: Vec<(VarId, String)> = Vec::new();
                                let binders: Vec<crate::pseudo::ast::Binder> = binders
                                    .into_iter()
                                    .enumerate()
                                    .map(|(i, b)| {
                                        let Some(Some(schema)) = fields.get(i) else {
                                            return b;
                                        };
                                        if b.as_str() == *schema {
                                            return b;
                                        }
                                        // `_` binders rename too: the field is
                                        // usually reached by a `.fields[i]`
                                        // projection prepare rewires onto the
                                        // binder; unused ones get the
                                        // `_`-prefix downstream (`_address`
                                        // beats `field_0`).
                                        renamed.push((b.var_id(), (*schema).to_string()));
                                        b.renamed((*schema).to_string())
                                    })
                                    .collect();
                                (
                                    WhenPattern::Constructor {
                                        type_hint,
                                        tag: 0,
                                        fields: binders,
                                        shape,
                                    },
                                    renamed,
                                )
                            }
                            (_, p) => (p, Vec::new()),
                        };
                        // Body first, then guard — the order the recursive
                        // arm walked them in.
                        let has_guard = clause.guard.is_some();
                        clause_children.push(clause.body);
                        if let Some(g) = clause.guard {
                            clause_children.push(g);
                        }
                        clause_meta.push((pattern, renamed, has_guard));
                    }
                    steps.push(RenameStep::Post(RenamePost::When {
                        subject_name,
                        clause_meta,
                    }));
                    // The clauses were walked BEFORE the subject in (the `clauses`
                    // binding was evaluated ahead of the struct literal), so the
                    // subject goes on first and pops last.
                    steps.push(RenameStep::Visit(subject.into_inner()));
                    for c in clause_children.into_iter().rev() {
                        steps.push(RenameStep::Visit(c));
                    }
                }
                // The remaining kinds are `map_children`: every child walked
                // with the same rule, the node rebuilt verbatim. Only the
                // binder-carrying ones need their own arms — the rest are
                // `plain_children` / `rebuild_plain`, and the leaves fall
                // through `Err` untouched (`map_children`'s `other => other`).
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(RenameStep::Post(RenamePost::Let { name, id }));
                    steps.push(RenameStep::Visit(body.into_inner()));
                    steps.push(RenameStep::Visit(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(RenameStep::Post(RenamePost::Lambda { params }));
                    steps.push(RenameStep::Visit(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(RenameStep::Post(RenamePost::RecFn { name, params }));
                    steps.push(RenameStep::Visit(body.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RenameStep::Post(RenamePost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(RenameStep::Visit(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            RenameStep::Post(post) => {
                let rebuilt = match post {
                    RenamePost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let subject = done.pop().expect("when subject");
                        let total = clause_meta
                            .iter()
                            .map(|(_, _, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = take(&mut done, total).into_iter();
                        let clauses = clause_meta
                            .into_iter()
                            .map(|(pattern, renamed, has_guard)| {
                                let mut body = parts.next().expect("when clause body");
                                let mut guard =
                                    has_guard.then(|| parts.next().expect("when guard"));
                                for (bid, new_name) in renamed {
                                    body =
                                        super::rename_var_use_by_id_in_expr(&body, bid, &new_name);
                                    if let Some(g) = guard.take() {
                                        guard = Some(super::rename_var_use_by_id_in_expr(
                                            &g, bid, &new_name,
                                        ));
                                    }
                                }
                                WhenClause {
                                    pattern,
                                    guard,
                                    body,
                                }
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    RenamePost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    RenamePost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    RenamePost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    RenamePost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rename_fields_walk must leave one result");
    done.pop().expect("rename_fields_walk result")
}

/// One candidate through the standard record gates: untyped, has a
/// single-shard single-variant tag-0 class, and its arity admits a
/// (unique-or-identical-tie) version layout for `ct`. On success the
/// class joins updates/typed/work.
#[allow(clippy::too_many_arguments)]
fn try_type_candidate(
    binder: VarId,
    ct: crate::decompile::simplify::postprocess::ContextType,
    names: &StubAdtNames,
    typed: &mut std::collections::BTreeSet<VarId>,
    typed_pairs: &mut Vec<(VarId, crate::decompile::simplify::postprocess::ContextType)>,
    updates: &mut Vec<(VarId, &'static str, &'static str)>,
    work: &mut Vec<(VarId, crate::decompile::simplify::postprocess::ContextType)>,
) {
    if typed.contains(&binder) {
        return;
    }
    let Some((type_name, variant_name)) = decl_names_for_context_type(ct) else {
        return;
    };
    let Some(class) = names.by_scrutinee.get(&binder) else {
        return;
    };
    let Some(arity) = single_tag0_arity(class) else {
        return;
    };
    if version_for_record_arity(ct, arity).is_none() {
        return;
    }
    updates.push((binder, type_name, variant_name));
    typed.insert(binder);
    typed_pairs.push((binder, ct));
    work.push((binder, ct));
}

/// Re-run the schema descent on the PREPARED tree, where the y-comb
/// unfolds have minted the `rec fn` iteration shapes the list-element
/// provenance needs, seeded with everything the pipeline-tree pass
/// already typed. Runs BEFORE `merge_isomorphic_stub_adts` so a class
/// this pass names is excluded from the merge — the Address class
/// would otherwise soft-merge with same-shape data pairs and become
/// un-nameable. VarIds are shared between the pipeline and prepared
/// trees (prepare re-mints only duplicates), so the prepared-tree
/// dataflow keys directly into `names.by_scrutinee`.
pub(crate) fn override_list_element_stub_adts(
    slots_expr: &PseudoExpr,
    prepared: &PseudoExpr,
    names: &mut StubAdtNames,
    registry: &mut BlueprintHintRegistry,
    roots: &[(VarId, crate::decompile::simplify::postprocess::ContextType)],
) -> Vec<(VarId, crate::decompile::simplify::postprocess::ContextType)> {
    if roots.is_empty() {
        return Vec::new();
    }
    let work: Vec<(VarId, crate::decompile::simplify::postprocess::ContextType)> = roots.to_vec();
    let typed: std::collections::BTreeSet<VarId> = roots.iter().map(|(v, _)| *v).collect();
    // Roots are already named by the pipeline-tree pass — start with NO pending
    // updates for them; only discoveries get pushed.
    run_schema_descent(
        slots_expr,
        prepared,
        names,
        registry,
        Vec::new(),
        work,
        typed,
    )
}

/// The declared Cardano record types the schema descent can ENTER (a
/// name seed roots the walk here).
fn context_type_for_decl_name(
    name: &str,
) -> Option<crate::decompile::simplify::postprocess::ContextType> {
    use crate::decompile::simplify::postprocess::ContextType as T;
    match name {
        "ScriptContext" => Some(T::ScriptContext),
        "TxInfo" => Some(T::TxInfo),
        "Interval" => Some(T::Interval),
        // Lower/Upper share one declared name and one layout.
        "IntervalBound" => Some(T::LowerBound),
        _ => None,
    }
}

/// Decl/variant names for record ContextTypes the descent may DISCOVER.
/// Sum types have no entry here — they are named by
/// `name_cardano_sum_arms`/`cardano_type_env`, not the stub override
/// (fail-closed).
fn decl_names_for_context_type(
    ct: crate::decompile::simplify::postprocess::ContextType,
) -> Option<(&'static str, &'static str)> {
    use crate::decompile::simplify::postprocess::ContextType as T;
    match ct {
        T::ScriptContext => Some(("ScriptContext", "ScriptContext")),
        T::TxInfo => Some(("TxInfo", "TxInfo")),
        T::Interval => Some(("Interval", "Interval")),
        T::LowerBound | T::UpperBound => Some(("IntervalBound", "IntervalBound")),
        T::TxOut => Some(("TxOut", "TxOut")),
        T::Address => Some(("Address", "Address")),
        T::TxOutRef => Some(("TxOutRef", "TxOutRef")),
        T::TxInInfo => Some(("TxInInfo", "TxInInfo")),
        // V3 governance records (layouts are V3-only, so
        // version_for_record_arity auto-gates: V1/V2 probes find no
        // layout and never match).
        T::ProposalProcedure => Some(("ProposalProcedure", "ProposalProcedure")),
        T::ProtocolVersion => Some(("ProtocolVersion", "ProtocolVersion")),
        T::RationalNumber => Some(("RationalNumber", "RationalNumber")),
        T::Constitution => Some(("Constitution", "Constitution")),
        T::GovActionId => Some(("GovActionId", "GovActionId")),
        // `TxId` gets NO stub decl. It is a one-field wrapper, and arity 1 with
        // tag 0 is the single most common shape a `Constr` can have, so the
        // record probe would match any unrelated newtype and declare it a
        // TransactionId. Naming `transaction_id.fields[0]` → `.hash` runs off
        // `context_field_at`, which needs a typed parent and so cannot make that
        // mistake; the decl adds nothing but the risk.
        // Same reasoning for the V1 list-of-tuple entries: a tag-0 `Constr` of
        // arity 2 is far too common a shape to claim from structure alone.
        T::TransactionId | T::WithdrawalEntry | T::DatumEntry => None,
    }
}

/// A class qualifies as a candidate RECORD when it has exactly one
/// shard holding exactly one variant with tag 0; returns that variant's
/// arity.
fn single_tag0_arity(class: &StubAdtClass) -> Option<usize> {
    if class.shards.len() != 1 {
        return None;
    }
    let adt = class.shards.values().next()?;
    if adt.variant_names.len() != 1 {
        return None;
    }
    let variant = adt.variant_names.keys().next()?;
    (variant.tag == 0).then_some(variant.arity)
}

/// Pick the Plutus version whose layout for `ct` has exactly `arity`
/// fields. Ambiguity is allowed only when every tying version's layout
/// is IDENTICAL (TxOut V2/V3); a tie between DIFFERENT layouts or no
/// match returns `None` — fail-closed.
fn version_for_record_arity(
    ct: crate::decompile::simplify::postprocess::ContextType,
    arity: usize,
) -> Option<crate::decompile::ScriptVersion> {
    use crate::decompile::ScriptVersion as V;
    use crate::decompile::simplify::postprocess::context_field_at;
    if arity == 0 {
        return None;
    }
    let layout = |v: V| -> Vec<_> {
        (0..arity + 1)
            .map_while(|i| context_field_at(ct, i, v))
            .collect()
    };
    let mut found: Option<V> = None;
    for v in [V::PlutusV1, V::PlutusV2, V::PlutusV3] {
        let fields = layout(v);
        if fields.len() != arity {
            continue;
        }
        match found {
            None => found = Some(v),
            Some(prev) => {
                if layout(prev) != fields {
                    // Two different layouts share this arity — refuse to
                    // guess.
                    return None;
                }
            }
        }
    }
    found
}

/// Field-PROJECTION aliases: `let X = Var(S).fields.head` maps X to
/// schema slot (S, 0); `let X = Var(S).fields[N]` to (S, N). The church
/// residue re-projects constructor fields positionally instead of using
/// the recovered destructure binder, so a child record's scrutinee is
/// often one of these aliases rather than the pattern binder. Keyed by
/// canonical source `S`; anything but these two exact shapes is ignored
/// (fail-closed).
fn collect_field_projection_aliases(expr: &PseudoExpr) -> BTreeMap<VarId, Vec<(usize, VarId)>> {
    use crate::pseudo::field_selector::FieldSelector;
    fn fields_of_var(e: &PseudoExpr) -> Option<VarId> {
        match e {
            PseudoExpr::FieldAccess { record, selector } if matches!(selector, FieldSelector::NamedField(n) if n == "fields") => {
                scrutinee_var_id(record)
            }
            _ => None,
        }
    }
    fn projection_of(e: &PseudoExpr) -> Option<(VarId, usize)> {
        match e {
            PseudoExpr::FieldAccess { record, selector }
                if matches!(selector, FieldSelector::ListHead) =>
            {
                fields_of_var(record).map(|s| (s, 0))
            }
            PseudoExpr::IndexAccess { collection, index } => {
                fields_of_var(collection).map(|s| (s, *index))
            }
            _ => None,
        }
    }
    fn walk(
        expr: &PseudoExpr,
        analysis: &AliasAnalysis,
        out: &mut BTreeMap<VarId, Vec<(usize, VarId)>>,
    ) {
        let mut pending = vec![expr];
        while let Some(expr) = pending.pop() {
            if let PseudoExpr::Let {
                id: Some(let_id),
                value,
                ..
            } = expr
            {
                if let Some((src, idx)) = projection_of(value) {
                    out.entry(analysis.canonical(src))
                        .or_default()
                        .push((idx, analysis.canonical(*let_id)));
                }
            }
            pending.extend(
                crate::decompile::render_prep::scope_recurse::children(expr)
                    .into_iter()
                    .rev(),
            );
        }
    }
    let analysis = build_alias_analysis(expr);
    let mut out = BTreeMap::new();
    walk(expr, &analysis, &mut out);
    out
}

/// For every `When` whose subject is a bare canonical `Var`, the
/// Constructor patterns' field-binder `VarId`s (canonicalized through
/// the alias map), in field order. `None` slots are non-id binders.
fn collect_scrutinee_field_binders(
    expr: &PseudoExpr,
) -> BTreeMap<VarId, Vec<(usize, Vec<Option<VarId>>)>> {
    fn walk(
        expr: &PseudoExpr,
        analysis: &AliasAnalysis,
        out: &mut BTreeMap<VarId, Vec<(usize, Vec<Option<VarId>>)>>,
    ) {
        let mut pending = vec![expr];
        while let Some(expr) = pending.pop() {
            if let PseudoExpr::When {
                subject, clauses, ..
            } = expr
            {
                if let Some(sid) = scrutinee_var_id(subject).map(|id| analysis.canonical(id)) {
                    for clause in clauses {
                        if let WhenPattern::Constructor { tag, fields, .. } = &clause.pattern {
                            let ids = fields
                                .iter()
                                .map(|b| Some(analysis.canonical(b.var_id())))
                                .collect();
                            out.entry(sid).or_default().push((*tag, ids));
                        }
                    }
                }
            }
            pending.extend(
                crate::decompile::render_prep::scope_recurse::children(expr)
                    .into_iter()
                    .rev(),
            );
        }
    }
    let analysis = build_alias_analysis(expr);
    let mut out = BTreeMap::new();
    walk(expr, &analysis, &mut out);
    out
}

/// One job on [`rewrite`]'s stack. Patterns are jobs of their own: called
/// `rewrite_pattern` mid-arm, and its `Literal` case descends straight back into
/// expression position.
enum RwStep {
    Visit(PseudoExpr),
    VisitPattern(WhenPattern, Option<VarId>),
    Post(RwPost),
}

enum RwPost {
    /// Ran after the `When`'s subject, before its clauses — the scrutinee id
    /// is read off the REWRITTEN subject, so the clause jobs cannot be pushed
    /// until it lands.
    WhenSubject {
        subject_name: Option<crate::pseudo::ast::Binder>,
        clauses: Vec<WhenClause>,
    },
    When {
        subject: PseudoExpr,
        subject_name: Option<crate::pseudo::ast::Binder>,
        /// One `has_guard` flag per clause; the patterns come off
        /// `done_patterns` in the same order.
        clause_meta: Vec<bool>,
    },
    Let {
        name: String,
        id: Option<VarId>,
    },
    Lambda {
        params: Vec<crate::pseudo::ast::Binder>,
    },
    RecFn {
        name: crate::pseudo::ast::Binder,
        params: Vec<crate::pseudo::ast::Binder>,
    },
    /// `WhenPattern::Literal(Constr)` — the hint is decided in the visit arm
    /// (it needs no walked child); the fields go through the ordinary
    /// expression rewriter and are re-wrapped here.
    LiteralConstrPattern {
        type_hint: Option<TypeHintId>,
        tag: usize,
        shape: ConstructorShape,
        count: usize,
    },
    /// `WhenPattern::Literal(non-Constr)`.
    LiteralPattern,
    Plain(PlainPost),
}

/// A `When` computing its scrutinee id from the already-rewritten subject, before
/// the clause patterns can resolve, is its own step (`WhenSubject`). Everything
/// else is "children, then rebuild": each `Constr`'s hint depends only on its own
/// tag/arity/shape, so it is decided in the visit arm and carried on the post step.
fn rewrite(expr: PseudoExpr, names: &StubAdtNames, analysis: &AliasAnalysis) -> PseudoExpr {
    let mut steps: Vec<RwStep> = vec![RwStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();
    // Rewritten clause patterns, drained by the matching `RwPost::When`. LIFO
    // like `done`: a clause's own subtree (and any nested `When` in it)
    // completes before the next clause's job runs.
    let mut done_patterns: Vec<WhenPattern> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RwStep::Visit(expr) => match expr {
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    steps.push(RwStep::Post(RwPost::WhenSubject {
                        subject_name,
                        clauses,
                    }));
                    steps.push(RwStep::Visit(subject.into_inner()));
                }
                PseudoExpr::Constr {
                    shape,
                    tag,
                    fields,
                    type_hint,
                } => {
                    // Set type_hint only when this Constr is unresolved AND
                    // a minted name exists for it.
                    let resolved_hint = if matches!(shape, ConstructorShape::Unknown { .. })
                        && type_hint.is_none()
                    {
                        let arity = fields.len();
                        let variant = StubVariant { tag, arity };
                        // Expression-position: prefer arity bucket (per
                        // collector's rule). Let-bound value-position Constrs
                        // are handled by the `Let` arm below.
                        names
                            .by_arity
                            .get(&arity)
                            .filter(|t| t.variant_names.contains_key(&variant))
                            .map(|t| t.type_hint.clone())
                    } else {
                        None
                    };
                    let count = fields.len();
                    steps.push(RwStep::Post(RwPost::Plain(PlainPost::Constr {
                        tag,
                        shape,
                        type_hint: type_hint.or(resolved_hint),
                        count,
                    })));
                    for f in fields.into_vec().into_iter().rev() {
                        steps.push(RwStep::Visit(f));
                    }
                }
                PseudoExpr::Let {
                    name,
                    id: Some(let_id),
                    value,
                    body,
                } if analysis.let_value_constrs.contains_key(&let_id) => {
                    // Def-use: collection promoted this value-position
                    // Constr to the scrutinee class. Route the rewrite the
                    // same way — the scrutinee class's hint when
                    // canonical(let_id) has one, else the arity bucket.
                    let canonical_id = analysis.canonical(let_id);
                    let value = value.into_inner();
                    steps.push(RwStep::Post(RwPost::Let {
                        name,
                        id: Some(let_id),
                    }));
                    steps.push(RwStep::Visit(body.into_inner()));
                    if let PseudoExpr::Constr {
                        shape,
                        tag,
                        fields,
                        type_hint,
                    } = value
                    {
                        let resolved_hint = if matches!(shape, ConstructorShape::Unknown { .. })
                            && type_hint.is_none()
                        {
                            let arity = fields.len();
                            let variant = StubVariant { tag, arity };
                            names
                                .by_scrutinee
                                .get(&canonical_id)
                                .and_then(|class| class.shards.get(&arity))
                                .filter(|t| t.variant_names.contains_key(&variant))
                                .map(|t| t.type_hint.clone())
                                .or_else(|| {
                                    names
                                        .by_arity
                                        .get(&arity)
                                        .filter(|t| t.variant_names.contains_key(&variant))
                                        .map(|t| t.type_hint.clone())
                                })
                        } else {
                            None
                        };
                        let count = fields.len();
                        steps.push(RwStep::Post(RwPost::Plain(PlainPost::Constr {
                            tag,
                            shape,
                            type_hint: type_hint.or(resolved_hint),
                            count,
                        })));
                        for f in fields.into_vec().into_iter().rev() {
                            steps.push(RwStep::Visit(f));
                        }
                    } else {
                        // Defensive: pre-pass said this was a Constr value
                        // but it isn't anymore — fall back to regular rewrite.
                        steps.push(RwStep::Visit(value));
                    }
                }
                PseudoExpr::Let {
                    name,
                    id: Some(let_id),
                    value,
                    body,
                } if analysis.producer_leaf_fns.contains_key(&let_id) => {
                    // Witnessed producer fn — resolve its RETURN-LEAF
                    // raw Constrs against the scrutinee class (so they render
                    // `Unknown_S_N_t`), then do the ordinary rewrite on the rest.
                    let scrutinee = analysis.canonical(analysis.producer_leaf_fns[&let_id].0);
                    let value = rewrite_producer_leaves(value.into_inner(), names, scrutinee);
                    steps.push(RwStep::Post(RwPost::Let {
                        name,
                        id: Some(let_id),
                    }));
                    steps.push(RwStep::Visit(body.into_inner()));
                    steps.push(RwStep::Visit(value));
                }
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
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RwStep::Post(RwPost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(RwStep::Visit(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            // Pattern rewrite, mid-`When` arm.
            RwStep::VisitPattern(pattern, scrutinee_id) => match pattern {
                WhenPattern::Constructor {
                    type_hint,
                    tag,
                    fields,
                    shape,
                } => {
                    let resolved_hint = if matches!(shape, ConstructorShape::Unknown { .. })
                        && type_hint.is_none()
                    {
                        let arity = fields.len();
                        let variant = StubVariant { tag, arity };
                        scrutinee_id
                            .and_then(|sid| names.by_scrutinee.get(&sid))
                            .and_then(|class| class.shards.get(&arity))
                            .filter(|t| t.variant_names.contains_key(&variant))
                            .map(|t| t.type_hint.clone())
                            .or_else(|| {
                                names
                                    .by_arity
                                    .get(&arity)
                                    .filter(|t| t.variant_names.contains_key(&variant))
                                    .map(|t| t.type_hint.clone())
                            })
                    } else {
                        None
                    };
                    done_patterns.push(WhenPattern::Constructor {
                        type_hint: type_hint.or(resolved_hint),
                        tag,
                        fields,
                        shape,
                    });
                }
                // Literal patterns carry an inner PseudoExpr; nested
                // Constrs go through the expression rewriter.
                WhenPattern::Literal(inner) => {
                    // The collector attributes the TOP-LEVEL Constr inside a
                    // Literal pattern to the scrutinee class; the general
                    // expression rewriter only checks `by_arity`. Mirror the
                    // collector here: scrutinee class first, arity bucket as
                    // fallback.
                    if let PseudoExpr::Constr {
                        shape,
                        tag,
                        fields,
                        type_hint,
                    } = inner
                    {
                        let resolved_hint = if matches!(shape, ConstructorShape::Unknown { .. })
                            && type_hint.is_none()
                        {
                            let arity = fields.len();
                            let variant = StubVariant { tag, arity };
                            scrutinee_id
                                .and_then(|sid| names.by_scrutinee.get(&sid))
                                .and_then(|class| class.shards.get(&arity))
                                .filter(|t| t.variant_names.contains_key(&variant))
                                .map(|t| t.type_hint.clone())
                                .or_else(|| {
                                    names
                                        .by_arity
                                        .get(&arity)
                                        .filter(|t| t.variant_names.contains_key(&variant))
                                        .map(|t| t.type_hint.clone())
                                })
                        } else {
                            None
                        };
                        let count = fields.len();
                        steps.push(RwStep::Post(RwPost::LiteralConstrPattern {
                            type_hint: type_hint.or(resolved_hint),
                            tag,
                            shape,
                            count,
                        }));
                        for f in fields.into_vec().into_iter().rev() {
                            steps.push(RwStep::Visit(f));
                        }
                    } else {
                        steps.push(RwStep::Post(RwPost::LiteralPattern));
                        steps.push(RwStep::Visit(inner));
                    }
                }
                // Other patterns don't carry Constrs.
                other @ (WhenPattern::List { .. }
                | WhenPattern::Tuple(_)
                | WhenPattern::Pair(_, _)
                | WhenPattern::Wildcard
                | WhenPattern::Var(_)) => done_patterns.push(other),
            },
            RwStep::Post(post) => {
                let rebuilt = match post {
                    RwPost::WhenSubject {
                        subject_name,
                        clauses,
                    } => {
                        let subject = done.pop().expect("when subject");
                        // Def-use: canonicalize the scrutinee id through the
                        // alias map so an aliased subject (`let Y = X; when Y is
                        // ...`) finds X's scrutinee class.
                        let scrutinee_id =
                            scrutinee_var_id(&subject).map(|id| analysis.canonical(id));
                        let mut clause_meta = Vec::with_capacity(clauses.len());
                        let mut children: Vec<RwStep> = Vec::new();
                        // Per clause, in the order the struct literal ran them:
                        // pattern, guard, body.
                        for clause in clauses {
                            clause_meta.push(clause.guard.is_some());
                            children.push(RwStep::VisitPattern(clause.pattern, scrutinee_id));
                            if let Some(g) = clause.guard {
                                children.push(RwStep::Visit(g));
                            }
                            children.push(RwStep::Visit(clause.body));
                        }
                        steps.push(RwStep::Post(RwPost::When {
                            subject,
                            subject_name,
                            clause_meta,
                        }));
                        for c in children.into_iter().rev() {
                            steps.push(c);
                        }
                        continue;
                    }
                    RwPost::When {
                        subject,
                        subject_name,
                        clause_meta,
                    } => {
                        let total = clause_meta
                            .iter()
                            .map(|has_guard| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = take(&mut done, total).into_iter();
                        let at = done_patterns.len() - clause_meta.len();
                        let mut patterns = done_patterns.split_off(at).into_iter();
                        let clauses = clause_meta
                            .into_iter()
                            .map(|has_guard| WhenClause {
                                pattern: patterns.next().expect("when clause pattern"),
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
                    RwPost::LiteralConstrPattern {
                        type_hint,
                        tag,
                        shape,
                        count,
                    } => {
                        let fields = take(&mut done, count);
                        done_patterns.push(WhenPattern::Literal(PseudoExpr::Constr {
                            type_hint,
                            tag,
                            fields: fields.into(),
                            shape,
                        }));
                        continue;
                    }
                    RwPost::LiteralPattern => {
                        let inner = done.pop().expect("literal pattern payload");
                        done_patterns.push(WhenPattern::Literal(inner));
                        continue;
                    }
                    RwPost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    debug_assert!(
        done_patterns.is_empty(),
        "rewrite must drain every clause pattern"
    );
    done.pop().expect("rewrite result")
}

/// Set the `type_hint` on a producer fn value's RETURN-LEAF
/// raw `Constr`s to the `scrutinee` class's shard (matching by
/// `(tag, arity)`), so the leaf renders as `Unknown_S_N_t` instead of the
/// `Unknown_E_arity` arity-bucket name. Descends the same leaf positions as
/// [`collect_producer_leaves`]. Leaves that don't match a declared
/// scrutinee variant are left untouched (fail-closed).
fn rewrite_producer_leaves(
    fn_value: PseudoExpr,
    names: &StubAdtNames,
    scrutinee: VarId,
) -> PseudoExpr {
    fn hint_for(
        names: &StubAdtNames,
        scrutinee: VarId,
        tag: usize,
        arity: usize,
    ) -> Option<TypeHintId> {
        let variant = StubVariant { tag, arity };
        names
            .by_scrutinee
            .get(&scrutinee)
            .and_then(|class| class.shards.get(&arity))
            .filter(|t| t.variant_names.contains_key(&variant))
            .map(|t| t.type_hint.clone())
    }
    /// One job on [`walk_body`]'s stack.
    enum LeafStep {
        Visit(PseudoExpr),
        Post(LeafPost),
    }

    /// Only the LEAF positions are descended, so each post variant carries the siblings
    /// moved through untouched (an `If`'s condition, a `Let`'s value, a `Trace`'s
    /// message, a `When`'s subject and guards).
    enum LeafPost {
        If {
            condition: PBox,
        },
        Let {
            name: String,
            id: Option<VarId>,
            value: PBox,
        },
        Trace {
            message: PBox,
        },
        When {
            subject: PBox,
            subject_name: Option<crate::pseudo::ast::Binder>,
            clause_meta: Vec<(WhenPattern, Option<PseudoExpr>)>,
        },
    }

    fn walk_body(expr: PseudoExpr, names: &StubAdtNames, scrutinee: VarId) -> PseudoExpr {
        let mut steps: Vec<LeafStep> = vec![LeafStep::Visit(expr)];
        let mut done: Vec<PseudoExpr> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                LeafStep::Visit(expr) => match expr {
                    PseudoExpr::Constr {
                        shape,
                        tag,
                        fields,
                        type_hint,
                    } if matches!(shape, ConstructorShape::Unknown { .. })
                        && type_hint.is_none() =>
                    {
                        let arity = fields.len();
                        let new_hint = hint_for(names, scrutinee, tag, arity);
                        done.push(PseudoExpr::Constr {
                            shape,
                            tag,
                            fields,
                            type_hint: new_hint,
                        });
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        steps.push(LeafStep::Post(LeafPost::If { condition }));
                        steps.push(LeafStep::Visit(else_branch.into_inner()));
                        steps.push(LeafStep::Visit(then_branch.into_inner()));
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
                    PseudoExpr::Trace { message, value } => {
                        steps.push(LeafStep::Post(LeafPost::Trace { message }));
                        steps.push(LeafStep::Visit(value.into_inner()));
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
                    other => done.push(other),
                },
                LeafStep::Post(post) => {
                    let rebuilt = match post {
                        LeafPost::If { condition } => {
                            let else_branch = done.pop().expect("if else");
                            let then_branch = done.pop().expect("if then");
                            PseudoExpr::If {
                                condition,
                                then_branch: PBox::new(then_branch),
                                else_branch: PBox::new(else_branch),
                            }
                        }
                        LeafPost::Let { name, id, value } => PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body: PBox::new(done.pop().expect("let body")),
                        },
                        LeafPost::Trace { message } => PseudoExpr::Trace {
                            message,
                            value: PBox::new(done.pop().expect("trace value")),
                        },
                        LeafPost::When {
                            subject,
                            subject_name,
                            clause_meta,
                        } => {
                            let mut parts =
                                super::scope_recurse::take(&mut done, clause_meta.len())
                                    .into_iter();
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
                    };
                    done.push(rebuilt);
                }
            }
        }

        debug_assert_eq!(done.len(), 1, "walk_body must leave one result");
        done.pop().expect("walk_body result")
    }
    match fn_value {
        PseudoExpr::Lambda { params, body } => PseudoExpr::Lambda {
            params,
            body: PBox::new(walk_body(body.into_inner(), names, scrutinee)),
        },
        PseudoExpr::RecFn { name, params, body } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(walk_body(body.into_inner(), names, scrutinee)),
        },
        other => other,
    }
}

#[cfg(test)]
mod tests;
