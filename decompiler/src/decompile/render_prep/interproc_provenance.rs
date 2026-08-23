//! Inter-procedural parameter-slot provenance. Analysis-only: the per-param
//! verdicts feed a `DEHOSK_PROVENANCE`-gated dump and nothing else, so they
//! change no output.
//!
//! Stub-ADT fields and projection-eliminator heads (`x.fst(k)`, `x.2nd(k0,k1)`)
//! that reach a function through a parameter cannot be classified by the
//! intra-procedural [`super::field_kind_inference`]: the construction site is
//! the call site, not the body. This joins, for each named function and each
//! parameter slot, the [`FieldKind`] of the actual argument at every call site
//! in the (closed) program. `field_kind_inference::seed_from_field_expr` is the
//! per-site classifier; its flat lattice supplies the join.
//!
//! Fail-closed (the Data-cannot-hold-functions lever): a slot is judged Scott
//! only when its call set is fully enumerable and every argument across all
//! call sites is itself a proven Scott value (built in-validator from decoded
//! `Data`, hence never an external HOF). The call set is enumerable only if
//! every occurrence of the function's identifier is an `Apply` head — used as
//! a value (passed as an argument, returned, or Scott-matched as a `when`
//! subject), a function may be invoked through paths this analysis cannot see,
//! so its slots are `Unreliable`. Arity-mismatched call sites and functions
//! with no call sites are likewise non-committal.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

use super::field_kind_inference::{
    ArityCatalog, FieldKind, build_arity_catalog, seed_from_field_expr,
};
use super::scope_recurse::children;

/// A named function: its display name and the set of `VarId`s it can be called
/// under (a `let f = rec fn g(..)` is callable as both `f` and `g`).
#[derive(Debug, Clone)]
struct FunctionRecord {
    name: String,
    ids: Vec<VarId>,
    params: Vec<Binder>,
}

/// Per-parameter-slot verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum SlotVerdict {
    /// Every call site passes a proven Scott value of these arities AND the
    /// parameter is actually eliminated in the function body (`p.proj(..)` or
    /// `when p is`). This is the ONLY verdict that gates an eliminator rewrite.
    RewriteTarget(Vec<usize>),
    /// Proven Scott value, but the parameter only flows through (stored,
    /// returned, repacked), never eliminated here — nothing to rewrite.
    ScottFlowsThrough(Vec<usize>),
    /// Call set enumerable and consistent, but the joined kind is not Scott
    /// (a genuine `Fn`, `Native` data, `Opaque`, or `Conflict`).
    NotDecodable(FieldKind),
    /// The function is used as a VALUE somewhere → its call set is not
    /// enumerable → fail-closed.
    Unreliable,
    /// At least one call site had a different argument count than the params.
    ArityMismatch,
    /// The function is declared but never called.
    NoCallSites,
}

/// The provenance verdict for one function.
#[derive(Debug, Clone)]
pub(super) struct FunctionProvenance {
    pub name: String,
    pub slots: Vec<(String, SlotVerdict)>,
}

#[derive(Default)]
struct Collector {
    functions: Vec<FunctionRecord>,
    /// `VarId` → index into `functions`.
    by_id: HashMap<VarId, usize>,
    /// `VarId` → per-call-site argument kinds (one inner Vec per call).
    call_sites: HashMap<VarId, Vec<Vec<FieldKind>>>,
    /// Identifiers that appear at least once as a VALUE (not an `Apply` head).
    value_used: HashSet<VarId>,
    /// Identifiers ELIMINATED as a Scott/church value: `v.proj(..)` (a
    /// projection-applied FieldAccess head) or `when v is`. A rewrite target
    /// must be eliminated, not merely Scott-typed.
    eliminated: HashSet<VarId>,
}

/// If `e` is a function literal, its parameter binders.
fn function_params(e: &PseudoExpr) -> Option<&[Binder]> {
    match e {
        PseudoExpr::Lambda { params, .. } | PseudoExpr::RecFn { params, .. } => Some(params),
        _ => None,
    }
}

impl Collector {
    /// Register `id` as callable for a function record (creating or extending).
    fn register_function(&mut self, id: VarId, name: &str, params: &[Binder]) {
        if self.by_id.contains_key(&id) {
            return; // already mapped (e.g. inner RecFn id seen after the Let)
        }
        let idx = self.functions.len();
        self.functions.push(FunctionRecord {
            name: name.to_string(),
            ids: vec![id],
            params: params.to_vec(),
        });
        self.by_id.insert(id, idx);
    }

    /// Alias `extra_id` onto the same record as `primary_id` (the `let f = rec
    /// fn g` case where both name the one function).
    fn alias_id(&mut self, primary_id: VarId, extra_id: VarId) {
        if let Some(&idx) = self.by_id.get(&primary_id) {
            if !self.by_id.contains_key(&extra_id) {
                self.functions[idx].ids.push(extra_id);
                self.by_id.insert(extra_id, idx);
            }
        }
    }

    fn walk(&mut self, root: &PseudoExpr, catalog: &ArityCatalog) {
        let mut pending: Vec<&PseudoExpr> = vec![root];
        while let Some(expr) = pending.pop() {
            match expr {
                PseudoExpr::Let {
                    id: Some(let_id),
                    name,
                    value,
                    body,
                } => {
                    // A `let`-bound function is reached by name, so it does NOT
                    // escape: register it and walk its BODY directly, never
                    // through the standalone RecFn arm (which marks it unreliable).
                    match &**value {
                        PseudoExpr::Lambda {
                            params,
                            body: fbody,
                        } => {
                            self.register_function(*let_id, name, params);
                            pending.push(body);
                            pending.push(fbody);
                        }
                        PseudoExpr::RecFn {
                            name: rec_name,
                            params,
                            body: fbody,
                        } => {
                            self.register_function(*let_id, name, params);
                            self.alias_id(*let_id, rec_name.id);
                            pending.push(body);
                            pending.push(fbody);
                        }
                        _ => {
                            pending.push(body);
                            pending.push(value);
                        }
                    }
                }
                PseudoExpr::RecFn { name, params, body } => {
                    // A standalone RecFn reached HERE sits in a value position —
                    // neither a `let` binding nor an IIFE head, both handled above.
                    // It escapes, so its call set is not enumerable → fail-closed.
                    self.register_function(name.id, &name.name, params);
                    self.value_used.insert(name.id);
                    pending.push(body);
                }
                PseudoExpr::Apply { function, args } => {
                    match &**function {
                        PseudoExpr::Var { id: Some(fid), .. } => {
                            // Direct call: record the per-arg kinds; the head Var is
                            // a call-head, NOT a value-use.
                            let kinds: Vec<FieldKind> = args
                                .iter()
                                .map(|a| seed_from_field_expr(a, catalog))
                                .collect();
                            self.call_sites.entry(*fid).or_default().push(kinds);
                            for a in args.iter().rev() {
                                pending.push(a);
                            }
                        }
                        // Direct (IIFE) application of a named rec fn,
                        // `(rec fn g(p){..})(arg)`: the entry args ARE a call site
                        // for `g` — unrecorded, the invocation is invisible and a
                        // self-recursive Scott call alone would look like a target.
                        PseudoExpr::RecFn { name, params, body } => {
                            let kinds: Vec<FieldKind> = args
                                .iter()
                                .map(|a| seed_from_field_expr(a, catalog))
                                .collect();
                            self.call_sites.entry(name.id).or_default().push(kinds);
                            // Register + walk the BODY directly (this is a call, not
                            // a value escape — do NOT route through the standalone
                            // RecFn arm).
                            self.register_function(name.id, &name.name, params);
                            for a in args.iter().rev() {
                                pending.push(a);
                            }
                            pending.push(body);
                        }
                        // `v.proj(..)`: a projection-applied head ELIMINATES v as a
                        // Scott value. (`v` is still a value-use, recorded below.)
                        PseudoExpr::FieldAccess { record, .. } => {
                            if let PseudoExpr::Var { id: Some(vid), .. } = &**record {
                                self.eliminated.insert(*vid);
                            }
                            for a in args.iter().rev() {
                                pending.push(a);
                            }
                            pending.push(function);
                        }
                        // Indirect head (nested Apply / anonymous lambda / Let): its
                        // sub-Vars are walked as value-uses, so any tracked function
                        // reached through it fails closed.
                        _ => {
                            for a in args.iter().rev() {
                                pending.push(a);
                            }
                            pending.push(function);
                        }
                    }
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    // `when v is { .. }` eliminates v as a Scott value.
                    if let PseudoExpr::Var { id: Some(vid), .. } = &**subject {
                        self.eliminated.insert(*vid);
                    }
                    let _ = subject_name;
                    for clause in clauses.iter().rev() {
                        pending.push(&clause.body);
                        if let Some(g) = &clause.guard {
                            pending.push(g);
                        }
                        // A literal pattern carries an expression that can hold
                        // Var/Apply uses, and `children()` omits it — untraversed,
                        // a function value-used only in a pattern would escape.
                        if let crate::pseudo::ast::WhenPattern::Literal(e) = &clause.pattern {
                            pending.push(e);
                        }
                    }
                    pending.push(subject);
                }
                PseudoExpr::Var { id: Some(vid), .. } => {
                    // A bare Var in any non-call-head position is a value-use.
                    self.value_used.insert(*vid);
                }
                other => {
                    for child in children(other).into_iter().rev() {
                        pending.push(child);
                    }
                }
            }
        }
    }
}

/// Join a parameter slot's kind across all enumerated call sites.
fn join_slot(per_call_kinds: &[FieldKind]) -> FieldKind {
    per_call_kinds
        .iter()
        .cloned()
        .fold(FieldKind::Unknown, FieldKind::join)
}

/// Compute the per-function parameter-slot provenance for `expr`.
pub(super) fn analyze(expr: &PseudoExpr) -> Vec<FunctionProvenance> {
    let catalog = build_arity_catalog(expr);
    let mut c = Collector::default();
    c.walk(expr, &catalog);

    let mut out = Vec::new();
    for func in &c.functions {
        // Fail-closed: any value-use of any alias means the call set is not
        // enumerable.
        let enumerable = !func.ids.iter().any(|id| c.value_used.contains(id));
        // Merge call sites recorded under any alias.
        let mut calls: Vec<&Vec<FieldKind>> = Vec::new();
        for id in &func.ids {
            if let Some(v) = c.call_sites.get(id) {
                calls.extend(v.iter());
            }
        }

        let slots = func
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let verdict = if !enumerable {
                    SlotVerdict::Unreliable
                } else if calls.is_empty() {
                    SlotVerdict::NoCallSites
                } else if calls.iter().any(|c| c.len() != func.params.len()) {
                    SlotVerdict::ArityMismatch
                } else {
                    let per_call: Vec<FieldKind> = calls.iter().map(|c| c[i].clone()).collect();
                    match join_slot(&per_call) {
                        // Scott value AND eliminated here => an actual rewrite
                        // target; Scott but only stored/threaded => flows through.
                        FieldKind::Scott(ar) => {
                            if c.eliminated.contains(&p.id) {
                                SlotVerdict::RewriteTarget(ar)
                            } else {
                                SlotVerdict::ScottFlowsThrough(ar)
                            }
                        }
                        other => SlotVerdict::NotDecodable(other),
                    }
                };
                (p.name.clone(), verdict)
            })
            .collect();

        out.push(FunctionProvenance {
            name: func.name.clone(),
            slots,
        });
    }
    out
}

/// Render a human-readable provenance report — every function param's
/// verdict, headed by the `RewriteTarget` and `ScottFlowsThrough` counts.
pub(super) fn report(provenances: &[FunctionProvenance]) -> String {
    let mut targets = 0usize;
    let mut flows_through = 0usize;
    let mut lines = Vec::new();
    for f in provenances {
        if f.slots.is_empty() {
            continue;
        }
        lines.push(format!("fn {}:", f.name));
        for (pname, verdict) in &f.slots {
            let tag = match verdict {
                SlotVerdict::RewriteTarget(ar) => {
                    targets += 1;
                    format!("REWRITE TARGET Scott{ar:?} (proven-Scott AND eliminated here)")
                }
                SlotVerdict::ScottFlowsThrough(ar) => {
                    flows_through += 1;
                    format!(
                        "scott-flows-through Scott{ar:?} (stored/threaded, not eliminated here)"
                    )
                }
                SlotVerdict::NotDecodable(k) => format!("not-decodable ({k:?})"),
                SlotVerdict::Unreliable => {
                    "unreliable (function value-used; call set not enumerable)".to_string()
                }
                SlotVerdict::ArityMismatch => "arity-mismatch".to_string(),
                SlotVerdict::NoCallSites => "no call sites".to_string(),
            };
            lines.push(format!("    {pname}: {tag}"));
        }
    }
    format!(
        "=== inter-procedural param-slot provenance ===\n{} functions, {targets} REWRITE TARGET(s), {flows_through} scott-flows-through\n{}",
        provenances.iter().filter(|f| !f.slots.is_empty()).count(),
        lines.join("\n")
    )
}

#[cfg(test)]
mod tests;
