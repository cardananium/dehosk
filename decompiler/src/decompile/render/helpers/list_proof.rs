//! Structural list-ness proof for the compilable-data-access `coll[N]` →
//! `head_list(tail_list^N(coll))` lowering, with call-site propagation.
//!
//! Indexing a tuple/pair with `head_list` is the valid-looking-wrong bug,
//! so a collection lowers only on a structural proof — never the solver
//! type table. Fail-closed fixpoint `S` of provably-list `VarId`s:
//!
//! - **(a) let binders:** `let x = <value>` joins `S` when the value is
//!   a list given `S` (list literal; applied `tail_list`/`un_list_data`/
//!   `un_map_data` in either spelling; `un_constr_data(_).2nd`; or a
//!   `Var` already in `S`).
//! - **(b) when list-tails:** the tail binder of `[h, ..t]` joins `S`
//!   when the subject is a list given `S`. Heads never join (`List<Data>`
//!   elements are `Data`).
//! - **(c) call-site params:** param `P` of an enumerable function `F`
//!   joins `S` when every call site passes a list in that slot and at
//!   least one call is external. A self-call is checked under
//!   `S ∪ {P} ∪ {when-tails from P}`; an external call under plain `S`.
//!   Every entry to `F` is then either an external call (arg proven
//!   outright) or a self-call from an activation where `P` already held
//!   a list.
//!
//! `S` starts empty and grows only from structural facts, so ungrounded
//! cycles cannot bootstrap themselves. The ≥1-external-call rule keeps
//! self-evidence from standing alone.
//!
//! A function is enumerable iff all of these hold (fail-closed):
//! - none of its ids occurs as a value (only as an `Apply` head);
//! - no id-less `Var { id: None }` shares any of its names;
//! - it has ≥ 1 call site (an all-quantifier over zero calls is vacuous);
//! - every call passes exactly `params.len()` args;
//! - no `PseudoExpr::Raw` exists anywhere — a `Raw` blob can hide a
//!   call site. One `Raw` disables all param proofs; rules (a)/(b)
//!   still apply.
//!
//! The scan is a hand-rolled exhaustive match (no wildcard) whose child
//! coverage mirrors `fold::walk_inner`, including `WhenPattern::Literal`
//! payloads, clause guards, and `List` literal tails
//! (`scope_recurse::children` omits pattern payloads).
//!
//! The prepared tree does not uphold program-wide VarId uniqueness.
//! Any id bound by more than one binder is conflicted: it never enters
//! `S` and vetoes any fn whose let/self/param ids touch it.
//!
//! Read-only, render-time, compilable mode only.

use std::collections::{HashMap, HashSet};

use crate::builtins::BuiltinId;
use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

/// The applied-builtin matcher, normalizing BOTH AST spellings (mirrors
/// `traversal::count_tail_chain_any`): `BuiltinCall { B, [x] }` and
/// `Apply { BuiltinCall { B, [] }, [x] }`. Returns the single argument.
fn applied1<'a>(expr: &'a PseudoExpr, accept: &[BuiltinId]) -> Option<&'a PseudoExpr> {
    match expr {
        PseudoExpr::BuiltinCall { name, args } if args.len() == 1 && accept.contains(name) => {
            Some(&args[0])
        }
        PseudoExpr::Apply { function, args } if args.len() == 1 => match function.as_ref() {
            PseudoExpr::BuiltinCall { name, args: ba }
                if ba.is_empty() && accept.contains(name) =>
            {
                Some(&args[0])
            }
            _ => None,
        },
        _ => None,
    }
}

/// Is `expr` provably a list GIVEN the proven set? Structural arms:
/// - a `List` literal;
/// - a `Var` whose id is already proven;
/// - applied `tail_list` / `un_list_data` / `un_map_data` (either spelling;
///   `un_map_data` yields the assoc-list `List<Pair<Data, Data>>`);
/// - `un_constr_data(_).2nd` / `Constr.unpack(_).2nd` — the fields list of
///   `Pair<Int, List<Data>>` (either spelling of the unconstr call);
/// - the BRANCH-TAIL JOIN: a value-position statement shape evaluates to
///   exactly one of its tails, so it is a list when EVERY non-diverging
///   tail is (and ≥ 1 non-diverging tail exists — an all-`fail` shape has
///   no list evidence): `Let` → its body; `If` → both branches; `When` →
///   every clause body; `expect!(cond, value[, msg])` → the value
///   (`args[1]`; the display-layer wrapper evaluates to its continuation
///   or diverges). Diverging = `Error` or `BuiltinCall(Error)`.
///
/// There is deliberately NO `type_resolution() == List` arm: that resolution
/// derives from literal kinds only (Int/ByteArray/String/Bool/Unit/Data) and
/// can never yield `List`, and a solver mis-type here would lower a tuple
/// index to `head_list`.
///
/// Test-only convenience wrapper (no `list_returning` context); production
/// callers use [`is_provably_list_with`] directly.
#[cfg(test)]
pub(in crate::decompile::render) fn is_provably_list_given(
    expr: &PseudoExpr,
    proven: &HashSet<VarId>,
) -> bool {
    is_provably_list_with(expr, proven, &HashMap::new())
}

/// The full prover: `proven` plus the RETURN JOIN — a full-arity call (head
/// `Var` or direct IIFE `RecFn`, `Force` wrappers peeled) of an fn in
/// `list_returning` (every return leaf proven or an exact-arity self-call,
/// with ≥ 1 grounded non-self leaf — see the solve loop) is a list.
///
/// The whole predicate is one CONJUNCTION — every recursive call in the
/// former shape propagated its `false` straight up — so the pending
/// sub-goals live on a stack and the first refuted goal answers `false` for
/// the lot. The predicate is pure, so the order goals are discharged in
/// cannot change the answer.
fn is_provably_list_with<'a>(
    expr: &'a PseudoExpr,
    proven: &HashSet<VarId>,
    list_returning: &HashMap<VarId, usize>,
) -> bool {
    let mut goals: Vec<&'a PseudoExpr> = vec![expr];

    while let Some(expr) = goals.pop() {
        match expr {
            PseudoExpr::List { .. } => {}
            PseudoExpr::Var { id: Some(v), .. } => {
                if !proven.contains(v) {
                    return false;
                }
            }
            PseudoExpr::FieldAccess {
                record,
                selector: FieldSelector::PairSnd,
            } => {
                if applied1(record, &[BuiltinId::DataUnConstr, BuiltinId::ConstrUnpack]).is_none() {
                    return false;
                }
            }
            // Branch-tail join. A `let x = fail; [..]` body still counts — the
            // strict value diverges, so a lowering inside unreachable code is
            // semantically inert (bottom evidence, not wrong evidence).
            PseudoExpr::Let { body, .. } => goals.push(body),
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                let branches = [then_branch.as_ref(), else_branch.as_ref()];
                if !push_non_diverging_tails(&branches, &mut goals) {
                    return false;
                }
            }
            PseudoExpr::When { clauses, .. } => {
                let bodies: Vec<&PseudoExpr> = clauses.iter().map(|c| &c.body).collect();
                if !push_non_diverging_tails(&bodies, &mut goals) {
                    return false;
                }
            }
            other => {
                // `expect!(cond, value[, msg])` — the display-layer statement
                // wrapper: evaluates to `value` or diverges. Matched by NAME,
                // not by an `id: None` head gate — the nameless round-trip
                // stamps ids onto formerly id-less heads. `!` cannot occur in
                // a user identifier, so the name is unambiguous.
                if let PseudoExpr::Apply { function, args } = other {
                    if super::traversal::is_expect_bang(function)
                        && (args.len() == 2 || args.len() == 3)
                    {
                        goals.push(&args[1]);
                        continue;
                    }
                    // Return join: a FULL-arity call of a proven list-returning
                    // fn (Force wrappers on the head are renderer-elided
                    // residue). Both head forms — a `Var` reference and the
                    // direct IIFE `RecFn` head.
                    let mut head = function.as_ref();
                    while let PseudoExpr::Force(inner) = head {
                        head = inner.as_ref();
                    }
                    let head_id = match head {
                        PseudoExpr::Var { id: Some(f), .. } => Some(*f),
                        PseudoExpr::RecFn { name, .. } => Some(name.id),
                        _ => None,
                    };
                    if let Some(f) = head_id
                        && let Some(arity) = list_returning.get(&f)
                        && args.len() == *arity
                    {
                        continue;
                    }
                }
                if applied1(
                    other,
                    &[
                        BuiltinId::ListTail,
                        BuiltinId::DataUnList,
                        BuiltinId::DataUnMap,
                    ],
                )
                .is_none()
                {
                    return false;
                }
            }
        }
    }

    true
}

/// Queue every NON-diverging tail as a goal; `false` when there is none.
///
/// ANDed the tails' own results together and short-circuited on the first `false`; here
/// they join the shared conjunction stack, which short-circuits identically.
fn push_non_diverging_tails<'a>(tails: &[&'a PseudoExpr], goals: &mut Vec<&'a PseudoExpr>) -> bool {
    let mut non_diverging = 0usize;
    for tail in tails {
        if is_diverging(tail) {
            continue;
        }
        non_diverging += 1;
        goals.push(tail);
    }
    non_diverging > 0
}

/// `fail` in either AST form (`collapse_trace_fail_let` produces the bare
/// `Error`; some paths keep the builtin call).
fn is_diverging(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Error { .. })
        || matches!(
            expr,
            PseudoExpr::BuiltinCall {
                name: BuiltinId::Error,
                ..
            }
        )
}

/// An enumerable-function candidate: a `let`-bound `Lambda`/`RecFn` or an
/// IIFE `RecFn` head.
struct FnRec<'a> {
    /// All ids the fn is callable under: the `let` binder id and (for a
    /// `RecFn` value) the inner self-name id.
    ids: Vec<VarId>,
    /// All display/semantic names the fn is reachable under, for the
    /// id-less-Var veto.
    names: Vec<&'a str>,
    /// Param `VarId`s in slot order.
    params: Vec<VarId>,
    /// The fn body, for the return join.
    body: &'a PseudoExpr,
}

/// One recorded call: the full argument slice plus the ids of every fn whose
/// BODY lexically encloses the call site (for the self-vs-external split).
struct CallRec<'a> {
    args: &'a [PseudoExpr],
    enclosing_fn_ids: Vec<VarId>,
}

#[derive(Default)]
struct Scan<'a> {
    /// `let` binder id → bound value (non-fn values only).
    let_values: Vec<(VarId, &'a PseudoExpr)>,
    /// `[h, ..t]` tail binder id → the `when`'s subject.
    when_tails: Vec<(VarId, &'a PseudoExpr)>,
    /// Enumerable-fn candidates.
    fns: Vec<FnRec<'a>>,
    /// Call head id → recorded calls.
    calls: HashMap<VarId, Vec<CallRec<'a>>>,
    /// Ids reached as a VALUE (not an `Apply` head).
    value_used: HashSet<VarId>,
    /// Display names of id-less `Var`s (unattributable references).
    idless_names: HashSet<&'a str>,
    /// A `PseudoExpr::Raw` exists somewhere — closed world broken.
    saw_raw: bool,
    /// Ids of the fns whose bodies the scan is currently inside.
    enclosing_fn_ids: Vec<VarId>,
    /// Every BINDER occurrence per id (let binders, lambda/recfn
    /// name+params, when subject_name, pattern binders). An id bound by
    /// MORE than one binder is a VarId COLLISION, and id-keyed reasoning
    /// is unsound for it: a `Var` carrying it may reference either
    /// binder. Conflicted ids are excluded from `S` and veto any fn they
    /// touch (fail-closed).
    binder_counts: HashMap<VarId, u32>,
}

impl Scan<'_> {
    fn record_binder(&mut self, id: VarId) {
        *self.binder_counts.entry(id).or_insert(0) += 1;
    }
}

/// One call partitioned for rule (c): `is_self` means the call site is
/// lexically inside the fn's own body (executes only within an activation
/// of it, or in a closure capturing one).
struct SlotCall<'a> {
    args: &'a [PseudoExpr],
    is_self: bool,
}

/// The fixpoint result: the proven-list `VarId` set plus the proven
/// list-RETURNING fns (id → arity), consumed together by the render gate
/// (an `IndexAccess` directly on a full-arity call of a list-returning fn
/// lowers too).
pub(in crate::decompile::render) struct ListProof {
    proven: HashSet<VarId>,
    list_returning: HashMap<VarId, usize>,
}

impl ListProof {
    pub(in crate::decompile::render) fn is_provably_list(&self, expr: &PseudoExpr) -> bool {
        is_provably_list_with(expr, &self.proven, &self.list_returning)
    }
}

/// Test-facing view of the proven set.
#[cfg(test)]
fn collect_provably_list_var_ids(expr: &PseudoExpr) -> HashSet<VarId> {
    collect_list_proof(expr).proven
}

/// Compute the fixpoint for the whole render tree. Pure / read-only; called
/// once per render in compilable mode.
pub(in crate::decompile::render) fn collect_list_proof(expr: &PseudoExpr) -> ListProof {
    let mut scan = Scan::default();
    scan_expr(expr, &mut scan);

    // VarId-collision (Conflict) gate: an id bound by MORE than one binder
    // never enters S, and any fn whose let/self/param ids touch one is
    // vetoed — without it a proven let's id would "prove" an unrelated
    // same-id pattern binder.
    let conflicted: HashSet<VarId> = scan
        .binder_counts
        .iter()
        .filter(|(_, n)| **n > 1)
        .map(|(id, _)| *id)
        .collect();

    // Resolve rule (c)'s per-fn gates once; the per-slot all-call-sites check
    // re-runs every fixpoint round (it reads S).
    let mut fn_slots: Vec<(Vec<VarId>, Vec<SlotCall>)> = Vec::new();
    if !scan.saw_raw {
        for f in &scan.fns {
            if f.ids.iter().any(|i| scan.value_used.contains(i)) {
                continue;
            }
            if f.ids.iter().any(|i| conflicted.contains(i))
                || f.params.iter().any(|p| conflicted.contains(p))
            {
                continue;
            }
            if f.names.iter().any(|n| scan.idless_names.contains(n)) {
                continue;
            }
            let mut calls: Vec<SlotCall> = Vec::new();
            for i in &f.ids {
                if let Some(cs) = scan.calls.get(i) {
                    calls.extend(cs.iter().map(|c| SlotCall {
                        args: c.args,
                        is_self: c.enclosing_fn_ids.iter().any(|e| f.ids.contains(e)),
                    }));
                }
            }
            // ≥1 EXTERNAL (grounded) call required: an fn reachable only
            // from its own body is dead code, and an all-quantifier over
            // self-evidence alone would be trust-by-vacuity.
            if !calls.iter().any(|c| !c.is_self) {
                continue;
            }
            if calls.iter().any(|c| c.args.len() != f.params.len()) {
                continue;
            }
            fn_slots.push((f.params.clone(), calls));
        }
    }

    // Return-join candidates: id attribution must be safe (no conflicted
    // ids). Enumerability is NOT required — an fn's return shape depends
    // only on its body, not its callers; `Raw` elsewhere is also irrelevant
    // (a `Raw` inside the body surfaces as an unprovable leaf).
    let returning_candidates: Vec<&FnRec> = scan
        .fns
        .iter()
        .filter(|f| !f.ids.iter().any(|i| conflicted.contains(i)))
        .collect();

    let mut s: HashSet<VarId> = HashSet::new();
    let mut returning: HashMap<VarId, usize> = HashMap::new();
    loop {
        let before_s = s.len();
        let before_r = returning.len();
        for (vid, value) in &scan.let_values {
            if !s.contains(vid)
                && !conflicted.contains(vid)
                && is_provably_list_with(value, &s, &returning)
            {
                s.insert(*vid);
            }
        }
        for (tid, subject) in &scan.when_tails {
            if !s.contains(tid)
                && !conflicted.contains(tid)
                && is_provably_list_with(subject, &s, &returning)
            {
                s.insert(*tid);
            }
        }
        for (params, calls) in &fn_slots {
            for (slot, pid) in params.iter().enumerate() {
                if s.contains(pid) {
                    continue;
                }
                let aug = std::cell::OnceCell::new();
                let ok = calls.iter().all(|c| {
                    if c.is_self {
                        let aug = aug.get_or_init(|| {
                            augment_with_param(&s, *pid, &scan.when_tails, &conflicted, &returning)
                        });
                        is_provably_list_with(&c.args[slot], aug, &returning)
                    } else {
                        is_provably_list_with(&c.args[slot], &s, &returning)
                    }
                });
                if ok {
                    s.insert(*pid);
                }
            }
        }
        // Return join: an fn whose EVERY return leaf is provably a list
        // or an exact-arity SELF-call, with ≥ 1 grounded non-self leaf,
        // returns a list from every terminating activation. Induction is
        // strictly self-only — a co-recursive cycle cannot prove through
        // itself: each fn would need the other already in `returning`
        // from a prior round, and entry is only by grounded evidence.
        for f in &returning_candidates {
            if f.ids.iter().any(|i| returning.contains_key(i)) {
                continue;
            }
            let mut leaves: Vec<&PseudoExpr> = Vec::new();
            collect_return_leaves(f.body, &mut leaves);
            let mut grounded = false;
            let mut all_ok = true;
            for leaf in &leaves {
                if is_self_call(leaf, &f.ids, f.params.len()) {
                    continue;
                }
                if is_provably_list_with(leaf, &s, &returning) {
                    grounded = true;
                } else {
                    all_ok = false;
                    break;
                }
            }
            if all_ok && grounded {
                for i in &f.ids {
                    returning.insert(*i, f.params.len());
                }
            }
        }
        if s.len() == before_s && returning.len() == before_r {
            return ListProof {
                proven: s,
                list_returning: returning,
            };
        }
    }
}

/// The return leaves of an fn body: descend `Let`→body, `If`→both branches,
/// `When`→every clause body, name-matched `expect!`→value; skip diverging
/// tails; everything else is a leaf.
fn collect_return_leaves<'a>(body: &'a PseudoExpr, out: &mut Vec<&'a PseudoExpr>) {
    let mut pending: Vec<&'a PseudoExpr> = vec![body];

    while let Some(body) = pending.pop() {
        match body {
            PseudoExpr::Let { body, .. } => pending.push(body),
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
            }
            PseudoExpr::When { clauses, .. } => {
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                }
            }
            other => {
                if is_diverging(other) {
                    continue;
                }
                if let PseudoExpr::Apply { function, args } = other
                    && super::traversal::is_expect_bang(function)
                    && (args.len() == 2 || args.len() == 3)
                {
                    pending.push(&args[1]);
                    continue;
                }
                out.push(other);
            }
        }
    }
}

/// An exact-arity self-call leaf: head (`Force` wrappers peeled) is a `Var`
/// carrying one of the fn's own ids.
fn is_self_call(leaf: &PseudoExpr, fn_ids: &[VarId], arity: usize) -> bool {
    let PseudoExpr::Apply { function, args } = leaf else {
        return false;
    };
    if args.len() != arity {
        return false;
    }
    let mut head = function.as_ref();
    while let PseudoExpr::Force(inner) = head {
        head = inner.as_ref();
    }
    matches!(head, PseudoExpr::Var { id: Some(v), .. } if fn_ids.contains(v))
}

/// The self-call assumption set for param `p`: `S ∪ {p}` closed under the
/// when-tail rule (a tail of a list in the set is in the set). Everything in
/// the result is a list UNDER THE ASSUMPTION that `p` holds a list in the
/// enclosing activation.
fn augment_with_param(
    s: &HashSet<VarId>,
    p: VarId,
    when_tails: &[(VarId, &PseudoExpr)],
    conflicted: &HashSet<VarId>,
    list_returning: &HashMap<VarId, usize>,
) -> HashSet<VarId> {
    let mut aug = s.clone();
    aug.insert(p);
    loop {
        let before = aug.len();
        for (tid, subject) in when_tails {
            if !aug.contains(tid)
                && !conflicted.contains(tid)
                && is_provably_list_with(subject, &aug, list_returning)
            {
                aug.insert(*tid);
            }
        }
        if aug.len() == before {
            return aug;
        }
    }
}

/// A job on [`scan_expr`]'s stack. `PopFn` and `Clause` are the points run between two
/// child walks — the enclosing-fn stack is popped exactly where the fn-body descent
/// returned, and a clause's binders are recorded after the previous clause finished —
/// so each is its own step.
enum ScanStep<'a> {
    Visit(&'a PseudoExpr),
    /// Drop the last `n` ids off `enclosing_fn_ids`, closing an fn body.
    PopFn(usize),
    /// One `When` clause, with the subject its list-tail binder refers to.
    Clause {
        clause: &'a crate::pseudo::ast::WhenClause,
        subject: &'a PseudoExpr,
    },
}

/// Exhaustive scan. NO wildcard arm — child coverage mirrors
/// `fold::walk_inner` so a new `PseudoExpr` variant is a compile error here,
/// not a silent value-use hole.
fn scan_expr<'a>(expr: &'a PseudoExpr, scan: &mut Scan<'a>) {
    let mut steps: Vec<ScanStep<'a>> = vec![ScanStep::Visit(expr)];

    while let Some(step) = steps.pop() {
        let expr = match step {
            ScanStep::Visit(expr) => expr,
            ScanStep::PopFn(n) => {
                for _ in 0..n {
                    scan.enclosing_fn_ids.pop();
                }
                continue;
            }
            ScanStep::Clause { clause, subject } => {
                for bid in clause.pattern.bound_ids() {
                    scan.record_binder(bid);
                }
                // Reversed so they pop in source order: the pattern's
                // `Literal` payload, then the guard, then the body.
                steps.push(ScanStep::Visit(&clause.body));
                if let Some(guard) = &clause.guard {
                    steps.push(ScanStep::Visit(guard));
                }
                match &clause.pattern {
                    WhenPattern::List {
                        elements: _,
                        tail: Some(tail),
                    } => scan.when_tails.push((tail.id, subject)),
                    WhenPattern::Constructor { shape, fields, .. }
                        if *shape == ConstructorShape::Known(KnownConstructor::Cons)
                            && fields.len() == 2 =>
                    {
                        scan.when_tails.push((fields[1].id, subject))
                    }
                    WhenPattern::Literal(payload) => steps.push(ScanStep::Visit(payload)),
                    WhenPattern::List { .. }
                    | WhenPattern::Constructor { .. }
                    | WhenPattern::Tuple(_)
                    | WhenPattern::Pair(_, _)
                    | WhenPattern::Wildcard
                    | WhenPattern::Var(_) => {}
                }
                continue;
            }
        };
        match expr {
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                if let Some(lid) = id {
                    scan.record_binder(*lid);
                }
                // The body walk runs LAST in every case below, so it is pushed
                // FIRST and pops last.
                steps.push(ScanStep::Visit(body));
                match (id, value.as_ref()) {
                    (
                        Some(lid),
                        PseudoExpr::Lambda {
                            params,
                            body: fbody,
                        },
                    ) => {
                        for p in params {
                            scan.record_binder(p.id);
                        }
                        let let_name = let_display_name(expr);
                        scan.fns.push(FnRec {
                            ids: vec![*lid],
                            names: let_name.into_iter().collect(),
                            params: params.iter().map(|p| p.id).collect(),
                            body: fbody,
                        });
                        scan.enclosing_fn_ids.push(*lid);
                        steps.push(ScanStep::PopFn(1));
                        steps.push(ScanStep::Visit(fbody));
                    }
                    (
                        Some(lid),
                        PseudoExpr::RecFn {
                            name,
                            params,
                            body: fbody,
                        },
                    ) => {
                        // The let binder and the RecFn self-name may carry the
                        // SAME id (post-rename collapse) — that is one binder,
                        // not a collision: record/list it once.
                        if name.id != *lid {
                            scan.record_binder(name.id);
                        }
                        for p in params {
                            scan.record_binder(p.id);
                        }
                        let mut names: Vec<&'a str> = let_display_name(expr).into_iter().collect();
                        names.push(name.name.as_str());
                        if name.semantic_name != name.name {
                            names.push(name.semantic_name.as_str());
                        }
                        let mut ids = vec![*lid];
                        if name.id != *lid {
                            ids.push(name.id);
                        }
                        scan.fns.push(FnRec {
                            ids,
                            names,
                            params: params.iter().map(|p| p.id).collect(),
                            body: fbody,
                        });
                        scan.enclosing_fn_ids.push(*lid);
                        scan.enclosing_fn_ids.push(name.id);
                        steps.push(ScanStep::PopFn(2));
                        steps.push(ScanStep::Visit(fbody));
                    }
                    (Some(lid), other_value) => {
                        scan.let_values.push((*lid, other_value));
                        steps.push(ScanStep::Visit(value));
                    }
                    (None, _) => {
                        steps.push(ScanStep::Visit(value));
                    }
                }
            }
            PseudoExpr::Lambda { params, body } => {
                for p in params {
                    scan.record_binder(p.id);
                }
                steps.push(ScanStep::Visit(body));
            }
            PseudoExpr::RecFn { name, params, body } => {
                // A bare `RecFn` in value position escapes as a value; it is NOT
                // registered (its params can never be proven) — only its body is
                // scanned. Let-bound and IIFE forms are handled at their parents.
                scan.record_binder(name.id);
                for p in params {
                    scan.record_binder(p.id);
                }
                steps.push(ScanStep::Visit(body));
            }
            PseudoExpr::Apply { function, args } => {
                // Stray `Force` wrappers around call heads are decompiler
                // residue the renderer elides (`force(f)(arg)` prints `f(arg)`)
                // — peel them so the call is attributed instead of marking the
                // head value-used. A BARE (un-applied) `Force(Var)` elsewhere
                // still scans generically → value-use (fail-closed).
                let mut head = function.as_ref();
                while let PseudoExpr::Force(inner) = head {
                    head = inner.as_ref();
                }
                // The arg walks run LAST, so they are pushed FIRST (reversed, to
                // pop in source order) and the head's own jobs go on top.
                for a in args.iter().rev() {
                    steps.push(ScanStep::Visit(a));
                }
                match head {
                    // Call head: a CALL, not a value-use. Record the full arg
                    // slice + the enclosing-fn stack (self-vs-external split).
                    PseudoExpr::Var { id: Some(fid), .. } => {
                        scan.calls.entry(*fid).or_default().push(CallRec {
                            args: args.as_slice(),
                            enclosing_fn_ids: scan.enclosing_fn_ids.clone(),
                        });
                    }
                    // An id-less call head is an unattributable reference —
                    // the name-veto catches any same-named fn.
                    PseudoExpr::Var { id: None, name, .. } => {
                        scan.idless_names.insert(name.as_str());
                    }
                    // IIFE: `(rec fn g(..) { .. })(args)` — register g with this
                    // entry call (external — it happens outside g's body) so its
                    // self-recursion can participate.
                    PseudoExpr::RecFn { name, params, body } => {
                        scan.record_binder(name.id);
                        for p in params {
                            scan.record_binder(p.id);
                        }
                        let mut names: Vec<&'a str> = vec![name.name.as_str()];
                        if name.semantic_name != name.name {
                            names.push(name.semantic_name.as_str());
                        }
                        scan.fns.push(FnRec {
                            ids: vec![name.id],
                            names,
                            params: params.iter().map(|p| p.id).collect(),
                            body,
                        });
                        scan.calls.entry(name.id).or_default().push(CallRec {
                            args: args.as_slice(),
                            enclosing_fn_ids: scan.enclosing_fn_ids.clone(),
                        });
                        scan.enclosing_fn_ids.push(name.id);
                        steps.push(ScanStep::PopFn(1));
                        steps.push(ScanStep::Visit(body));
                    }
                    other => steps.push(ScanStep::Visit(other)),
                }
            }
            PseudoExpr::Var { id: Some(v), .. } => {
                scan.value_used.insert(*v);
            }
            PseudoExpr::Var { id: None, name, .. } => {
                scan.idless_names.insert(name.as_str());
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                if let Some(sn) = subject_name {
                    scan.record_binder(sn.id);
                }
                // Reversed: subject first, then the clauses in source order.
                for clause in clauses.iter().rev() {
                    steps.push(ScanStep::Clause {
                        clause,
                        subject: subject.as_ref(),
                    });
                }
                steps.push(ScanStep::Visit(subject));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                steps.push(ScanStep::Visit(else_branch));
                steps.push(ScanStep::Visit(then_branch));
                steps.push(ScanStep::Visit(condition));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    steps.push(ScanStep::Visit(t));
                }
                for e in elements.iter().rev() {
                    steps.push(ScanStep::Visit(e));
                }
            }
            PseudoExpr::Tuple(items) => {
                for i in items.iter().rev() {
                    steps.push(ScanStep::Visit(i));
                }
            }
            PseudoExpr::Pair(a, b) => {
                steps.push(ScanStep::Visit(b));
                steps.push(ScanStep::Visit(a));
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    steps.push(ScanStep::Visit(f));
                }
            }
            PseudoExpr::FieldAccess { record, .. } => steps.push(ScanStep::Visit(record)),
            PseudoExpr::IndexAccess { collection, .. } => steps.push(ScanStep::Visit(collection)),
            PseudoExpr::BinOp { left, right, .. } => {
                steps.push(ScanStep::Visit(right));
                steps.push(ScanStep::Visit(left));
            }
            PseudoExpr::UnOp { operand, .. } => steps.push(ScanStep::Visit(operand)),
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    steps.push(ScanStep::Visit(a));
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                steps.push(ScanStep::Visit(inner))
            }
            PseudoExpr::Trace { message, value } => {
                steps.push(ScanStep::Visit(value));
                steps.push(ScanStep::Visit(message));
            }
            PseudoExpr::Raw { .. } => {
                scan.saw_raw = true;
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
}

/// The display name of a `Let` node, for the id-less-Var veto.
fn let_display_name(expr: &PseudoExpr) -> Option<&str> {
    match expr {
        PseudoExpr::Let { name, .. } => Some(name.as_str()),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
