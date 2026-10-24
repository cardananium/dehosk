//! Extract repeated subexpressions to a local `let` binding.
//!
//! V1 scripts often repeat one non-trivial subexpression inside a
//! scope. Alpha-equivalent copies (structure only; binder names
//! differ) collapse to `let w = …` so later uses are refs. Roots:
//! `Lambda`/`RecFn` bodies, `when`-clause bodies, `if` branches, and
//! (≥2-ref) `Let` bodies. Duplicates keyed by a `Canonicaliser`-style
//! signature; ≥2 occurrences of one non-trivial signature (≥ 5 AST
//! nodes) wrap the root in `Let { name: "w", id: fresh, value: first
//! occurrence }` and replace every occurrence with a ref to that
//! binder.
//!
//! Every free var of the duplicate must also be free in the root, or
//! the `let` would reference a variable bound below it. The duplicate
//! must be evaluated on every path (`collect_eval_position_sigs`):
//! the hoisted `let` is eager, so lifting a value reached only inside
//! `if`/`when` branches, `&&`/`||` right-operands, `delay` thunks, or
//! nested fn-bodies would force evaluation on paths that skipped it.
//! Sharp case: a recursive self-call duplicated across both branches
//! of an `if` *inside* a list-fold cons clause; the `[]` base never
//! evaluates it, so hoisting above the `when` loops forever. Skip
//! `trace` and messaged `fail` — dedup would merge two identical
//! emissions. A message-less abort is extractable only when its first
//! occurrence dominates the root's eager spine, so the abort is never
//! reordered ahead of an earlier effect. Skip trivial nodes (Var,
//! literal, simple FieldAccess). Sequential extractions all use `w`;
//! `prepare_for_render` re-runs `disambiguate_shadowed_lets` immediately
//! after this pass, so extras become `w_2`, `w_3`, … with uses rewired by `VarId`.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::pseudo::ast::{BinaryOp, PseudoExpr, WhenClause};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn extract_repeated_subexpr(expr: PseudoExpr) -> PseudoExpr {
    let mut walk = Walk::default();
    let expr = rewrite_bottom_up(expr, |expr| try_rewrite(expr, &mut walk));
    // `try_rewrite` only wraps bodies it meets during the walk, so a
    // validator whose entry lambda was peeled leaves its top-level `Let`
    // chain unprocessed. Treat the ROOT as an extraction body when it is
    // not already a scope-opener.
    match expr {
        PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => expr,
        // Abort-only at the bare root: extract just the dominating
        // bare-abort candidate, not general pure ones — those belong to
        // the scoped roots, where `collect_eval_position_sigs` also stops
        // at an effect-bearing eager sibling so nothing is hoisted above
        // an emission. The abort path is gated independently by
        // `first_occurrence_dominates`.
        other => wrap_with_extracted_lets(other, /* abort_only */ true, &mut walk),
    }
}

/// What one extraction walk carries from body to body.
///
/// Bodies nest — every lambda body, branch and clause body is one, and so is
/// a `let`'s body — and each looks at everything below it, so a chain of
/// them as deep as the script likes would cost time quadratic in that depth.
struct Walk {
    /// Work left, counted in nodes looked at. Real scripts use a small
    /// fraction (a 15 KB mainnet validator takes about a million); past
    /// it the remaining bodies are left as they are — a missed extraction,
    /// never an unsound one — so no script can make the pass take minutes.
    budget: usize,
    /// `let`s whose body was already found to hold no candidate. The walk is
    /// bottom-up and a body that held none was not rewritten, so an
    /// enclosing body need not look through it again.
    clean_let_bodies: std::collections::HashSet<VarId>,
    /// Every `let` id met so far, and those met more than once.
    seen_lets: std::collections::HashSet<VarId>,
    shared_ids: std::collections::HashSet<VarId>,
}

impl Default for Walk {
    fn default() -> Self {
        Walk {
            budget: 16_000_000,
            clean_let_bodies: Default::default(),
            seen_lets: Default::default(),
            shared_ids: Default::default(),
        }
    }
}

impl Walk {
    /// Spend `n` nodes of work; false once the budget is gone.
    fn spend(&mut self, n: usize) -> bool {
        self.budget = self.budget.saturating_sub(n);
        self.budget > 0
    }
}

fn try_rewrite(expr: PseudoExpr, walk: &mut Walk) -> PseudoExpr {
    // Shapes with a single "body" that a `Let` can wrap.
    match expr {
        PseudoExpr::Lambda { params, body } => {
            let body = wrap_with_extracted_lets(body.into_inner(), /* abort_only */ false, walk);
            PseudoExpr::Lambda {
                params,
                body: PBox::new(body),
            }
        }
        PseudoExpr::RecFn { name, params, body } => {
            let body = wrap_with_extracted_lets(body.into_inner(), /* abort_only */ false, walk);
            PseudoExpr::RecFn {
                name,
                params,
                body: PBox::new(body),
            }
        }
        // When-clause bodies and If branches are extraction scopes too: a
        // duplicate confined to one arm is invisible from the enclosing
        // fn-body root (`collect_eval_position_sigs` does not descend into
        // conditional branches), and hoisting WITHIN the arm keeps the
        // evaluation exactly as conditional as before — the `let` lives
        // inside the branch. All gates (eval-position from the ARM root,
        // free-vars, overlap, effect / abort-dominance) apply unchanged.
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => PseudoExpr::When {
            subject,
            subject_name,
            clauses: clauses
                .into_iter()
                .map(|c| WhenClause {
                    pattern: c.pattern,
                    guard: c.guard,
                    body: wrap_with_extracted_lets(c.body, /* abort_only */ false, walk),
                })
                .collect(),
        },
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => PseudoExpr::If {
            condition,
            then_branch: PBox::new(wrap_with_extracted_lets(
                then_branch.into_inner(),
                /* abort_only */ false,
                walk,
            )),
            else_branch: PBox::new(wrap_with_extracted_lets(
                else_branch.into_inner(),
                /* abort_only */ false,
                walk,
            )),
        },
        // A Let BODY is an extraction root too — needed when a duplicate's
        // free vars include THIS let's binder: the enclosing fn/arm root
        // would have to hoist the candidate above its binding (its
        // free-vars gate rightly rejects that), while the point just below
        // the binding is sound. Pre-filter: only a binder referenced >= 2
        // times can host such a duplicate (one reference per occurrence),
        // which keeps the per-root signature scan off straight-line lets.
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            // Two `let`s sharing an id cannot vouch for each other's body.
            if let Some(vid) = id
                && !walk.seen_lets.insert(vid)
            {
                walk.clean_let_bodies.remove(&vid);
                walk.shared_ids.insert(vid);
            }
            let body = if let Some(vid) = id
                && references_at_least_twice(&body, vid)
            {
                let body = body.into_inner();
                if may_hold_candidate(&body, walk) {
                    extract_from(body, /* abort_only */ false, walk)
                } else {
                    if !walk.shared_ids.contains(&vid) {
                        walk.clean_let_bodies.insert(vid);
                    }
                    body
                }
            } else {
                body.into_inner()
            };
            PseudoExpr::Let {
                name,
                id,
                value,
                body: PBox::new(body),
            }
        }
        other => other,
    }
}

/// Whether `vid` is referenced at least twice in `expr`, pattern-literal
/// payloads included. Stops at the second reference: it runs once per `let`
/// of a chain, over the rest of the chain.
fn references_at_least_twice(expr: &PseudoExpr, vid: VarId) -> bool {
    let mut seen = 0;
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::Var { id: Some(id), .. } = current
            && *id == vid
        {
            seen += 1;
            if seen == 2 {
                return true;
            }
        }
        current.child_refs_into(&mut pending);
    }
    false
}

/// Inspect `body` for repeated complex subexpressions and wrap it in
/// `let w = <duplicate>` for each, rewriting every occurrence to the
/// new binder. Candidates whose free vars would be unbound at the
/// body's scope are skipped.
fn wrap_with_extracted_lets(body: PseudoExpr, abort_only: bool, walk: &mut Walk) -> PseudoExpr {
    // Every nested lambda body, `if` branch and clause body is a root of its
    // own, so a chain of them would pay one whole-body analysis per level.
    // Most cannot hold a candidate at all, and their eager spine says so.
    if !may_hold_candidate(&body, walk) {
        return body;
    }
    extract_from(body, abort_only, walk)
}

/// [`wrap_with_extracted_lets`] for a body [`may_hold_candidate`] passed.
fn extract_from(body: PseudoExpr, abort_only: bool, walk: &mut Walk) -> PseudoExpr {

    // A candidate can only be hoisted to the top of `body` if every
    // var it references is already visible there. Params in scope
    // aren't tracked here, so the check is the conservative
    // `free(candidate) ⊆ free(body)` — it rejects some safe
    // candidates but never allows an unsafe extraction.
    let body_free = collect_free_vars(&body);

    let facts = Facts::of(&body);
    if !walk.spend(facts.of.len()) {
        return body;
    }
    let shared = SharedSignatures::of(&body, &facts);

    // Signatures in always-evaluated position relative to `body`. Only
    // these are safe to hoist into an eager `let` at the body's top; a
    // candidate absent here is reached only under a conditional or
    // thunk and must stay put.
    let eval_sigs = collect_eval_position_sigs(&body, &facts, &shared);

    // (signature, occurrences, first occurrence, holds a bare abort, its facts)
    let mut candidates: Vec<(String, usize, PseudoExpr, bool, NodeFacts)> = shared
        .counts
        .into_iter()
        .filter(|(sig, (c, _))| *c >= 2 && eval_sigs.contains(sig))
        .filter_map(|(sig, (c, first))| {
            // Reject if rep's free vars escape the body's scope.
            let rep_free = collect_free_vars(first);
            if !rep_free.is_subset(&body_free) {
                return None;
            }
            // A candidate containing a bare abort (`Error { message: None }`,
            // e.g. a `_ -> fail` guard) is sound to hoist only when its first
            // occurrence DOMINATES the body — nothing fail/diverge-capable runs
            // before it — so the hoisted abort is never reordered ahead of an
            // earlier effect. The effect gate lets a bare abort through as
            // non-blocking; this is the placement gate. At most one candidate
            // can dominate, so two abort candidates can never race.
            let target = facts.get(first);
            let abort = target.bare_abort;
            if abort
                && !first_occurrence_dominates(&body, |node| {
                    let f = facts.get(node);
                    f.shape == target.shape && f.size == target.size && signature(node) == sig
                })
            {
                return None;
            }
            Some((sig, c, first.clone(), abort, target))
        })
        .collect();
    // With a dominating bare-abort candidate present, extract only abort
    // candidates and drop the pure ones. A pure candidate NESTED inside the
    // abort candidate would otherwise land in a `let` OUTSIDE the abort
    // `let` (the abort fails the post-substitution recheck), evaluating that
    // pure op BEFORE the abort and reordering a possible divergence ahead of
    // it. Dropped pure candidates stay inside the abort `let`'s value — a
    // missed extraction, never unsound.
    if abort_only || candidates.iter().any(|(_, _, _, abort, _)| *abort) {
        candidates.retain(|(_, _, _, abort, _)| *abort);
    }
    // A total order over candidates so no HashMap-iteration
    // nondeterminism leaks: two decompile runs of the same input
    // must pick the same candidates in the same order to mint
    // identical VarIds via `VarId::fresh_binding()`.
    candidates.sort_by(|a, b| {
        // Abort-bearing candidates sort LAST so they are hoisted OUTERMOST
        // (= evaluated FIRST). `first_occurrence_dominates` proved each is
        // the first risky op, so an outermost `let` keeps its abort at that
        // original position; pure candidates, hoisted inside, all came after
        // it. Otherwise a pure candidate outside an abort `let` would
        // evaluate before the abort and could diverge/fail first.
        // false (pure) < true (abort).
        a.3.cmp(&b.3)
            .then_with(|| b.1.cmp(&a.1))
            .then_with(|| b.0.len().cmp(&a.0.len()))
            .then_with(|| a.0.cmp(&b.0))
    });
    if candidates.is_empty() {
        return body;
    }
    // Apply candidates in order. Each substitution may invalidate
    // some siblings (overlapping subtrees) — re-check after each
    // round by recomputing signatures of the rewritten body.
    let mut current = body;
    let mut consumed: std::collections::HashSet<String> = Default::default();
    for (sig, _count, rep, _abort, target) in candidates {
        if consumed.contains(&sig) {
            continue;
        }
        // Re-verify the signature still has ≥2 occurrences in
        // `current` (a previous round may have rewritten some away).
        let occurrences = Occurrences::of(&current, &sig, target);
        walk.spend(occurrences.looked_at);
        if occurrences.counted < 2 {
            continue;
        }
        let w_id = VarId::fresh_binding();
        // `w`, not `_w`: an extracted subexpression occurs ≥2× in
        // always-evaluated position, so the binder is always used — the
        // leading `_` of the unused-binder convention would mislead.
        let w_name = "w".to_string();
        let w_var = PseudoExpr::Var {
            name: w_name.clone(),
            id: Some(w_id),
        };
        substitute_in_place(&mut current, &occurrences.nodes, &w_var);
        current = PseudoExpr::Let {
            name: w_name,
            id: Some(w_id),
            value: PBox::new(rep),
            body: PBox::new(current),
        };
        consumed.insert(sig);
    }
    current
}

/// What the extraction asks about each node of one body, folded bottom-up
/// in a single walk.
///
/// Asked one subtree walk at a time — the node count, the effect scans, the
/// signature string — at every node, the questions cost time and memory
/// quadratic in the body's depth, and a script picks its depth: 32 KiB of
/// flat nests tens of thousands of constructors.
pub(super) struct Facts {
    of: HashMap<*const PseudoExpr, NodeFacts>,
}

#[derive(Clone, Copy)]
pub(super) struct NodeFacts {
    /// Nodes in the subtree, counted through [`scope_children`] (pattern-
    /// literal payloads not included).
    size: usize,
    /// Holds an observable effect — a `trace` or a messaged `fail`, pattern
    /// literals included — which bars extraction.
    effect: bool,
    /// Holds a bare `Error { message: None }`, pattern literals included.
    bare_abort: bool,
    /// Eager evaluation always reaches an abort (`Error`, bare or messaged)
    /// before producing a value, through [`eager_children`] only.
    eager_abort: bool,
    /// Worth extracting: not trivial, at least five nodes, free of effects,
    /// not a builtin call on literals alone.
    extractable: bool,
    /// A hash of what [`Canon`] writes for the node, binder placeholders and
    /// variable references left out. Nodes with one signature share it, so a
    /// signature is only built for a node that shares its shape. The same
    /// holds for [`abstract_signature`], which differs only in how it writes
    /// variables.
    shape: u64,
}

impl NodeFacts {
    /// `(shape, size)`: two nodes with one signature, abstract or not, have
    /// one key.
    pub(super) fn key(&self) -> (u64, usize) {
        (self.shape, self.size)
    }
}

impl Facts {
    pub(super) fn of(root: &PseudoExpr) -> Self {
        let mut of: HashMap<*const PseudoExpr, NodeFacts> = HashMap::new();
        // Post-order over every child, pattern literals included: a node is
        // folded once all of its children are.
        let mut pending: Vec<(&PseudoExpr, bool)> = vec![(root, false)];
        let mut kids: Vec<&PseudoExpr> = Vec::new();
        while let Some((node, expanded)) = pending.pop() {
            if expanded {
                let facts = NodeFacts::fold(node, &of);
                of.insert(node as *const PseudoExpr, facts);
                continue;
            }
            pending.push((node, true));
            kids.clear();
            node.child_refs_into(&mut kids);
            pending.extend(kids.iter().map(|kid| (*kid, false)));
        }
        Facts { of }
    }

    pub(super) fn get(&self, node: &PseudoExpr) -> NodeFacts {
        self.of[&(node as *const PseudoExpr)]
    }
}

impl NodeFacts {
    /// The node's facts from its children's, which `of` already holds.
    fn fold(node: &PseudoExpr, of: &HashMap<*const PseudoExpr, NodeFacts>) -> NodeFacts {
        let get = |child: &PseudoExpr| of[&(child as *const PseudoExpr)];
        let mut all: Vec<&PseudoExpr> = Vec::new();
        node.child_refs_into(&mut all);

        let size = 1 + scope_children(node)
            .into_iter()
            .map(|child| get(child).size)
            .sum::<usize>();
        let effect = is_trace_node(node)
            || matches!(node, PseudoExpr::Error { message: Some(_) })
            || all.iter().any(|child| get(child).effect);
        let bare_abort = matches!(node, PseudoExpr::Error { message: None })
            || all.iter().any(|child| get(child).bare_abort);
        let eager_abort = match node {
            PseudoExpr::Error { .. } => true,
            PseudoExpr::Let { value, body, .. } => get(value).eager_abort || get(body).eager_abort,
            other => eager_children(other)
                .into_iter()
                .any(|child| get(child).eager_abort),
        };
        // BuiltinCall with only literal args — extracting just adds a
        // let with no readability gain.
        let literal_call = matches!(node, PseudoExpr::BuiltinCall { args, .. } if args.iter().all(|a| {
            matches!(
                a,
                PseudoExpr::Int(_)
                    | PseudoExpr::ByteArray(_)
                    | PseudoExpr::String(_)
                    | PseudoExpr::Bool(_)
                    | PseudoExpr::Unit
            )
        }));
        // Never extract an expression containing an observable effect: a
        // `trace` or a messaged `fail`. Extraction dedups occurrences —
        // merging two identical `trace`s into one changes the emitted
        // log — and hoists the value to the top of the body, which can
        // move the emission ahead of a preceding binding that would
        // itself have diverged first. `collect_eval_position_sigs`
        // already prevents hoisting out of a conditional; this covers
        // the sequential-reordering case.
        let extractable = extractable_kind(node) && !effect && !literal_call && size >= 5;

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        hash_own_shape(node, &mut hasher);
        for child in &all {
            get(child).shape.hash(&mut hasher);
        }
        NodeFacts {
            size,
            effect,
            bare_abort,
            eager_abort,
            extractable,
            shape: hasher.finish(),
        }
    }
}

/// Worth extracting by kind alone — the size and effect gates aside:
/// - Not itself a `Let`, `Lambda`, or `RecFn` (those open new scopes).
/// - Not a trivial projector (`Var`, a literal, `var.fst`, etc.).
fn extractable_kind(expr: &PseudoExpr) -> bool {
    if matches!(
        expr,
        PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Let { .. }
            | PseudoExpr::Lambda { .. }
            | PseudoExpr::RecFn { .. }
    ) {
        return false;
    }
    // FieldAccess on a Var (e.g., `x.fst`) is trivial.
    !matches!(expr, PseudoExpr::FieldAccess { record, .. } if matches!(record.as_ref(), PseudoExpr::Var { .. }))
}

/// Feed `hasher` the part of [`Canon`]'s text that is the node's own: its
/// kind and its non-child data, but no binder placeholder or variable
/// reference. Equal signatures therefore always hash alike; the converse is
/// left to the signature itself.
fn hash_own_shape(expr: &PseudoExpr, hasher: &mut impl Hasher) {
    use crate::pseudo::ast::WhenPattern;

    std::mem::discriminant(expr).hash(hasher);
    match expr {
        PseudoExpr::Lambda { params, .. } | PseudoExpr::RecFn { params, .. } => {
            params.len().hash(hasher)
        }
        PseudoExpr::Apply { args, .. } => args.len().hash(hasher),
        PseudoExpr::When { clauses, .. } => {
            clauses.len().hash(hasher);
            for clause in clauses {
                std::mem::discriminant(&clause.pattern).hash(hasher);
                match &clause.pattern {
                    WhenPattern::Constructor { tag, fields, .. } => {
                        tag.hash(hasher);
                        fields.len().hash(hasher);
                    }
                    WhenPattern::List { elements, tail } => {
                        elements.len().hash(hasher);
                        tail.is_some().hash(hasher);
                    }
                    WhenPattern::Tuple(fields) => fields.len().hash(hasher),
                    WhenPattern::Pair(..)
                    | WhenPattern::Wildcard
                    | WhenPattern::Literal(_)
                    | WhenPattern::Var(_) => {}
                }
                clause.guard.is_some().hash(hasher);
            }
        }
        PseudoExpr::List { elements, tail } => {
            elements.len().hash(hasher);
            tail.is_some().hash(hasher);
        }
        PseudoExpr::Tuple(elements) => elements.len().hash(hasher),
        PseudoExpr::Constr {
            tag, fields, shape, ..
        } => {
            tag.hash(hasher);
            format!("{:?}", shape).hash(hasher);
            fields.len().hash(hasher);
        }
        PseudoExpr::FieldAccess { selector, .. } => format!("{:?}", selector).hash(hasher),
        PseudoExpr::IndexAccess { index, .. } => index.hash(hasher),
        PseudoExpr::BinOp { op, .. } => format!("{:?}", op).hash(hasher),
        PseudoExpr::UnOp { op, .. } => format!("{:?}", op).hash(hasher),
        PseudoExpr::BuiltinCall { name, args } => {
            format!("{:?}", name).hash(hasher);
            args.len().hash(hasher);
        }
        PseudoExpr::Int(n) => n.hash(hasher),
        PseudoExpr::ByteArray(bytes) => bytes.hash(hasher),
        PseudoExpr::String(text) => text.hash(hasher),
        PseudoExpr::Bool(b) => b.hash(hasher),
        PseudoExpr::Error { message } => message.hash(hasher),
        PseudoExpr::HelperSymbol(symbol) => format!("{:?}", symbol).hash(hasher),
        // The kind is all `Canon` writes of these (a `Data` or `Raw` payload
        // is not written at all).
        PseudoExpr::Var { .. }
        | PseudoExpr::Let { .. }
        | PseudoExpr::If { .. }
        | PseudoExpr::Pair(..)
        | PseudoExpr::Delay(_)
        | PseudoExpr::Force(_)
        | PseudoExpr::Trace { .. }
        | PseudoExpr::Unit
        | PseudoExpr::Raw { .. }
        | PseudoExpr::Data(_) => {}
    }
}

/// Whether `body` can hold a candidate at all, judged from its eager spine
/// without building any facts.
///
/// A candidate sits in always-evaluated position and occurs twice, so it is
/// never `body` itself — nothing inside `body` can repeat the whole of it —
/// and, being at least five nodes, it has children. This walks a superset of
/// the always-evaluated positions (it does not stop after an aborting or
/// effectful sibling).
fn may_hold_candidate(body: &PseudoExpr, walk: &mut Walk) -> bool {
    let mut pending: Vec<&PseudoExpr> = Vec::new();
    push_eval_position_children(body, &mut pending, walk);
    let mut looked_at = 0;
    let mut found = false;
    while let Some(current) = pending.pop() {
        looked_at += 1;
        if extractable_kind(current) && has_at_least_nodes(current, 5) {
            found = true;
            break;
        }
        push_eval_position_children(current, &mut pending, walk);
    }
    // Out of budget, nothing more is extracted.
    walk.spend(looked_at) && found
}

/// Whether `expr` has at least `n` nodes as [`NodeFacts`] counts them,
/// looking at no more than `n` of them.
fn has_at_least_nodes(expr: &PseudoExpr, n: usize) -> bool {
    let mut seen = 0;
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        seen += 1;
        if seen >= n {
            return true;
        }
        pending.extend(scope_children(current));
    }
    false
}

/// The children [`collect_eval_position_sigs`] descends into, before it
/// stops at an aborting or effectful sibling — except below the body of a
/// `let` already found clean, where only the body's own root is left to
/// look at.
fn push_eval_position_children<'a>(
    expr: &'a PseudoExpr,
    out: &mut Vec<&'a PseudoExpr>,
    walk: &Walk,
) {
    if let PseudoExpr::Let {
        id: Some(id),
        value,
        body,
        ..
    } = expr
        && walk.clean_let_bodies.contains(id)
    {
        out.push(value);
        if extractable_kind(body) && has_at_least_nodes(body, 5) {
            out.push(body);
        }
        return;
    }
    match expr {
        PseudoExpr::If { condition, .. } => out.push(condition),
        PseudoExpr::When { subject, .. } => out.push(subject),
        PseudoExpr::BinOp {
            op: BinaryOp::And | BinaryOp::Or,
            left,
            ..
        } => out.push(left),
        PseudoExpr::Delay(_) | PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => {}
        other => out.extend(scope_children(other)),
    }
}

/// Occurrence counts of the signatures `body`'s extractable nodes share,
/// over the nodes a pre-order walk through [`scope_children`] meets.
///
/// A node whose shape no other extractable node has cannot share its
/// signature: it occurs once, can never be a candidate, and its signature —
/// a string as long as its subtree — is never built.
struct SharedSignatures<'a> {
    /// Signature → (occurrences, first occurrence in pre-order).
    counts: HashMap<String, (usize, &'a PseudoExpr)>,
    /// The signature of each node counted in `counts`.
    of: HashMap<*const PseudoExpr, String>,
}

impl<'a> SharedSignatures<'a> {
    fn of(body: &'a PseudoExpr, facts: &Facts) -> Self {
        let mut extractable: Vec<&'a PseudoExpr> = Vec::new();
        let mut pending: Vec<&'a PseudoExpr> = vec![body];
        while let Some(current) = pending.pop() {
            if facts.get(current).extractable {
                extractable.push(current);
            }
            pending.extend(scope_children(current).into_iter().rev());
        }
        let mut per_shape: HashMap<(u64, usize), usize> = HashMap::new();
        for node in &extractable {
            let f = facts.get(node);
            *per_shape.entry((f.shape, f.size)).or_insert(0) += 1;
        }
        let mut counts: HashMap<String, (usize, &'a PseudoExpr)> = HashMap::new();
        let mut of = HashMap::new();
        for node in extractable {
            let f = facts.get(node);
            if per_shape[&(f.shape, f.size)] < 2 {
                continue;
            }
            let sig = signature(node);
            counts.entry(sig.clone()).or_insert((0, node)).0 += 1;
            of.insert(node as *const PseudoExpr, sig);
        }
        SharedSignatures { counts, of }
    }
}

/// Record signatures of extractable subexpressions that sit in a
/// position evaluated on EVERY path through `expr` (the extraction
/// point). Descends only through unconditionally-evaluated children,
/// stopping at `if`/`when` branches, `&&`/`||` right-operands, `delay`
/// thunks and `Lambda`/`RecFn` bodies. A signature past one of those
/// boundaries is NOT recorded, so `wrap_with_extracted_lets` refuses
/// to hoist it: binding it eagerly at the top would change
/// strictness/termination. Conservative — a value in fact always
/// evaluated but reachable only under a `force(delay …)` is skipped
/// too, costing a missed extraction, never an unsafe one.
///
/// Only shared signatures are recorded: any other occurs once and can never
/// be a candidate.
fn collect_eval_position_sigs(
    expr: &PseudoExpr,
    facts: &Facts,
    shared: &SharedSignatures<'_>,
) -> std::collections::HashSet<String> {
    let mut out: std::collections::HashSet<String> = Default::default();
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        if let Some(sig) = shared.of.get(&(cur as *const PseudoExpr)) {
            out.insert(sig.clone());
        }
        match cur {
            // Only the condition is always evaluated; the branches are not.
            PseudoExpr::If { condition, .. } => pending.push(condition),
            // Only the scrutinee is always evaluated; clause guards/bodies
            // are conditional on which arm matches.
            PseudoExpr::When { subject, .. } => pending.push(subject),
            // `&&` / `||` short-circuit: the left operand is always
            // evaluated, the right one only conditionally.
            PseudoExpr::BinOp {
                op: BinaryOp::And | BinaryOp::Or,
                left,
                ..
            } => pending.push(left),
            // Deferred / lazy positions — stop descending.
            PseudoExpr::Delay(_) | PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => {}
            // Everything else evaluates all of its children eagerly, IN ORDER —
            // but STOP after a child that unconditionally aborts: its later
            // siblings are never reached, so they are NOT always-evaluated.
            // Otherwise `Pair(fail, p())` would record `p()` as always-evaluated
            // and a pure-but-diverging `p()` could be hoisted ahead of the abort.
            other => {
                let mut kids: Vec<&PseudoExpr> = Vec::new();
                for c in scope_children(other) {
                    kids.push(c);
                    // Stop after an aborting child (its later siblings never
                    // run) and after an effect-bearing child: hoisting a later
                    // sibling's candidate to the root top would reorder it
                    // ahead of the emission, so a trace is an abort boundary
                    // too.
                    let f = facts.get(c);
                    if f.eager_abort || f.effect {
                        break;
                    }
                }
                pending.extend(kids.into_iter().rev());
            }
        }
    }
    out
}

/// Where `sig` occurs in `expr`: how often among the nodes a pre-order walk
/// through [`scope_children`] meets (what decides whether it is still worth a
/// `let`), and every node a substitution replaces — pattern-literal payloads
/// included.
struct Occurrences {
    counted: usize,
    nodes: std::collections::HashSet<*const PseudoExpr>,
    /// Nodes the search folded facts for.
    looked_at: usize,
}

impl Occurrences {
    /// `target` is the facts of a node with signature `sig`: every node with
    /// that signature shares its shape and size.
    fn of(expr: &PseudoExpr, sig: &str, target: NodeFacts) -> Self {
        use crate::pseudo::ast::WhenPattern;

        let facts = Facts::of(expr);
        let looked_at = facts.of.len();
        let mut counted = 0;
        let mut nodes = std::collections::HashSet::new();
        // (node, reached without passing through a pattern-literal payload)
        let mut pending: Vec<(&PseudoExpr, bool)> = vec![(expr, true)];
        let mut kids: Vec<&PseudoExpr> = Vec::new();
        while let Some((current, scoped)) = pending.pop() {
            let f = facts.get(current);
            // An occurrence's descendants are smaller, so none of them can
            // share its signature: no need to look inside.
            if f.extractable
                && f.shape == target.shape
                && f.size == target.size
                && signature(current) == sig
            {
                nodes.insert(current as *const PseudoExpr);
                if scoped {
                    counted += 1;
                }
                continue;
            }
            if let PseudoExpr::When {
                subject, clauses, ..
            } = current
            {
                pending.push((subject, scoped));
                for clause in clauses {
                    if let WhenPattern::Literal(lit) = &clause.pattern {
                        pending.push((lit, false));
                    }
                    if let Some(guard) = &clause.guard {
                        pending.push((guard, scoped));
                    }
                    pending.push((&clause.body, scoped));
                }
            } else {
                kids.clear();
                current.child_refs_into(&mut kids);
                pending.extend(kids.iter().map(|kid| (*kid, scoped)));
            }
        }
        Occurrences {
            counted,
            nodes,
            looked_at,
        }
    }
}

/// One pending step of [`collect_free_vars`]'s stack. `Bind` / `Unbind` are
/// the scope edits between two child walks — a `let` binder opens only over
/// the body, a clause's pattern binders only over its guard and body — so
/// each is its own step.
enum FvStep<'a> {
    Visit(&'a PseudoExpr),
    Bind(Vec<VarId>),
    Unbind(Vec<VarId>),
}

/// Collect all VarIds that appear FREE in `expr` (not bound by an
/// inner Let/Lambda/RecFn/WhenPattern).
pub(super) fn collect_free_vars(expr: &PseudoExpr) -> std::collections::HashSet<VarId> {
    let mut out: std::collections::HashSet<VarId> = std::collections::HashSet::new();
    let mut bound: std::collections::HashSet<VarId> = std::collections::HashSet::new();
    let mut steps: Vec<FvStep<'_>> = vec![FvStep::Visit(expr)];

    while let Some(step) = steps.pop() {
        let expr = match step {
            FvStep::Visit(expr) => expr,
            FvStep::Bind(ids) => {
                for v in &ids {
                    bound.insert(*v);
                }
                continue;
            }
            FvStep::Unbind(ids) => {
                for v in &ids {
                    bound.remove(v);
                }
                continue;
            }
        };
        match expr {
            PseudoExpr::Var { id: Some(v), .. } => {
                if !bound.contains(v) {
                    out.insert(*v);
                }
            }
            PseudoExpr::Let {
                id: Some(let_id),
                value,
                body,
                ..
            } => {
                // Reversed: value (still outside the binding), bind, body,
                // unbind.
                steps.push(FvStep::Unbind(vec![*let_id]));
                steps.push(FvStep::Visit(body));
                steps.push(FvStep::Bind(vec![*let_id]));
                steps.push(FvStep::Visit(value));
            }
            PseudoExpr::Lambda { params, body } => {
                let pre: Vec<_> = params.iter().map(|p| p.id).collect();
                steps.push(FvStep::Unbind(pre.clone()));
                steps.push(FvStep::Visit(body));
                steps.push(FvStep::Bind(pre));
            }
            PseudoExpr::RecFn { name, params, body } => {
                let pre: Vec<_> = params.iter().map(|p| p.id).collect();
                // This removes the params, then the self name; a
                // set makes the order immaterial.
                let mut off = pre.clone();
                off.push(name.id);
                let mut on = vec![name.id];
                on.extend(pre);
                steps.push(FvStep::Unbind(off));
                steps.push(FvStep::Visit(body));
                steps.push(FvStep::Bind(on));
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                // Built in source order, then drained onto `steps` in
                // reverse so the jobs pop in source order.
                let mut jobs: Vec<FvStep<'_>> = Vec::new();
                for c in clauses {
                    // A `Literal` pattern's payload is an executable expression
                    // matched against the subject in the OUTER scope — its var
                    // references are FREE (it binds nothing). Without visiting it,
                    // a candidate whose literal pattern references a locally-bound
                    // var would pass the `free(rep) ⊆ free(body)` gate and could be
                    // hoisted above that binder.
                    if let crate::pseudo::ast::WhenPattern::Literal(e) = &c.pattern {
                        jobs.push(FvStep::Visit(e));
                    }
                    let pat_binders = pattern_binders(&c.pattern);
                    jobs.push(FvStep::Bind(pat_binders.clone()));
                    if let Some(g) = &c.guard {
                        jobs.push(FvStep::Visit(g));
                    }
                    jobs.push(FvStep::Visit(&c.body));
                    jobs.push(FvStep::Unbind(pat_binders));
                }
                while let Some(job) = jobs.pop() {
                    steps.push(job);
                }
                steps.push(FvStep::Visit(subject));
            }
            other => {
                for c in scope_children(other).into_iter().rev() {
                    steps.push(FvStep::Visit(c));
                }
            }
        }
    }
    out
}

pub(super) fn pattern_binders(p: &crate::pseudo::ast::WhenPattern) -> Vec<VarId> {
    use crate::pseudo::ast::WhenPattern;
    match p {
        WhenPattern::Constructor { fields, .. } => fields.iter().map(|b| b.id).collect(),
        WhenPattern::List { elements, tail } => {
            let mut v: Vec<_> = elements.iter().map(|b| b.id).collect();
            if let Some(t) = tail {
                v.push(t.id);
            }
            v
        }
        WhenPattern::Tuple(fs) => fs.iter().map(|b| b.id).collect(),
        WhenPattern::Pair(a, b) => vec![a.id, b.id],
        WhenPattern::Var(b) => vec![b.id],
        WhenPattern::Wildcard | WhenPattern::Literal(_) => vec![],
    }
}

/// Replace every node of `targets` in `expr` with `replacement`.
///
/// In place, so the nodes still sit at the addresses they were found at.
/// The targets never nest — two nodes with one signature have one size — so
/// the order they are met in does not matter.
fn substitute_in_place(
    expr: &mut PseudoExpr,
    targets: &std::collections::HashSet<*const PseudoExpr>,
    replacement: &PseudoExpr,
) {
    let mut pending: Vec<&mut PseudoExpr> = vec![expr];
    while let Some(node) = pending.pop() {
        if targets.contains(&(&*node as *const PseudoExpr)) {
            *node = replacement.clone();
            continue;
        }
        push_children_mut(node, &mut pending);
    }
}

/// Every child of `expr`, pattern-literal payloads included — the mutable
/// counterpart of [`PseudoExpr::child_refs_into`].
pub(super) fn push_children_mut<'a>(expr: &'a mut PseudoExpr, out: &mut Vec<&'a mut PseudoExpr>) {
    use crate::pseudo::ast::WhenPattern;

    match expr {
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => out.push(body),
        PseudoExpr::Apply { function, args } => {
            out.push(function);
            out.extend(args.iter_mut());
        }
        PseudoExpr::Let { value, body, .. } => {
            out.push(value);
            out.push(body);
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            out.push(condition);
            out.push(then_branch);
            out.push(else_branch);
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            out.push(subject);
            for clause in clauses.iter_mut() {
                if let WhenPattern::Literal(lit) = &mut clause.pattern {
                    out.push(lit);
                }
                if let Some(guard) = clause.guard.as_mut() {
                    out.push(guard);
                }
                out.push(&mut clause.body);
            }
        }
        PseudoExpr::List { elements, tail } => {
            out.extend(elements.iter_mut());
            if let Some(tail) = tail {
                out.push(tail);
            }
        }
        PseudoExpr::Tuple(elements) => out.extend(elements.iter_mut()),
        PseudoExpr::Pair(first, second) => {
            out.push(first);
            out.push(second);
        }
        PseudoExpr::Constr { fields, .. } => out.extend(fields.iter_mut()),
        PseudoExpr::FieldAccess { record, .. } => out.push(record),
        PseudoExpr::IndexAccess { collection, .. } => out.push(collection),
        PseudoExpr::BinOp { left, right, .. } => {
            out.push(left);
            out.push(right);
        }
        PseudoExpr::UnOp { operand, .. } => out.push(operand),
        PseudoExpr::BuiltinCall { args, .. } => out.extend(args.iter_mut()),
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => out.push(inner),
        PseudoExpr::Trace { message, value } => {
            out.push(message);
            out.push(value);
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


/// A trace emission — the structural `PseudoExpr::Trace` or the raw
/// `builtin.trace` call (`BuiltinCall { name: Trace }`), which render-prep
/// preserves by default. Both EMIT an observable log, so both block
/// extraction and count as "risky" for the eager-spine-head check (the
/// emit precedes the returned value).
///
/// The effect gate ([`NodeFacts::effect`]) blocks on those and on
/// `Error { message: Some(_) }` — the message is observable. A bare
/// `Error { message: None }` (what a `_ -> fail` guard becomes once the
/// earlier `collapse_trace_fail_let` strips its trace message) is NOT
/// blocking: it aborts instead of returning, so merging N alpha-equivalent
/// bare aborts is sound — the first eval aborts, the rest never run, and a
/// bare `Error` emits no log. `collect_eval_position_sigs` and
/// `first_occurrence_dominates` then keep the single hoisted abort from
/// being reordered ahead of an earlier effect.
fn is_trace_node(expr: &PseudoExpr) -> bool {
    match expr {
        PseudoExpr::Trace { .. } => true,
        PseudoExpr::BuiltinCall { name, .. } => *name == crate::BuiltinId::Trace,
        _ => false,
    }
}

enum EagerHit {
    Candidate,
    OtherRisky,
    Nothing,
}

/// Eagerly-evaluated children of `expr`, in evaluation order, EXCLUDING lazy
/// positions (When arms, If branches, `&&`/`||` right operand, Delay thunks,
/// Lambda/RecFn bodies). Mirrors the descent in `collect_eval_position_sigs`.
fn eager_children(expr: &PseudoExpr) -> Vec<&PseudoExpr> {
    match expr {
        PseudoExpr::If { condition, .. } => vec![condition.as_ref()],
        PseudoExpr::When { subject, .. } => vec![subject.as_ref()],
        PseudoExpr::BinOp {
            op: BinaryOp::And | BinaryOp::Or,
            left,
            ..
        } => vec![left.as_ref()],
        PseudoExpr::Delay(_) | PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => vec![],
        other => scope_children(other),
    }
}

fn eager_first(expr: &PseudoExpr, is_target: &dyn Fn(&PseudoExpr) -> bool) -> EagerHit {
    enum Frame<'a> {
        // Awaiting the result of a Let's `value`; `body` runs next only if
        // that result was `Nothing`.
        LetValue {
            body: &'a PseudoExpr,
        },
        // Awaiting the result of `children[next - 1]`; if `Nothing`, try
        // `children[next]`, else (list exhausted) the node is `OtherRisky`.
        OtherChildren {
            children: Vec<&'a PseudoExpr>,
            next: usize,
        },
    }

    let mut stack: Vec<Frame> = Vec::new();
    let mut node = expr;
    loop {
        // Descend from `node`, pushing frames, until something resolves to
        // a concrete EagerHit.
        let mut result = loop {
            if is_target(node) {
                break EagerHit::Candidate;
            }
            if is_trace_node(node) {
                break EagerHit::OtherRisky;
            }
            match node {
                PseudoExpr::Var { .. }
                | PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
                | PseudoExpr::HelperSymbol(_)
                | PseudoExpr::Delay(_)
                | PseudoExpr::Lambda { .. }
                | PseudoExpr::RecFn { .. } => break EagerHit::Nothing,
                PseudoExpr::Let { value, body, .. } => {
                    stack.push(Frame::LetValue { body });
                    node = value;
                }
                other => {
                    let children = eager_children(other);
                    if children.is_empty() {
                        break EagerHit::OtherRisky;
                    }
                    node = children[0];
                    stack.push(Frame::OtherChildren { children, next: 1 });
                }
            }
        };

        // Propagate `result` up through frames. A non-`Nothing` result
        // bubbles straight to the top (or out of the function) without
        // trying any sibling. A `Nothing` result lets the enclosing frame
        // move on to its next pending child, if any.
        loop {
            match stack.pop() {
                None => return result,
                Some(Frame::LetValue { body }) => {
                    if matches!(result, EagerHit::Nothing) {
                        node = body;
                        break;
                    }
                }
                Some(Frame::OtherChildren { children, next }) => {
                    if matches!(result, EagerHit::Nothing) {
                        if next < children.len() {
                            node = children[next];
                            stack.push(Frame::OtherChildren {
                                children,
                                next: next + 1,
                            });
                            break;
                        }
                        result = EagerHit::OtherRisky;
                    }
                }
            }
        }
    }
}

/// Is the candidate `sig` the FIRST fail/diverge-capable operation reached in
/// eager evaluation order through `body`? Fail-closed: `true` ONLY when the
/// candidate is reached before any other non-trivial node's own
/// (possibly-aborting) operation, so hoisting `let w = E` to the top keeps E
/// at its original first position and reorders its abort ahead of nothing.
fn first_occurrence_dominates(body: &PseudoExpr, is_target: impl Fn(&PseudoExpr) -> bool) -> bool {
    matches!(eager_first(body, &is_target), EagerHit::Candidate)
}

/// Alpha-canonical signature. Same scheme as
/// `cse_alpha_equivalent_lambda_helpers::Canonicaliser`, inlined
/// here to avoid coupling the modules; a per-subtree string is all
/// this pass compares.
fn signature(expr: &PseudoExpr) -> String {
    let mut canon = Canon::default();
    canon.visit(expr);
    canon.out
}

/// Signature with free variables replaced by placeholders numbered in order
/// of first occurrence, and those variables (with their display names) in the
/// same order. Two expressions that differ only in WHICH variables they read
/// share the signature; the variable lists say where they differ.
pub(super) fn abstract_signature(expr: &PseudoExpr) -> (String, Vec<(VarId, String)>) {
    let mut canon = Canon {
        abstract_free: true,
        ..Canon::default()
    };
    canon.visit(expr);
    (canon.out, canon.free)
}

#[derive(Default)]
pub(super) struct Canon {
    out: String,
    locals: HashMap<VarId, String>,
    abstract_free: bool,
    free: Vec<(VarId, String)>,
}

impl Canon {
    fn declare(&mut self, vid: VarId) -> String {
        let next = self.locals.len();
        let ph = format!("L{}", next);
        self.locals.entry(vid).or_insert(ph.clone());
        ph
    }

    fn visit(&mut self, expr: &PseudoExpr) {
        use crate::pseudo::ast::WhenPattern;
        use std::fmt::Write;

        enum Instr<'a> {
            Text(&'static str),
            Owned(String),
            Visit(&'a PseudoExpr),
            VisitPattern(&'a WhenPattern),
        }

        let mut stack: Vec<Instr> = vec![Instr::Visit(expr)];
        while let Some(instr) = stack.pop() {
            match instr {
                Instr::Text(s) => self.out.push_str(s),
                Instr::Owned(s) => self.out.push_str(&s),
                Instr::Visit(node) => match node {
                    PseudoExpr::Var { id, name } => match id {
                        Some(v) => {
                            if let Some(p) = self.locals.get(v).cloned() {
                                self.out.push_str(&p);
                            } else if self.abstract_free {
                                let index = match self.free.iter().position(|(f, _)| f == v) {
                                    Some(i) => i,
                                    None => {
                                        self.free.push((*v, name.clone()));
                                        self.free.len() - 1
                                    }
                                };
                                write!(self.out, "F{}", index).unwrap();
                            } else {
                                write!(self.out, "OV{:?}", v).unwrap();
                            }
                        }
                        None => write!(self.out, "VN{}", name).unwrap(),
                    },
                    PseudoExpr::Let {
                        id, value, body, ..
                    } => {
                        self.out.push_str("Let(");
                        if let Some(vid) = id {
                            let ph = self.declare(*vid);
                            self.out.push_str(&ph);
                        }
                        self.out.push(',');
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(body));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(value));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        self.out.push_str("Lam[");
                        for p in params {
                            let ph = self.declare(p.id);
                            self.out.push_str(&ph);
                            self.out.push(',');
                        }
                        self.out.push(';');
                        stack.push(Instr::Text("]"));
                        stack.push(Instr::Visit(body));
                    }
                    PseudoExpr::Apply { function, args } => {
                        self.out.push_str("Ap(");
                        stack.push(Instr::Text(")"));
                        for a in args.iter().rev() {
                            stack.push(Instr::Text(","));
                            stack.push(Instr::Visit(a));
                        }
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(function));
                    }
                    PseudoExpr::When {
                        subject, clauses, ..
                    } => {
                        self.out.push_str("Wh(");
                        stack.push(Instr::Text(")"));
                        for c in clauses.iter().rev() {
                            stack.push(Instr::Visit(&c.body));
                            stack.push(Instr::Text(",b"));
                            if let Some(g) = &c.guard {
                                stack.push(Instr::Visit(g));
                                stack.push(Instr::Text(",g"));
                            }
                            stack.push(Instr::VisitPattern(&c.pattern));
                            stack.push(Instr::Text(","));
                        }
                        stack.push(Instr::Visit(subject));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        self.out.push_str("If(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(else_branch));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(then_branch));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(condition));
                    }
                    PseudoExpr::Pair(a, b) => {
                        self.out.push_str("Pr(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(b));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(a));
                    }
                    PseudoExpr::Tuple(items) => {
                        self.out.push_str("Tup(");
                        stack.push(Instr::Text(")"));
                        for i in items.iter().rev() {
                            stack.push(Instr::Text(","));
                            stack.push(Instr::Visit(i));
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        self.out.push_str("L(");
                        stack.push(Instr::Text(")"));
                        if let Some(t) = tail {
                            stack.push(Instr::Visit(t));
                            stack.push(Instr::Text(".."));
                        }
                        for e in elements.iter().rev() {
                            stack.push(Instr::Text(","));
                            stack.push(Instr::Visit(e));
                        }
                    }
                    PseudoExpr::Constr {
                        tag, fields, shape, ..
                    } => {
                        write!(self.out, "Co{}({:?},", tag, shape).unwrap();
                        stack.push(Instr::Text(")"));
                        for f in fields.iter().rev() {
                            stack.push(Instr::Text(","));
                            stack.push(Instr::Visit(f));
                        }
                    }
                    PseudoExpr::FieldAccess { record, selector } => {
                        self.out.push_str("FA(");
                        stack.push(Instr::Owned(format!(",{:?})", selector)));
                        stack.push(Instr::Visit(record));
                    }
                    PseudoExpr::IndexAccess { collection, index } => {
                        self.out.push_str("IA(");
                        stack.push(Instr::Owned(format!(",{})", index)));
                        stack.push(Instr::Visit(collection));
                    }
                    PseudoExpr::BinOp { op, left, right } => {
                        write!(self.out, "BO{:?}(", op).unwrap();
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(right));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(left));
                    }
                    PseudoExpr::UnOp { op, operand } => {
                        write!(self.out, "UO{:?}(", op).unwrap();
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(operand));
                    }
                    PseudoExpr::BuiltinCall { name, args } => {
                        write!(self.out, "BC{:?}(", name).unwrap();
                        stack.push(Instr::Text(")"));
                        for a in args.iter().rev() {
                            stack.push(Instr::Text(","));
                            stack.push(Instr::Visit(a));
                        }
                    }
                    PseudoExpr::Delay(inner) => {
                        self.out.push_str("D(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(inner));
                    }
                    PseudoExpr::Force(inner) => {
                        self.out.push_str("F(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(inner));
                    }
                    PseudoExpr::Trace { message, value } => {
                        self.out.push_str("Tr(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(value));
                        stack.push(Instr::Text(","));
                        stack.push(Instr::Visit(message));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        self.out.push_str("RFn(");
                        let n_ph = self.declare(name.id);
                        self.out.push_str(&n_ph);
                        for p in params {
                            let ph = self.declare(p.id);
                            self.out.push_str(&ph);
                            self.out.push(',');
                        }
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(body));
                    }
                    PseudoExpr::Int(n) => write!(self.out, "I{}", n).unwrap(),
                    PseudoExpr::ByteArray(b) => write!(self.out, "BA{:?}", b).unwrap(),
                    PseudoExpr::String(s) => write!(self.out, "S{:?}", s).unwrap(),
                    PseudoExpr::Bool(b) => write!(self.out, "B{}", b).unwrap(),
                    PseudoExpr::Unit => self.out.push('U'),
                    PseudoExpr::Error { message } => write!(self.out, "Er{:?}", message).unwrap(),
                    PseudoExpr::Raw { .. } => self.out.push_str("Raw"),
                    PseudoExpr::Data(_) => self.out.push_str("Da"),
                    PseudoExpr::HelperSymbol(s) => write!(self.out, "Hs{:?}", s).unwrap(),
                },
                Instr::VisitPattern(p) => match p {
                    WhenPattern::Constructor { tag, fields, .. } => {
                        write!(self.out, "C{}(", tag).unwrap();
                        for f in fields {
                            let ph = self.declare(f.id);
                            self.out.push_str(&ph);
                            self.out.push(',');
                        }
                        self.out.push(')');
                    }
                    WhenPattern::List { elements, tail } => {
                        self.out.push_str("L[");
                        for e in elements {
                            let ph = self.declare(e.id);
                            self.out.push_str(&ph);
                            self.out.push(',');
                        }
                        if let Some(t) = tail {
                            let ph = self.declare(t.id);
                            self.out.push_str(&ph);
                        }
                        self.out.push(']');
                    }
                    WhenPattern::Tuple(fs) => {
                        self.out.push_str("T[");
                        for f in fs {
                            let ph = self.declare(f.id);
                            self.out.push_str(&ph);
                            self.out.push(',');
                        }
                        self.out.push(']');
                    }
                    WhenPattern::Pair(a, b) => {
                        let pa = self.declare(a.id);
                        let pb = self.declare(b.id);
                        write!(self.out, "P[{},{}]", pa, pb).unwrap();
                    }
                    WhenPattern::Wildcard => self.out.push('_'),
                    WhenPattern::Literal(e) => {
                        self.out.push_str("Li(");
                        stack.push(Instr::Text(")"));
                        stack.push(Instr::Visit(e));
                    }
                    WhenPattern::Var(b) => {
                        let ph = self.declare(b.id);
                        write!(self.out, "V{}", ph).unwrap();
                    }
                },
            }
        }
    }
}

fn scope_children(expr: &PseudoExpr) -> Vec<&PseudoExpr> {
    use super::scope_recurse::children;
    children(expr)
}

#[cfg(test)]
mod tests;
