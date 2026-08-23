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

use crate::pseudo::ast::{BinaryOp, PseudoExpr, WhenClause};
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn extract_repeated_subexpr(expr: PseudoExpr) -> PseudoExpr {
    let expr = extract_repeated_subexpr_rec(expr);
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
        other => wrap_with_extracted_lets(other, /* abort_only */ true),
    }
}

fn extract_repeated_subexpr_rec(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_rewrite)
}

fn try_rewrite(expr: PseudoExpr) -> PseudoExpr {
    // Shapes with a single "body" that a `Let` can wrap.
    match expr {
        PseudoExpr::Lambda { params, body } => {
            let body = wrap_with_extracted_lets(body.into_inner(), /* abort_only */ false);
            PseudoExpr::Lambda {
                params,
                body: PBox::new(body),
            }
        }
        PseudoExpr::RecFn { name, params, body } => {
            let body = wrap_with_extracted_lets(body.into_inner(), /* abort_only */ false);
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
                    body: wrap_with_extracted_lets(c.body, /* abort_only */ false),
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
            )),
            else_branch: PBox::new(wrap_with_extracted_lets(
                else_branch.into_inner(),
                /* abort_only */ false,
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
            let body = if let Some(vid) = id
                && count_id_refs(&body, vid) >= 2
            {
                wrap_with_extracted_lets(body.into_inner(), /* abort_only */ false)
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

/// Reference count of `vid` in `expr` (complete walk incl. pattern-literal
/// payloads via `fold::ExprVisitor`).
fn count_id_refs(expr: &PseudoExpr, vid: VarId) -> usize {
    use crate::pseudo::fold::ExprVisitor;
    struct C {
        vid: VarId,
        n: usize,
    }
    impl ExprVisitor for C {
        fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
            if *id == Some(self.vid) {
                self.n += 1;
            }
        }
    }
    let mut c = C { vid, n: 0 };
    c.walk(expr);
    c.n
}

/// Inspect `body` for repeated complex subexpressions and wrap it in
/// `let w = <duplicate>` for each, rewriting every occurrence to the
/// new binder. Candidates whose free vars would be unbound at the
/// body's scope are skipped.
fn wrap_with_extracted_lets(body: PseudoExpr, abort_only: bool) -> PseudoExpr {
    // A candidate can only be hoisted to the top of `body` if every
    // var it references is already visible there. Params in scope
    // aren't tracked here, so the check is the conservative
    // `free(candidate) ⊆ free(body)` — it rejects some safe
    // candidates but never allows an unsafe extraction.
    let body_free = collect_free_vars(&body);

    let mut counts: HashMap<String, usize> = HashMap::new();
    let mut representatives: HashMap<String, PseudoExpr> = HashMap::new();
    collect_signatures(&body, &mut counts, &mut representatives);

    // Signatures in always-evaluated position relative to `body`. Only
    // these are safe to hoist into an eager `let` at the body's top; a
    // candidate absent here is reached only under a conditional or
    // thunk and must stay put.
    let mut eval_sigs: std::collections::HashSet<String> = Default::default();
    collect_eval_position_sigs(&body, &mut eval_sigs);

    let mut candidates: Vec<(String, usize, PseudoExpr)> = counts
        .into_iter()
        .filter(|(sig, c)| *c >= 2 && eval_sigs.contains(sig))
        .filter_map(|(sig, c)| {
            let rep = representatives.remove(&sig)?;
            // Reject if rep's free vars escape the body's scope.
            let rep_free = collect_free_vars(&rep);
            if !rep_free.is_subset(&body_free) {
                return None;
            }
            // A candidate containing a bare abort (`Error { message: None }`,
            // e.g. a `_ -> fail` guard) is sound to hoist only when its first
            // occurrence DOMINATES the body — nothing fail/diverge-capable runs
            // before it — so the hoisted abort is never reordered ahead of an
            // earlier effect. `contains_effect` lets a bare abort through as
            // non-blocking; this is the placement gate. At most one candidate
            // can dominate, so two abort candidates can never race.
            if contains_bare_abort(&rep) && !first_occurrence_dominates(&body, &sig) {
                return None;
            }
            Some((sig, c, rep))
        })
        .collect();
    // With a dominating bare-abort candidate present, extract only abort
    // candidates and drop the pure ones. A pure candidate NESTED inside the
    // abort candidate would otherwise land in a `let` OUTSIDE the abort
    // `let` (the abort fails the post-substitution recheck), evaluating that
    // pure op BEFORE the abort and reordering a possible divergence ahead of
    // it. Dropped pure candidates stay inside the abort `let`'s value — a
    // missed extraction, never unsound.
    if abort_only
        || candidates
            .iter()
            .any(|(_, _, rep)| contains_bare_abort(rep))
    {
        candidates.retain(|(_, _, rep)| contains_bare_abort(rep));
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
        let a_abort = contains_bare_abort(&a.2);
        let b_abort = contains_bare_abort(&b.2);
        a_abort
            .cmp(&b_abort)
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
    for (sig, _count, rep) in candidates {
        if consumed.contains(&sig) {
            continue;
        }
        // Re-verify the signature still has ≥2 occurrences in
        // `current` (a previous round may have rewritten some away).
        let mut recheck: HashMap<String, usize> = HashMap::new();
        count_signatures_only(&current, &mut recheck);
        if recheck.get(&sig).copied().unwrap_or(0) < 2 {
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
        current = substitute_by_sig(current, &sig, &w_var);
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

fn collect_signatures(
    expr: &PseudoExpr,
    counts: &mut HashMap<String, usize>,
    reps: &mut HashMap<String, PseudoExpr>,
) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        if is_extractable(cur) {
            let sig = signature(cur);
            *counts.entry(sig.clone()).or_insert(0) += 1;
            reps.entry(sig).or_insert_with(|| cur.clone());
        }
        pending.extend(scope_children(cur).into_iter().rev());
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
fn collect_eval_position_sigs(expr: &PseudoExpr, out: &mut std::collections::HashSet<String>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        if is_extractable(cur) {
            out.insert(signature(cur));
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
                    if eager_aborts(c) || contains_effect(c) {
                        break;
                    }
                }
                pending.extend(kids.into_iter().rev());
            }
        }
    }
}

/// Does eager evaluation of `expr` ALWAYS reach an abort (`Error`, bare or
/// messaged) before producing a value? `collect_eval_position_sigs` uses
/// it to stop treating later siblings as always-evaluated once an earlier
/// sibling unconditionally aborts. Conditional aborts (inside an `if`/`when`
/// branch, `&&`/`||` right operand, or a thunk) do NOT count — only the
/// eager spine. Fail-closed: anything not provably an unconditional abort
/// returns false.
fn eager_aborts(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Error { .. } => return true,
            // Trivial-total leaves + lazy positions never unconditionally abort.
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
            | PseudoExpr::RecFn { .. } => {}
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            // A generic node aborts iff some eager child (in eval order) aborts.
            // `eager_children` already restricts If/When/&&||/Delay to their
            // always-evaluated parts, so conditional aborts are excluded.
            other => pending.extend(eager_children(other)),
        }
    }
    false
}

fn count_signatures_only(expr: &PseudoExpr, counts: &mut HashMap<String, usize>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        if is_extractable(cur) {
            let sig = signature(cur);
            *counts.entry(sig).or_insert(0) += 1;
        }
        pending.extend(scope_children(cur));
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
fn collect_free_vars(expr: &PseudoExpr) -> std::collections::HashSet<VarId> {
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

fn pattern_binders(p: &crate::pseudo::ast::WhenPattern) -> Vec<VarId> {
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

fn substitute_by_sig(expr: PseudoExpr, target_sig: &str, replacement: &PseudoExpr) -> PseudoExpr {
    struct Substitute<'a> {
        target_sig: &'a str,
        replacement: &'a PseudoExpr,
    }

    impl ExprFolder for Substitute<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            if is_extractable(expr) && signature(expr) == self.target_sig {
                FoldAction::Replace(self.replacement.clone())
            } else {
                FoldAction::Walk
            }
        }
    }

    Substitute {
        target_sig,
        replacement,
    }
    .fold(expr)
}

/// Worth extracting when:
/// - Non-trivial size (≥ 5 nodes — accounts for the `let X = V; …`
///   wrapping cost so size-4 duplicates are a wash, not a win).
/// - Not itself a `Let`, `Lambda`, or `RecFn` (those open new scopes).
/// - Not a trivial projector (`Var`, `var.fst`, etc.).
/// - Free of observable effects (`trace`, messaged `fail`).
/// - Not a small `BuiltinCall` whose args are all literals
///   (extracting `add(1, 2)` is shorter inlined).
fn is_extractable(expr: &PseudoExpr) -> bool {
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
    if let PseudoExpr::FieldAccess { record, .. } = expr {
        if matches!(record.as_ref(), PseudoExpr::Var { .. }) {
            return false;
        }
    }
    // Never extract an expression containing an observable effect: a
    // `trace` or a messaged `fail`. Extraction dedups occurrences —
    // merging two identical `trace`s into one changes the emitted
    // log — and hoists the value to the top of the body, which can
    // move the emission ahead of a preceding binding that would
    // itself have diverged first. `collect_eval_position_sigs`
    // already prevents hoisting out of a conditional; this covers
    // the sequential-reordering case.
    if contains_effect(expr) {
        return false;
    }
    // BuiltinCall with only literal args — extracting just adds a
    // let with no readability gain.
    if let PseudoExpr::BuiltinCall { args, .. } = expr {
        let all_literal = args.iter().all(|a| {
            matches!(
                a,
                PseudoExpr::Int(_)
                    | PseudoExpr::ByteArray(_)
                    | PseudoExpr::String(_)
                    | PseudoExpr::Bool(_)
                    | PseudoExpr::Unit
            )
        });
        if all_literal {
            return false;
        }
    }
    count_nodes(expr) >= 5
}

fn count_nodes(expr: &PseudoExpr) -> usize {
    let mut n = 0;
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        n += 1;
        pending.extend(scope_children(cur));
    }
    n
}

/// A trace emission — the structural `PseudoExpr::Trace` or the raw
/// `builtin.trace` call (`BuiltinCall { name: Trace }`), which render-prep
/// preserves by default. Both EMIT an observable log, so both block
/// extraction and count as "risky" for the eager-spine-head check (the
/// emit precedes the returned value).
///
/// `contains_effect`, below, blocks on those and on
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

fn contains_effect(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if is_trace_node(current) || matches!(current, PseudoExpr::Error { message: Some(_) }) {
            return true;
        }
        // A bare `Error { message: None }` is non-blocking (see above).
        // `scope_children` omits `WhenPattern::Literal` payloads, which are
        // real executable sub-expressions — check them explicitly so an
        // effect inside one can't evade the gate.
        if let PseudoExpr::When { clauses, .. } = current {
            for c in clauses {
                if let crate::pseudo::ast::WhenPattern::Literal(e) = &c.pattern {
                    pending.push(e);
                }
            }
        }
        pending.extend(scope_children(current));
    }
    false
}

/// Does `expr` contain a bare `Error { message: None }` anywhere? Such a
/// candidate is sound to hoist ONLY when its abort cannot be reordered
/// ahead of an earlier effect — see `first_occurrence_dominates`.
fn contains_bare_abort(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if matches!(current, PseudoExpr::Error { message: None }) {
            return true;
        }
        // `scope_children` omits `WhenPattern::Literal` payloads — check them too.
        if let PseudoExpr::When { clauses, .. } = current {
            for c in clauses {
                if let crate::pseudo::ast::WhenPattern::Literal(e) = &c.pattern {
                    pending.push(e);
                }
            }
        }
        pending.extend(scope_children(current));
    }
    false
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

fn eager_first(expr: &PseudoExpr, sig: &str) -> EagerHit {
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
            if signature(node) == sig {
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
fn first_occurrence_dominates(body: &PseudoExpr, sig: &str) -> bool {
    matches!(eager_first(body, sig), EagerHit::Candidate)
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

#[derive(Default)]
struct Canon {
    out: String,
    locals: HashMap<VarId, String>,
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
