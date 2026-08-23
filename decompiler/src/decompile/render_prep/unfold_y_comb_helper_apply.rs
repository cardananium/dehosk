//! Unfold call sites of a hoisted half-Z fixpoint helper.
//!
//! `unfold_y_comb_apply` needs the half-Z lambda inline in function
//! position. Compiled scripts hoist it to a named helper, so the head
//! is a bare `Var` and that pass bails — the driver then reads as an
//! opaque callback instead of the self-reference it is.
//!
//! Same unfold, keyed on the helper's `VarId`:
//! `App(YC, λself,x. body) = rec fn self(x) { body }` for
//! `YC = λv. rec fn s(x). v(s, x)`.
//!
//! Fail-closed:
//! - Helper value is exactly the half-Z lambda (same predicate as
//!   `cse_y_comb_consts::is_y_comb_defining_lambda`). The flattened
//!   2-outer-param form is rejected — its self slot is not a function.
//! - Helper `VarId` bound exactly once (collided id is ambiguous).
//! - Call is `Apply{Var(helper), [driver]}` or `[driver, descent]`
//!   with a literal 2-param driver. 1-arg → bare `RecFn`; 2-arg →
//!   define-then-call. 3+ args left alone.
//!
//! The driver's binders become the `rec fn`'s binders (pure
//! restructuring). Only the 2-arg form's let binder is a fresh `VarId`.
//! In let-value position the `rec fn` is re-displayed with the let
//! name so `ExitLetRecFnSameName` collapses `let b = rec fn b`.
//! `drop_dead_pure_lets` sweeps the helper once every site unfolds.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn unfold_y_comb_helper_applications(expr: PseudoExpr) -> PseudoExpr {
    let helpers = collect_half_z_helpers(&expr);
    if helpers.is_empty() {
        return expr;
    }
    // 2-arg (applied) sites mint a fresh let-binder id, so raise the
    // global counter above the tree max FIRST — minting with a lagging
    // counter collides with ids already in the tree.
    VarId::ensure_binding_counter_above(super::alpha_uniquify::max_fresh_range_id(&expr));
    rewrite(expr, &helpers)
}

/// Half-Z helper binder ids: every `Let` whose value matches the half-Z
/// lambda shape AND whose `VarId` is bound exactly once program-wide.
fn collect_half_z_helpers(expr: &PseudoExpr) -> HashSet<VarId> {
    struct Scan {
        candidates: HashSet<VarId>,
        binder_seen: HashMap<VarId, usize>,
    }
    impl Scan {
        fn record_binder(&mut self, id: VarId) {
            *self.binder_seen.entry(id).or_insert(0) += 1;
        }
    }
    impl ExprVisitor for Scan {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, value: &PseudoExpr) {
            if let Some(vid) = id {
                self.record_binder(*vid);
                if is_half_z_lambda(value) {
                    self.candidates.insert(*vid);
                }
            }
        }
        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for p in params {
                self.record_binder(p.var_id());
            }
        }
        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            self.record_binder(name.var_id());
            for p in params {
                self.record_binder(p.var_id());
            }
        }
        fn visit_when_clause_pre(
            &mut self,
            subject_name: Option<&Binder>,
            clause: &crate::pseudo::ast::WhenClause,
        ) {
            if let Some(b) = subject_name {
                self.record_binder(b.var_id());
            }
            for id in clause.pattern.bound_ids() {
                self.record_binder(id);
            }
        }
    }
    let mut scan = Scan {
        candidates: HashSet::new(),
        binder_seen: HashMap::new(),
    };
    scan.walk(expr);
    scan.candidates
        .into_iter()
        .filter(|id| scan.binder_seen.get(id) == Some(&1))
        .collect()
}

/// The half-Z fixpoint lambda: `λv. rec fn s(x) { v(s, x) }` — the same
/// structural predicate as `cse_y_comb_consts::is_y_comb_defining_lambda`.
fn is_half_z_lambda(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let outer_id = params[0].var_id();
    let PseudoExpr::RecFn {
        name: self_name,
        params: inner_params,
        body: rec_body,
    } = body.as_ref()
    else {
        return false;
    };
    if inner_params.len() != 1 {
        return false;
    }
    let self_id = self_name.var_id();
    let inner_id = inner_params[0].var_id();
    let PseudoExpr::Apply { function, args } = rec_body.as_ref() else {
        return false;
    };
    if !matches!(
        function.as_ref(),
        PseudoExpr::Var { id: Some(vid), .. } if *vid == outer_id
    ) {
        return false;
    }
    matches!(
        args.as_slice(),
        [
            PseudoExpr::Var { id: Some(a), .. },
            PseudoExpr::Var { id: Some(b), .. },
        ] if *a == self_id && *b == inner_id
    )
}

/// One pending job of the two walks below: a node still to visit, or rebuild after
/// children.
enum UnfoldStep {
    Visit(PseudoExpr),
    Post(UnfoldPost),
}

enum UnfoldPost {
    Let {
        name: String,
        id: Option<VarId>,
    },
    /// The `redisplay_rec_fn` that ran on an unfolded LET VALUE once its own children
    /// had been rewritten — its own step, (between the value's descent and the let's
    /// rebuild).
    Redisplay {
        let_name: String,
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

/// `map_children(node, <the enclosing walk>)` expressed as jobs: push the
/// node's reconstruction, then its children in REVERSE so they pop — and so
/// land on `done` — in source order. Leaves have no children and are finished
/// on the spot, matching `map_children`'s `other => other`.
fn push_map_children(node: PseudoExpr, steps: &mut Vec<UnfoldStep>, done: &mut Vec<PseudoExpr>) {
    match node {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            steps.push(UnfoldStep::Post(UnfoldPost::Let { name, id }));
            steps.push(UnfoldStep::Visit(body.into_inner()));
            steps.push(UnfoldStep::Visit(value.into_inner()));
        }
        PseudoExpr::Lambda { params, body } => {
            steps.push(UnfoldStep::Post(UnfoldPost::Lambda { params }));
            steps.push(UnfoldStep::Visit(body.into_inner()));
        }
        PseudoExpr::RecFn { name, params, body } => {
            steps.push(UnfoldStep::Post(UnfoldPost::RecFn { name, params }));
            steps.push(UnfoldStep::Visit(body.into_inner()));
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
            steps.push(UnfoldStep::Post(UnfoldPost::When {
                subject_name,
                clause_meta,
            }));
            for c in clause_children.into_iter().rev() {
                steps.push(UnfoldStep::Visit(c));
            }
            steps.push(UnfoldStep::Visit(subject.into_inner()));
        }
        other => match plain_children(other) {
            Ok((kind, children)) => {
                steps.push(UnfoldStep::Post(UnfoldPost::Plain(kind)));
                for c in children.into_iter().rev() {
                    steps.push(UnfoldStep::Visit(c));
                }
            }
            Err(leaf) => done.push(leaf),
        },
    }
}

/// Reassemble one node from the already-rewritten children the walk left on
/// `done`, in the order they were pushed.
fn rebuild_step(post: UnfoldPost, done: &mut Vec<PseudoExpr>) -> PseudoExpr {
    match post {
        UnfoldPost::Let { name, id } => {
            let body = done.pop().expect("let body");
            let value = done.pop().expect("let value");
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
        UnfoldPost::Redisplay { let_name } => {
            let rec_fn = done.pop().expect("unfolded let value");
            redisplay_rec_fn(rec_fn, &let_name)
        }
        UnfoldPost::Lambda { params } => PseudoExpr::Lambda {
            params,
            body: PBox::new(done.pop().expect("lambda body")),
        },
        UnfoldPost::RecFn { name, params } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(done.pop().expect("recfn body")),
        },
        UnfoldPost::When {
            subject_name,
            clause_meta,
        } => {
            let total = 1 + clause_meta
                .iter()
                .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                .sum::<usize>();
            let mut parts = take(done, total).into_iter();
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
        UnfoldPost::Plain(kind) => rebuild_plain(kind, done),
    }
}

/// `try_unfold_call` still runs on the way DOWN, before any child is visited,
/// because the 2-arg form mints a `VarId::fresh_binding()` and those ids are
/// handed out in visit order — a reordered walk would renumber the program.
/// `redisplay_rec_fn` after an unfolded let value's children is its own
/// `Redisplay` step in the same place.
fn rewrite(expr: PseudoExpr, helpers: &HashSet<VarId>) -> PseudoExpr {
    let mut steps: Vec<UnfoldStep> = vec![UnfoldStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            UnfoldStep::Visit(expr) => {
                // Let-value call site: rewrite + re-display with the let's name so
                // the `let b = rec fn b(…)` collapse fires.
                if let PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } = expr
                {
                    match try_unfold_call(value.into_inner(), helpers) {
                        Ok(rec_fn) => {
                            steps.push(UnfoldStep::Post(UnfoldPost::Let {
                                name: name.clone(),
                                id,
                            }));
                            steps.push(UnfoldStep::Visit(body.into_inner()));
                            steps.push(UnfoldStep::Post(UnfoldPost::Redisplay { let_name: name }));
                            // The driver body may hold nested helper calls.
                            push_map_children(rec_fn, &mut steps, &mut done);
                        }
                        Err(original) => {
                            steps.push(UnfoldStep::Post(UnfoldPost::Let { name, id }));
                            steps.push(UnfoldStep::Visit(body.into_inner()));
                            steps.push(UnfoldStep::Visit(original));
                        }
                    }
                    continue;
                }
                // Any other position: rewrite in place keeping the driver's own
                // self-param display name.
                match try_unfold_call(expr, helpers) {
                    Ok(rec_fn) => push_map_children(rec_fn, &mut steps, &mut done),
                    Err(original) => push_map_children(original, &mut steps, &mut done),
                }
            }
            UnfoldStep::Post(post) => {
                let rebuilt = rebuild_step(post, &mut done);
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

/// `Apply{Var(helper), [λ(self_p, arg_p). D]}` ⇒
/// `RecFn{name: self_p, params: [arg_p], body: D}`.
///
/// `Apply{Var(helper), [λ(self_p, arg_p). D, descent]}` ⇒
/// `let self_p = rec fn self_p(arg_p) { D }; self_p(descent)` — a
/// define-then-call block whose let binder gets a fresh `VarId` (the
/// counter was raised at pass entry). Evaluation order holds: building
/// the rec-closure is pure and `descent` is evaluated at the call.
///
/// Returns the input unchanged in `Err` when any gate fails.
fn try_unfold_call(expr: PseudoExpr, helpers: &HashSet<VarId>) -> Result<PseudoExpr, PseudoExpr> {
    let PseudoExpr::Apply { function, args } = expr else {
        return Err(expr);
    };
    let is_helper_call = matches!(
        function.as_ref(),
        PseudoExpr::Var { id: Some(fid), .. } if helpers.contains(fid)
    );
    if !is_helper_call || args.is_empty() || args.len() > 2 {
        return Err(PseudoExpr::Apply { function, args });
    }
    let driver = &args[0];
    let PseudoExpr::Lambda { params, .. } = driver else {
        return Err(PseudoExpr::Apply { function, args });
    };
    if params.len() != 2 {
        return Err(PseudoExpr::Apply { function, args });
    }
    let mut args = args;
    let descent = (args.len() == 2).then(|| args.pop().expect("len checked"));
    let PseudoExpr::Lambda { params, body } = args.remove(0) else {
        unreachable!("shape checked above");
    };
    let mut params = params.into_iter();
    let self_p = params.next().expect("2 params checked");
    let arg_p = params.next().expect("2 params checked");
    let rec_fn = PseudoExpr::RecFn {
        name: self_p.clone(),
        params: vec![arg_p],
        body,
    };
    Ok(match descent {
        None => rec_fn,
        Some(descent) => {
            let let_id = VarId::fresh_binding();
            let display = self_p.display_name().to_string();
            PseudoExpr::Let {
                name: display.clone(),
                id: Some(let_id),
                value: PBox::new(rec_fn),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::Var {
                        name: display,
                        id: Some(let_id),
                    }),
                    args: vec![descent].into(),
                }),
            }
        }
    })
}

/// Re-display the unfolded `rec fn`'s name and self-call `Var`s with the
/// enclosing let binder's name (ids untouched), so the printer collapses
/// `let b = rec fn b(…)` to `rec fn b(…)` and self-calls read `b(…)`.
/// Non-RecFn input passes through unchanged, including the 2-arg
/// define-then-call `Let` form, which in a let-value position renders as
/// a nested block instead of adopting the outer name — correct, just
/// less compact.
///
/// The collapse (`ExitLetRecFnSameName`) matches by display-NAME equality
/// between the let and the rec-fn binder (distinct `VarId`s), so the
/// let's name must already be scope-unique — the FIRST
/// `disambiguate_shadowed_lets` run makes it so, before this pass copies
/// it onto the rec-fn name. Re-suffixing the let after this pass would
/// degrade the pairing to the still-sound `let b_2 = rec fn b(…)` form.
fn redisplay_rec_fn(expr: PseudoExpr, let_name: &str) -> PseudoExpr {
    let PseudoExpr::RecFn { name, params, body } = expr else {
        return expr;
    };
    let self_id = name.var_id();
    let body = rename_var_display(body.into_inner(), self_id, let_name);
    PseudoExpr::RecFn {
        name: name.renamed(let_name.to_string()),
        params,
        body: PBox::new(body),
    }
}

/// Rename the DISPLAY name of every `Var{id: Some(target)}` (ids kept).
fn rename_var_display(expr: PseudoExpr, target: VarId, new_name: &str) -> PseudoExpr {
    let mut steps: Vec<UnfoldStep> = vec![UnfoldStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            UnfoldStep::Visit(expr) => match expr {
                PseudoExpr::Var { id: Some(id), .. } if id == target => {
                    done.push(PseudoExpr::Var {
                        name: new_name.to_string(),
                        id: Some(id),
                    })
                }
                other => push_map_children(other, &mut steps, &mut done),
            },
            UnfoldStep::Post(post) => {
                let rebuilt = rebuild_step(post, &mut done);
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rename_var_display must leave one result");
    done.pop().expect("rename_var_display result")
}

#[cfg(test)]
mod tests;
