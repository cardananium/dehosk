//! Copy-propagate pure bare-`Var` aliases: `let A = e … A …` becomes
//! `… e …`, with the alias `let` dropped.
//!
//! Minted inside `prepare_for_render` (`beta_reduce_lambda_apply`,
//! `extract_repeated_subexpr`, pack/identity inlining).
//! `drop_dead_pure_lets` only handles zero uses. A bare-`Var` RHS does
//! no evaluation and changes no eval order. A `True` literal must not
//! be propagated — that would erase the provenance
//! `complete_church_nil_to_empty_list` keys on and print `[] -> True`.
//!
//! Fail-closed:
//! - G0: needs the `decompiled` marker; a `let decompiled` is never a
//!   candidate.
//! - G1: value is `Var { id: Some(rid) }`, `rid != aid`, RHS name
//!   does not start with `_`.
//! - G2: `rid` has a known binder kind, is not a `RecFn` name, and is
//!   not multiply-bound. Unresolved → skip.
//! - G3: every body `Var` matching the alias by id also renders as the
//!   alias name, and the two counts match. A name-only `Var { id: None }`
//!   keeps the alias (dropping the let would orphan it).
//! - G4: no inner binder below the alias-let renders like the RHS name
//!   or carries `rid` — the printer resolves by name. `scope_recurse`
//!   does not enter `WhenPattern::Literal`; a use hiding there fails
//!   the census and the alias stands.
//! - G5: single-use folds any name; multi-use folds only the synthetic
//!   `w`/`w_2` family. A named multi-use alias may be a deliberate
//!   rename or carry a `FinalTypeTable` annotation.
//!
//! A folded `When` subject's `subject_name` becomes the RHS binder
//! (reuse `rid`). Fixpoint; no fresh `VarId`s.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::decompile::render::sanitize_identifier;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, children, plain_children, rebuild_plain, take};

pub(super) fn copy_propagate_var_aliases(expr: PseudoExpr) -> PseudoExpr {
    if !super::drop_dead_pure_lets::contains_decompiled_marker(&expr) {
        return expr;
    }
    let mut expr = expr;
    // Fixpoint: each round removes >= 1 alias let, so this terminates.
    loop {
        let kinds = collect_binder_kinds(&expr);
        let mut changed = false;
        expr = rewrite(expr, &kinds, &mut changed);
        if !changed {
            return expr;
        }
    }
}

/// What a `VarId` is bound by, program-wide. `Conflict` marks an id bound
/// by more than one binder (a latent VarId collision — fail-closed).
#[derive(Clone, Copy, PartialEq)]
enum BinderKind {
    LetBound,
    LambdaParam,
    RecFnName,
    RecFnParam,
    PatternBinder,
    Conflict,
}

fn collect_binder_kinds(expr: &PseudoExpr) -> HashMap<VarId, BinderKind> {
    struct Collector {
        kinds: HashMap<VarId, BinderKind>,
    }
    impl Collector {
        fn record(&mut self, id: VarId, kind: BinderKind) {
            self.kinds
                .entry(id)
                .and_modify(|k| *k = BinderKind::Conflict)
                .or_insert(kind);
        }
    }
    impl ExprVisitor for Collector {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, _value: &PseudoExpr) {
            if let Some(vid) = id {
                self.record(*vid, BinderKind::LetBound);
            }
        }
        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for p in params {
                self.record(p.id, BinderKind::LambdaParam);
            }
        }
        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            self.record(name.id, BinderKind::RecFnName);
            for p in params {
                self.record(p.id, BinderKind::RecFnParam);
            }
        }
        fn visit_when_clause_pre(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            if let Some(b) = subject_name {
                self.record(b.id, BinderKind::PatternBinder);
            }
            for id in clause.pattern.bound_ids() {
                self.record(id, BinderKind::PatternBinder);
            }
        }
    }
    let mut c = Collector {
        kinds: HashMap::new(),
    };
    c.walk(expr);
    c.kinds
}

/// One pending job of the two walks below ([`rewrite`] and [`substitute_all_uses`]): a
/// node still to visit, or rebuild after children.
enum PropStep {
    Visit(PseudoExpr),
    Post(PropPost),
}

enum PropPost {
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
    /// A `When` whose SUBJECT was itself an alias use: the subject is the RHS `Var`
    /// (substituted and counted when the node was visited, ), so only the clause
    /// children come off `done`.
    WhenSubstitutedSubject {
        subject: PBox,
        subject_name: Option<Binder>,
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// `map_children(node, <the enclosing walk>)` expressed as jobs: push the
/// node's reconstruction, then its children in REVERSE so they pop — and so
/// land on `done` — in source order. Leaves have no children and are finished
/// on the spot, matching `map_children`'s `other => other`.
fn push_map_children(node: PseudoExpr, steps: &mut Vec<PropStep>, done: &mut Vec<PseudoExpr>) {
    match node {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            steps.push(PropStep::Post(PropPost::Let { name, id }));
            steps.push(PropStep::Visit(body.into_inner()));
            steps.push(PropStep::Visit(value.into_inner()));
        }
        PseudoExpr::Lambda { params, body } => {
            steps.push(PropStep::Post(PropPost::Lambda { params }));
            steps.push(PropStep::Visit(body.into_inner()));
        }
        PseudoExpr::RecFn { name, params, body } => {
            steps.push(PropStep::Post(PropPost::RecFn { name, params }));
            steps.push(PropStep::Visit(body.into_inner()));
        }
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => {
            let (clause_meta, clause_children) = split_clauses(clauses);
            steps.push(PropStep::Post(PropPost::When {
                subject_name,
                clause_meta,
            }));
            for c in clause_children.into_iter().rev() {
                steps.push(PropStep::Visit(c));
            }
            steps.push(PropStep::Visit(subject.into_inner()));
        }
        other => match plain_children(other) {
            Ok((kind, children)) => {
                steps.push(PropStep::Post(PropPost::Plain(kind)));
                for c in children.into_iter().rev() {
                    steps.push(PropStep::Visit(c));
                }
            }
            Err(leaf) => done.push(leaf),
        },
    }
}

/// Split a clause list into the per-clause metadata a `Post` step needs and
/// the guard/body children to visit, in `map_children`'s order.
fn split_clauses(clauses: Vec<WhenClause>) -> (Vec<(WhenPattern, bool)>, Vec<PseudoExpr>) {
    let mut clause_meta = Vec::with_capacity(clauses.len());
    let mut clause_children = Vec::new();
    for c in clauses {
        clause_meta.push((c.pattern, c.guard.is_some()));
        if let Some(g) = c.guard {
            clause_children.push(g);
        }
        clause_children.push(c.body);
    }
    (clause_meta, clause_children)
}

/// Reassemble one node from the already-rewritten children the walk left on
/// `done`, in the order they were pushed.
fn rebuild_step(post: PropPost, done: &mut Vec<PseudoExpr>) -> PseudoExpr {
    match post {
        PropPost::Let { name, id } => {
            let body = done.pop().expect("let body");
            let value = done.pop().expect("let value");
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
        PropPost::Lambda { params } => PseudoExpr::Lambda {
            params,
            body: PBox::new(done.pop().expect("lambda body")),
        },
        PropPost::RecFn { name, params } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(done.pop().expect("recfn body")),
        },
        PropPost::When {
            subject_name,
            clause_meta,
        } => {
            let total = 1 + clause_child_count(&clause_meta);
            let mut parts = take(done, total).into_iter();
            let subject = parts.next().expect("when subject");
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses: rebuild_clauses(clause_meta, &mut parts),
            }
        }
        PropPost::WhenSubstitutedSubject {
            subject,
            subject_name,
            clause_meta,
        } => {
            let total = clause_child_count(&clause_meta);
            let mut parts = take(done, total).into_iter();
            PseudoExpr::When {
                subject,
                subject_name,
                clauses: rebuild_clauses(clause_meta, &mut parts),
            }
        }
        PropPost::Plain(kind) => rebuild_plain(kind, done),
    }
}

fn clause_child_count(clause_meta: &[(WhenPattern, bool)]) -> usize {
    clause_meta
        .iter()
        .map(|(_, has_guard)| usize::from(*has_guard) + 1)
        .sum()
}

fn rebuild_clauses(
    clause_meta: Vec<(WhenPattern, bool)>,
    parts: &mut std::vec::IntoIter<PseudoExpr>,
) -> Vec<WhenClause> {
    clause_meta
        .into_iter()
        .map(|(pattern, has_guard)| WhenClause {
            pattern,
            guard: has_guard.then(|| parts.next().expect("when guard")),
            body: parts.next().expect("when clause body"),
        })
        .collect()
}

/// Children first, then `try_propagate` on the rebuilt node — the fold
/// runs in each node's `Post` step. `changed` is threaded directly; every
/// alias folded anywhere still sets the one flag the caller's fixpoint
/// loop reads. Leaves skip `try_propagate`, which is the identity on
/// anything but a `Let`.
fn rewrite(expr: PseudoExpr, kinds: &HashMap<VarId, BinderKind>, changed: &mut bool) -> PseudoExpr {
    let mut steps: Vec<PropStep> = vec![PropStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            PropStep::Visit(expr) => push_map_children(expr, &mut steps, &mut done),
            PropStep::Post(post) => {
                let rebuilt = rebuild_step(post, &mut done);
                done.push(try_propagate(rebuilt, kinds, changed));
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

fn try_propagate(
    expr: PseudoExpr,
    kinds: &HashMap<VarId, BinderKind>,
    changed: &mut bool,
) -> PseudoExpr {
    let PseudoExpr::Let {
        name,
        id,
        value,
        body,
    } = expr
    else {
        return expr;
    };
    // Marker + shape check (per-site).
    let (
        Some(aid),
        PseudoExpr::Var {
            name: rname,
            id: Some(rid),
        },
    ) = (id, value.as_ref())
    else {
        return PseudoExpr::Let {
            name,
            id,
            value,
            body,
        };
    };
    let (rname, rid) = (rname.clone(), *rid);
    if name == "decompiled" || rid == aid || rname.starts_with('_') {
        return PseudoExpr::Let {
            name,
            id,
            value,
            body,
        };
    }
    // RHS kind known, not a RecFn name, not a collided id.
    match kinds.get(&rid) {
        Some(BinderKind::RecFnName) | Some(BinderKind::Conflict) | None => {
            return PseudoExpr::Let {
                name,
                id,
                value,
                body,
            };
        }
        Some(_) => {}
    }
    // Dual-keyed use census (None = sets don't coincide; fail-closed).
    let Some(use_count) = dual_keyed_use_census(&body, aid, &name) else {
        return PseudoExpr::Let {
            name,
            id,
            value,
            body,
        };
    };
    if use_count == 0 {
        // Dead alias — `drop_dead_pure_lets` handles those.
        return PseudoExpr::Let {
            name,
            id,
            value,
            body,
        };
    }
    // Multi-use folds only for the synthetic CSE `w`-family.
    if use_count > 1 && !is_synthetic_w_family(&name) {
        return PseudoExpr::Let {
            name,
            id,
            value,
            body,
        };
    }
    // Every use reachable and capture-free (rendered-name comparison).
    let s_rname = sanitize_identifier(&rname);
    let scan = scan_uses(&body, aid, &s_rname, rid);
    if scan.found != use_count || !scan.all_clean {
        return PseudoExpr::Let {
            name,
            id,
            value,
            body,
        };
    }
    // Substitute every use and drop the let.
    let rhs = PseudoExpr::Var {
        name: rname.clone(),
        id: Some(rid),
    };
    let mut substituted = 0usize;
    let new_body = substitute_all_uses(
        body.into_inner(),
        aid,
        &name,
        &rhs,
        &rname,
        rid,
        &mut substituted,
    );
    if substituted != use_count {
        // Should be unreachable given the census/scan; fail-closed restore.
        return PseudoExpr::Let {
            name,
            id,
            value: PBox::new(rhs),
            body: PBox::new(new_body),
        };
    }
    *changed = true;
    new_body
}

/// Is `name` the synthetic `extract_repeated_subexpr` binder family — `w`,
/// or `w` with `_<digits>` suffixes (`w_2`, `w_3_2`)? The CSE names every
/// extraction literally `w` and `disambiguate_shadowed_lets` suffixes
/// collisions, so no such name is user-meaningful.
fn is_synthetic_w_family(name: &str) -> bool {
    let Some(rest) = name.strip_prefix('w') else {
        return false;
    };
    if rest.is_empty() {
        return true;
    }
    // Each suffix segment must be `_<digits>`.
    rest.split('_')
        .skip(1)
        .all(|seg| !seg.is_empty() && seg.bytes().all(|b| b.is_ascii_digit()))
        && rest.starts_with('_')
}

/// G3: census of the alias's uses. `Some(n)` when the id-keyed and
/// rendered-name-keyed reference sets coincide exactly (`n` nodes, every
/// id-matched node renders as the alias name, no extra name-only
/// matches); `None` otherwise. Names are compared after
/// `sanitize_identifier` because the printer prints that form: an alias
/// raw-named `when` renders `when_`, and a raw-string count would miss an
/// id-less compat ref spelled `when_` and orphan it.
fn dual_keyed_use_census(body: &PseudoExpr, aid: VarId, aname: &str) -> Option<usize> {
    struct Counter<'a> {
        aid: VarId,
        s_aname: &'a str,
        id_count: usize,
        name_count: usize,
        every_id_node_named_a: bool,
    }
    impl ExprVisitor for Counter<'_> {
        fn visit_var(&mut self, name: &str, id: &Option<VarId>) {
            let renders_as_a = sanitize_identifier(name) == self.s_aname;
            if *id == Some(self.aid) {
                self.id_count += 1;
                if !renders_as_a {
                    self.every_id_node_named_a = false;
                }
            }
            if renders_as_a {
                self.name_count += 1;
            }
        }
    }
    let s_aname = sanitize_identifier(aname);
    let mut c = Counter {
        aid,
        s_aname: &s_aname,
        id_count: 0,
        name_count: 0,
        every_id_node_named_a: true,
    };
    c.walk(body);
    (c.id_count == c.name_count && c.every_id_node_named_a).then_some(c.id_count)
}

/// G4 scan result: how many `Var(aid)` uses the scope walker reached, and
/// whether every one of them sits under NO binder (below the alias-let)
/// that renders like `rname` or carries `rid`.
struct UseScan {
    found: usize,
    all_clean: bool,
}

/// G4: top-down scope walk over ALL uses; at each `Var(aid)` the
/// accumulated `shadowed` state decides cleanliness. Names are compared
/// after `sanitize_identifier` because the printer prints that form: an
/// RHS raw-named `validator` renders `validator_`, which a binder
/// literally named `validator_` then print-captures.
///
/// `WhenPattern::Literal` payloads are deliberately not entered; a use
/// hiding there stays uncounted and the caller's `found != census` check
/// vetoes — a fail-closed miss.
///
/// `shadowed` was a call ARGUMENT, so it rides on each job rather than on a
/// frame: a binder that renders like the RHS name (or carries `rid`) sets it
/// for the subtree it scopes and for that subtree only — a `Let`'s binder
/// covers its BODY but not its VALUE, which is exactly the two jobs the `Let`
/// arm pushes.
fn scan_uses(body: &PseudoExpr, aid: VarId, s_rname: &str, rid: VarId) -> UseScan {
    let shadows = |name: &str, id: VarId| sanitize_identifier(name) == s_rname || id == rid;
    let mut out = UseScan {
        found: 0,
        all_clean: true,
    };
    let mut stack: Vec<(&PseudoExpr, bool)> = vec![(body, false)];

    while let Some((expr, shadowed)) = stack.pop() {
        match expr {
            PseudoExpr::Var { id, .. } => {
                if *id == Some(aid) {
                    out.found += 1;
                    if shadowed {
                        out.all_clean = false;
                    }
                }
            }
            PseudoExpr::Lambda { params, body } => {
                let sh = shadowed || params.iter().any(|p| shadows(&p.name, p.id));
                stack.push((body.as_ref(), sh));
            }
            PseudoExpr::RecFn { name, params, body } => {
                let sh = shadowed
                    || shadows(&name.name, name.id)
                    || params.iter().any(|p| shadows(&p.name, p.id));
                stack.push((body.as_ref(), sh));
            }
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                // The let's own binder scopes only its BODY, not its value.
                let sh = shadowed || sanitize_identifier(name) == s_rname || *id == Some(rid);
                stack.push((body.as_ref(), sh));
                // Pushed last so it pops FIRST, keeping source order.
                stack.push((value.as_ref(), shadowed));
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                let subject_shadows = subject_name
                    .as_ref()
                    .is_some_and(|b| shadows(&b.name, b.id));
                for clause in clauses.iter().rev() {
                    let pattern_shadows = clause
                        .pattern
                        .bound_names()
                        .iter()
                        .any(|n| sanitize_identifier(n) == s_rname)
                        || clause.pattern.bound_ids().contains(&rid);
                    let sh = shadowed || subject_shadows || pattern_shadows;
                    stack.push((&clause.body, sh));
                    if let Some(guard) = &clause.guard {
                        stack.push((guard, sh));
                    }
                }
                stack.push((subject.as_ref(), shadowed));
            }
            other => {
                for child in children(other).into_iter().rev() {
                    stack.push((child, shadowed));
                }
            }
        }
    }
    out
}

/// Replace EVERY `Var(aid)` use with `rhs`, counting replacements. At a
/// `When` whose SUBJECT is a use, also rewrite a `subject_name` that
/// names/ids the alias to the RHS binder (reusing `rid` — no fresh
/// `VarId`), keeping the printer's name-based subject matching consistent.
fn substitute_all_uses(
    expr: PseudoExpr,
    aid: VarId,
    aname: &str,
    rhs: &PseudoExpr,
    rname: &str,
    rid: VarId,
    substituted: &mut usize,
) -> PseudoExpr {
    let mut steps: Vec<PropStep> = vec![PropStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            PropStep::Visit(expr) => match expr {
                PseudoExpr::Var { name, id } => {
                    if id == Some(aid) {
                        *substituted += 1;
                        done.push(rhs.clone());
                    } else {
                        done.push(PseudoExpr::Var { name, id });
                    }
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } if matches!(subject.as_ref(), PseudoExpr::Var { id, .. } if *id == Some(aid)) => {
                    *substituted += 1;
                    let subject_name = match subject_name {
                        Some(b) if b.name == aname || b.id == aid => {
                            Some(Binder::new(rname.to_string(), rid))
                        }
                        other => other,
                    };
                    // Clause guards/bodies may hold further uses — keep walking.
                    let (clause_meta, clause_children) = split_clauses(clauses);
                    steps.push(PropStep::Post(PropPost::WhenSubstitutedSubject {
                        subject: PBox::new(rhs.clone()),
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(PropStep::Visit(c));
                    }
                }
                other => push_map_children(other, &mut steps, &mut done),
            },
            PropStep::Post(post) => {
                let rebuilt = rebuild_step(post, &mut done);
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "substitute_all_uses must leave one result");
    done.pop().expect("substitute_all_uses result")
}

#[cfg(test)]
mod tests;
