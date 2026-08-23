//! Alpha-uniquify duplicate binder `VarId`s.
//!
//! Several inline/hoist passes clone a binder-bearing subtree
//! (`inline_pattern_field_access`, `extract_repeated_subexpr`,
//! `hoist_pure_multi_arg_calls`). Each clone keeps the original binder
//! `VarId`s, so the same id is bound in two places and every id-keyed
//! analysis (DCE and inliner ref-counting, rename application, the
//! Cardano type env, the compilable list witness) silently conflates
//! the copies.
//!
//! Walking parent-first, the first binder occurrence keeps its id; any
//! later binder carrying an already-seen id is re-minted with
//! `VarId::fresh_binding()` and its scope references are rewritten
//! (substitution stops at any deeper rebinding of the old id — deeper
//! duplicates re-mint themselves when reached). Under the lexical
//! interpretation of id-shadowing (a `Var` refers to its nearest
//! enclosing binder with that id) this is semantics-preserving.
//! Display names are never touched — the surgery is invisible to the
//! renderer.
//!
//! A `let f = rec fn g` pair where the let id equals the inner self-name
//! id is one binder (the collapse convention), not a duplicate.
//!
//! Duplicates are discovered in a fixed tree-walk order, so the re-mint
//! sequence is deterministic. `prepare_for_render`'s two runs start from
//! the same canonical input and re-mint their own ids; display names
//! never change and re-minted ids preserve the relative order of fresh
//! ids, so the rendered output is identical across runs.
//!
//! A re-minted binder's fresh id is absent from VarId-keyed side tables
//! (`FinalTypeTable` annotations, `kind_annotations`), so a clone-copy
//! binder can lose a display-only `: T` annotation the old shared id
//! carried. Semantics-safe: that shared annotation was wrong for one of
//! the two binders anyway.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;
use std::rc::Rc;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

/// Re-mint every duplicate binder id in `expr`.
///
/// The thread's `fresh_binding` counter is first synced ABOVE the maximum
/// id present in the tree: the tree can carry fresh-range ids from a
/// DIFFERENT counter epoch (another thread, an earlier pass), and an
/// unsynced mint could hand back an id already bound elsewhere in the same
/// tree. The sync also protects every DOWNSTREAM pass that mints via
/// `fresh_binding` into this tree.
pub(super) fn uniquify_duplicate_binders(expr: PseudoExpr) -> PseudoExpr {
    VarId::ensure_binding_counter_above(max_fresh_range_id(&expr));
    let mut seen: HashSet<VarId> = HashSet::new();
    rewrite(expr, &mut seen)
}

/// The maximum id occurring ANYWHERE in the tree (binders and refs) below
/// the compat-placeholder range.
pub(crate) fn max_fresh_range_id(expr: &PseudoExpr) -> u32 {
    let max = std::cell::Cell::new(0u32);
    let upd = |id: VarId| {
        if !id.is_compat_placeholder() && id.as_u32() > max.get() {
            max.set(id.as_u32());
        }
    };
    let mut on_binder = upd;
    let mut on_ref = upd;
    walk_ids(expr, &mut on_binder, &mut on_ref);
    max.get()
}

/// Count distinct ids bound by MORE than one binder — the invariant probe
/// (0 after `uniquify_duplicate_binders`). Used by the end-of-prepare
/// debug assertion and tests.
pub(crate) fn count_duplicate_binder_ids(expr: &PseudoExpr) -> usize {
    let mut counts: std::collections::HashMap<VarId, u32> = std::collections::HashMap::new();
    walk_ids(
        expr,
        &mut |id| {
            *counts.entry(id).or_insert(0) += 1;
        },
        &mut |_| {},
    );
    counts.values().filter(|n| **n > 1).count()
}

/// The shared COMPLETE id walker: `on_binder` fires once per binder
/// occurrence (let binders — a `let f = rec fn f` same-id pair counted
/// ONCE; lambda/recfn name+params; when subject_name ONCE PER WHEN; every
/// pattern binder), `on_ref` once per `Var` reference, and `Literal`
/// pattern payloads are walked in full. Hand-rolled with no wildcard arm
/// so a new variant is a compile error, and because `ExprVisitor`'s clause
/// hook fires per clause, which cannot count a subject_name exactly once.
fn walk_ids(expr: &PseudoExpr, on_binder: &mut impl FnMut(VarId), on_ref: &mut impl FnMut(VarId)) {
    let mut steps: Vec<IdStep<'_>> = vec![IdStep::Visit(expr)];

    while let Some(step) = steps.pop() {
        let expr = match step {
            IdStep::Visit(expr) => expr,
            // The `When` subject_name binder: reported BETWEEN the subject
            // walk and the clause walks, so it is its own step.
            IdStep::Bind(id) => {
                on_binder(id);
                continue;
            }
            // One `When` clause: its pattern binders fire before its
            // sub-expressions, and after the previous clause finished.
            IdStep::Clause(clause) => {
                for id in clause.pattern.bound_ids() {
                    on_binder(id);
                }
                // Reversed so they pop in source order.
                steps.push(IdStep::Visit(&clause.body));
                if let Some(guard) = &clause.guard {
                    steps.push(IdStep::Visit(guard));
                }
                if let WhenPattern::Literal(payload) = &clause.pattern {
                    steps.push(IdStep::Visit(payload));
                }
                continue;
            }
        };
        match expr {
            PseudoExpr::Var { id, .. } => {
                if let Some(v) = id {
                    on_ref(*v);
                }
            }
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                if let Some(lid) = id {
                    on_binder(*lid);
                }
                // Pushed first so it pops last, after the value subtree.
                steps.push(IdStep::Visit(body.as_ref()));
                // A `let f = rec fn f` same-id pair is ONE binder: visit the
                // RecFn manually so its name is not double-counted.
                if let PseudoExpr::RecFn {
                    name,
                    params,
                    body: rbody,
                } = value.as_ref()
                    && Some(name.id) == *id
                {
                    for p in params {
                        on_binder(p.id);
                    }
                    steps.push(IdStep::Visit(rbody.as_ref()));
                } else {
                    steps.push(IdStep::Visit(value.as_ref()));
                }
            }
            PseudoExpr::Lambda { params, body } => {
                for p in params {
                    on_binder(p.id);
                }
                steps.push(IdStep::Visit(body.as_ref()));
            }
            PseudoExpr::RecFn { name, params, body } => {
                on_binder(name.id);
                for p in params {
                    on_binder(p.id);
                }
                steps.push(IdStep::Visit(body.as_ref()));
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                // Reversed: subject, then the subject_name binder, then the
                // clauses in source order.
                for clause in clauses.iter().rev() {
                    steps.push(IdStep::Clause(clause));
                }
                if let Some(sn) = subject_name {
                    steps.push(IdStep::Bind(sn.id));
                }
                steps.push(IdStep::Visit(subject.as_ref()));
            }
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    steps.push(IdStep::Visit(a));
                }
                steps.push(IdStep::Visit(function.as_ref()));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                steps.push(IdStep::Visit(else_branch.as_ref()));
                steps.push(IdStep::Visit(then_branch.as_ref()));
                steps.push(IdStep::Visit(condition.as_ref()));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    steps.push(IdStep::Visit(t.as_ref()));
                }
                for e in elements.iter().rev() {
                    steps.push(IdStep::Visit(e));
                }
            }
            PseudoExpr::Tuple(items) => {
                for i in items.iter().rev() {
                    steps.push(IdStep::Visit(i));
                }
            }
            PseudoExpr::Pair(a, b) => {
                steps.push(IdStep::Visit(b.as_ref()));
                steps.push(IdStep::Visit(a.as_ref()));
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    steps.push(IdStep::Visit(f));
                }
            }
            PseudoExpr::FieldAccess { record, .. } => steps.push(IdStep::Visit(record.as_ref())),
            PseudoExpr::IndexAccess { collection, .. } => {
                steps.push(IdStep::Visit(collection.as_ref()))
            }
            PseudoExpr::BinOp { left, right, .. } => {
                steps.push(IdStep::Visit(right.as_ref()));
                steps.push(IdStep::Visit(left.as_ref()));
            }
            PseudoExpr::UnOp { operand, .. } => steps.push(IdStep::Visit(operand.as_ref())),
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    steps.push(IdStep::Visit(a));
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                steps.push(IdStep::Visit(inner.as_ref()))
            }
            PseudoExpr::Trace { message, value } => {
                steps.push(IdStep::Visit(value.as_ref()));
                steps.push(IdStep::Visit(message.as_ref()));
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
}

/// A job on [`walk_ids`]'s stack. `Bind` and `Clause` are the points run between two
/// child walks; they must stay separate steps.
enum IdStep<'a> {
    Visit(&'a PseudoExpr),
    Bind(VarId),
    Clause(&'a WhenClause),
}

/// Re-mint `binder` if its id was already seen, returning the
/// `(old, fresh)` rename to substitute through its scope; `None` when the
/// binder kept its id.
fn admit(binder: &mut Binder, seen: &mut HashSet<VarId>) -> Option<(VarId, VarId)> {
    let old = binder.id;
    if seen.insert(old) {
        return None;
    }
    let fresh = VarId::fresh_binding();
    seen.insert(fresh);
    binder.id = fresh;
    Some((old, fresh))
}

/// Apply the pending renames to a scope subtree: every `Var` carrying an
/// old id becomes the fresh id (NAME UNTOUCHED); substitution stops below
/// any node that REBINDS the old id (the deeper duplicate re-mints itself
/// when the main walk reaches it).
fn subst_scope(expr: PseudoExpr, renames: &[(VarId, VarId)]) -> PseudoExpr {
    if renames.is_empty() {
        return expr;
    }
    let mut steps: Vec<SubstStep> = vec![SubstStep::Visit(expr, Rc::new(renames.to_vec()))];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            SubstStep::Visit(expr, renames) => {
                // early return: an empty live set leaves the whole subtree untouched
                // rather than rebuilding it node by node.
                if renames.is_empty() {
                    done.push(expr);
                    continue;
                }
                match expr {
                    PseudoExpr::Var { name, id: Some(v) } => {
                        // LAST match wins: within one batch, renames are pushed
                        // outer-to-inner (subject_name before pattern binders, earlier
                        // params before later), and the INNER binder lexically shadows
                        // — two same-old entries must resolve to the later one.
                        let id = renames
                            .iter()
                            .rev()
                            .find(|(old, _)| *old == v)
                            .map(|(_, fresh)| *fresh)
                            .unwrap_or(v);
                        done.push(PseudoExpr::Var { name, id: Some(id) });
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        let live: Rc<Vec<(VarId, VarId)>> = Rc::new(
                            renames
                                .iter()
                                .filter(|(old, _)| id != Some(*old))
                                .copied()
                                .collect(),
                        );
                        steps.push(SubstStep::Post(SubstPost::Let { name, id }));
                        steps.push(SubstStep::Visit(body.into_inner(), live));
                        steps.push(SubstStep::Visit(value.into_inner(), renames));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let live: Rc<Vec<(VarId, VarId)>> = Rc::new(
                            renames
                                .iter()
                                .filter(|(old, _)| !params.iter().any(|p| p.id == *old))
                                .copied()
                                .collect(),
                        );
                        steps.push(SubstStep::Post(SubstPost::Lambda { params }));
                        steps.push(SubstStep::Visit(body.into_inner(), live));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let live: Rc<Vec<(VarId, VarId)>> = Rc::new(
                            renames
                                .iter()
                                .filter(|(old, _)| {
                                    name.id != *old && !params.iter().any(|p| p.id == *old)
                                })
                                .copied()
                                .collect(),
                        );
                        steps.push(SubstStep::Post(SubstPost::RecFn { name, params }));
                        steps.push(SubstStep::Visit(body.into_inner(), live));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let sn_rebind = subject_name.as_ref().map(|b| b.id);
                        let mut layout: Vec<SubstClause> = Vec::with_capacity(clauses.len());
                        // Built in source order, then drained onto `steps` in
                        // reverse so the jobs pop in source order.
                        let mut jobs: Vec<SubstStep> = Vec::new();
                        for clause in clauses {
                            let bound = clause.pattern.bound_ids();
                            let live: Rc<Vec<(VarId, VarId)>> = Rc::new(
                                renames
                                    .iter()
                                    .filter(|(old, _)| {
                                        !bound.contains(old) && sn_rebind != Some(*old)
                                    })
                                    .copied()
                                    .collect(),
                            );
                            let pattern = match clause.pattern {
                                // A literal payload is substituted with the
                                // FULL renames, not the clause's live set.
                                WhenPattern::Literal(payload) => {
                                    jobs.push(SubstStep::Visit(payload, Rc::clone(&renames)));
                                    None
                                }
                                other => Some(other),
                            };
                            let has_guard = clause.guard.is_some();
                            if let Some(g) = clause.guard {
                                jobs.push(SubstStep::Visit(g, Rc::clone(&live)));
                            }
                            jobs.push(SubstStep::Visit(clause.body, live));
                            layout.push(SubstClause { pattern, has_guard });
                        }
                        steps.push(SubstStep::Post(SubstPost::When {
                            subject_name,
                            layout,
                        }));
                        while let Some(job) = jobs.pop() {
                            steps.push(job);
                        }
                        steps.push(SubstStep::Visit(subject.into_inner(), renames));
                    }
                    // The non-binding variants, in `map_children`'s order.
                    other => match super::scope_recurse::plain_children(other) {
                        Ok((kind, children)) => {
                            steps.push(SubstStep::Post(SubstPost::Plain(kind)));
                            for c in children.into_iter().rev() {
                                steps.push(SubstStep::Visit(c, Rc::clone(&renames)));
                            }
                        }
                        Err(leaf) => done.push(leaf),
                    },
                }
            }
            SubstStep::Post(post) => {
                let rebuilt = match post {
                    SubstPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    SubstPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    SubstPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    SubstPost::When {
                        subject_name,
                        layout,
                    } => {
                        let mut parts =
                            super::scope_recurse::take(&mut done, 1 + clause_child_count(&layout))
                                .into_iter();
                        let subject = parts.next().expect("when subject");
                        let clauses = layout.into_iter().map(|c| c.rebuild(&mut parts)).collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    SubstPost::Plain(kind) => super::scope_recurse::rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    done.pop().expect("subst_scope leaves exactly one result")
}

/// A job on [`subst_scope`]'s stack. The rename set travels WITH the node
/// (`Rc`, so a scope's filtered `live` set is shared by its whole subtree)
/// rather than as a call argument.
enum SubstStep {
    Visit(PseudoExpr, Rc<Vec<(VarId, VarId)>>),
    Post(SubstPost),
}

enum SubstPost {
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
        layout: Vec<SubstClause>,
    },
    Plain(super::scope_recurse::PlainPost),
}

/// One `When` clause awaiting reassembly: everything that is NOT an
/// expression, plus how many expressions it left on `done`.
struct SubstClause {
    /// `None` for a `Literal` pattern, whose payload went through the walk
    /// and is rebuilt from `done`.
    pattern: Option<WhenPattern>,
    has_guard: bool,
}

impl SubstClause {
    fn child_count(&self) -> usize {
        usize::from(self.pattern.is_none()) + usize::from(self.has_guard) + 1
    }

    fn rebuild(self, parts: &mut impl Iterator<Item = PseudoExpr>) -> WhenClause {
        let pattern = match self.pattern {
            Some(p) => p,
            None => WhenPattern::Literal(parts.next().expect("literal payload")),
        };
        let guard = if self.has_guard {
            Some(parts.next().expect("clause guard"))
        } else {
            None
        };
        WhenClause {
            pattern,
            guard,
            body: parts.next().expect("clause body"),
        }
    }
}

fn clause_child_count(layout: &[SubstClause]) -> usize {
    layout.iter().map(SubstClause::child_count).sum()
}

/// The main parent-first walk.
///
/// The scope (`seen`) is a single insert-only set carried by the loop, so it needs no
/// per-frame save/restore. Admitting a binder, minting a rename, substituting a
/// scope — work between two child descents — is a distinct step variant.
fn rewrite(expr: PseudoExpr, seen: &mut HashSet<VarId>) -> PseudoExpr {
    let mut steps: Vec<RwStep> = vec![RwStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();
    // `When` clause reassembly data, pushed by `Clause` and drained by the
    // matching `Post::When`. LIFO like `done`: a clause's own subtree (and
    // any nested `When` in it) completes before the next clause's step runs.
    let mut clauses_done: Vec<SubstClause> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RwStep::Visit(expr) => match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    // The `let f = rec fn f` same-id pair is one binder: admit the
                    // let id once, mirror a re-mint onto the inner self-name, and
                    // substitute the rename into the RecFn body (its self-calls
                    // reference the pair id). The pair's RecFn is processed inline
                    // so the generic RecFn arm doesn't re-admit the mirrored name.
                    let mut renames: Vec<(VarId, VarId)> = Vec::new();
                    let mut id = id;
                    let was_pair = matches!(
                        (id, value.as_ref()),
                        (Some(lid), PseudoExpr::RecFn { name: rn, .. }) if rn.id == lid
                    );
                    if let Some(lid) = id {
                        let mut fake = Binder::new(name.clone(), lid);
                        if let Some((old, fresh)) = admit(&mut fake, seen) {
                            id = Some(fresh);
                            renames.push((old, fresh));
                        }
                    }
                    let (value, pair) = if was_pair {
                        let PseudoExpr::RecFn {
                            name: mut rec_name,
                            mut params,
                            body: rbody,
                        } = value.into_inner()
                        else {
                            unreachable!("was_pair checked the RecFn shape");
                        };
                        if let Some((_, fresh)) = renames.first() {
                            rec_name.id = *fresh;
                        }
                        let mut inner_renames = renames.clone();
                        for p in &mut params {
                            if let Some(r) = admit(p, seen) {
                                inner_renames.push(r);
                            }
                        }
                        let rbody = subst_scope(rbody.into_inner(), &inner_renames);
                        (rbody, Some((rec_name, params)))
                    } else {
                        // A non-pair value is NOT scoped by the let binder — an
                        // occurrence of the old id inside it refers to the OUTER
                        // duplicate, so the rename must not be substituted there.
                        (value.into_inner(), None)
                    };
                    // Reversed: the value subtree, then the body's scope
                    // substitution, then the body subtree, then rebuild.
                    steps.push(RwStep::Post(RwPost::Let { name, id, pair }));
                    steps.push(RwStep::LetBody {
                        body: body.into_inner(),
                        renames,
                    });
                    steps.push(RwStep::Visit(value));
                }
                PseudoExpr::Lambda { mut params, body } => {
                    let mut renames = Vec::new();
                    for p in &mut params {
                        if let Some(r) = admit(p, seen) {
                            renames.push(r);
                        }
                    }
                    let body = subst_scope(body.into_inner(), &renames);
                    steps.push(RwStep::Post(RwPost::Lambda { params }));
                    steps.push(RwStep::Visit(body));
                }
                PseudoExpr::RecFn {
                    mut name,
                    mut params,
                    body,
                } => {
                    let mut renames = Vec::new();
                    if let Some(r) = admit(&mut name, seen) {
                        renames.push(r);
                    }
                    for p in &mut params {
                        if let Some(r) = admit(p, seen) {
                            renames.push(r);
                        }
                    }
                    let body = subst_scope(body.into_inner(), &renames);
                    steps.push(RwStep::Post(RwPost::RecFn { name, params }));
                    steps.push(RwStep::Visit(body));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    // The subject is rewritten BEFORE `subject_name` is
                    // admitted, so the admit is its own step.
                    steps.push(RwStep::WhenSubject {
                        subject_name,
                        clauses,
                    });
                    steps.push(RwStep::Visit(subject.into_inner()));
                }
                // The non-binding variants, in `pipe_rewrite_children`'s order.
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
            // Ran after the let value, before the let body — where
            // `let body = subst_scope(body, &renames)` sat.
            RwStep::LetBody { body, renames } => {
                let body = subst_scope(body, &renames);
                steps.push(RwStep::Visit(body));
            }
            // Ran after the subject, before the first clause.
            RwStep::WhenSubject {
                mut subject_name,
                clauses,
            } => {
                let mut subject_renames = Vec::new();
                if let Some(sn) = subject_name.as_mut()
                    && let Some(r) = admit(sn, seen)
                {
                    subject_renames.push(r);
                }
                let count = clauses.len();
                steps.push(RwStep::Post(RwPost::When {
                    subject_name,
                    count,
                }));
                // Reversed so clause 0 is processed first: a later clause's
                // binder admissions must see everything the earlier clauses
                // minted, since `fresh_binding` hands out ids in call order.
                for clause in clauses.into_iter().rev() {
                    steps.push(RwStep::Clause {
                        clause,
                        subject_renames: subject_renames.clone(),
                    });
                }
            }
            // One clause: admit its pattern binders (this is what must not be
            // hoisted out of clause order), then queue its sub-expressions.
            RwStep::Clause {
                clause,
                subject_renames,
            } => {
                let WhenClause {
                    pattern,
                    guard,
                    body,
                } = clause;
                let mut renames = subject_renames;
                let (pattern, payload) = match pattern {
                    WhenPattern::Constructor {
                        type_hint,
                        tag,
                        mut fields,
                        shape,
                    } => {
                        for b in &mut fields {
                            if let Some(r) = admit(b, seen) {
                                renames.push(r);
                            }
                        }
                        (
                            Some(WhenPattern::Constructor {
                                type_hint,
                                tag,
                                fields,
                                shape,
                            }),
                            None,
                        )
                    }
                    WhenPattern::List { mut elements, tail } => {
                        for b in &mut elements {
                            if let Some(r) = admit(b, seen) {
                                renames.push(r);
                            }
                        }
                        let tail = tail.map(|mut t| {
                            if let Some(r) = admit(&mut t, seen) {
                                renames.push(r);
                            }
                            t
                        });
                        (Some(WhenPattern::List { elements, tail }), None)
                    }
                    WhenPattern::Tuple(mut items) => {
                        for b in &mut items {
                            if let Some(r) = admit(b, seen) {
                                renames.push(r);
                            }
                        }
                        (Some(WhenPattern::Tuple(items)), None)
                    }
                    WhenPattern::Pair(mut a, mut b) => {
                        if let Some(r) = admit(&mut a, seen) {
                            renames.push(r);
                        }
                        if let Some(r) = admit(&mut b, seen) {
                            renames.push(r);
                        }
                        (Some(WhenPattern::Pair(a, b)), None)
                    }
                    WhenPattern::Var(mut v) => {
                        if let Some(r) = admit(&mut v, seen) {
                            renames.push(r);
                        }
                        (Some(WhenPattern::Var(v)), None)
                    }
                    // `WhenPattern::Literal(rewrite(payload, seen))`: the
                    // payload becomes a child, rebuilt in `Post::When`.
                    WhenPattern::Literal(payload) => (None, Some(payload)),
                    WhenPattern::Wildcard => (Some(WhenPattern::Wildcard), None),
                };
                let has_guard = guard.is_some();
                clauses_done.push(SubstClause { pattern, has_guard });
                // Reversed: literal payload, then guard, then the body's
                // substitution + rewrite — source order.
                steps.push(RwStep::ClauseBody {
                    body,
                    renames: renames.clone(),
                });
                if let Some(g) = guard {
                    let g = subst_scope(g, &renames);
                    steps.push(RwStep::Visit(g));
                }
                if let Some(payload) = payload {
                    steps.push(RwStep::Visit(payload));
                }
            }
            // Ran after the clause guard, before the clause body — where
            // `let body = subst_scope(clause.body, &renames)` sat.
            RwStep::ClauseBody { body, renames } => {
                let body = subst_scope(body, &renames);
                steps.push(RwStep::Visit(body));
            }
            RwStep::Post(post) => {
                let rebuilt = match post {
                    RwPost::Let { name, id, pair } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        let value = match pair {
                            Some((rec_name, params)) => PseudoExpr::RecFn {
                                name: rec_name,
                                params,
                                body: PBox::new(value),
                            },
                            None => value,
                        };
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
                        count,
                    } => {
                        let layout = clauses_done.split_off(clauses_done.len() - count);
                        let mut parts =
                            super::scope_recurse::take(&mut done, 1 + clause_child_count(&layout))
                                .into_iter();
                        let subject = parts.next().expect("when subject");
                        let clauses = layout.into_iter().map(|c| c.rebuild(&mut parts)).collect();
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

    done.pop().expect("rewrite leaves exactly one result")
}

/// A job on [`rewrite`]'s stack. Every variant other than `Visit`/`Post` is a point run
/// between two child walks.
enum RwStep {
    Visit(PseudoExpr),
    LetBody {
        body: PseudoExpr,
        renames: Vec<(VarId, VarId)>,
    },
    WhenSubject {
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    },
    Clause {
        clause: WhenClause,
        subject_renames: Vec<(VarId, VarId)>,
    },
    ClauseBody {
        body: PseudoExpr,
        renames: Vec<(VarId, VarId)>,
    },
    Post(RwPost),
}

enum RwPost {
    Let {
        name: String,
        id: Option<VarId>,
        /// `Some` for a `let f = rec fn f` pair: the RecFn the value subtree
        /// is wrapped back into, with the mirrored name and admitted params.
        pair: Option<(Binder, Vec<Binder>)>,
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
        count: usize,
    },
    Plain(super::scope_recurse::PlainPost),
}

#[cfg(test)]
mod tests;
