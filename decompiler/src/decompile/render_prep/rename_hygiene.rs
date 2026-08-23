//! Shared binder-rename primitives for the render-prep passes.
//!
//! Several passes pick a better display name for a binder and then have
//! to (a) prove the name is free, and (b) rewrite the declaration and
//! every reference together. Each had grown its own copy of that
//! machinery, and the copies had drifted — most consequentially
//! [`rename_pattern_binders`], whose `resolve_tx_info_field_indices`
//! copy handled only `Constructor` and `List` patterns and silently
//! skipped `Tuple` / `Pair` / `Var` ones. A rename hitting such a binder
//! renamed its REFERENCES but not its DECLARATION, which is exactly the
//! capture-shaped bug this module exists to make impossible.
//!
//! Everything here is keyed by [`VarId`], so a pass only ever affects the
//! binders it put in the map: covering every binder kind costs nothing
//! and closes the hole above. Display names only — no `VarId` is minted,
//! moved or re-pointed, so these are presentational rewrites.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, children, plain_children, rebuild_plain, take};

/// Give `binder` its new display name, if it has one.
pub(super) fn rename_binder(mut binder: Binder, renames: &HashMap<VarId, String>) -> Binder {
    if let Some(new_name) = renames.get(&binder.var_id()) {
        binder.set_display_name(new_name.clone());
    }
    binder
}

/// Rename every binder a `when` pattern declares — EVERY pattern kind,
/// so no declaration can be left behind while its references move.
pub(super) fn rename_pattern_binders(
    pattern: WhenPattern,
    renames: &HashMap<VarId, String>,
) -> WhenPattern {
    let rb = |b: Binder| rename_binder(b, renames);
    match pattern {
        WhenPattern::Constructor {
            type_hint,
            tag,
            fields,
            shape,
        } => WhenPattern::Constructor {
            type_hint,
            tag,
            fields: fields.into_iter().map(rb).collect(),
            shape,
        },
        WhenPattern::List { elements, tail } => WhenPattern::List {
            elements: elements.into_iter().map(rb).collect(),
            tail: tail.map(rb),
        },
        WhenPattern::Tuple(items) => WhenPattern::Tuple(items.into_iter().map(rb).collect()),
        WhenPattern::Pair(a, b) => WhenPattern::Pair(rb(a), rb(b)),
        WhenPattern::Var(b) => WhenPattern::Var(rb(b)),
        // Nothing is bound by these.
        other @ (WhenPattern::Wildcard | WhenPattern::Literal(_)) => other,
    }
}

/// Apply `renames` across `expr`: every `Var` reference AND every binder
/// site — `let`, lambda params, rec-fn name and params, a `when`'s
/// subject binder, and its clause patterns.
///
/// A binder whose `VarId` is not in the map is returned untouched, so a
/// pass that only means to rename (say) let-aliases is unaffected by the
/// other arms being covered.
pub(super) fn apply_renames(expr: PseudoExpr, renames: &HashMap<VarId, String>) -> PseudoExpr {
    let mut steps: Vec<RenameStep> = vec![RenameStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RenameStep::Enter(expr) => match expr {
                PseudoExpr::Var {
                    id: Some(vid),
                    name,
                } => done.push(PseudoExpr::Var {
                    name: renames.get(&vid).cloned().unwrap_or(name),
                    id: Some(vid),
                }),
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    // An id-less `let` went through `map_children` and kept
                    // its name; only an id-carrying one can be renamed.
                    let name = match id {
                        Some(bid) => renames.get(&bid).cloned().unwrap_or(name),
                        None => name,
                    };
                    steps.push(RenameStep::Post(RenamePost::Let { name, id }));
                    steps.push(RenameStep::Enter(body.into_inner()));
                    steps.push(RenameStep::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    let params = params
                        .into_iter()
                        .map(|p| rename_binder(p, renames))
                        .collect();
                    steps.push(RenameStep::Post(RenamePost::Lambda { params }));
                    steps.push(RenameStep::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let name = rename_binder(name, renames);
                    let params = params
                        .into_iter()
                        .map(|p| rename_binder(p, renames))
                        .collect();
                    steps.push(RenameStep::Post(RenamePost::RecFn { name, params }));
                    steps.push(RenameStep::Enter(body.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let subject_name = subject_name.map(|b| rename_binder(b, renames));
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut clause_children = Vec::new();
                    for c in clauses {
                        clause_meta.push((
                            rename_pattern_binders(c.pattern, renames),
                            c.guard.is_some(),
                        ));
                        if let Some(g) = c.guard {
                            clause_children.push(g);
                        }
                        clause_children.push(c.body);
                    }
                    steps.push(RenameStep::Post(RenamePost::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(RenameStep::Enter(c));
                    }
                    steps.push(RenameStep::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RenameStep::Post(RenamePost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(RenameStep::Enter(c));
                        }
                    }
                    // `map_children` returned a leaf unchanged — including
                    // an id-less `Var`.
                    Err(leaf) => done.push(leaf),
                },
            },
            RenameStep::Post(post) => {
                let rebuilt = match post {
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
                    RenamePost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = take(&mut done, total).into_iter();
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
                    RenamePost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "apply_renames must leave one result");
    done.pop().expect("apply_renames result")
}

/// One pending step of [`apply_renames`]'s explicit stack.
enum RenameStep {
    Enter(PseudoExpr),
    Post(RenamePost),
}

/// Everything about a node that is NOT one of its child expressions —
/// already renamed — held while those children are being rewritten.
enum RenamePost {
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
        /// Per clause: its already-renamed pattern and whether it had a
        /// guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Every binder / reference name currently in the tree, so a rename
/// target can be checked against them before it is committed.
///
/// `children()` does not surface `When` binder sites (the clause
/// patterns' `bound_names` and the optional `subject_name`), so this
/// collects them explicitly — without that, a target could shadow a
/// pattern binder.
pub(super) fn collect_used_names(expr: &PseudoExpr, out: &mut HashSet<String>) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr {
            PseudoExpr::Let { name, .. } | PseudoExpr::Var { name, .. } => {
                out.insert(name.clone());
            }
            PseudoExpr::Lambda { params, .. } => {
                out.extend(params.iter().map(|p| p.as_str().to_string()));
            }
            PseudoExpr::RecFn { name, params, .. } => {
                out.insert(name.as_str().to_string());
                out.extend(params.iter().map(|p| p.as_str().to_string()));
            }
            PseudoExpr::When {
                subject_name,
                clauses,
                ..
            } => {
                if let Some(sn) = subject_name {
                    out.insert(sn.as_str().to_string());
                }
                for clause in clauses {
                    out.extend(clause.pattern.bound_names());
                }
            }
            _ => {}
        }
        for child in children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// Commit a pass's rename candidates, conservatively.
///
/// A target that already exists as a name in the tree would shadow it,
/// and a target two candidates both want is ambiguous — both are DROPPED
/// rather than applied, so a rename can only ever make the output
/// clearer, never capture a reference. Survivors have their declaration
/// and every `VarId`-matched use rewritten together.
///
/// Sibling passes that pick binder names share this policy by calling
/// through here.
pub(super) fn commit_binder_renames(
    expr: PseudoExpr,
    candidates: Vec<(VarId, String)>,
) -> PseudoExpr {
    if candidates.is_empty() {
        return expr;
    }
    // Names already in the tree — never reuse one (would shadow).
    let mut used_names: HashSet<String> = HashSet::new();
    collect_used_names(&expr, &mut used_names);
    // A target name produced by more than one candidate is ambiguous — drop both.
    let mut target_counts: HashMap<&str, usize> = HashMap::new();
    for (_, n) in &candidates {
        *target_counts.entry(n.as_str()).or_insert(0) += 1;
    }
    let renames: HashMap<VarId, String> = candidates
        .iter()
        .filter(|(_, n)| target_counts[n.as_str()] == 1 && !used_names.contains(n))
        .map(|(id, n)| (*id, n.clone()))
        .collect();
    if renames.is_empty() {
        return expr;
    }
    apply_renames(expr, &renames)
}

/// The cons-`tail` binder of a `when <Var(param0)> is { [_, ..tail] -> … }`
/// anywhere in `body` — the witness that a rec-fn's slot-0 argument is its
/// own recursive sub-list rather than an independent value.
///
/// Requires EXACTLY ONE leading element, which is what `[_, ..tail]` means
/// and what both call sites' doc comments describe. A `[a, b, ..tail]` peel
/// is not the witness: an unrecognised slot-0 argument disqualifies the
/// inference rather than being silently waved through.
pub(super) fn find_param_cons_tail(body: &PseudoExpr, param0: VarId) -> Option<VarId> {
    let mut stack: Vec<&PseudoExpr> = vec![body];
    while let Some(body) = stack.pop() {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = body
            && matches!(subject.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == param0)
        {
            for c in clauses {
                if let WhenPattern::List {
                    elements,
                    tail: Some(tail),
                } = &c.pattern
                    && elements.len() == 1
                {
                    return Some(tail.var_id());
                }
            }
        }
        for child in children(body).into_iter().rev() {
            stack.push(child);
        }
    }
    None
}
