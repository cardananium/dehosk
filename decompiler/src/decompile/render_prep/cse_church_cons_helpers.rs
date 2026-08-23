//! CSE for structurally identical Church-cons helper definitions.
//!
//! After `curry_split_partial_helpers`, a Church-cons constructor
//! `fn(h, t, _, k) { k(h, t) }` is a top-level 2-param function with a
//! nested 2-param Lambda. Copies are alpha-equivalent: they build
//! `Cons(head, tail)` as `fn(nil_arm, cons_arm) { cons_arm(head, tail) }`,
//! discarding the Nil arm. Generated ordinal names carry no role.
//!
//! Walks the top-level Let chain. If ≥ 2 helpers match
//! `fn(a, b) { fn(_, k) { k(a, b) } }` — 2 outer params, inner Lambda
//! of 2 params, inner body `Apply { function: Var(k), args: [Var(a),
//! Var(b)] }` — the first is canonical, renamed `church_cons`; the
//! others' references redirect to its VarId and their Lets drop. Other
//! arities / bodies are left alone.
//!
//! The canonical's own id maps to itself so refs still carrying the
//! old binder name re-render as `church_cons`. After
//! `curry_split_partial_helpers`, which produces the nested form.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn cse_church_cons_helpers(expr: PseudoExpr) -> PseudoExpr {
    let mut chain: Vec<LetEntry> = Vec::new();
    let tail = peel_let_chain(expr, &mut chain);

    let church_cons_ids: Vec<(usize, VarId)> = chain
        .iter()
        .enumerate()
        .filter(|(_, e)| is_church_cons_defining_lambda(&e.value))
        .map(|(i, e)| (i, e.id.expect("helper must have an id")))
        .collect();
    if church_cons_ids.len() < 2 {
        return rebuild_chain(chain, tail);
    }

    // First match is canonical. Subsequent matches get redirected.
    let canonical_idx = church_cons_ids[0].0;
    let canonical_id = church_cons_ids[0].1;
    // Every cons-helper id maps to canonical_id, the canonical included:
    // that self-entry makes refs still carrying the old binder name
    // re-render as `church_cons`.
    let redirects: HashMap<VarId, VarId> = church_cons_ids
        .iter()
        .map(|(_, id)| (*id, canonical_id))
        .collect();
    let drop_indices: Vec<usize> = church_cons_ids.iter().skip(1).map(|(i, _)| *i).collect();

    // Rebuild: drop the dead helper Lets, rename the canonical
    // binder, and redirect Var refs in the surviving values
    // and the tail.
    let mut rebuilt = redirect_vars(tail, &redirects);
    for (i, entry) in chain.into_iter().enumerate().rev() {
        if drop_indices.contains(&i) {
            continue;
        }
        let value = redirect_vars(entry.value, &redirects);
        let name = if i == canonical_idx {
            "church_cons".to_string()
        } else {
            entry.name
        };
        rebuilt = PseudoExpr::Let {
            name,
            id: entry.id,
            value: PBox::new(value),
            body: PBox::new(rebuilt),
        };
    }
    let _ = canonical_id; // canonical_id is the rename target — referenced via redirects map
    rebuilt
}

struct LetEntry {
    name: String,
    id: Option<VarId>,
    value: PseudoExpr,
}

fn peel_let_chain(mut expr: PseudoExpr, chain: &mut Vec<LetEntry>) -> PseudoExpr {
    loop {
        match expr {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                chain.push(LetEntry {
                    name,
                    id,
                    value: value.into_inner(),
                });
                expr = body.into_inner();
            }
            other => return other,
        }
    }
}

fn rebuild_chain(chain: Vec<LetEntry>, tail: PseudoExpr) -> PseudoExpr {
    let mut rebuilt = tail;
    for entry in chain.into_iter().rev() {
        rebuilt = PseudoExpr::Let {
            name: entry.name,
            id: entry.id,
            value: PBox::new(entry.value),
            body: PBox::new(rebuilt),
        };
    }
    rebuilt
}

/// Match the canonical Church-Cons helper shape:
/// `Lambda { params: [a, b], body: Lambda { params: [_, k],
///   body: Apply { function: Var(k), args: [Var(a), Var(b)] } } }`
fn is_church_cons_defining_lambda(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    if params.len() != 2 {
        return false;
    }
    let a_id = params[0].var_id();
    let b_id = params[1].var_id();
    let PseudoExpr::Lambda {
        params: inner_params,
        body: inner_body,
    } = body.as_ref()
    else {
        return false;
    };
    if inner_params.len() != 2 {
        return false;
    }
    let k_id = inner_params[1].var_id();
    let PseudoExpr::Apply { function, args } = inner_body.as_ref() else {
        return false;
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        return false;
    };
    if *fn_id != k_id {
        return false;
    }
    if args.len() != 2 {
        return false;
    }
    matches!(
        &args[0],
        PseudoExpr::Var { id: Some(vid), .. } if *vid == a_id
    ) && matches!(
        &args[1],
        PseudoExpr::Var { id: Some(vid), .. } if *vid == b_id
    )
}

/// One pending step of [`redirect_vars`]'s explicit job stack.
enum Step {
    Enter(PseudoExpr),
    Post(PostKind),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being redirected.
enum PostKind {
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
        /// Per clause: its pattern (never descended into, exactly as the
        /// recursion left it) and whether it had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// The only node the walk actually rewrites: a `Var` whose id is a
/// redirected cons-helper binder becomes a reference to the canonical
/// `church_cons`. Every other leaf is returned unchanged, exactly as the
/// recursion's `other => other` arm did.
fn redirect_leaf(expr: PseudoExpr, redirects: &HashMap<VarId, VarId>) -> PseudoExpr {
    match expr {
        PseudoExpr::Var {
            name,
            id: Some(vid),
        } => {
            if let Some(target) = redirects.get(&vid) {
                PseudoExpr::Var {
                    name: "church_cons".to_string(),
                    id: Some(*target),
                }
            } else {
                PseudoExpr::Var {
                    name,
                    id: Some(vid),
                }
            }
        }
        other => other,
    }
}

/// Rebuild every node from its already-redirected children.
///
/// Children are pushed in REVERSE so they pop in source order, and are
/// popped off `done` in that same order when the node is rebuilt.
fn redirect_vars(expr: PseudoExpr, redirects: &HashMap<VarId, VarId>) -> PseudoExpr {
    if redirects.is_empty() {
        return expr;
    }
    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(Step::Post(PostKind::Let { name, id }));
                    steps.push(Step::Enter(body.into_inner()));
                    steps.push(Step::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(Step::Post(PostKind::Lambda { params }));
                    steps.push(Step::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(Step::Post(PostKind::RecFn { name, params }));
                    steps.push(Step::Enter(body.into_inner()));
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
                    steps.push(Step::Post(PostKind::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(Step::Enter(c));
                    }
                    steps.push(Step::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(Step::Post(PostKind::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(Step::Enter(c));
                        }
                    }
                    Err(leaf) => done.push(redirect_leaf(leaf, redirects)),
                },
            },
            Step::Post(post) => {
                let rebuilt = match post {
                    PostKind::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    PostKind::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    PostKind::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    PostKind::When {
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
                    PostKind::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    done.pop().expect("redirect_vars leaves exactly one result")
}

// Quiet unused-import warning for Binder (referenced via AST destructure).
#[allow(dead_code)]
fn _unused(_b: Binder) {}

#[cfg(test)]
mod tests;
