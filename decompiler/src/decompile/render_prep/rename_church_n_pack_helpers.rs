//! Rename top-level Church-N-pack helper definitions to `pack_N`
//! where N is the helper's arity.
//!
//! After `curry_split_partial_helpers`, a Church-encoded N-tuple
//! constructor has the shape of `pair_pack(a, b) = fn(x) { x(a, b) }`
//! at arity N: a let-bound lambda that wraps its params in a
//! one-arg eliminator. This pass renames every such helper with
//! N ≥ 3; arity 2 already carries `pair_pack`. The `_N` suffix
//! makes the constructor's arity visible at every call site.
//!
//! Rewrites by `VarId` (helper and its params: `a, b, c, …` outer,
//! `x` for the inner eliminator).
//!
//! After `cse_church_cons_helpers` so its 2-param church-cons
//! helpers — a different shape with a dead arm — are already
//! collapsed and cannot reach this pass's pattern.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn rename_church_n_pack_helpers(expr: PseudoExpr) -> PseudoExpr {
    let mut chain = Vec::new();
    let tail = peel_let_chain(expr, &mut chain);

    // Map each N-pack helper's binder VarId to its `pack_N` name.
    let mut renames: HashMap<VarId, String> = HashMap::new();
    // Matched pack-helper VarIds; their params are normalised to
    // a, b, c, … in the rewrite below.
    let mut pack_ids: Vec<VarId> = Vec::new();
    for entry in &chain {
        if let Some(id) = entry.id
            && let Some(arity) = match_n_pack(&entry.value)
        {
            renames.insert(id, format!("pack_{}", arity));
            pack_ids.push(id);
            // Also queue param VarId renames: a, b, c, … for the outer
            // params and `x` for the church-eliminator's inner param.
            if let PseudoExpr::Lambda { params, body } = &entry.value {
                for (i, p) in params.iter().enumerate() {
                    renames.insert(p.var_id(), letter_at(i).to_string());
                }
                if let PseudoExpr::Lambda { params: inner, .. } = body.as_ref() {
                    if inner.len() == 1 {
                        renames.insert(inner[0].var_id(), "x".to_string());
                    }
                }
            }
        }
    }
    if renames.is_empty() {
        return rebuild_chain(chain, tail);
    }
    let pack_set: std::collections::HashSet<VarId> = pack_ids.iter().copied().collect();

    let tail = redirect_var_names(tail, &renames);
    let chain: Vec<LetEntry> = chain
        .into_iter()
        .map(|entry| {
            let entry_id = entry.id;
            let new_name = if let Some(id) = entry_id
                && let Some(canonical) = renames.get(&id)
            {
                canonical.clone()
            } else {
                entry.name
            };
            // For pack-helper values, also rename binder display names
            // on params so the rendered signature matches the args.
            let new_value = match entry.value {
                PseudoExpr::Lambda { params, body }
                    if entry_id.is_some_and(|id| pack_set.contains(&id)) =>
                {
                    let params: Vec<Binder> = params
                        .into_iter()
                        .enumerate()
                        .map(|(i, mut b)| {
                            b.set_display_name(letter_at(i));
                            b
                        })
                        .collect();
                    let body = match body.into_inner() {
                        PseudoExpr::Lambda {
                            params: mut inner,
                            body: inner_body,
                        } if inner.len() == 1 => {
                            inner[0].set_display_name("x");
                            PseudoExpr::Lambda {
                                params: inner,
                                body: PBox::new(redirect_var_names(
                                    inner_body.into_inner(),
                                    &renames,
                                )),
                            }
                        }
                        other => redirect_var_names(other, &renames),
                    };
                    PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    }
                }
                other => redirect_var_names(other, &renames),
            };
            LetEntry {
                name: new_name,
                id: entry_id,
                value: new_value,
            }
        })
        .collect();
    rebuild_chain(chain, tail)
}

/// Single-letter display name for a 0-indexed position:
/// 0→`a`, 1→`b`, …, 25→`z`; past 25 every position is `a`.
fn letter_at(i: usize) -> &'static str {
    const LETTERS: [&str; 26] = [
        "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r",
        "s", "t", "u", "v", "w", "x", "y", "z",
    ];
    LETTERS.get(i).copied().unwrap_or("a")
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

/// Match the canonical Church-N-pack helper shape (N ≥ 3):
/// `Lambda { params: [a_0, ..., a_{N-1}], body: Lambda { params: [x],
///   body: Apply { function: Var(x), args: [Var(a_0), ..., Var(a_{N-1})] } } }`
/// Returns the arity N when matched.
fn match_n_pack(expr: &PseudoExpr) -> Option<usize> {
    let PseudoExpr::Lambda { params, body } = expr else {
        return None;
    };
    let n = params.len();
    if n < 3 {
        return None;
    }
    let outer_ids: Vec<VarId> = params.iter().map(|b| b.var_id()).collect();
    let PseudoExpr::Lambda {
        params: inner_params,
        body: inner_body,
    } = body.as_ref()
    else {
        return None;
    };
    if inner_params.len() != 1 {
        return None;
    }
    let x_id = inner_params[0].var_id();
    let PseudoExpr::Apply { function, args } = inner_body.as_ref() else {
        return None;
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        return None;
    };
    if *fn_id != x_id {
        return None;
    }
    if args.len() != n {
        return None;
    }
    for (i, arg) in args.iter().enumerate() {
        let PseudoExpr::Var {
            id: Some(arg_id), ..
        } = arg
        else {
            return None;
        };
        if *arg_id != outer_ids[i] {
            return None;
        }
    }
    Some(n)
}

/// Rewrite every `Var { id: Some(vid) }` whose id is in `renames` to carry the
/// new display name (ids untouched).
fn redirect_var_names(expr: PseudoExpr, renames: &HashMap<VarId, String>) -> PseudoExpr {
    let mut steps: Vec<RenameStep> = vec![RenameStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RenameStep::Visit(expr) => match expr {
                PseudoExpr::Var {
                    name,
                    id: Some(vid),
                } => {
                    if let Some(new_name) = renames.get(&vid) {
                        done.push(PseudoExpr::Var {
                            name: new_name.clone(),
                            id: Some(vid),
                        })
                    } else {
                        done.push(PseudoExpr::Var {
                            name,
                            id: Some(vid),
                        })
                    }
                }
                other => push_map_children(other, &mut steps, &mut done),
            },
            RenameStep::Post(post) => {
                let rebuilt = rebuild_step(post, &mut done);
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "redirect_var_names must leave one result");
    done.pop().expect("redirect_var_names result")
}

/// A job on [`redirect_var_names`]'s stack: a node still to visit, or rebuild after
/// children.
enum RenameStep {
    Visit(PseudoExpr),
    Post(RenamePost),
}

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
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Per-variant descent as jobs: push the node's
/// reconstruction, then its children in REVERSE so they pop — and so land on `done` —
/// in source order. Leaves are finished on the spot.
fn push_map_children(node: PseudoExpr, steps: &mut Vec<RenameStep>, done: &mut Vec<PseudoExpr>) {
    match node {
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
            steps.push(RenameStep::Post(RenamePost::When {
                subject_name,
                clause_meta,
            }));
            for c in clause_children.into_iter().rev() {
                steps.push(RenameStep::Visit(c));
            }
            steps.push(RenameStep::Visit(subject.into_inner()));
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
    }
}

/// Reassemble one node from the already-renamed children on `done`.
fn rebuild_step(post: RenamePost, done: &mut Vec<PseudoExpr>) -> PseudoExpr {
    match post {
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
        RenamePost::Plain(kind) => rebuild_plain(kind, done),
    }
}

#[allow(dead_code)]
fn _unused(_b: Binder) {}

#[cfg(test)]
mod tests;
