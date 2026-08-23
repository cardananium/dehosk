use crate::pseudo::ast::PBox;
use std::collections::HashSet;
use std::rc::Rc;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

/// Split a node into a SHELL — every immediate child replaced by a `Unit`
/// placeholder — plus those children in `map_children` order. The shell is
/// refilled by [`join_children`], which re-walks the same slots in the same
/// order, so the placeholders are never observed.
fn split_children(expr: PseudoExpr) -> (PseudoExpr, Vec<PseudoExpr>) {
    let mut kids: Vec<PseudoExpr> = Vec::new();
    let shell = crate::decompile::render_prep::scope_recurse::map_children(expr, |c| {
        kids.push(c);
        PseudoExpr::Unit
    });
    (shell, kids)
}

/// Put rewritten children back into a shell from [`split_children`].
fn join_children(shell: PseudoExpr, kids: Vec<PseudoExpr>) -> PseudoExpr {
    let mut kids = kids.into_iter();
    crate::decompile::render_prep::scope_recurse::map_children(shell, |_| {
        kids.next().expect("split_children left one child per slot")
    })
}

/// Takes the last `n` items off `done` — the children of the node being
/// reassembled, left there in source order by the walk.
fn take_done(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
    let at = done.len() - n;
    done.split_off(at)
}

/// A job on [`rewrite_free_generated_var_to_binder`]'s stack. The `bound`
/// set travels WITH the node (`Rc`, so a scope is shared by its whole
/// subtree) rather than as a call argument.
enum RebindStep {
    Visit(PseudoExpr, Rc<HashSet<VarId>>),
    Post(RebindPost),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum RebindPost {
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
        /// Per clause: its pattern (never descended into) and whether it
        /// had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    /// A non-binding node: its `split_children` shell plus its child count.
    Plain(PseudoExpr, usize),
}

/// The scope is the `bound` set: the binding nodes (`Let` body, `Lambda`,
/// `RecFn`, each `When` clause) extend it for their scoped children only,
/// and it rides on the job rather than on a call frame. Children are pushed
/// in REVERSE so they pop in source order and are popped off `done` in that
/// same order when the node is rebuilt.
pub(in crate::decompile::late::normalize) fn rewrite_free_generated_var_to_binder(
    expr: PseudoExpr,
    target: &Binder,
    binder: &Binder,
    bound: &HashSet<VarId>,
) -> PseudoExpr {
    let mut steps: Vec<RebindStep> = vec![RebindStep::Visit(expr, Rc::new(bound.clone()))];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RebindStep::Visit(expr, bound) => match expr {
                PseudoExpr::Var { name, id } => {
                    // compat refs carry `id: None`, and the collectors normalize
                    // those to a fresh placeholder id when building `target`, so
                    // the ids never compare equal — match by name instead.
                    let matches_target =
                        id == Some(target.id) || (id.is_none() && name == target.name);
                    done.push(if matches_target && !bound.contains(&target.id) {
                        PseudoExpr::var_with_id(binder.name.clone(), binder.id)
                    } else {
                        PseudoExpr::Var { name, id }
                    });
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    let mut next_bound = (*bound).clone();
                    if let Some(id_val) = id {
                        next_bound.insert(id_val);
                    }
                    steps.push(RebindStep::Post(RebindPost::Let { name, id }));
                    steps.push(RebindStep::Visit(body.into_inner(), Rc::new(next_bound)));
                    steps.push(RebindStep::Visit(value.into_inner(), bound));
                }
                PseudoExpr::Lambda { params, body } => {
                    let mut next_bound = (*bound).clone();
                    next_bound.extend(params.iter().map(|param| param.id));
                    steps.push(RebindStep::Post(RebindPost::Lambda { params }));
                    steps.push(RebindStep::Visit(body.into_inner(), Rc::new(next_bound)));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let mut next_bound = (*bound).clone();
                    next_bound.insert(name.id);
                    next_bound.extend(params.iter().map(|param| param.id));
                    steps.push(RebindStep::Post(RebindPost::RecFn { name, params }));
                    steps.push(RebindStep::Visit(body.into_inner(), Rc::new(next_bound)));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    // Built in source order, then drained onto `steps` in
                    // reverse so the jobs pop in source order.
                    let mut jobs: Vec<RebindStep> = Vec::new();
                    for clause in clauses {
                        let mut next_bound = (*bound).clone();
                        if let Some(subject_name) = &subject_name {
                            next_bound.insert(subject_name.id);
                        }
                        next_bound.extend(clause.pattern.bound_ids());
                        let next_bound = Rc::new(next_bound);
                        clause_meta.push((clause.pattern, clause.guard.is_some()));
                        if let Some(guard) = clause.guard {
                            jobs.push(RebindStep::Visit(guard, Rc::clone(&next_bound)));
                        }
                        jobs.push(RebindStep::Visit(clause.body, next_bound));
                    }
                    steps.push(RebindStep::Post(RebindPost::When {
                        subject_name,
                        clause_meta,
                    }));
                    while let Some(job) = jobs.pop() {
                        steps.push(job);
                    }
                    steps.push(RebindStep::Visit(subject.into_inner(), bound));
                }
                // The non-binding variants, in `map_children`'s order — the same order
                // rebuilt them in. Leaves split into a zero-child shell and rejoin
                // unchanged.
                other => {
                    let (shell, kids) = split_children(other);
                    steps.push(RebindStep::Post(RebindPost::Plain(shell, kids.len())));
                    for kid in kids.into_iter().rev() {
                        steps.push(RebindStep::Visit(kid, Rc::clone(&bound)));
                    }
                }
            },
            RebindStep::Post(post) => {
                let rebuilt = match post {
                    RebindPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    RebindPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    RebindPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    RebindPost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let child_count: usize = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| 1 + usize::from(*has_guard))
                            .sum::<usize>();
                        let mut parts = take_done(&mut done, child_count).into_iter();
                        let subject = parts.next().expect("when subject");
                        let clauses = clause_meta
                            .into_iter()
                            .map(|(pattern, has_guard)| WhenClause {
                                pattern,
                                guard: has_guard.then(|| parts.next().expect("clause guard")),
                                body: parts.next().expect("clause body"),
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    RebindPost::Plain(shell, n) => {
                        let kids = take_done(&mut done, n);
                        join_children(shell, kids)
                    }
                };
                done.push(rebuilt);
            }
        }
    }

    done.pop()
        .expect("rewrite_free_generated_var_to_binder leaves exactly one result")
}
