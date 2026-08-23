//! Make a closure-returning fn's return value visible.
//!
//! A fn whose entire body is a bare `rec fn` definition returns that
//! closure, but the render gives the reader nothing to see it by.
//! Rewrap the tail as define-then-reference —
//! `let x_21 = rec fn x_21(…) { … }; x_21` — which the printer's
//! `ExitLetRecFnSameName` collapse renders as the definition followed
//! by an explicit trailing `x_21` return line.
//!
//! Gates: only a `Lambda` body that is a `RecFn` node directly. The
//! tail of a Let-chain carries the same ambiguity but is left alone.
//! The let binder reuses the rec-fn's display name with a fresh
//! `VarId` (the binding counter is raised above the tree max first),
//! and the reference is wired to that fresh id, so DCE sees a used
//! binding and the rec-fn's own name id stays uniquely bound.
//!
//! Idempotent: after the rewrap the Lambda body is a `Let`, which the
//! gate no longer matches.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn clarify_recfn_tail_return(expr: PseudoExpr) -> PseudoExpr {
    if !super::drop_dead_pure_lets::contains_decompiled_marker(&expr) {
        return expr;
    }
    VarId::ensure_binding_counter_above(super::alpha_uniquify::max_fresh_range_id(&expr));
    rewrite(expr)
}

/// One pending step of [`rewrite`]'s explicit job stack.
enum Step {
    Enter(PseudoExpr),
    Post(PostKind),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum PostKind {
    /// A `Lambda` whose body was a bare `RecFn` — the rewrap. It sits AFTER
    /// the body subtree because this mints its
    /// `VarId::fresh_binding()` only once that subtree had returned, and
    /// `fresh_binding` hands out ids in call order.
    LambdaRecFn {
        params: Vec<Binder>,
    },
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
        /// Per clause: its pattern (never descended into, exactly as
        /// `map_children` leaves it) and whether it had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Children are pushed in REVERSE so they pop in source order, and are
/// popped off `done` in that same order when the node is rebuilt — which is
/// also what keeps the `VarId::fresh_binding()` call sequence identical.
fn rewrite(expr: PseudoExpr) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match expr {
                PseudoExpr::Lambda { params, body }
                    if matches!(body.as_ref(), PseudoExpr::RecFn { .. }) =>
                {
                    steps.push(Step::Post(PostKind::LambdaRecFn { params }));
                    steps.push(Step::Enter(body.into_inner()));
                }
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
                    Err(leaf) => done.push(leaf),
                },
            },
            Step::Post(post) => {
                let rebuilt = match post {
                    PostKind::LambdaRecFn { params } => {
                        let rec_fn = done.pop().expect("lambda recfn body");
                        let PseudoExpr::RecFn { ref name, .. } = rec_fn else {
                            unreachable!("gate matched RecFn");
                        };
                        let display = name.display_name().to_string();
                        let fresh = VarId::fresh_binding();
                        PseudoExpr::Lambda {
                            params,
                            body: PBox::new(PseudoExpr::Let {
                                name: display.clone(),
                                id: Some(fresh),
                                value: PBox::new(rec_fn),
                                body: PBox::new(PseudoExpr::Var {
                                    name: display,
                                    id: Some(fresh),
                                }),
                            }),
                        }
                    }
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

    done.pop().expect("rewrite leaves exactly one result")
}

#[cfg(test)]
mod tests;
