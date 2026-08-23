//! Strip `(Void)` from calls to zero-arity Constr-valued constants.
//!
//! Some scripts compile a constructor reference through Plutus's
//! `delay`, thunking the underlying Constr value. The decompiler
//! surfaces the resulting `force` as `c1(Void)` — the constant
//! applied to Unit to force evaluation. Both forms denote the same
//! Constr value, and calling it as if it were a function is neither
//! type-safe nor readable, so `c1(Void)` is rewritten to `c1`.
//!
//! Collect the `VarId` of every binder whose value is a
//! `Constr { fields: [] }` (zero-arg constructor — `True`/`False`,
//! Nil, or any user-defined nullary variant), then rewrite
//! `Apply { function: Var(let_id), args: [Unit] }` to `Var(let_id)`.
//! Multi-arg applies, non-Unit args, and applies on non-Constr
//! constants are left alone.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, children, plain_children, rebuild_plain, take};

pub(super) fn strip_void_apply_on_constr(expr: PseudoExpr) -> PseudoExpr {
    let mut zero_arg_constrs: HashSet<VarId> = HashSet::new();
    collect_zero_arg_constr_consts(&expr, &mut zero_arg_constrs);
    if zero_arg_constrs.is_empty() {
        return expr;
    }
    rewrite(expr, &zero_arg_constrs)
}

fn collect_zero_arg_constr_consts(expr: &PseudoExpr, out: &mut HashSet<VarId>) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if let PseudoExpr::Let { id, value, .. } = expr
            && let Some(binder_id) = id
            && matches!(
                value.as_ref(),
                PseudoExpr::Constr { fields, .. } if fields.is_empty()
            )
        {
            out.insert(*binder_id);
        }
        for child in children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// One pending job of [`rewrite`]'s explicit stack: a node still to visit, or rebuild
/// after children.
enum StripStep {
    Visit(PseudoExpr),
    Post(StripPost),
}

enum StripPost {
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

/// Every arm below rebuilds its node verbatim from rewritten children, so the
/// non-binding kinds go through `plain_children` / `rebuild_plain`. The
/// `Var(zero-arg constr)(Void)` arm fires BEFORE any descent.
fn rewrite(expr: PseudoExpr, zero_arg_constrs: &HashSet<VarId>) -> PseudoExpr {
    let mut steps: Vec<StripStep> = vec![StripStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            StripStep::Visit(expr) => match expr {
                PseudoExpr::Apply { function, args }
                    if args.len() == 1
                        && matches!(&args[0], PseudoExpr::Unit)
                        && matches!(
                            function.as_ref(),
                            PseudoExpr::Var { id: Some(vid), .. } if zero_arg_constrs.contains(vid)
                        ) =>
                {
                    // The stripped function is the bare `Var`; returned it without
                    // descending, so it is finished.
                    done.push(function.into_inner());
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(StripStep::Post(StripPost::Let { name, id }));
                    // Reversed so they pop — and so land on `done` — in order.
                    steps.push(StripStep::Visit(body.into_inner()));
                    steps.push(StripStep::Visit(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(StripStep::Post(StripPost::Lambda { params }));
                    steps.push(StripStep::Visit(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(StripStep::Post(StripPost::RecFn { name, params }));
                    steps.push(StripStep::Visit(body.into_inner()));
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
                    steps.push(StripStep::Post(StripPost::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(StripStep::Visit(c));
                    }
                    steps.push(StripStep::Visit(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(StripStep::Post(StripPost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(StripStep::Visit(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            StripStep::Post(post) => {
                let rebuilt = match post {
                    StripPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    StripPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    StripPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    StripPost::When {
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
                    StripPost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

#[cfg(test)]
mod tests;
