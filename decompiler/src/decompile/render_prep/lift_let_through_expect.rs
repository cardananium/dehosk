//! The chain renderer emits `Apply(Var("expect!"), [cond, body])` as
//! `expect <cond>; <body>`. When `cond` is a `Let` — bare, or under a
//! `Not` — the rendered output reads `expect !let X = v; …`, which is
//! invalid surface syntax: a let-statement is not an expression there.
//!
//! Lift the let out of the expect chain. The forms agree because the
//! let-value is evaluated eagerly in either one and the negation applies
//! only to the let-body's result.
//!
//! Safety: the let-binder must not appear free in the later args (the
//! chain's continuation, plus the fail message of the 3-arg form) —
//! lifting would capture them, so bail instead. The pass does not
//! alpha-rename to recover from a collision.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

/// A job on [`lift_let_through_expect`]'s stack. `Post` variants run after
/// that node's children.
enum Step {
    Visit(PseudoExpr),
    Post(Post),
}

enum Post {
    /// The bottom-up lift decision, made on the already-rewritten
    /// function/args — here.
    Apply {
        argc: usize,
    },
    /// The `Let` a lift just minted: its VALUE is carried here rather than re-walked.
    LiftedLet {
        name: String,
        id: Option<VarId>,
        value: PBox,
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
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Lift any `expect !(let X = v in b)` chain step out so the rendered
/// output reads `let X = v; expect !b; …`.
///
/// The rewrite is bottom-up, so every arm is "children, then rebuild" and needs no work
/// BETWEEN two child descents. The one decision that is not a plain rebuild — whether
/// an `Apply(expect!, …)` lifts — sits in its own `Post::Apply` step, reading the
/// already-rewritten children off `done`.
pub(super) fn lift_let_through_expect(expr: PseudoExpr) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(expr) => match expr {
                PseudoExpr::Apply { function, args } => {
                    // Recurse first — bottom-up rewrite. Reversed so the
                    // children pop — and so land on `done` — in source order.
                    let argc = args.len();
                    steps.push(Step::Post(Post::Apply { argc }));
                    for a in args.into_vec().into_iter().rev() {
                        steps.push(Step::Visit(a));
                    }
                    steps.push(Step::Visit(function.into_inner()));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(Step::Post(Post::Let { name, id }));
                    steps.push(Step::Visit(body.into_inner()));
                    steps.push(Step::Visit(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(Step::Post(Post::Lambda { params }));
                    steps.push(Step::Visit(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(Step::Post(Post::RecFn { name, params }));
                    steps.push(Step::Visit(body.into_inner()));
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
                    steps.push(Step::Post(Post::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(Step::Visit(c));
                    }
                    steps.push(Step::Visit(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(Step::Post(Post::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(Step::Visit(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            Step::Post(post) => {
                let rebuilt = match post {
                    Post::Apply { argc } => {
                        let args = take(&mut done, argc);
                        let function = done.pop().expect("apply function");
                        match try_lift(function, args) {
                            Lift::Lifted {
                                name,
                                id,
                                value,
                                inner,
                            } => {
                                // Re-visit: each lift yields an Apply that may itself
                                // match the Let-in-cond shape, so a chain lifts fully.
                                // This is re-entrant `lift_let_through_expect` call on
                                // the new inner Apply.
                                steps.push(Step::Post(Post::LiftedLet { name, id, value }));
                                steps.push(Step::Visit(inner));
                                continue;
                            }
                            Lift::Kept(apply) => apply,
                        }
                    }
                    Post::LiftedLet { name, id, value } => {
                        let body = done.pop().expect("lifted let body");
                        PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body: PBox::new(body),
                        }
                    }
                    Post::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    Post::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    Post::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    Post::When {
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
                    Post::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(
        done.len(),
        1,
        "lift_let_through_expect must leave one result"
    );
    done.pop().expect("lift_let_through_expect result")
}

/// Outcome of the lift check on one already-rewritten `Apply`.
enum Lift {
    /// The let lifted: wrap the (re-visited) `inner` Apply in this `Let`.
    Lifted {
        name: String,
        id: Option<VarId>,
        value: PBox,
        inner: PseudoExpr,
    },
    /// No lift — the `Apply` rebuilt as-is.
    Kept(PseudoExpr),
}

/// The body of the old `Apply` arm, minus the child recursion: decide whether
/// this `Apply(expect!, …)` lifts a `Let` out of its cond position.
fn try_lift(function: PseudoExpr, args: Vec<PseudoExpr>) -> Lift {
    // Both the 2-arg `[cond, body]` and the 3-arg
    // `[cond, body, fail_msg]` chains lift the Let; the
    // church-Bool 3-arg shape belongs to
    // `expect_three_arg_conditional`.
    if (args.len() == 2 || args.len() == 3)
        && let PseudoExpr::Var { name, .. } = &function
        && name.as_str() == "expect!"
    {
        // Shape A: bare Let in cond position,
        // `Apply(expect!, [Let{X=v, body}, tail])` →
        // `Let{X=v, Apply(expect!, [body, tail])}`.
        if let PseudoExpr::Let {
            name: let_name,
            id: let_id,
            value: let_value,
            body: let_body,
        } = &args[0]
        {
            let later_args = &args[1..];
            let captures = later_args
                .iter()
                .any(|a| expr_contains_free_name(a, let_name));
            if !captures {
                let mut new_args = Vec::with_capacity(args.len());
                new_args.push((**let_body).clone());
                new_args.extend(later_args.iter().cloned());
                return Lift::Lifted {
                    name: let_name.clone(),
                    id: *let_id,
                    value: let_value.clone(),
                    inner: PseudoExpr::Apply {
                        function: PBox::new(function.clone()),
                        args: new_args.into(),
                    },
                };
            }
        }
        // Shape B: `Apply(expect!,
        // [Not(Let{...}), tail])`.
        if let PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand,
        } = &args[0]
            && let PseudoExpr::Let {
                name: let_name,
                id: let_id,
                value: let_value,
                body: let_body,
            } = operand.as_ref()
        {
            // Bail if let_name appears free in
            // a later arg (tail or fail-msg) —
            // lifting would capture it.
            let later_args = &args[1..];
            let captures = later_args
                .iter()
                .any(|a| expr_contains_free_name(a, let_name));
            if !captures {
                let mut new_args = Vec::with_capacity(args.len());
                new_args.push(PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand: PBox::new((**let_body).clone()),
                });
                new_args.extend(later_args.iter().cloned());
                return Lift::Lifted {
                    name: let_name.clone(),
                    id: *let_id,
                    value: let_value.clone(),
                    inner: PseudoExpr::Apply {
                        function: PBox::new(function.clone()),
                        args: new_args.into(),
                    },
                };
            }
        }
    }

    Lift::Kept(PseudoExpr::Apply {
        function: PBox::new(function),
        args: args.into(),
    })
}

/// Free-name check by textual name, not `VarId`: two distinct
/// binders sharing a string read as a capture, so the lift is
/// refused where it would in fact be safe.
fn expr_contains_free_name(expr: &PseudoExpr, name: &str) -> bool {
    contains_free(expr, name)
}

fn contains_free(expr: &PseudoExpr, name: &str) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Var { name: n, .. } => {
                if n == name {
                    return true;
                }
            }
            PseudoExpr::Let {
                name: n,
                value,
                body,
                ..
            } => {
                // value sees outer scope; if let binds the same name,
                // the body shadows.
                pending.push(value);
                if n != name {
                    pending.push(body);
                }
            }
            PseudoExpr::Lambda { params, body } => {
                if !params.iter().any(|p| p.as_str() == name) {
                    pending.push(body);
                }
            }
            PseudoExpr::RecFn {
                name: rec_name,
                params,
                body,
            } => {
                if rec_name.as_str() != name && !params.iter().any(|p| p.as_str() == name) {
                    pending.push(body);
                }
            }
            PseudoExpr::Apply { function, args } => {
                pending.extend(args.iter().rev());
                pending.push(function);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                    if let Some(g) = &c.guard {
                        pending.push(g);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail.as_deref() {
                    pending.push(t);
                }
                pending.extend(elements.iter().rev());
            }
            PseudoExpr::Tuple(items) => pending.extend(items.iter().rev()),
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter().rev()),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter().rev()),
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
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
    false
}

#[cfg(test)]
mod tests;
