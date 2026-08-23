//! Recover the correct polarity of an inverted *terminal* church Boolean
//! that simplify collapsed to `!cond || (trace MSG: church_false)`.
//!
//! A church Boolean used directly as a validator outcome decompiles from
//! the lowering seed `when (if cond { church_true } else { church_false })
//! is { Constr<0> -> church_true; Constr<1> -> trace MSG: church_false }`.
//! The correct collapse is `cond || (trace MSG: church_false)` (cond
//! true → success, cond false → log + church_false).
//!
//! But the simplify church-when collapse maps the two continuations with
//! the CIP convention (tag 1 = True / tag 0 = False), while this program
//! encodes church_true = `Constr<0>` (selects continuation 0). For the
//! terminal case the church_true continuation is decoded to a native
//! `True`, so the collapse + the `if cond { expr } else { True } ->
//! !cond || expr` readability fold emit the inverted
//! `!cond || (trace MSG: church_false)` — success on cond false.
//!
//! `recover_church_booleans` recovers the *re-dispatched* church bools
//! tag-faithfully; this handles the collapsed/terminal variant the
//! two-level recoverer never sees.
//!
//! The witness is the church_false — a nullary `Constr<1>` behind a
//! trace — reachable only on the short-circuit RHS of `||` under a
//! negated condition. church_false belongs on the cond-false path, so
//! its being reachable exactly when cond is true is the inversion
//! signature, and requiring it keeps the pass off a legitimately-negated
//! `||`. The witness is purely structural: see `rhs_returns_church_false`
//! for why the constructor's `origin` cannot be consulted. The fix drops
//! the `!`.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn recover_inverted_church_or(expr: PseudoExpr) -> PseudoExpr {
    rewrite_top_down(expr, |expr| try_rewrite(&expr).unwrap_or(expr))
}

/// One pending step of [`rewrite_top_down`]'s explicit stack.
enum Step {
    Enter(PseudoExpr),
    Post(Post),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum Post {
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
        /// Per clause: its pattern (never descended into) and whether it had
        /// a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// TOP-DOWN: the polarity test runs on a node BEFORE any descent, and a hit
/// lifts the `!`'s operand into the node's own left slot — the children that
/// are then walked are the REWRITTEN node's. `rewrite_bottom_up` would be
/// the wrong helper. `f` also runs on leaves. Children are pushed in
/// REVERSE so they pop in source order and are popped off `done` in that
/// same order when the node is rebuilt.
fn rewrite_top_down(expr: PseudoExpr, mut f: impl FnMut(PseudoExpr) -> PseudoExpr) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match f(expr) {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(Step::Post(Post::Let { name, id }));
                    steps.push(Step::Enter(body.into_inner()));
                    steps.push(Step::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(Step::Post(Post::Lambda { params }));
                    steps.push(Step::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(Step::Post(Post::RecFn { name, params }));
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
                    steps.push(Step::Post(Post::When {
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
                        steps.push(Step::Post(Post::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(Step::Enter(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            Step::Post(post) => {
                let rebuilt = match post {
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

    debug_assert_eq!(done.len(), 1, "rewrite_top_down must leave one result");
    done.pop().expect("rewrite_top_down result")
}

fn try_rewrite(expr: &PseudoExpr) -> Option<PseudoExpr> {
    let PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left,
        right,
    } = expr
    else {
        return None;
    };
    // Left must be `!cond` (the negated church condition).
    let PseudoExpr::UnOp {
        op: UnaryOp::Not,
        operand: cond,
    } = left.as_ref()
    else {
        return None;
    };
    // Right (the `||` short-circuit branch) must be a `trace MSG:
    // church_false` — the inversion witness.
    if !rhs_returns_church_false(right) {
        return None;
    }
    Some(PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: cond.clone(),
        right: right.clone(),
    })
}

/// True when `expr` is a `trace MSG: church_false` — a `Trace` (the
/// assertion shape) whose value (peeling further traces) is a nullary
/// `Constr<1>` church_false sentinel.
///
/// The leading `Trace` is required (an assertion logs, then yields the
/// false sentinel) rather than a bare `Constr<1>`; that keeps the pass
/// off any non-assertion `|| Constr<1>`. The constructor's `origin` is
/// NOT consulted: a downstream rebuild site resets the Scott→church
/// provenance to `DataTag` before render-prep, so a `ScottPositional`
/// gate would never fire — the structural shape is the whole witness.
fn rhs_returns_church_false(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Trace { value, .. } = expr else {
        return false;
    };
    peel_to_church_false(value)
}

fn peel_to_church_false(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Trace { value, .. } => pending.push(value),
            PseudoExpr::Constr { tag: 1, fields, .. } => return fields.is_empty(),
            _ => return false,
        }
    }
    false
}
