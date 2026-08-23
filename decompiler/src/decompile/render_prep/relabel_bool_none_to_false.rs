//! Re-label an `Option::None` value leaf that is actually `Bool(false)`.
//!
//! Exact mirror of [`super::fix_option_false_to_none`]: that pass rewrites a
//! mis-decoded `Bool(false)` back to `None`; this one rewrites a mis-decoded
//! `None` back to `False`. Both break the `None`/`False` nullary tie from
//! opposite directions, each gated by a non-circular witness that its direction is correct.
//!
//! A blind `None -> False` is polarity-unsafe: under CIP,
//! `None = Constr<1> = True`, so the relabel would invert. Both facts
//! are required. (1) Polarity is `InverseCip` (`church_true =
//! Constr<0>`, so `Constr<1> = church_false = False`); under CIP this
//! is a no-op. The leaf maps to `False` only because the program is
//! proven inverse-CIP (the sibling `ifThenElse(constr0, constr1)`
//! collapse pins it) — never as a blanket `None = False`. Those UPLC
//! leaves are `(constr 1)` of `ifThenElse(equalsByteString, (constr
//! 0), (constr 1))`. (2) The leaf sits in a Bool-consuming position —
//! a tail/result of an `&&`/`||` operand or an `if` condition (Bool
//! by typing and by the church-`&&`/`ifThenElse` they lower from).
//! The operand must be `Bool`-or-`None` on every tail with at least
//! one definite Bool tail (comparison/logical `BinOp`, `!`, or `Bool`
//! literal), so a genuine `Option`-returning operand never qualifies.
//!
//! Never touched: `Some`/`None` patterns (value leaves only, never a
//! `WhenPattern`); genuine `Option::None` outside a Bool-consuming position
//! (`if cond { None } else …` — the `if` is not a Bool operand and sibling
//! tails are `None`/`Some`); everything under `ChurchPolarity::Cip`. `Constr<1>`
//! is the same datum either way; only the type label is corrected under a proven
//! Bool context.

use crate::decompile::church_polarity::ChurchPolarity;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr, UnaryOp, WhenClause};
use crate::pseudo::constructor::KnownConstructor;

use super::ctx::RenderCtx;
use super::scope_recurse::rewrite_bottom_up;

pub(super) fn relabel_bool_none_to_false(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    // Gate (1): only inverse-CIP programs map `None`(`Constr<1>`) → `False`.
    // Under CIP `Constr<1> = True`, so the pass is a complete no-op.
    if ctx.church_polarity() != ChurchPolarity::InverseCip {
        return expr;
    }
    rewrite(expr)
}

fn rewrite(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_relabel)
}

fn try_relabel(expr: PseudoExpr) -> PseudoExpr {
    match expr {
        // Gate (2a): `&&`/`||` operands are Bool by the language's own typing
        // (and by the church-`&&`/`||` UPLC they lower from), so their `None`
        // tail leaves are mis-decoded Bools.
        PseudoExpr::BinOp {
            op: BinaryOp::And,
            left,
            right,
        } => PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(relabel_if_bool_operand(left.into_inner())),
            right: PBox::new(relabel_if_bool_operand(right.into_inner())),
        },
        PseudoExpr::BinOp {
            op: BinaryOp::Or,
            left,
            right,
        } => PseudoExpr::BinOp {
            op: BinaryOp::Or,
            left: PBox::new(relabel_if_bool_operand(left.into_inner())),
            right: PBox::new(relabel_if_bool_operand(right.into_inner())),
        },
        // Gate (2b): an `if` condition is Bool. Its branches are not, so
        // they stay untouched and genuine `if cond { None }` Options survive.
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => PseudoExpr::If {
            condition: PBox::new(relabel_if_bool_operand(condition.into_inner())),
            then_branch,
            else_branch,
        },
        other => other,
    }
}

/// Relabel `None` tail leaves → `False` in `operand`, but ONLY when
/// `operand` is `Bool`-or-`None` on every tail and has at least one
/// definite-Bool tail leaf; otherwise it is returned unchanged.
fn relabel_if_bool_operand(operand: PseudoExpr) -> PseudoExpr {
    if bool_or_none_operand(&operand) {
        rewrite_tail_none_to_false(operand)
    } else {
        operand
    }
}

/// True when every tail/result leaf of `expr` is a definite `Bool`
/// (comparison/logical `BinOp`, `!`, or `Bool` literal), a divergent
/// `fail`, or a nullary `None`/`Bool(false)` candidate — AND at least one
/// tail is a definite `Bool`. That last requirement excludes a genuine
/// `Option`, whose tails are `Some(payload)`, opaque calls, or `None`.
fn bool_or_none_operand(expr: &PseudoExpr) -> bool {
    let mut saw_definite_bool = false;
    all_tails_bool_or_none(expr, &mut saw_definite_bool) && saw_definite_bool
}

fn all_tails_bool_or_none(expr: &PseudoExpr, saw_bool: &mut bool) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    let mut all_ok = true;
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::When { clauses, .. } => {
                pending.extend(clauses.iter().map(|c| &c.body));
            }
            PseudoExpr::Let { body, .. } => pending.push(body),
            PseudoExpr::Trace { value, .. } => pending.push(value),
            // `fail` diverges, so it cannot contradict Bool-ness.
            PseudoExpr::Error { .. } => {}
            // A definite Bool leaf — the witness that this is a Bool, not Option.
            PseudoExpr::Bool(_) => *saw_bool = true,
            PseudoExpr::BinOp { op, .. } if is_bool_binop(op) => *saw_bool = true,
            PseudoExpr::UnOp {
                op: UnaryOp::Not, ..
            } => *saw_bool = true,
            // A nullary `None` leaf — a relabel candidate, not a definite-Bool
            // witness (that is the ambiguity), so all-`None` never qualifies.
            _ if is_nullary_none(current) => {}
            // Anything else (a `Some(payload)`, a non-Option constructor, an
            // opaque call/var, …) is not a Bool-or-None tail.
            _ => all_ok = false,
        }
    }
    all_ok
}

/// Rewrite nullary `None` leaves → `Bool(false)` in the tail/result
/// positions of `expr` only — recursing through `if`/`when`/`let`/`trace`
/// tails, never into conditions, operands, sub-values, or patterns.
fn rewrite_tail_none_to_false(expr: PseudoExpr) -> PseudoExpr {
    enum Frame {
        If {
            condition: PBox,
        },
        When {
            subject: PBox,
            subject_name: Option<crate::pseudo::ast::Binder>,
            pattern_guards: Vec<(crate::pseudo::ast::WhenPattern, Option<PseudoExpr>)>,
        },
        Let {
            name: String,
            id: Option<crate::pseudo::var_id::VarId>,
            value: PBox,
        },
        Trace {
            message: PBox,
        },
    }

    enum Step {
        Enter(PseudoExpr),
        Post(Frame),
    }

    let mut steps = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(e) if is_nullary_none(&e) => {
                done.push(PseudoExpr::Bool(false));
            }
            Step::Enter(PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            }) => {
                steps.push(Step::Post(Frame::If { condition }));
                steps.push(Step::Enter(else_branch.into_inner()));
                steps.push(Step::Enter(then_branch.into_inner()));
            }
            Step::Enter(PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            }) => {
                let mut pattern_guards = Vec::with_capacity(clauses.len());
                let mut bodies = Vec::with_capacity(clauses.len());
                for c in clauses {
                    pattern_guards.push((c.pattern, c.guard));
                    bodies.push(c.body);
                }
                steps.push(Step::Post(Frame::When {
                    subject,
                    subject_name,
                    pattern_guards,
                }));
                for body in bodies.into_iter().rev() {
                    steps.push(Step::Enter(body));
                }
            }
            Step::Enter(PseudoExpr::Let {
                name,
                id,
                value,
                body,
            }) => {
                steps.push(Step::Post(Frame::Let { name, id, value }));
                steps.push(Step::Enter(body.into_inner()));
            }
            Step::Enter(PseudoExpr::Trace { message, value }) => {
                steps.push(Step::Post(Frame::Trace { message }));
                steps.push(Step::Enter(value.into_inner()));
            }
            Step::Enter(other) => done.push(other),

            Step::Post(Frame::If { condition }) => {
                let else_branch = done.pop().expect("rewrite_tail_none_to_false: if else");
                let then_branch = done.pop().expect("rewrite_tail_none_to_false: if then");
                done.push(PseudoExpr::If {
                    condition,
                    then_branch: PBox::new(then_branch),
                    else_branch: PBox::new(else_branch),
                });
            }
            Step::Post(Frame::When {
                subject,
                subject_name,
                pattern_guards,
            }) => {
                let at = done.len() - pattern_guards.len();
                let bodies = done.split_off(at);
                let clauses = pattern_guards
                    .into_iter()
                    .zip(bodies)
                    .map(|((pattern, guard), body)| WhenClause {
                        pattern,
                        guard,
                        body,
                    })
                    .collect();
                done.push(PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                });
            }
            Step::Post(Frame::Let { name, id, value }) => {
                let body = done.pop().expect("rewrite_tail_none_to_false: let body");
                done.push(PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body: PBox::new(body),
                });
            }
            Step::Post(Frame::Trace { message }) => {
                let value = done.pop().expect("rewrite_tail_none_to_false: trace value");
                done.push(PseudoExpr::Trace {
                    message,
                    value: PBox::new(value),
                });
            }
        }
    }

    done.pop()
        .expect("rewrite_tail_none_to_false: machine must leave one result")
}

/// A nullary `Option::None` value leaf (`Constr<1> []`, printed `None`).
fn is_nullary_none(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Constr { shape, fields, .. }
            if fields.is_empty()
                && matches!(shape.as_known(), Some(KnownConstructor::None))
    )
}

fn is_bool_binop(op: &BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::Eq
            | BinaryOp::Neq
            | BinaryOp::Lt
            | BinaryOp::Lte
            | BinaryOp::Gt
            | BinaryOp::Gte
            | BinaryOp::And
            | BinaryOp::Or
    )
}

#[cfg(test)]
mod tests;
