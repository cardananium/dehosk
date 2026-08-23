//! Shared structural witness: "this expression is provably a `Bool`".
//!
//! `None`/`False` share a nullary `Constr _ []` encoding, so a church
//! decoder can confuse a Bool fall-through (`False`, tag 0) with an
//! `Option::None` (tag 1) — and vice-versa. Proving the surrounding value
//! is a boolean expression breaks the tie: its `False` leaves are then
//! genuine `False`, never mis-decoded `None`.
//!
//! The witness is a *definite* Bool tail leaf — a comparison/logical
//! `BinOp` (`==`/`<`/`&&`/`||`/…), `UnOp::Not`, or the `Bool(true)`
//! literal — in a tail/result position. An `Option`-typed value can never
//! carry such a leaf in tail position (its tails are `None`,
//! `Some(payload)`, or an opaque call/var returning `Option`), so the
//! witness cannot misfire on a genuine `Option`.
//!
//! [`has_definite_bool_tail_leaf`] deliberately does not count
//! `Bool(false)`: it is the value the `False`/`None` ambiguity is about,
//! so counting it would make every candidate self-classify.

use crate::pseudo::ast::{BinaryOp, PseudoExpr, UnaryOp};

/// True when any tail/result leaf of `expr` is a *definitely* boolean
/// expression (comparison/logical `BinOp`, `UnOp::Not`, or `Bool(true)`).
///
/// Recurses only through tail positions: `if` branches, `when` clause
/// bodies, `let` bodies, and `trace` values. Conditions, guards,
/// operands, constructor fields, call arguments, and trace messages are
/// NOT tail positions and are not inspected.
///
/// This is an EXISTENCE (`any`) witness — "at least one tail is Bool". It
/// is the right tool for a VETO ("if there is any Bool evidence, do not
/// treat a `Bool(false)` as `None`"), NOT for a positive assertion that
/// the whole value is Bool — use [`is_provably_bool`] for that.
pub(super) fn has_definite_bool_tail_leaf(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
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
            PseudoExpr::Bool(true) => return true,
            PseudoExpr::BinOp { op, .. } if is_bool_binop(op) => return true,
            PseudoExpr::UnOp {
                op: UnaryOp::Not, ..
            } => return true,
            _ => {}
        }
    }
    false
}

/// True when `expr` is provably a `Bool` on EVERY path: every tail/result
/// leaf is a definite boolean expression (comparison/logical `BinOp`,
/// `UnOp::Not`, `Bool(true)`, or `Bool(false)`) or a divergent `fail`
/// (`Error`, which is bottom and produces no non-Bool value), and at least
/// one leaf is an actual Bool (so an all-`fail` value does not qualify).
///
/// Unlike [`has_definite_bool_tail_leaf`] this is a UNIVERSAL (`all`)
/// witness: it rejects a mixed producer such as
/// `if c { a == b } else { SomeCtor() }` whose value is Bool on one path
/// but a constructor on another. Required before asserting a value is Bool
/// (e.g. to rewrite an `Option`-named `when` over it into an `if`).
pub(super) fn is_provably_bool(expr: &PseudoExpr) -> bool {
    let mut saw_bool = false;
    all_tails_bool(expr, &mut saw_bool) && saw_bool
}

fn all_tails_bool(expr: &PseudoExpr, saw_bool: &mut bool) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    let mut all_true = true;
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
            // `fail` is bottom — it diverges and yields no non-Bool value, so a
            // tail of `fail` does not contradict Bool-ness.
            PseudoExpr::Error { .. } => {}
            PseudoExpr::Bool(_) => *saw_bool = true,
            PseudoExpr::BinOp { op, .. } if is_bool_binop(op) => *saw_bool = true,
            PseudoExpr::UnOp {
                op: UnaryOp::Not, ..
            } => *saw_bool = true,
            // Anything else (a constructor, var, call, …) is not provably Bool.
            _ => all_true = false,
        }
    }
    all_true
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
