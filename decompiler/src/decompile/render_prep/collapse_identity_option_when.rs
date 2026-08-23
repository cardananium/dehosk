//! Collapse an identity `Option` re-match:
//!   `when X is { Some(p) -> Some(p)   None -> None }`  →  `X`
//! and the constant both-`None` fold:
//!   `when X is { Some(_) -> None      None -> None }`  →  `None`
//!
//! The first reconstructs `X` arm-for-arm, so the `when` is the identity on an
//! `Option` and equals `X` (the scrutinee is evaluated once either way). The
//! second always yields `None`, and folds only over a pure subject. A trailing
//! wildcard arm is tolerated (Some/None is exhaustive). Gated by VarId: the
//! Some body must rebuild `Some(<the arm's own payload binder>)`, never a
//! projection or a different variable.

use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

use super::purity::is_pure_value;
use super::scope_recurse::rewrite_bottom_up;

pub(super) fn collapse_identity_option_when(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_collapse_node)
}

fn try_collapse_node(expr: PseudoExpr) -> PseudoExpr {
    match expr {
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => match try_collapse(&subject, &clauses) {
            Some(replacement) => replacement,
            None => PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            },
        },
        other => other,
    }
}

fn try_collapse(subject: &PseudoExpr, clauses: &[WhenClause]) -> Option<PseudoExpr> {
    let mut some_arm: Option<(&[crate::pseudo::ast::Binder], &PseudoExpr)> = None;
    let mut none_body: Option<&PseudoExpr> = None;
    for (i, c) in clauses.iter().enumerate() {
        if c.guard.is_some() {
            return None;
        }
        match &c.pattern {
            WhenPattern::Constructor {
                shape: ConstructorShape::Known(KnownConstructor::Some),
                fields,
                ..
            } => {
                if some_arm.is_some() {
                    return None; // duplicate Some arm — first-match semantics, bail
                }
                some_arm = Some((fields, &c.body));
            }
            WhenPattern::Constructor {
                shape: ConstructorShape::Known(KnownConstructor::None),
                ..
            } => {
                if none_body.is_some() {
                    return None;
                }
                none_body = Some(&c.body);
            }
            // A wildcard is tolerated ONLY as the final clause: Some/None is
            // exhaustive so a trailing `_` is dead, but a leading one would
            // shadow the Some/None arms (first-match), breaking it.
            WhenPattern::Wildcard if i + 1 == clauses.len() => {}
            _ => return None,
        }
    }
    let (some_fields, some_body) = some_arm?;
    let none_body = none_body?;

    if !is_none_ctor(none_body) {
        return None;
    }
    // Identity: `Some(p) -> Some(p)` (same VarId) ⇒ the whole `when` is `X`.
    // X is returned, so its single evaluation is preserved.
    if some_fields.len() == 1 && is_some_of_var(some_body, some_fields[0].id) {
        return Some(subject.clone());
    }
    // Both arms yield `None` ⇒ the result is constant `None` — but this DISCARDS
    // X, so only fold when X is a pure value (the `when` would otherwise still
    // evaluate/inspect it; e.g. a Trace/Error/failing builtin must be kept).
    if is_none_ctor(some_body) && is_pure_value(subject) {
        return Some(none_body.clone());
    }
    None
}

fn is_none_ctor(e: &PseudoExpr) -> bool {
    matches!(
        e,
        PseudoExpr::Constr {
            shape: ConstructorShape::Known(KnownConstructor::None),
            ..
        }
    )
}

fn is_some_of_var(e: &PseudoExpr, id: VarId) -> bool {
    matches!(
        e,
        PseudoExpr::Constr {
            shape: ConstructorShape::Known(KnownConstructor::Some),
            fields,
            ..
        } if fields.len() == 1
            && matches!(&fields[0], PseudoExpr::Var { id: Some(v), .. } if *v == id)
    )
}

#[cfg(test)]
mod tests;
