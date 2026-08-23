use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

fn is_subject_field0_access(expr: &PseudoExpr, subject_id: VarId) -> bool {
    matches!(
        expr,
        PseudoExpr::IndexAccess {
            collection,
            index: 0,
        } if matches!(
            collection.as_ref(),
            PseudoExpr::FieldAccess { record, selector, .. }
                if selector.as_pretty_name() == "fields"
                    && matches!(record.as_ref(), PseudoExpr::Var { id, .. } if *id == Some(subject_id))
        )
    )
}

/// A pure existential `||` fold: the first qualifying node answers `true`.
/// Children are pushed in REVERSE so they pop in source order.
pub(in crate::decompile::late::normalize) fn contains_subject_field0_access(
    expr: &PseudoExpr,
    subject_id: VarId,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];

    while let Some(expr) = pending.pop() {
        match expr {
            PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::String(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::Data(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. } => {}
            _ if is_subject_field0_access(expr, subject_id) => return true,
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for clause in clauses.iter().rev() {
                    pending.push(&clause.body);
                    if let Some(guard) = &clause.guard {
                        pending.push(guard);
                    }
                }
                pending.push(subject);
            }
            _ => {
                for child in expr.provenance_children().into_iter().rev() {
                    pending.push(child);
                }
            }
        }
    }

    false
}

/// Only the `let` BODY is ever descended into, so the peeled outer `let`
/// shells are stacked on the way down and rewrapped around the stripped body
/// on the way out, innermost first. A `None` answer consumes the input tree.
pub(in crate::decompile::late::normalize) fn extract_subject_field0_binder(
    body: PseudoExpr,
    subject_id: VarId,
) -> Option<(Binder, PseudoExpr)> {
    // The `let` shells peeled off above the match, outermost first.
    let mut peeled: Vec<(String, Option<VarId>, PBox)> = Vec::new();
    let mut current = body;

    loop {
        match current {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                if is_subject_field0_access(value.as_ref(), subject_id) {
                    let binder_id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
                    let mut stripped_body = body.into_inner();
                    // Rewrap innermost-first.
                    while let Some((name, id, value)) = peeled.pop() {
                        stripped_body = PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body: PBox::new(stripped_body),
                        };
                    }
                    return Some((Binder::new(name, binder_id), stripped_body));
                }

                peeled.push((name, id, value));
                current = body.into_inner();
            }
            _ => return None,
        }
    }
}
