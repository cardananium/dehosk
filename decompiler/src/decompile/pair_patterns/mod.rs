use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
#[cfg(test)]
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::constructor::KnownConstructor;

#[cfg(test)]
pub(crate) fn is_pair_pattern(pattern: &WhenPattern) -> bool {
    pair_pattern_binders(pattern).is_some()
}

#[cfg(test)]
pub(crate) fn pair_pattern_binders(pattern: &WhenPattern) -> Option<(String, String)> {
    pair_pattern_binders_with_ids(pattern)
        .map(|(first, second)| (first.to_string(), second.to_string()))
}

pub(crate) fn pair_pattern_binders_with_ids(pattern: &WhenPattern) -> Option<(Binder, Binder)> {
    match pattern {
        WhenPattern::Pair(first, second) => Some((first.clone(), second.clone())),
        WhenPattern::Constructor { shape, fields, .. }
            if shape.as_known() == Some(KnownConstructor::Pair) =>
        {
            Some((fields[0].clone(), fields[1].clone()))
        }
        _ => None,
    }
}

#[cfg(test)]
pub(crate) fn is_pair_field_access_of_var(
    expr: &PseudoExpr,
    record_name: &str,
    field_name: &str,
) -> bool {
    matches!(
        expr,
        PseudoExpr::FieldAccess { record, selector, .. }
            if selector.as_pretty_name() == field_name
                && matches!(record.as_ref(), PseudoExpr::Var { name, .. } if name == record_name)
    )
}

#[cfg(test)]
pub(crate) fn is_pair_field_payload_of_var(
    expr: &PseudoExpr,
    record_name: &str,
    field_name: &str,
) -> bool {
    is_pair_field_access_of_var(expr, record_name, field_name)
        || matches!(
            expr,
            PseudoExpr::Constr { tag: 0, fields, .. }
                if fields.len() == 1
                    && is_pair_field_access_of_var(&fields[0], record_name, field_name)
        )
}

pub(crate) fn body_contains_pair_field_access(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::FieldAccess {
                selector, record, ..
            } => {
                if selector.is_pair_fst() || selector.is_pair_snd() {
                    return true;
                }
                pending.push(record);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Apply { function, args } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
                }
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
                for clause in clauses.iter().rev() {
                    pending.push(&clause.body);
                    if let Some(guard) = &clause.guard {
                        pending.push(guard);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::Pair(left, right) | PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::IndexAccess {
                collection: operand,
                ..
            }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => pending.push(operand),
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
                }
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(tail) = tail {
                    pending.push(tail);
                }
                for element in elements.iter().rev() {
                    pending.push(element);
                }
            }
            PseudoExpr::Tuple(elements) => {
                for element in elements.iter().rev() {
                    pending.push(element);
                }
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields.iter().rev() {
                    pending.push(field);
                }
            }
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
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
