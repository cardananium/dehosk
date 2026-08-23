use crate::pseudo::ast::{PseudoExpr, WhenPattern};

pub(super) fn expr_binds_name(expr: &PseudoExpr, target: &str) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Lambda { params, body } => {
                if params.iter().any(|param| param == target) {
                    return true;
                }
                pending.push(body);
            }
            PseudoExpr::RecFn { name, params, body } => {
                if name == target || params.iter().any(|param| param == target) {
                    return true;
                }
                pending.push(body);
            }
            PseudoExpr::Let {
                name, value, body, ..
            } => {
                if name == target {
                    return true;
                }
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                if subject_name
                    .as_ref()
                    .is_some_and(|subject_name| subject_name == target)
                {
                    return true;
                }
                pending.push(subject);
                for clause in clauses {
                    if pattern_binds_name(&clause.pattern, target) {
                        return true;
                    }
                    if let Some(guard) = clause.guard.as_ref() {
                        pending.push(guard);
                    }
                    pending.push(&clause.body);
                }
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => pending.push(operand),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements);
                if let Some(tail) = tail.as_ref() {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items),
            PseudoExpr::Constr { fields, .. } => pending.extend(fields),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args),
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
    false
}

fn pattern_binds_name(pattern: &WhenPattern, target: &str) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields.iter().any(|field| field == target),
        WhenPattern::List { elements, tail } => {
            elements.iter().any(|element| element == target)
                || tail.as_ref().is_some_and(|tail| tail == target)
        }
        WhenPattern::Tuple(fields) => fields.iter().any(|field| field == target),
        WhenPattern::Pair(a, b) => a == target || b == target,
        WhenPattern::Var(var) => var == target,
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}
