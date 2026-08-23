use std::collections::HashSet;

use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::var_id::VarId;

pub(super) fn fresh_reserved_display_name(
    base: &str,
    id: VarId,
    reserved_display_names: &mut HashSet<String>,
) -> String {
    let mut candidate = format!("{base}_{}", id.as_u32());
    if reserved_display_names.insert(candidate.clone()) {
        return candidate;
    }

    let mut suffix = 2usize;
    loop {
        candidate = format!("{base}_{}_{}", id.as_u32(), suffix);
        if reserved_display_names.insert(candidate.clone()) {
            return candidate;
        }
        suffix += 1;
    }
}

enum Item<'a> {
    Expr(&'a PseudoExpr),
    Pattern(&'a WhenPattern),
    Name(&'a str),
}

pub(super) fn collect_display_names(expr: &PseudoExpr, names: &mut HashSet<String>) {
    let mut pending = vec![Item::Expr(expr)];
    while let Some(item) = pending.pop() {
        match item {
            Item::Expr(expr) => match expr {
                PseudoExpr::Var { name, .. } => {
                    names.insert(name.clone());
                }
                PseudoExpr::Let {
                    name, value, body, ..
                } => {
                    names.insert(name.clone());
                    pending.push(Item::Expr(body));
                    pending.push(Item::Expr(value));
                }
                PseudoExpr::Lambda { params, body } => {
                    for param in params {
                        names.insert(param.to_string());
                    }
                    pending.push(Item::Expr(body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    names.insert(name.to_string());
                    for param in params {
                        names.insert(param.to_string());
                    }
                    pending.push(Item::Expr(body));
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        pending.push(Item::Expr(arg));
                    }
                    pending.push(Item::Expr(function));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(Item::Expr(else_branch));
                    pending.push(Item::Expr(then_branch));
                    pending.push(Item::Expr(condition));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    for clause in clauses.iter().rev() {
                        pending.push(Item::Expr(&clause.body));
                        if let Some(guard) = &clause.guard {
                            pending.push(Item::Expr(guard));
                        }
                        pending.push(Item::Pattern(&clause.pattern));
                    }
                    if let Some(subject_name) = subject_name {
                        pending.push(Item::Name(subject_name.as_str()));
                    }
                    pending.push(Item::Expr(subject));
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(Item::Expr(right));
                    pending.push(Item::Expr(left));
                }
                PseudoExpr::UnOp { operand, .. }
                | PseudoExpr::Delay(operand)
                | PseudoExpr::Force(operand) => pending.push(Item::Expr(operand)),
                PseudoExpr::Trace { message, value } => {
                    pending.push(Item::Expr(value));
                    pending.push(Item::Expr(message));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        pending.push(Item::Expr(tail));
                    }
                    for element in elements.iter().rev() {
                        pending.push(Item::Expr(element));
                    }
                }
                PseudoExpr::Tuple(elements) => {
                    for element in elements.iter().rev() {
                        pending.push(Item::Expr(element));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    pending.push(Item::Expr(b));
                    pending.push(Item::Expr(a));
                }
                PseudoExpr::Constr { fields, .. } => {
                    for field in fields.iter().rev() {
                        pending.push(Item::Expr(field));
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => pending.push(Item::Expr(record)),
                PseudoExpr::IndexAccess { collection, .. } => pending.push(Item::Expr(collection)),
                PseudoExpr::BuiltinCall { args, .. } => {
                    for arg in args.iter().rev() {
                        pending.push(Item::Expr(arg));
                    }
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
            },
            Item::Pattern(pattern) => match pattern {
                WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                    for field in fields {
                        names.insert(field.to_string());
                    }
                }
                WhenPattern::List { elements, tail } => {
                    for element in elements {
                        names.insert(element.to_string());
                    }
                    if let Some(tail) = tail {
                        names.insert(tail.to_string());
                    }
                }
                WhenPattern::Pair(a, b) => {
                    names.insert(a.to_string());
                    names.insert(b.to_string());
                }
                WhenPattern::Var(v) => {
                    names.insert(v.to_string());
                }
                WhenPattern::Literal(expr) => pending.push(Item::Expr(expr)),
                WhenPattern::Wildcard => {}
            },
            Item::Name(name) => {
                names.insert(name.to_string());
            }
        }
    }
}
