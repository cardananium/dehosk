//! Structural questions about a body, asked by the naming decisions.
//!
//! Does it call this builtin, on this variable? Use this variable as a
//! `when` subject, project a field off it, compare it? Each probe has a
//! `clause_*` companion so a `when` arm can be asked the same question.
//!
//! Pure reads — nothing here rewrites.

use super::*;

/// Check if body contains a specific builtin call.
pub(super) fn body_contains_builtin_call(expr: &PseudoExpr, target: &str) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::BuiltinCall { name, .. } => {
                if name == target {
                    return true;
                }
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args.iter());
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                pending.extend(clauses.iter().map(|c| &c.body));
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
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::Constr { fields, .. } => {
                pending.extend(fields.iter());
            }
            _ => {}
        }
    }
    false
}

/// Whether `expr` EVALUATES TO one of `targets` — the call is in tail
/// position, through a `let` chain, not merely somewhere inside.
///
/// `extract_int` is a claim about the return value. Scanning the whole
/// body instead makes any `un_i_data` in a nested lambda rename a
/// function that returns something else entirely.
pub(super) fn returns_builtin_call(expr: &PseudoExpr, targets: &[&str]) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        let tail = unwrap_lets(current);
        match tail {
            PseudoExpr::BuiltinCall { name, .. } => {
                if !targets.iter().any(|t| name == t) {
                    return false;
                }
            }
            // `f(x)` where `f` is the builtin — the flattened apply form.
            PseudoExpr::Apply { function, .. } => pending.push(function),
            // Wrappers that do not change what the branch evaluates to.
            PseudoExpr::Trace { value, .. } => pending.push(value),
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => pending.push(inner),
            // A conditional still RETURNS the extraction when every arm
            // does. Failing arms are the exhaustiveness tail, not a result.
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::When { clauses, .. } => {
                let mut live = clauses.iter().filter(|c| !is_fail_body(&c.body)).peekable();
                if live.peek().is_none() {
                    return false;
                }
                pending.extend(live.map(|c| &c.body));
            }
            _ => return false,
        }
    }
    true
}

pub(super) fn body_contains_any_builtin_call(expr: &PseudoExpr, targets: &[&str]) -> bool {
    targets
        .iter()
        .any(|target| body_contains_builtin_call(expr, target))
}

pub(super) fn clause_contains_builtin_call_on_var(
    clause: &WhenClause,
    targets: &[&str],
    var_name: &str,
    var_id: Option<VarId>,
) -> bool {
    clause
        .guard
        .as_ref()
        .is_some_and(|guard| expr_contains_builtin_call_on_var(guard, targets, var_name, var_id))
        || expr_contains_builtin_call_on_var(&clause.body, targets, var_name, var_id)
}

pub(super) fn expr_contains_builtin_call_on_var(
    expr: &PseudoExpr,
    targets: &[&str],
    var_name: &str,
    var_id: Option<VarId>,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::BuiltinCall { name, args } => {
                let matches_target = targets.iter().any(|target| *name == *target);
                if matches_target
                    && args
                        .iter()
                        .any(|arg| expr_matches_named_var_identity(arg, var_name, var_id))
                {
                    return true;
                }
                pending.extend(args.iter());
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args.iter());
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
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for clause in clauses {
                    if let Some(guard) = clause.guard.as_ref() {
                        pending.push(guard);
                    }
                    pending.push(&clause.body);
                }
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(tail) = tail.as_ref() {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(elements) => pending.extend(elements.iter()),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            _ => {}
        }
    }
    false
}

pub(super) fn clause_uses_var_as_when_subject(
    clause: &WhenClause,
    var_name: &str,
    var_id: Option<VarId>,
) -> bool {
    clause
        .guard
        .as_ref()
        .is_some_and(|guard| expr_uses_var_as_when_subject(guard, var_name, var_id))
        || expr_uses_var_as_when_subject(&clause.body, var_name, var_id)
}

pub(super) fn expr_uses_var_as_when_subject(
    expr: &PseudoExpr,
    var_name: &str,
    var_id: Option<VarId>,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                if expr_matches_named_var_identity(subject.as_ref(), var_name, var_id) {
                    return true;
                }
                pending.push(subject);
                for clause in clauses {
                    if let Some(guard) = clause.guard.as_ref() {
                        pending.push(guard);
                    }
                    pending.push(&clause.body);
                }
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args.iter());
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
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(tail) = tail.as_ref() {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(elements) => pending.extend(elements.iter()),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
            _ => {}
        }
    }
    false
}

pub(super) fn clause_contains_var_field_access(
    clause: &WhenClause,
    var_name: &str,
    var_id: Option<VarId>,
) -> bool {
    clause
        .guard
        .as_ref()
        .is_some_and(|guard| expr_contains_var_field_access(guard, var_name, var_id))
        || expr_contains_var_field_access(&clause.body, var_name, var_id)
}

pub(super) fn expr_contains_var_field_access(
    expr: &PseudoExpr,
    var_name: &str,
    var_id: Option<VarId>,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::FieldAccess { record, .. } => {
                if expr_matches_named_var_identity(record.as_ref(), var_name, var_id) {
                    return true;
                }
                pending.push(record);
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                if expr_matches_named_var_identity(collection.as_ref(), var_name, var_id) {
                    return true;
                }
                pending.push(collection);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args.iter());
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
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for clause in clauses {
                    if let Some(guard) = clause.guard.as_ref() {
                        pending.push(guard);
                    }
                    pending.push(&clause.body);
                }
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(tail) = tail.as_ref() {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(elements) => pending.extend(elements.iter()),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
            _ => {}
        }
    }
    false
}

pub(super) fn clause_contains_var_comparison(
    clause: &WhenClause,
    var_name: &str,
    var_id: Option<VarId>,
) -> bool {
    clause
        .guard
        .as_ref()
        .is_some_and(|guard| expr_contains_var_comparison(guard, var_name, var_id))
        || expr_contains_var_comparison(&clause.body, var_name, var_id)
}

pub(super) fn expr_contains_var_comparison(
    expr: &PseudoExpr,
    var_name: &str,
    var_id: Option<VarId>,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::BinOp { op, left, right } => {
                if matches!(
                    op,
                    BinaryOp::Eq
                        | BinaryOp::Neq
                        | BinaryOp::Lt
                        | BinaryOp::Lte
                        | BinaryOp::Gt
                        | BinaryOp::Gte
                ) && (expr_matches_named_var_identity(left.as_ref(), var_name, var_id)
                    || expr_matches_named_var_identity(right.as_ref(), var_name, var_id))
                {
                    return true;
                }
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args.iter());
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
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for clause in clauses {
                    if let Some(guard) = clause.guard.as_ref() {
                        pending.push(guard);
                    }
                    pending.push(&clause.body);
                }
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(tail) = tail.as_ref() {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(elements) => pending.extend(elements.iter()),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
            _ => {}
        }
    }
    false
}

/// Check if body contains a specific builtin (by underlying name).
pub(super) fn body_contains_builtin(expr: &PseudoExpr, target: &str) -> bool {
    body_contains_builtin_call(expr, target)
}

/// Always false — `Var`/`Let` carry no inline type annotation to
/// probe. Kept as a stub for callers.
pub(super) fn body_references_type(_expr: &PseudoExpr, _type_str: &str) -> bool {
    false
}

/// Unwrap nested let bindings to get to the inner expression.
pub(super) fn unwrap_lets(expr: &PseudoExpr) -> &PseudoExpr {
    let mut current = expr;
    while let PseudoExpr::Let { body, .. } = current {
        current = body;
    }
    current
}

/// Check if when branches contain Data.to_bytes calls.
pub(super) fn has_data_to_bytes_in_branches(clauses: &[WhenClause]) -> bool {
    clauses
        .iter()
        .any(|c| body_contains_any_builtin_call(&c.body, DATA_BYTES_EXTRACTORS))
}

/// Check if when branches contain Data.to_int calls.
pub(super) fn has_data_to_int_in_branches(clauses: &[WhenClause]) -> bool {
    clauses
        .iter()
        .any(|c| body_contains_any_builtin_call(&c.body, DATA_INT_EXTRACTORS))
}

/// Check if when branches access pair fields (.fst, .snd).
/// Separates the Int pair-decoder shape from plain list recursion.
pub(super) fn has_pair_access_in_branches(clauses: &[WhenClause]) -> bool {
    clauses
        .iter()
        .any(|c| body_contains_pair_field_access(&c.body))
}

/// Check if when branches contain field extraction (Data.to_* calls).
pub(super) fn has_field_extraction_in_branches(clauses: &[WhenClause]) -> bool {
    clauses.iter().any(|c| {
        body_contains_any_builtin_call(&c.body, DATA_BYTES_EXTRACTORS)
            || body_contains_any_builtin_call(&c.body, DATA_INT_EXTRACTORS)
            || body_contains_any_builtin_call(&c.body, DATA_LIST_EXTRACTORS)
            || body_contains_any_builtin_call(&c.body, DATA_MAP_EXTRACTORS)
    })
}

/// Check if any branch is a wildcard or fail (expect-style pattern).
pub(super) fn has_wildcard_fail_branch(clauses: &[WhenClause]) -> bool {
    clauses
        .iter()
        .any(|c| matches!(&c.pattern, WhenPattern::Wildcard) || is_fail_body(&c.body))
}

/// Check if a body is a fail/error expression.
pub(super) fn is_fail_body(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Error { .. } => return true,
            PseudoExpr::Trace { value, .. } => pending.push(value),
            _ => {}
        }
    }
    false
}

/// Check if a body contains pair construction (Lambda returning applied pair).
pub(super) fn is_pair_construction_in_body(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Let { body, .. } => pending.push(body),
            PseudoExpr::Lambda { body, params } => {
                // fn(x) { x(a, b) } is a CPS pair
                if params.len() == 1
                    && let PseudoExpr::Apply { function, args } = body.as_ref()
                    && matches!(function.as_ref(), PseudoExpr::Var { .. })
                    && args.len() == 2
                {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Check if any clause has a Constr<0> pattern.
pub(super) fn has_constr0_pattern(clauses: &[WhenClause]) -> bool {
    clauses
        .iter()
        .any(|c| matches!(&c.pattern, WhenPattern::Constructor { tag: 0, .. }))
}

/// Check if expression constructs a pair (Lambda returning pair-like structure).
pub(super) fn is_pair_construction(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Lambda { body, .. } => {
                // fn(x) { x(a, b) } is a pair construction pattern
                if let PseudoExpr::Apply { function, args } = body.as_ref()
                    && matches!(function.as_ref(), PseudoExpr::Var { .. })
                    && args.len() == 2
                {
                    return true;
                }
            }
            PseudoExpr::Let { body, .. } => pending.push(body),
            _ => {}
        }
    }
    false
}
