//! Single-parameter list recursion: indexing, accumulation, and the
//! tail-call witness the rest of the naming gates on.
//!
//! `contains_recursive_call_with_tail` is the workhorse — it proves that
//! a body's self-call is fed the list's own tail, which is what makes
//! the shape a traversal rather than an arbitrary recursion.

use super::*;

/// Detect 1-param list recursion patterns:
/// `rec fn f(list) { when list is { [] -> []; [h,..t] -> [transform(h), ..f(t)] } }` → "map"
/// `rec fn f(list) { when list is { [] -> 0; [h,..t] -> h + f(t) } }` → "sum"
/// `rec fn f(list) { when list is { [] -> []; [h,..t] -> if cond(h) { [h,..f(t)] } else { f(t) } } }` → "filter"
pub(super) fn analyze_single_param_list_rec(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<String> {
    let [list_param] = params else {
        return None;
    };

    let PseudoExpr::When {
        subject, clauses, ..
    } = body
    else {
        return None;
    };
    if !expr_matches_binder_identity(subject.as_ref(), list_param) || clauses.len() != 2 {
        return None;
    }

    // Find [] / Nil clause and [h,..t] / Cons(h, t) clause
    // Supports both surface list sugar and Plinth constructor patterns
    let is_nil_pattern = |pat: &WhenPattern| match pat {
        WhenPattern::List {
            elements,
            tail: None,
        } => elements.is_empty(),
        WhenPattern::Constructor { shape, fields, .. } => {
            fields.is_empty() && shape.as_known() == Some(KnownConstructor::Nil)
        }
        _ => false,
    };
    let _empty_clause = clauses.iter().find(|c| is_nil_pattern(&c.pattern))?;
    let cons_clause = clauses.iter().find_map(|c| match &c.pattern {
        WhenPattern::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => Some((&elements[0], tail, &c.body)),
        WhenPattern::Constructor { shape, fields, .. }
            if fields.len() == 2 && shape.as_known() == Some(KnownConstructor::Cons) =>
        {
            Some((&fields[0], &fields[1], &c.body))
        }
        _ => None,
    })?;

    let _head_name = cons_clause.0.as_str();
    let head_binder = cons_clause.0;
    let tail_binder = cons_clause.1;
    let cons_body = cons_clause.2;

    // Check for boolean accumulation: `pred(h) && f(t)` → "all", `pred(h) || f(t)` → "any_list"
    if let PseudoExpr::BinOp { op, left, right } = cons_body {
        let left_is_rec = is_simple_recursive_call(left, rec_name, rec_id, tail_binder);
        let right_is_rec = is_simple_recursive_call(right, rec_name, rec_id, tail_binder);
        if left_is_rec || right_is_rec {
            return Some(
                match op {
                    BinaryOp::And => "all",
                    BinaryOp::Or => "any_list",
                    BinaryOp::Add => {
                        // Distinguish count (adding 1) from sum (adding variable)
                        let non_rec = if left_is_rec { right } else { left };
                        if matches!(&**non_rec, PseudoExpr::Int(n) if *n == 1.into()) {
                            "count"
                        } else {
                            "sum"
                        }
                    }
                    _ => "fold",
                }
                .to_string(),
            );
        }
    }

    if let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = unwrap_lets(cons_body)
    {
        if matches!(_empty_clause.body, PseudoExpr::Bool(false))
            && matches!(then_branch.as_ref(), PseudoExpr::Bool(true))
            && is_simple_recursive_call(else_branch, rec_name, rec_id, tail_binder)
        {
            if is_direct_var_equality_predicate(condition, head_binder) {
                return Some("contains".to_string());
            }
            return Some("any".to_string());
        }

        if matches!(_empty_clause.body, PseudoExpr::Bool(true))
            && is_simple_recursive_call(then_branch, rec_name, rec_id, tail_binder)
            && matches!(else_branch.as_ref(), PseudoExpr::Bool(false))
        {
            return Some("all".to_string());
        }
    }

    if matches!(&_empty_clause.body, PseudoExpr::Int(n) if *n == 0.into())
        && is_recursive_count_if_step(cons_body, rec_name, rec_id, tail_binder)
    {
        return Some("count".to_string());
    }

    // Check for filter pattern: if cond { [h,..f(t)] } else { f(t) }
    if let PseudoExpr::If {
        then_branch,
        else_branch,
        ..
    } = cons_body
    {
        let else_is_rec = is_simple_recursive_call(else_branch, rec_name, rec_id, tail_binder);
        let then_is_list_cons = list_cons_parts(then_branch)
            .is_some_and(|(_, tail)| is_simple_recursive_call(tail, rec_name, rec_id, tail_binder));
        if else_is_rec && then_is_list_cons {
            return Some("filter".to_string());
        }

        // Find/lookup pattern: if pred(h) { Some(val)/Constr<0>(val) } else { recurse(t) }
        // where the empty clause returns None / Bool.True-like
        if else_is_rec {
            let then_is_option_some = is_standard_option_some_candidate(then_branch.as_ref());
            let empty_body = &_empty_clause.body;
            let empty_is_none = is_naming_none_like(empty_body);
            if then_is_option_some && empty_is_none {
                return Some("find".to_string());
            }
        }
    }

    // Check for map pattern: [transform(h), ..f(t)] and equivalent cons-like forms.
    if let Some((_, tail)) = list_cons_parts(cons_body)
        && is_simple_recursive_call(tail, rec_name, rec_id, tail_binder)
    {
        return Some("map".to_string());
    }

    None
}

pub(super) fn analyze_list_index_rec_behavior(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<String> {
    let [first_param, second_param] = params else {
        return None;
    };

    let PseudoExpr::When {
        subject, clauses, ..
    } = body
    else {
        return None;
    };
    if clauses.len() != 2 {
        return None;
    }

    let (list_param, index_param) = if expr_matches_binder_identity(subject.as_ref(), first_param) {
        (first_param, second_param)
    } else if expr_matches_binder_identity(subject.as_ref(), second_param) {
        (second_param, first_param)
    } else {
        return None;
    };

    let empty_clause = clauses.iter().find(|c| {
        matches!(
            c.pattern,
            WhenPattern::List {
                ref elements,
                tail: None
            } if elements.is_empty()
        )
    })?;
    if !is_naming_none_like(&empty_clause.body) {
        return None;
    }

    let (head_binder, tail_binder, cons_body) = clauses.iter().find_map(|c| match &c.pattern {
        WhenPattern::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => Some((&elements[0], tail, &c.body)),
        _ => None,
    })?;

    if matches!(
        cons_body,
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } if is_index_zero_check(condition, index_param)
            && is_standard_option_some_of_var(then_branch, head_binder)
            && is_recursive_list_index_call(
                else_branch,
                rec_name,
                rec_id,
                tail_binder,
                index_param,
                list_param,
            )
    ) {
        return Some("get_at".to_string());
    }

    None
}

pub(super) fn analyze_list_index_param_hints<'a>(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &'a [crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<Vec<(&'a crate::pseudo::ast::Binder, &'static str)>> {
    let [first_param, second_param] = params else {
        return None;
    };

    let PseudoExpr::When {
        subject, clauses, ..
    } = body
    else {
        return None;
    };
    if clauses.len() != 2 {
        return None;
    }

    let (list_param, index_param) = if expr_matches_binder_identity(subject.as_ref(), first_param) {
        (first_param, second_param)
    } else if expr_matches_binder_identity(subject.as_ref(), second_param) {
        (second_param, first_param)
    } else {
        return None;
    };

    let empty_clause = clauses.iter().find(|c| {
        matches!(
            c.pattern,
            WhenPattern::List {
                ref elements,
                tail: None
            } if elements.is_empty()
        )
    })?;
    if !is_naming_none_like(&empty_clause.body) {
        return None;
    }

    let (head_binder, tail_binder, cons_body) = clauses.iter().find_map(|c| match &c.pattern {
        WhenPattern::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => Some((&elements[0], tail, &c.body)),
        _ => None,
    })?;

    if matches!(
        cons_body,
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } if is_index_zero_check(condition, index_param)
            && is_standard_option_some_of_var(then_branch, head_binder)
            && is_recursive_list_index_call(
                else_branch,
                rec_name,
                rec_id,
                tail_binder,
                index_param,
                list_param,
            )
    ) {
        return Some(vec![(list_param, "list"), (index_param, "index")]);
    }

    None
}

pub(super) fn analyze_single_param_list_rec_param_hints<'a>(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &'a [crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<Vec<(&'a crate::pseudo::ast::Binder, &'static str)>> {
    let [list_param] = params else {
        return None;
    };

    let PseudoExpr::When {
        subject, clauses, ..
    } = body
    else {
        return None;
    };
    if clauses.len() != 2 || !expr_matches_binder_identity(subject.as_ref(), list_param) {
        return None;
    }

    let (_head_name, tail_binder, cons_body) = clauses.iter().find_map(|c| match &c.pattern {
        WhenPattern::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => Some((elements[0].as_str(), tail, &c.body)),
        _ => None,
    })?;

    if contains_recursive_call_with_tail(cons_body, rec_name, rec_id, tail_binder, 1, list_param) {
        Some(vec![(list_param, "list")])
    } else {
        None
    }
}

pub(super) fn analyze_list_accumulator_param_hints<'a>(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &'a [crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<Vec<(&'a crate::pseudo::ast::Binder, &'static str)>> {
    let [first_param, second_param] = params else {
        return None;
    };

    let PseudoExpr::When {
        subject, clauses, ..
    } = body
    else {
        return None;
    };
    if clauses.len() != 2 {
        return None;
    }

    let (list_param, acc_param) = if expr_matches_binder_identity(subject.as_ref(), first_param) {
        (first_param, second_param)
    } else if expr_matches_binder_identity(subject.as_ref(), second_param) {
        (second_param, first_param)
    } else {
        return None;
    };

    let empty_clause = clauses.iter().find(|c| {
        matches!(
            c.pattern,
            WhenPattern::List {
                ref elements,
                tail: None
            } if elements.is_empty()
        )
    })?;
    if !expr_matches_binder_identity(&empty_clause.body, acc_param) {
        return None;
    }

    let (_head_name, tail_binder, cons_body) = clauses.iter().find_map(|c| match &c.pattern {
        WhenPattern::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => Some((elements[0].as_str(), tail, &c.body)),
        _ => None,
    })?;

    if contains_recursive_call_with_tail(cons_body, rec_name, rec_id, tail_binder, 2, list_param) {
        Some(vec![(list_param, "list"), (acc_param, "acc")])
    } else {
        None
    }
}

pub(super) fn contains_recursive_call_with_tail(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
    arity: usize,
    list_param: &Binder,
) -> bool {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr {
            PseudoExpr::Apply { function, args } => {
                if expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id)
                    && args.len() == arity
                    && args
                        .iter()
                        .any(|arg| expr_matches_binder_identity(arg, tail_binder))
                    && !args
                        .iter()
                        .any(|arg| expr_matches_binder_identity(arg, list_param))
                {
                    return true;
                }
                for arg in args.iter().rev() {
                    stack.push(arg);
                }
                stack.push(function);
            }
            PseudoExpr::Let { value, body, .. } => {
                stack.push(body);
                stack.push(value);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.push(else_branch);
                stack.push(then_branch);
                stack.push(condition);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for clause in clauses.iter().rev() {
                    stack.push(&clause.body);
                    if let Some(guard) = &clause.guard {
                        stack.push(guard);
                    }
                }
                stack.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                stack.push(right);
                stack.push(left);
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand)
            | PseudoExpr::FieldAccess {
                record: operand, ..
            } => stack.push(operand),
            PseudoExpr::IndexAccess { collection, .. } => stack.push(collection),
            PseudoExpr::BuiltinCall { args, .. }
            | PseudoExpr::List { elements: args, .. }
            | PseudoExpr::Tuple(args)
            | PseudoExpr::Constr { fields: args, .. } => {
                stack.extend(args.iter().rev());
            }
            PseudoExpr::Trace { message, value } => {
                stack.push(value);
                stack.push(message);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => stack.push(body),
            PseudoExpr::Var { .. }
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_)
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit => {}
        }
    }
    false
}

/// Check if expr is `rec_name(tail_name)` — a simple recursive call on the tail.
pub(super) fn is_simple_recursive_call(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
) -> bool {
    if let PseudoExpr::Apply { function, args } = expr {
        return args.len() == 1
            && expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id)
            && expr_matches_binder_identity(&args[0], tail_binder);
    }
    false
}

pub(super) fn is_direct_var_equality_predicate(expr: &PseudoExpr, binder: &Binder) -> bool {
    match expr {
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        } => {
            expr_matches_binder_identity(left.as_ref(), binder)
                && !expr_matches_binder_identity(right.as_ref(), binder)
                || expr_matches_binder_identity(right.as_ref(), binder)
                    && !expr_matches_binder_identity(left.as_ref(), binder)
        }
        _ => false,
    }
}

pub(super) fn is_recursive_count_if_step(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
) -> bool {
    let PseudoExpr::Let {
        name: result_name,
        id: Some(result_id),
        value,
        body,
        ..
    } = expr
    else {
        return false;
    };

    if !is_simple_recursive_call(value, rec_name, rec_id, tail_binder) {
        return false;
    }

    matches!(
        body.as_ref(),
        PseudoExpr::If {
            then_branch,
            else_branch,
            ..
        } if (is_var_plus_one(then_branch, result_name, Some(*result_id))
                && is_var_ref(else_branch, result_name, Some(*result_id)))
            || (is_var_plus_one(else_branch, result_name, Some(*result_id))
                && is_var_ref(then_branch, result_name, Some(*result_id)))
    )
}

pub(super) fn is_var_ref(expr: &PseudoExpr, name: &str, id: Option<VarId>) -> bool {
    expr_matches_named_var_identity(expr, name, id)
}

pub(super) fn is_var_plus_one(expr: &PseudoExpr, name: &str, id: Option<VarId>) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left,
            right,
        } if (expr_matches_named_var_identity(left.as_ref(), name, id)
            && matches!(right.as_ref(), PseudoExpr::Int(n) if *n == 1.into()))
            || (expr_matches_named_var_identity(right.as_ref(), name, id)
                && matches!(left.as_ref(), PseudoExpr::Int(n) if *n == 1.into()))
    )
}

pub(super) fn is_index_zero_check(expr: &PseudoExpr, index_binder: &Binder) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        } if (expr_matches_binder_identity(left.as_ref(), index_binder)
            && matches!(right.as_ref(), PseudoExpr::Int(n) if *n == 0.into()))
            || (expr_matches_binder_identity(right.as_ref(), index_binder)
                && matches!(left.as_ref(), PseudoExpr::Int(n) if *n == 0.into()))
    )
}

pub(super) fn is_standard_option_some_of_var(expr: &PseudoExpr, binder: &Binder) -> bool {
    extract_standard_option_some_fields(expr)
        .is_some_and(|fields| fields.len() == 1 && expr_matches_binder_identity(&fields[0], binder))
}

pub(super) fn is_naming_none_like(expr: &PseudoExpr) -> bool {
    is_standard_option_none_candidate(expr) || is_bool_false_like(expr)
}

pub(super) fn is_naming_lookup_empty_like(expr: &PseudoExpr) -> bool {
    is_naming_none_like(expr)
        || matches!(
            expr,
            PseudoExpr::BuiltinCall { name, .. }
                if matches!(
                    name.as_str(),
                    "List.empty" | "List.empty_pairs" | "mk_nil_data" | "mk_nil_pair_data"
                )
        )
        || matches!(
            expr,
            PseudoExpr::Apply { function, .. }
                if matches!(
                    function.as_ref(),
                    PseudoExpr::Var { name, .. }
                        if matches!(
                            name.as_str(),
                            "List.empty" | "List.empty_pairs" | "mk_nil_data" | "mk_nil_pair_data"
                        )
                )
        )
}

pub(super) fn is_recursive_list_index_call(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
    index_binder: &Binder,
    list_param: &Binder,
) -> bool {
    let PseudoExpr::Apply { function, args } = expr else {
        return false;
    };
    if !expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id) || args.len() != 2 {
        return false;
    }

    (expr_matches_binder_identity(&args[0], tail_binder)
        && is_index_decrement_of_var(&args[1], index_binder)
        && !expr_matches_binder_identity(&args[1], list_param))
        || (expr_matches_binder_identity(&args[1], tail_binder)
            && is_index_decrement_of_var(&args[0], index_binder)
            && !expr_matches_binder_identity(&args[0], list_param))
}

pub(super) fn is_index_decrement_of_var(expr: &PseudoExpr, index_binder: &Binder) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Sub,
            left,
            right,
        } if expr_matches_binder_identity(left.as_ref(), index_binder)
            && matches!(right.as_ref(), PseudoExpr::Int(n) if *n == 1.into())
    )
}
