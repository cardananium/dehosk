//! The `if list.is_empty(xs) { … } else { … }` traversal family, and
//! the boolean shapes its branches reduce to.
//!
//! One recogniser per idiom — count, filter-matches, any, all, fold,
//! assoc-lookup, sum/max accumulator — each pinned to the exact body
//! shape it names, so an unrecognised traversal keeps its mechanical
//! name rather than being given a plausible wrong one.

use super::*;

pub(super) fn analyze_list_rec_behavior(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<String> {
    if params.len() < 2 {
        return None;
    }

    let PseudoExpr::When {
        subject, clauses, ..
    } = body
    else {
        return None;
    };
    if clauses.len() != 2 {
        return None;
    }

    // Determine which param is the list (when subject) and which is the predicate.
    // Supports both (list, pred, ...) and (pred, list, ...) orderings.
    let (list_param, pred_param, extra_params) =
        if expr_matches_binder_identity(subject.as_ref(), &params[0]) {
            (&params[0], &params[1], &params[2..])
        } else if expr_matches_binder_identity(subject.as_ref(), &params[1]) {
            (&params[1], &params[0], &params[2..])
        } else {
            return None;
        };
    let extra_params: Vec<&Binder> = extra_params.iter().collect();

    let empty_clause = clauses.iter().find(|c| {
        matches!(
            c.pattern,
            WhenPattern::List {
                ref elements,
                tail: None
            } if elements.is_empty()
        )
    })?;
    let cons_clause = clauses.iter().find_map(|c| match &c.pattern {
        WhenPattern::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => Some((&elements[0], tail, &c.body)),
        _ => None,
    })?;

    let head_binder = cons_clause.0;
    let tail_binder = cons_clause.1;
    let cons_body = cons_clause.2;

    if matches!(empty_clause.body, PseudoExpr::Bool(false))
        && matches!(
            cons_body,
            PseudoExpr::BinOp {
                op: BinaryOp::Or,
                left,
                right,
            } if is_predicate_call(left, pred_param, head_binder)
                && is_recursive_list_call(
                    right,
                    rec_name,
                    rec_id,
                    tail_binder,
                    pred_param,
                    &extra_params,
                )
        )
    {
        return Some("any".to_string());
    }

    if params.len() == 2 {
        let acc_param = if list_param == &params[0] {
            &params[1]
        } else {
            &params[0]
        };

        if expr_matches_binder_identity(&empty_clause.body, acc_param) {
            if is_accumulator_sum_step(
                cons_body,
                rec_name,
                rec_id,
                tail_binder,
                list_param,
                acc_param,
            ) {
                return Some("sum".to_string());
            }

            if is_accumulator_max_step(
                cons_body,
                rec_name,
                rec_id,
                tail_binder,
                list_param,
                acc_param,
                head_binder,
            ) {
                return Some("max".to_string());
            }
        }
    }

    if matches!(empty_clause.body, PseudoExpr::Error { .. })
        && matches!(
            cons_body,
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } if is_predicate_call(condition, pred_param, head_binder)
            && expr_matches_binder_identity(then_branch.as_ref(), head_binder)
            && is_recursive_list_call(
                else_branch,
                rec_name,
                rec_id,
                tail_binder,
                pred_param,
                &extra_params,
            )
        )
    {
        return Some("find".to_string());
    }

    // Find variant: [] -> True/None; [h,..t] -> if pred(h) { Constr<0>(h)/Some(h) } else { recurse }
    // More lenient than the Error-base-case find: accepts True/None base and Constr<0> return
    {
        let empty_is_none_like = is_naming_none_like(&empty_clause.body);
        let cons_is_find = matches!(
            cons_body,
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } if is_predicate_call(condition, pred_param, head_binder)
                && is_standard_option_some_candidate(then_branch.as_ref())
                && is_recursive_list_call(
                    else_branch,
                    rec_name,
                    rec_id,
                    tail_binder,
                    pred_param,
                    &extra_params,
                )
        );
        if empty_is_none_like && cons_is_find {
            return Some("find".to_string());
        }
    }

    if matches!(
        &empty_clause.body,
        PseudoExpr::Var { name, .. } if name != list_param.as_str() && name != pred_param.as_str()
    ) && matches!(
        cons_body,
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } if is_predicate_call(condition, pred_param, head_binder)
            && is_list_cons_of_recursive_tail(
                then_branch,
                head_binder,
                rec_name,
                rec_id,
                tail_binder,
                pred_param,
                &extra_params,
            )
            && is_recursive_list_call(
                else_branch,
                rec_name,
                rec_id,
                tail_binder,
                pred_param,
                &extra_params,
            )
    ) {
        return Some("filter_matches".to_string());
    }

    None
}

pub(super) fn analyze_if_empty_list_rec_behavior(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<String> {
    let (list_idx, _list_param, empty_body, non_empty_body) =
        split_if_empty_list_shape(params, body)?;
    let list_param = &params[list_idx];

    if params.len() == 1 && is_if_empty_count_step(non_empty_body, rec_name, rec_id, list_param) {
        return Some("count".to_string());
    }

    if params.len() == 2 {
        let other_idx = 1 - list_idx;
        let other_param = &params[other_idx];

        if matches!(empty_body, PseudoExpr::Bool(true))
            && is_if_empty_all_body(
                non_empty_body,
                rec_name,
                rec_id,
                params,
                list_idx,
                other_param,
                list_param,
            )
        {
            return Some("all".to_string());
        }

        if matches!(empty_body, PseudoExpr::Bool(false))
            && is_if_empty_any_body(
                non_empty_body,
                rec_name,
                rec_id,
                params,
                list_idx,
                other_param,
                list_param,
            )
        {
            return Some("any".to_string());
        }

        if is_if_empty_assoc_lookup_body(non_empty_body, rec_name, rec_id, list_param, other_param)
            && (matches!(empty_body, PseudoExpr::Int(_)) || is_naming_lookup_empty_like(empty_body))
        {
            return Some("lookup".to_string());
        }
    }

    if params.len() == 3 {
        let pred_idx = usize::from(list_idx == 0);
        let acc_idx = 3 - list_idx - pred_idx;
        let pred_param = &params[pred_idx];
        let acc_param = &params[acc_idx];

        if expr_matches_binder_identity(empty_body, acc_param) {
            if is_if_empty_filter_matches_body(
                non_empty_body,
                rec_name,
                rec_id,
                params,
                list_idx,
                pred_param,
                list_param,
            ) {
                return Some("filter_matches".to_string());
            }

            if is_if_empty_fold_step(
                non_empty_body,
                rec_name,
                rec_id,
                params,
                list_idx,
                pred_param,
                acc_param,
                list_param,
            ) {
                return Some("fold".to_string());
            }
        }
    }

    None
}

pub(super) fn analyze_if_empty_list_rec_param_hints<'a>(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &'a [crate::pseudo::ast::Binder],
    body: &'a PseudoExpr,
) -> Option<Vec<(&'a crate::pseudo::ast::Binder, &'static str)>> {
    let (list_idx, list_param, empty_body, non_empty_body) =
        split_if_empty_list_shape(params, body)?;

    if params.len() == 1 && is_if_empty_count_step(non_empty_body, rec_name, rec_id, list_param) {
        return Some(vec![(list_param, "list")]);
    }

    if params.len() == 2 {
        let other_idx = 1 - list_idx;
        let other_param = &params[other_idx];

        if matches!(empty_body, PseudoExpr::Bool(true))
            && is_if_empty_all_body(
                non_empty_body,
                rec_name,
                rec_id,
                params,
                list_idx,
                other_param,
                list_param,
            )
        {
            return Some(vec![(list_param, "list"), (other_param, "predicate")]);
        }

        if matches!(empty_body, PseudoExpr::Bool(false))
            && is_if_empty_any_body(
                non_empty_body,
                rec_name,
                rec_id,
                params,
                list_idx,
                other_param,
                list_param,
            )
        {
            return Some(vec![(list_param, "list"), (other_param, "predicate")]);
        }

        if is_if_empty_assoc_lookup_body(non_empty_body, rec_name, rec_id, list_param, other_param)
            && (matches!(empty_body, PseudoExpr::Int(_)) || is_naming_lookup_empty_like(empty_body))
        {
            return Some(vec![(list_param, "pairs"), (other_param, "needle")]);
        }
    }

    if params.len() == 3 {
        let pred_idx = usize::from(list_idx == 0);
        let acc_idx = 3 - list_idx - pred_idx;
        let pred_param = &params[pred_idx];
        let acc_param = &params[acc_idx];

        if expr_matches_binder_identity(empty_body, acc_param)
            && (is_if_empty_filter_matches_body(
                non_empty_body,
                rec_name,
                rec_id,
                params,
                list_idx,
                pred_param,
                list_param,
            ) || is_if_empty_fold_step(
                non_empty_body,
                rec_name,
                rec_id,
                params,
                list_idx,
                pred_param,
                acc_param,
                list_param,
            ))
        {
            return Some(vec![
                (list_param, "list"),
                (pred_param, "predicate"),
                (acc_param, "acc"),
            ]);
        }
    }

    None
}

pub(super) fn split_if_empty_list_shape<'a>(
    params: &'a [crate::pseudo::ast::Binder],
    body: &'a PseudoExpr,
) -> Option<(
    usize,
    &'a crate::pseudo::ast::Binder,
    &'a PseudoExpr,
    &'a PseudoExpr,
)> {
    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = body
    else {
        return None;
    };

    params.iter().enumerate().find_map(|(idx, param)| {
        if is_list_empty_of_binder(condition, param) {
            Some((idx, param, then_branch.as_ref(), else_branch.as_ref()))
        } else {
            None
        }
    })
}

pub(super) fn is_list_empty_of_binder(expr: &PseudoExpr, list_binder: &Binder) -> bool {
    matches!(
        expr,
        PseudoExpr::BuiltinCall { name, args }
            if *name == crate::BuiltinId::ListIsEmpty
                && args.len() == 1
                && expr_matches_binder_identity(&args[0], list_binder)
    ) || matches!(
        expr,
        // Apply(Var, [arg]) — covers cases where the builtin alias survives as a
        // `Var` (not yet canonicalized into `BuiltinCall`).
        PseudoExpr::Apply { function, args }
            if args.len() == 1
                && expr_matches_binder_identity(&args[0], list_binder)
                && matches!(function.as_ref(), PseudoExpr::Var { name, .. } if *name == "List.is_empty" || *name == "null_list")
    ) || matches!(
        expr,
        PseudoExpr::Apply { function, args }
            if args.len() == 1
                && expr_matches_binder_identity(&args[0], list_binder)
                && matches!(
                    function.as_ref(),
                    PseudoExpr::BuiltinCall { name, args: builtin_args }
                        if *name == crate::BuiltinId::ListIsEmpty && builtin_args.is_empty()
                )
    )
}

pub(super) fn is_list_head_of_binder(expr: &PseudoExpr, list_binder: &Binder) -> bool {
    matches!(
        expr,
        PseudoExpr::FieldAccess { record, selector, .. }
            if selector.is_list_head()
                && expr_matches_binder_identity(record.as_ref(), list_binder)
    )
}

pub(super) fn is_list_tail_of_binder(expr: &PseudoExpr, list_binder: &Binder) -> bool {
    matches!(
        expr,
        PseudoExpr::BuiltinCall { name, args }
            if *name == crate::BuiltinId::ListTail
                && args.len() == 1
                && expr_matches_binder_identity(&args[0], list_binder)
    ) || matches!(
        expr,
        // Apply(Var, [arg]) — covers cases where the alias survives as a `Var`
        // (not yet canonicalized into `BuiltinCall`).
        PseudoExpr::Apply { function, args }
            if args.len() == 1
                && expr_matches_binder_identity(&args[0], list_binder)
                && matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "List.tail" || name == "tail_list")
    ) || matches!(
        expr,
        PseudoExpr::Apply { function, args }
            if args.len() == 1
                && expr_matches_binder_identity(&args[0], list_binder)
                && matches!(
                    function.as_ref(),
                    PseudoExpr::BuiltinCall { name, args: builtin_args }
                        if *name == crate::BuiltinId::ListTail && builtin_args.is_empty()
                )
    ) || matches!(
        expr,
        PseudoExpr::IndexAccess { collection, index }
            if *index == 1
                && expr_matches_binder_identity(collection.as_ref(), list_binder)
    )
}

pub(super) fn is_if_empty_recursive_call(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    list_idx: usize,
) -> bool {
    let PseudoExpr::Apply { function, args } = expr else {
        return false;
    };
    if !expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id)
        || args.len() != params.len()
    {
        return false;
    }

    args.iter().enumerate().all(|(idx, arg)| {
        if idx == list_idx {
            is_list_tail_of_binder(arg, &params[list_idx])
        } else {
            expr_matches_binder_identity(arg, &params[idx])
        }
    })
}

pub(super) fn is_not_list_empty_of_binder(expr: &PseudoExpr, list_binder: &Binder) -> bool {
    matches!(
        expr,
        PseudoExpr::UnOp {
            op: crate::pseudo::ast::UnaryOp::Not,
            operand,
        } if is_list_empty_of_binder(operand, list_binder)
    )
}

pub(super) fn is_collapsed_any_list_body(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    list_idx: usize,
    pred_param: &Binder,
    list_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::And,
            left,
            right,
        } if (is_not_list_empty_of_binder(left, list_param)
            && is_if_empty_any_body(right, rec_name, rec_id, params, list_idx, pred_param, list_param))
            || (is_not_list_empty_of_binder(right, list_param)
                && is_if_empty_any_body(left, rec_name, rec_id, params, list_idx, pred_param, list_param))
    )
}

pub(super) fn is_collapsed_all_list_body(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    list_idx: usize,
    pred_param: &Binder,
    list_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Or,
            left,
            right,
        } if (is_list_empty_of_binder(left, list_param)
            && is_if_empty_all_body(right, rec_name, rec_id, params, list_idx, pred_param, list_param))
            || (is_list_empty_of_binder(right, list_param)
                && is_if_empty_all_body(left, rec_name, rec_id, params, list_idx, pred_param, list_param))
    )
}

pub(super) fn is_if_empty_count_step(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    list_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left,
            right,
        } if (is_list_tail_count_call(left, rec_name, rec_id, list_param)
            && matches!(right.as_ref(), PseudoExpr::Int(n) if *n == 1.into()))
            || (is_list_tail_count_call(right, rec_name, rec_id, list_param)
                && matches!(left.as_ref(), PseudoExpr::Int(n) if *n == 1.into()))
    )
}

pub(super) fn is_list_tail_count_call(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    list_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::Apply { function, args }
            if expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id)
                && args.len() == 1
                && is_list_tail_of_binder(&args[0], list_param)
    )
}

pub(super) fn is_if_empty_filter_matches_body(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    list_idx: usize,
    pred_param: &Binder,
    list_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } if is_predicate_call_on_list_head(condition, pred_param, list_param)
            && is_list_cons_of_if_empty_recursive_tail(
                then_branch,
                list_param,
                rec_name,
                rec_id,
                params,
                list_idx,
            )
            && is_if_empty_recursive_call(else_branch, rec_name, rec_id, params, list_idx)
    )
}

pub(super) fn is_if_empty_any_body(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    list_idx: usize,
    pred_param: &Binder,
    list_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Or,
            left,
            right,
        } if (is_predicate_call_on_list_head(left, pred_param, list_param)
            && is_if_empty_recursive_call(right, rec_name, rec_id, params, list_idx))
            || (is_predicate_call_on_list_head(right, pred_param, list_param)
                && is_if_empty_recursive_call(left, rec_name, rec_id, params, list_idx))
    )
}

pub(super) fn is_if_empty_all_body(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    list_idx: usize,
    pred_param: &Binder,
    list_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::And,
            left,
            right,
        } if (is_predicate_call_on_list_head(left, pred_param, list_param)
            && is_if_empty_recursive_call(right, rec_name, rec_id, params, list_idx))
            || (is_predicate_call_on_list_head(right, pred_param, list_param)
                && is_if_empty_recursive_call(left, rec_name, rec_id, params, list_idx))
    )
}

// Single-shot AST pattern recognizer; all 8 args describe the candidate
// fold-step shape, no natural sub-grouping.
#[allow(clippy::too_many_arguments)]
pub(super) fn is_if_empty_fold_step(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    list_idx: usize,
    step_param: &Binder,
    acc_param: &Binder,
    list_param: &Binder,
) -> bool {
    let PseudoExpr::Apply { function, args } = expr else {
        return false;
    };
    if !expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id)
        || args.len() != params.len()
    {
        return false;
    }

    args.iter().enumerate().all(|(idx, arg)| {
        if idx == list_idx {
            is_list_tail_of_binder(arg, list_param)
        } else if params[idx].var_id() == step_param.var_id() {
            expr_matches_binder_identity(arg, step_param)
        } else if params[idx].var_id() == acc_param.var_id() {
            is_step_call_on_acc_and_list_head(arg, step_param, acc_param, list_param)
        } else {
            expr_matches_binder_identity(arg, &params[idx])
        }
    })
}

pub(super) fn is_if_empty_assoc_lookup_body(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    list_param: &Binder,
    other_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } if is_list_head_pair_field_eq_param(condition, list_param, "fst", other_param)
            && is_list_head_pair_field_payload(then_branch, list_param, "snd")
            && matches!(
                else_branch.as_ref(),
                PseudoExpr::Apply { function, args }
                    if expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id)
                        && args.len() == 2
                        && is_list_tail_of_binder(&args[0], list_param)
                        && expr_matches_binder_identity(&args[1], other_param)
            )
    )
}

pub(super) fn is_predicate_call_on_list_head(
    expr: &PseudoExpr,
    pred_param: &Binder,
    list_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::Apply { function, args }
            if expr_matches_binder_identity(function.as_ref(), pred_param)
                && args.len() == 1
                && is_list_head_of_binder(&args[0], list_param)
    )
}

pub(super) fn is_step_call_on_acc_and_list_head(
    expr: &PseudoExpr,
    step_param: &Binder,
    acc_param: &Binder,
    list_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::Apply { function, args }
            if expr_matches_binder_identity(function.as_ref(), step_param)
                && args.len() == 2
                && ((expr_matches_binder_identity(&args[0], acc_param)
                    && is_list_head_of_binder(&args[1], list_param))
                    || (expr_matches_binder_identity(&args[1], acc_param)
                        && is_list_head_of_binder(&args[0], list_param)))
    )
}

pub(super) fn is_list_cons_of_if_empty_recursive_tail(
    expr: &PseudoExpr,
    list_param: &Binder,
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    list_idx: usize,
) -> bool {
    if let Some((head, tail)) = list_cons_parts(expr) {
        return is_list_head_of_binder(head, list_param)
            && is_if_empty_recursive_call(tail, rec_name, rec_id, params, list_idx);
    }
    false
}

pub(super) fn is_list_head_pair_field_eq_param(
    expr: &PseudoExpr,
    list_param: &Binder,
    field: &str,
    other_param: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        } if (is_list_head_pair_field(left, list_param, field)
            && expr_matches_binder_identity(right.as_ref(), other_param))
            || (is_list_head_pair_field(right, list_param, field)
                && expr_matches_binder_identity(left.as_ref(), other_param))
    )
}

pub(super) fn is_list_head_pair_field(expr: &PseudoExpr, list_param: &Binder, field: &str) -> bool {
    matches!(
        expr,
        PseudoExpr::FieldAccess {
            record,
            selector,
            ..
        } if selector.as_pretty_name() == field && is_list_head_of_binder(record, list_param)
    )
}

pub(super) fn is_list_head_pair_field_payload(
    expr: &PseudoExpr,
    list_param: &Binder,
    field: &str,
) -> bool {
    is_list_head_pair_field(expr, list_param, field)
        || matches!(
            expr,
            PseudoExpr::BuiltinCall { args, .. } | PseudoExpr::Apply { args, .. }
                if args.len() == 1 && is_list_head_pair_field(&args[0], list_param, field)
        )
        || matches!(
            expr,
            PseudoExpr::Constr { fields, .. }
                if fields.len() == 1 && is_list_head_pair_field(&fields[0], list_param, field)
        )
}

pub(super) fn is_accumulator_sum_step(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
    list_param: &Binder,
    acc_param: &Binder,
) -> bool {
    let PseudoExpr::Apply { function, args } = expr else {
        return false;
    };
    if !expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id) || args.len() != 2 {
        return false;
    }

    let (tail_arg, acc_arg) = if expr_matches_binder_identity(&args[0], tail_binder)
        && !expr_matches_binder_identity(&args[1], list_param)
    {
        (&args[0], &args[1])
    } else if expr_matches_binder_identity(&args[1], tail_binder)
        && !expr_matches_binder_identity(&args[0], list_param)
    {
        (&args[1], &args[0])
    } else {
        return false;
    };

    expr_matches_binder_identity(tail_arg, tail_binder)
        && matches!(
            acc_arg,
            PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left,
                right,
            } if expr_matches_binder_identity(left.as_ref(), acc_param)
                || expr_matches_binder_identity(right.as_ref(), acc_param)
        )
}

pub(super) fn is_accumulator_max_step(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
    list_param: &Binder,
    acc_param: &Binder,
    head_binder: &Binder,
) -> bool {
    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = expr
    else {
        return false;
    };

    let compares_head_and_acc = matches!(
        condition.as_ref(),
        PseudoExpr::BinOp { left, right, .. }
            if (expr_matches_binder_identity(left.as_ref(), head_binder)
                && expr_matches_binder_identity(right.as_ref(), acc_param))
                || (expr_matches_binder_identity(left.as_ref(), acc_param)
                    && expr_matches_binder_identity(right.as_ref(), head_binder))
    );
    compares_head_and_acc
        && is_recursive_accumulator_call(
            then_branch,
            rec_name,
            rec_id,
            tail_binder,
            list_param,
            head_binder.as_str(),
            Some(head_binder.var_id()),
        )
        && is_recursive_accumulator_call(
            else_branch,
            rec_name,
            rec_id,
            tail_binder,
            list_param,
            acc_param.as_str(),
            Some(acc_param.var_id()),
        )
}

pub(super) fn is_recursive_accumulator_call(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
    list_param: &Binder,
    acc_value_name: &str,
    acc_value_id: Option<VarId>,
) -> bool {
    let PseudoExpr::Apply { function, args } = expr else {
        return false;
    };
    if !expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id) || args.len() != 2 {
        return false;
    }

    (expr_matches_binder_identity(&args[0], tail_binder)
        && expr_matches_named_var_identity(&args[1], acc_value_name, acc_value_id)
        && !expr_matches_binder_identity(&args[1], list_param))
        || (expr_matches_binder_identity(&args[1], tail_binder)
            && expr_matches_named_var_identity(&args[0], acc_value_name, acc_value_id)
            && !expr_matches_binder_identity(&args[0], list_param))
}

pub(super) fn is_lambda_param_equality_predicate(body: &PseudoExpr, item_param: &str) -> bool {
    match body {
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        } => {
            matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == item_param)
                && !matches!(right.as_ref(), PseudoExpr::Var { name, .. } if name == item_param)
                || matches!(right.as_ref(), PseudoExpr::Var { name, .. } if name == item_param)
                    && !matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == item_param)
        }
        _ => false,
    }
}

pub(super) fn is_predicate_call(
    expr: &PseudoExpr,
    pred_binder: &Binder,
    head_binder: &Binder,
) -> bool {
    matches!(
        expr,
        PseudoExpr::Apply { function, args }
            if expr_matches_binder_identity(function.as_ref(), pred_binder)
                && args.len() == 1
                && expr_matches_binder_identity(&args[0], head_binder)
    )
}

pub(super) fn is_recursive_list_call(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
    pred_binder: &Binder,
    extra_params: &[&Binder],
) -> bool {
    let PseudoExpr::Apply { function, args } = expr else {
        return false;
    };
    if !expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id) {
        return false;
    }
    if args.len() != 2 + extra_params.len() {
        return false;
    }
    // Accept both (tail, pred, extras) and (pred, tail, extras) orderings
    let first_two_match = (expr_matches_binder_identity(&args[0], tail_binder)
        && expr_matches_binder_identity(&args[1], pred_binder))
        || (expr_matches_binder_identity(&args[0], pred_binder)
            && expr_matches_binder_identity(&args[1], tail_binder));
    first_two_match
        && args[2..]
            .iter()
            .zip(extra_params.iter())
            .all(|(arg, param)| expr_matches_binder_identity(arg, param))
}

pub(super) fn is_list_cons_of_recursive_tail(
    expr: &PseudoExpr,
    head_binder: &Binder,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
    pred_binder: &Binder,
    extra_params: &[&Binder],
) -> bool {
    if let Some((head, tail)) = list_cons_parts(expr)
        && expr_matches_binder_identity(head, head_binder)
        && is_recursive_list_call(
            tail,
            rec_name,
            rec_id,
            tail_binder,
            pred_binder,
            extra_params,
        )
    {
        return true;
    }
    false
}

/// Check if body is a boolean negation: `when x: Bool is { True -> False, False -> True }`
pub(super) fn is_boolean_negation(body: &PseudoExpr) -> bool {
    if let PseudoExpr::When { clauses, .. } = body
        && clauses.len() == 2
    {
        let has_true_to_false = clauses
            .iter()
            .any(|c| matches_bool_pattern(&c.pattern, true) && is_bool_false(&c.body));
        let has_false_to_true = clauses
            .iter()
            .any(|c| matches_bool_pattern(&c.pattern, false) && is_bool_true(&c.body));
        return has_true_to_false && has_false_to_true;
    }
    false
}

/// Check if expression represents boolean `true` (Bool literal or True constructor).
pub(super) fn is_bool_true(expr: &PseudoExpr) -> bool {
    is_bool_true_like(expr)
}

/// Check if expression represents boolean `false` (Bool literal or False constructor).
pub(super) fn is_bool_false(expr: &PseudoExpr) -> bool {
    is_bool_false_like(expr)
}

/// Check if a when pattern matches a Bool constructor.
pub(super) fn matches_bool_pattern(pattern: &WhenPattern, val: bool) -> bool {
    let WhenPattern::Constructor { shape, .. } = pattern else {
        return false;
    };
    match shape.as_known() {
        Some(KnownConstructor::True) => val,
        Some(KnownConstructor::False) => !val,
        Some(_) => false,
        None => {
            let tag = shape.tag();
            (val && tag == 1) || (!val && tag == 0)
        }
    }
}
