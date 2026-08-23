//! Association-list lookup: `[(k, v), …]` walked until a key matches.
//!
//! The `is_pair_*` family recognises the key/value halves of a pair
//! element, and the `*_ordered_*` / `*_cutoff_*` variants additionally
//! recognise the SORTED form, which stops early on a key past the
//! target.

use super::*;

pub(super) fn analyze_assoc_lookup_rec_behavior(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<String> {
    if params.is_empty() {
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

    // Find which param is the list (when subject) — supports any position
    let list_idx = params
        .iter()
        .position(|p| expr_matches_binder_identity(subject.as_ref(), p))?;
    let _list_param = &params[list_idx];
    let extra_params: Vec<&Binder> = params
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != list_idx)
        .map(|(_, p)| p)
        .collect();
    let extra_params = extra_params.as_slice();

    let empty_clause = clauses.iter().find(|c| {
        matches!(
            c.pattern,
            WhenPattern::List {
                ref elements,
                tail: None
            } if elements.is_empty()
        )
    })?;
    // Base case: literal (Int/Bool/Error) or a variable (the default/accumulator param)
    let empty_ok = matches!(
        &empty_clause.body,
        PseudoExpr::Int(_) | PseudoExpr::Error { .. }
    ) || extra_params
        .iter()
        .any(|param| expr_matches_binder_identity(&empty_clause.body, param))
        || is_naming_lookup_empty_like(&empty_clause.body);
    if !empty_ok {
        return None;
    }

    let (head_binder, tail_binder, cons_body) = clauses.iter().find_map(|c| match &c.pattern {
        WhenPattern::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => Some((&elements[0], tail, &c.body)),
        _ => None,
    })?;
    let (key_alias, lookup_body) =
        split_pair_fst_key_alias(cons_body, head_binder.as_str(), Some(head_binder.var_id()));

    if matches!(
        lookup_body,
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } if is_pair_fst_equality_with_alias(
                condition,
                head_binder.as_str(),
                Some(head_binder.var_id()),
                key_alias,
            )
            && is_pair_snd_payload(
                then_branch,
                head_binder.as_str(),
                Some(head_binder.var_id()),
            )
            && is_recursive_assoc_lookup_call(
                else_branch,
                rec_name,
                rec_id,
                tail_binder,
                extra_params,
            )
    ) {
        return Some("lookup".to_string());
    }

    if is_ordered_assoc_lookup_body(
        lookup_body,
        head_binder.as_str(),
        Some(head_binder.var_id()),
        key_alias,
        rec_name,
        rec_id,
        tail_binder,
        extra_params,
    ) {
        return Some("lookup".to_string());
    }

    None
}

pub(super) fn analyze_assoc_lookup_param_hints<'a>(
    params: &'a [crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<Vec<(&'a crate::pseudo::ast::Binder, &'static str)>> {
    if params.is_empty() {
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

    let list_idx = params
        .iter()
        .position(|p| expr_matches_binder_identity(subject.as_ref(), p))?;
    let list_param = &params[list_idx];
    let extra_params: Vec<&crate::pseudo::ast::Binder> = params
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != list_idx)
        .map(|(_, p)| p)
        .collect();

    let empty_clause = clauses.iter().find(|c| {
        matches!(
            c.pattern,
            WhenPattern::List {
                ref elements,
                tail: None
            } if elements.is_empty()
        )
    })?;
    let empty_ok = matches!(
        &empty_clause.body,
        PseudoExpr::Int(_) | PseudoExpr::Error { .. }
    ) || extra_params
        .iter()
        .any(|param| expr_matches_binder_identity(&empty_clause.body, param))
        || is_naming_lookup_empty_like(&empty_clause.body);
    if !empty_ok {
        return None;
    }

    let (head_binder, tail_binder, cons_body) = clauses.iter().find_map(|c| match &c.pattern {
        WhenPattern::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => Some((&elements[0], tail, &c.body)),
        _ => None,
    })?;
    let (key_alias, lookup_body) =
        split_pair_fst_key_alias(cons_body, head_binder.as_str(), Some(head_binder.var_id()));

    let is_lookup = matches!(
        lookup_body,
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } if is_pair_fst_equality_with_alias(
                condition,
                head_binder.as_str(),
                Some(head_binder.var_id()),
                key_alias,
            )
            && is_pair_snd_payload(
                then_branch,
                head_binder.as_str(),
                Some(head_binder.var_id()),
            )
            && is_any_recursive_assoc_lookup_call(else_branch, tail_binder, extra_params.as_slice())
    ) || is_any_ordered_assoc_lookup_body(
        lookup_body,
        head_binder.as_str(),
        Some(head_binder.var_id()),
        key_alias,
        tail_binder,
        extra_params.as_slice(),
    );

    if !is_lookup {
        return None;
    }

    let mut hints = vec![(list_param, "pairs")];
    if extra_params.len() == 1 {
        hints.push((extra_params[0], "needle"));
    }
    Some(hints)
}

pub(super) fn analyze_assoc_lookup_then_rec_behavior(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<String> {
    let [cont_param, list_param] = params else {
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

    let empty_clause = clauses.iter().find(|c| {
        matches!(
            c.pattern,
            WhenPattern::List {
                ref elements,
                tail: None
            } if elements.is_empty()
        )
    })?;
    if !matches!(
        &empty_clause.body,
        PseudoExpr::Int(_) | PseudoExpr::Error { .. }
    ) {
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
            } if is_pair_fst_equality(
                    condition,
                    head_binder.as_str(),
                    Some(head_binder.var_id()),
                )
                && is_assoc_lookup_then_branch(
                    then_branch,
                    cont_param,
                    head_binder.as_str(),
                    Some(head_binder.var_id()),
                )
                && matches!(
                    else_branch.as_ref(),
                    PseudoExpr::Apply { function, args }
                        if expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id)
                            && args.len() == 2
                        && expr_matches_binder_identity(&args[0], cont_param)
                        && expr_matches_binder_identity(&args[1], tail_binder)
            )
    ) {
        return Some("lookup_then".to_string());
    }

    None
}

pub(super) fn is_pair_field_access_of_var_identity(
    expr: &PseudoExpr,
    record_name: &str,
    record_id: Option<VarId>,
    field_name: &str,
) -> bool {
    matches!(
        expr,
        PseudoExpr::FieldAccess { record, selector, .. }
            if selector.as_pretty_name() == field_name
                && expr_matches_named_var_identity(record.as_ref(), record_name, record_id)
    )
}

pub(super) fn is_pair_field_payload_of_var_identity(
    expr: &PseudoExpr,
    record_name: &str,
    record_id: Option<VarId>,
    field_name: &str,
) -> bool {
    is_pair_field_access_of_var_identity(expr, record_name, record_id, field_name)
        || matches!(
            expr,
            PseudoExpr::Constr { tag: 0, fields, .. }
                if fields.len() == 1
                    && is_pair_field_access_of_var_identity(
                        &fields[0],
                        record_name,
                        record_id,
                        field_name,
                    )
        )
}

pub(super) fn is_pair_fst_equality(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
) -> bool {
    is_pair_fst_equality_with_alias(expr, head_name, head_id, None)
}

pub(super) fn is_pair_fst_equality_with_alias(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
    key_alias: Option<(&str, Option<VarId>)>,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        } if is_pair_fst_key_expr(left, head_name, head_id, key_alias)
            || is_pair_fst_key_expr(right, head_name, head_id, key_alias)
    )
}

pub(super) fn is_pair_fst_access(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
) -> bool {
    is_pair_field_access_of_var_identity(expr, head_name, head_id, "fst")
}

pub(super) fn is_pair_fst_key_alias_value(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
) -> bool {
    is_pair_fst_access(expr, head_name, head_id)
        || matches!(
            expr,
            PseudoExpr::BuiltinCall { args, .. } | PseudoExpr::Apply { args, .. }
                if args.len() == 1 && is_pair_fst_access(&args[0], head_name, head_id)
        )
}

pub(super) fn split_pair_fst_key_alias<'a>(
    expr: &'a PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
) -> (Option<(&'a str, Option<VarId>)>, &'a PseudoExpr) {
    match expr {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
            ..
        } if is_pair_fst_key_alias_value(value, head_name, head_id) => {
            (Some((name.as_str(), *id)), body.as_ref())
        }
        _ => (None, expr),
    }
}

pub(super) fn is_pair_fst_key_expr(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
    key_alias: Option<(&str, Option<VarId>)>,
) -> bool {
    is_pair_fst_access(expr, head_name, head_id)
        || key_alias.is_some_and(|(alias_name, alias_id)| {
            expr_matches_named_var_identity(expr, alias_name, alias_id)
        })
}

pub(super) fn is_pair_snd_access(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
) -> bool {
    is_pair_field_access_of_var_identity(expr, head_name, head_id, "snd")
}

pub(super) fn is_pair_snd_payload(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
) -> bool {
    is_pair_field_payload_of_var_identity(expr, head_name, head_id, "snd")
        // Apply(transform_fn, [head.snd]) — transform applied to pair value
        || matches!(
            expr,
            PseudoExpr::Apply { args, .. }
                if args.len() == 1 && is_pair_snd_access(&args[0], head_name, head_id)
        )
        // BuiltinCall(transform, [head.snd]) — direct builtin extractor on pair value
        || matches!(
            expr,
            PseudoExpr::BuiltinCall { args, .. }
                if args.len() == 1 && is_pair_snd_access(&args[0], head_name, head_id)
        )
        || extract_standard_option_some_fields(expr).is_some_and(|fields| {
            fields.len() == 1
                && is_pair_field_payload_of_var_identity(
                    &fields[0],
                    head_name,
                    head_id,
                    "snd",
                )
        })
}

// Single-shot AST pattern recognizer; all 8 args are independent inputs
// describing the candidate shape, no natural sub-grouping.
#[allow(clippy::too_many_arguments)]
pub(super) fn is_ordered_assoc_lookup_body(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
    key_alias: Option<(&str, Option<VarId>)>,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
    extra_params: &[&Binder],
) -> bool {
    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = expr
    else {
        return false;
    };

    if is_pair_fst_equality_with_alias(condition, head_name, head_id, key_alias)
        && is_pair_snd_payload(then_branch, head_name, head_id)
    {
        let Some(other_operand) =
            pair_fst_equality_other_with_alias(condition, head_name, head_id, key_alias)
        else {
            return false;
        };

        return matches!(
            else_branch.as_ref(),
            PseudoExpr::If {
                condition: lt_condition,
                then_branch: lt_then,
                else_branch: recurse_branch,
            } if is_pair_fst_order_cutoff_with_alias(
                    lt_condition,
                    head_name,
                    head_id,
                    key_alias,
                    other_operand,
                )
                && is_naming_none_like(lt_then.as_ref())
                && is_recursive_assoc_lookup_call(
                    recurse_branch,
                    rec_name,
                    rec_id,
                    tail_binder,
                    extra_params,
                )
        );
    }

    let PseudoExpr::If {
        condition: eq_condition,
        then_branch: eq_then,
        else_branch: eq_else,
    } = then_branch.as_ref()
    else {
        return false;
    };

    let Some(other_operand) =
        pair_fst_equality_other_with_alias(eq_condition, head_name, head_id, key_alias)
    else {
        return false;
    };

    is_pair_fst_non_greater_cutoff_with_alias(
        condition,
        head_name,
        head_id,
        key_alias,
        other_operand,
    ) && is_pair_fst_equality_with_alias(eq_condition, head_name, head_id, key_alias)
        && is_pair_snd_payload(eq_then, head_name, head_id)
        && is_naming_none_like(eq_else.as_ref())
        && is_recursive_assoc_lookup_call(else_branch, rec_name, rec_id, tail_binder, extra_params)
}

pub(super) fn is_any_ordered_assoc_lookup_body(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
    key_alias: Option<(&str, Option<VarId>)>,
    tail_binder: &Binder,
    extra_params: &[&Binder],
) -> bool {
    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = expr
    else {
        return false;
    };

    if is_pair_fst_equality_with_alias(condition, head_name, head_id, key_alias)
        && is_pair_snd_payload(then_branch, head_name, head_id)
    {
        let Some(other_operand) =
            pair_fst_equality_other_with_alias(condition, head_name, head_id, key_alias)
        else {
            return false;
        };

        return matches!(
            else_branch.as_ref(),
            PseudoExpr::If {
                condition: lt_condition,
                then_branch: lt_then,
                else_branch: recurse_branch,
            } if is_pair_fst_order_cutoff_with_alias(
                    lt_condition,
                    head_name,
                    head_id,
                    key_alias,
                    other_operand,
                )
                && is_naming_none_like(lt_then.as_ref())
                && is_any_recursive_assoc_lookup_call(recurse_branch, tail_binder, extra_params)
        );
    }

    let PseudoExpr::If {
        condition: eq_condition,
        then_branch: eq_then,
        else_branch: eq_else,
    } = then_branch.as_ref()
    else {
        return false;
    };

    let Some(other_operand) =
        pair_fst_equality_other_with_alias(eq_condition, head_name, head_id, key_alias)
    else {
        return false;
    };

    is_pair_fst_non_greater_cutoff_with_alias(
        condition,
        head_name,
        head_id,
        key_alias,
        other_operand,
    ) && is_pair_fst_equality_with_alias(eq_condition, head_name, head_id, key_alias)
        && is_pair_snd_payload(eq_then, head_name, head_id)
        && is_naming_none_like(eq_else.as_ref())
        && is_any_recursive_assoc_lookup_call(else_branch, tail_binder, extra_params)
}

pub(super) fn pair_fst_equality_other_with_alias<'a>(
    expr: &'a PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
    key_alias: Option<(&str, Option<VarId>)>,
) -> Option<&'a PseudoExpr> {
    let PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left,
        right,
    } = expr
    else {
        return None;
    };

    if is_pair_fst_key_expr(left, head_name, head_id, key_alias) {
        Some(right)
    } else if is_pair_fst_key_expr(right, head_name, head_id, key_alias) {
        Some(left)
    } else {
        None
    }
}

pub(super) fn is_pair_fst_order_cutoff_with_alias(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
    key_alias: Option<(&str, Option<VarId>)>,
    other: &PseudoExpr,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Lt,
            left,
            right,
        } if left.as_ref().structural_eq(other)
            && is_pair_fst_key_expr(right, head_name, head_id, key_alias)
    ) || matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Gt,
            left,
            right,
        } if is_pair_fst_key_expr(left, head_name, head_id, key_alias)
            && right.as_ref().structural_eq(other)
    )
}

pub(super) fn is_pair_fst_non_greater_cutoff_with_alias(
    expr: &PseudoExpr,
    head_name: &str,
    head_id: Option<VarId>,
    key_alias: Option<(&str, Option<VarId>)>,
    other: &PseudoExpr,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Lte,
            left,
            right,
        } if left.as_ref().structural_eq(other)
            && is_pair_fst_key_expr(right, head_name, head_id, key_alias)
    ) || matches!(
        expr,
        PseudoExpr::BinOp {
            op: BinaryOp::Gte,
            left,
            right,
        } if is_pair_fst_key_expr(left, head_name, head_id, key_alias)
            && right.as_ref().structural_eq(other)
    )
}

pub(super) fn is_recursive_assoc_lookup_call(
    expr: &PseudoExpr,
    rec_name: &str,
    rec_id: Option<VarId>,
    tail_binder: &Binder,
    extra_params: &[&Binder],
) -> bool {
    matches!(
        expr,
        PseudoExpr::Apply { function, args }
            if expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id)
                && args.len() == 1 + extra_params.len()
                && expr_matches_binder_identity(&args[0], tail_binder)
                && args[1..].iter().zip(extra_params.iter()).all(
                    |(arg, param)| expr_matches_binder_identity(arg, param)
                )
    )
}

pub(super) fn is_any_recursive_assoc_lookup_call(
    expr: &PseudoExpr,
    tail_binder: &Binder,
    extra_params: &[&Binder],
) -> bool {
    matches!(
        expr,
        PseudoExpr::Apply { args, .. }
            if args.len() == 1 + extra_params.len()
                && expr_matches_binder_identity(&args[0], tail_binder)
                && args[1..].iter().zip(extra_params.iter()).all(
                    |(arg, param)| expr_matches_binder_identity(arg, param)
                )
    )
}

pub(super) fn is_assoc_lookup_then_branch(
    expr: &PseudoExpr,
    cont_param: &Binder,
    head_name: &str,
    head_id: Option<VarId>,
) -> bool {
    matches!(
        expr,
        PseudoExpr::Apply { function, args }
            if expr_matches_binder_identity(function.as_ref(), cont_param)
                && args.len() == 2
                && expr_matches_binder_identity(&args[0], cont_param)
                && matches!(
                    &args[1],
                    PseudoExpr::BuiltinCall { name, args }
                        if DATA_MAP_EXTRACTORS.contains(&name.as_str())
                            && args.len() == 1
                            && is_pair_snd_access(&args[0], head_name, head_id)
                )
    )
}

pub(super) fn is_self_applied_lookup_lambda(params: &[Binder], body: &PseudoExpr) -> bool {
    let [self_param, list_param] = params else {
        return false;
    };

    matches!(
        body,
        PseudoExpr::When {
            subject,
            clauses,
            ..
        } if expr_matches_binder_identity(subject.as_ref(), list_param)
            && clauses.len() == 2
            && clauses.iter().any(|c| {
                matches!(
                    c.pattern,
                    WhenPattern::List {
                        ref elements,
                        tail: None
                    } if elements.is_empty()
                ) && matches!(c.body, PseudoExpr::Int(_) | PseudoExpr::Error { .. })
            })
            && clauses.iter().any(|c| match &c.pattern {
                WhenPattern::List {
                    elements,
                    tail: Some(tail_name),
                } if elements.len() == 1 => matches!(
                    &c.body,
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } if is_pair_fst_equality(
                            condition,
                            elements[0].as_str(),
                            Some(elements[0].var_id()),
                        )
                        && is_pair_snd_access(
                            then_branch,
                            elements[0].as_str(),
                            Some(elements[0].var_id()),
                        )
                        && matches!(
                            else_branch.as_ref(),
                            PseudoExpr::Apply { function, args }
                                if expr_matches_binder_identity(function.as_ref(), self_param)
                                    && args.len() == 2
                                    && expr_matches_binder_identity(&args[0], self_param)
                                    && expr_matches_binder_identity(&args[1], tail_name)
                        )
                ),
                _ => false,
            })
    )
}
