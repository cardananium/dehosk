//! What a single `let` binding IS, so it can be named after that.
//!
//! One `analyze_*_binding` per recognised shape — a function, a
//! temporary, a data-list peel, a field alias, a constructor payload
//! alias, a unit check, an arithmetic temp, an extractor, an Option
//! wrapper — each returning a display-name hint or nothing.
//!
//! The `*_with_consistency` variants take the consistently-referenced id
//! set from `hint_collection`: a hint derived from a reference the
//! pipeline may still retarget is not safe to commit.

use super::*;

/// Return a name hint for a `let name = value` binding, drawn
/// from the value's shape.
///
/// Only fires on generic names (`f_N`, `fn_N`, `fold_result_N`)
/// and temporary helper names.
pub(super) fn analyze_function_binding(name: &str, value: &PseudoExpr) -> Option<String> {
    if !is_generic_name(name) && !is_temporary_helper_name(name) {
        return None;
    }

    match value {
        PseudoExpr::Lambda { body, params, .. } => analyze_function_body(name, body, params.len()),
        PseudoExpr::RecFn {
            name: rec_name,
            body,
            params,
        } => {
            if name.starts_with("fold_result_") {
                return Some(name.replace("fold_result_", "fold_"));
            }
            analyze_rec_function_body(name, Some(rec_name.var_id()), params, body)
        }
        _ => {
            if name.starts_with("fold_result_") {
                return Some(name.replace("fold_result_", "fold_"));
            }
            None
        }
    }
}

pub(super) fn analyze_function_binding_with_fold_rec_candidates(
    name: &str,
    value: &PseudoExpr,
    fold_rec_candidates: &HashSet<FoldRecCandidateKey>,
) -> Option<String> {
    analyze_function_binding(name, value).or_else(|| {
        if !is_generic_name(name) && !is_temporary_helper_name(name) {
            return None;
        }

        let PseudoExpr::Lambda { params, body } = value else {
            return None;
        };
        analyze_map_fold_forwarder(params, body, fold_rec_candidates)
    })
}

#[cfg(test)]
pub(super) fn analyze_temporary_value_binding(name: &str, value: &PseudoExpr) -> Option<String> {
    analyze_temporary_value_binding_with_consistency(name, value, None)
}

#[cfg(test)]
pub(super) fn analyze_temporary_value_binding_with_consistency(
    name: &str,
    value: &PseudoExpr,
    consistent_ref_ids: Option<&HashSet<VarId>>,
) -> Option<String> {
    analyze_temporary_value_binding_with_consistency_impl(name, value, consistent_ref_ids)
}

pub(super) fn analyze_temporary_value_binding_with_consistency_impl(
    name: &str,
    value: &PseudoExpr,
    _consistent_ref_ids: Option<&HashSet<VarId>>,
) -> Option<String> {
    if !is_temporary_helper_name(name) {
        return None;
    }

    let PseudoExpr::Let {
        name: inner_name,
        value: inner_value,
        body: call_body,
        ..
    } = value
    else {
        return None;
    };

    let PseudoExpr::RecFn {
        name: rec_name,
        params,
        body: rec_body,
    } = inner_value.as_ref()
    else {
        return None;
    };
    if rec_name.as_str() != inner_name {
        return None;
    }

    let PseudoExpr::Apply { function, .. } = call_body.as_ref() else {
        return None;
    };
    if !matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == inner_name) {
        return None;
    }

    analyze_rec_function_body(rec_name, Some(rec_name.var_id()), params, rec_body)
        .map(|hint| format!("{}_result", hint))
}

pub(super) fn analyze_data_list_temp_binding(value: &PseudoExpr) -> Option<String> {
    if data_list_call_wraps_apply(value, None) {
        return Some("data_list".to_string());
    }

    let PseudoExpr::Let {
        name: inner_name,
        value: inner_value,
        body: call_body,
        ..
    } = value
    else {
        return None;
    };

    let PseudoExpr::RecFn { name: rec_name, .. } = inner_value.as_ref() else {
        return None;
    };
    if rec_name.as_str() != inner_name {
        return None;
    }

    if data_list_call_wraps_apply(call_body, Some(inner_name)) {
        Some("data_list".to_string())
    } else {
        None
    }
}

pub(super) fn data_list_call_wraps_apply(
    expr: &PseudoExpr,
    expected_function: Option<&str>,
) -> bool {
    matches!(
        expr,
        PseudoExpr::BuiltinCall { name, args }
            if *name == crate::BuiltinId::DataList
                && args.len() == 1
                && matches!(
                    &args[0],
                    PseudoExpr::Apply { function, .. }
                        if matches!(
                            function.as_ref(),
                            PseudoExpr::Var { name, .. }
                                if expected_function.is_none_or(|expected| name == expected)
                        )
                )
    )
}

pub(super) fn analyze_field_alias_temp_binding(
    value: &PseudoExpr,
    consistent_ref_ids: Option<&HashSet<VarId>>,
) -> Option<String> {
    match value {
        PseudoExpr::IndexAccess { collection, index } => match collection.as_ref() {
            PseudoExpr::BuiltinCall { name, args }
                if *index == 0
                    && DATA_MAP_EXTRACTORS.iter().any(|builtin| *name == *builtin)
                    && args.len() == 1 =>
            {
                Some("entry".to_string())
            }
            payload_ref if *index == 0 && payload_seed_matches(payload_ref, consistent_ref_ids) => {
                Some("variant".to_string())
            }
            payload_ref if *index == 1 && payload_seed_matches(payload_ref, consistent_ref_ids) => {
                Some("map".to_string())
            }
            payload_ref if *index == 2 && payload_seed_matches(payload_ref, consistent_ref_ids) => {
                Some("item".to_string())
            }
            PseudoExpr::FieldAccess {
                record, selector, ..
            } if selector.as_pretty_name() == "fields"
                && payload_seed_matches(record.as_ref(), consistent_ref_ids)
                && *index == 0 =>
            {
                Some("variant".to_string())
            }
            PseudoExpr::FieldAccess {
                record, selector, ..
            } if selector.as_pretty_name() == "fields"
                && payload_seed_matches(record.as_ref(), consistent_ref_ids)
                && *index == 1 =>
            {
                Some("map".to_string())
            }
            PseudoExpr::FieldAccess {
                record, selector, ..
            } if selector.as_pretty_name() == "fields"
                && payload_seed_matches(record.as_ref(), consistent_ref_ids)
                && *index == 2 =>
            {
                Some("item".to_string())
            }
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn payload_seed_matches(
    expr: &PseudoExpr,
    consistent_ref_ids: Option<&HashSet<VarId>>,
) -> bool {
    let PseudoExpr::Var { name, id } = expr else {
        return false;
    };

    if name != "payload" {
        return false;
    }

    if let Some(id) = id.get() {
        consistent_ref_ids.is_none_or(|consistent_ref_ids| consistent_ref_ids.contains(&id))
    } else {
        true
    }
}

pub(super) fn analyze_constructor_payload_alias_temp_binding(value: &PseudoExpr) -> Option<String> {
    match value {
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => {
            let (subject_name, subject_id) = if let Some(subject_name) = subject_name.as_ref() {
                (subject_name.as_str(), Some(subject_name.var_id()))
            } else {
                let PseudoExpr::Var { name, id } = subject.as_ref() else {
                    return None;
                };
                (name.as_str(), id.get())
            };
            if !subject_name.starts_with("variant") {
                return None;
            }

            clauses.iter().find_map(|clause| match &clause.body {
                body if expr_matches_named_var_identity(body, subject_name, subject_id) => {
                    Some("payload".to_string())
                }
                PseudoExpr::IndexAccess { collection, index }
                    if *index == 0
                        && expr_matches_named_var_identity(
                            collection.as_ref(),
                            subject_name,
                            subject_id,
                        ) =>
                {
                    Some("payload".to_string())
                }
                PseudoExpr::IndexAccess { collection, index }
                    if *index == 0
                        && matches!(
                            collection.as_ref(),
                            PseudoExpr::FieldAccess { record, selector, .. }
                                if selector.as_pretty_name() == "fields"
                                    && expr_matches_named_var_identity(
                                        record.as_ref(),
                                        subject_name,
                                        subject_id,
                                    )
                        ) =>
                {
                    Some("payload".to_string())
                }
                _ => None,
            })
        }
        _ => None,
    }
}

pub(super) fn expr_matches_named_var_identity(
    expr: &PseudoExpr,
    expected_name: &str,
    expected_id: Option<VarId>,
) -> bool {
    expr_matches_named_var_identity_with_consistency(expr, expected_name, expected_id, None)
}

pub(super) fn expr_matches_binder_identity(expr: &PseudoExpr, binder: &Binder) -> bool {
    expr_matches_named_var_identity(expr, binder.as_str(), Some(binder.var_id()))
}

pub(super) fn expr_matches_named_var_identity_with_consistency(
    expr: &PseudoExpr,
    expected_name: &str,
    expected_id: Option<VarId>,
    consistent_ref_ids: Option<&HashSet<VarId>>,
) -> bool {
    let PseudoExpr::Var { name, id } = expr else {
        return false;
    };

    if let Some(actual_id) = id.get() {
        expected_id == Some(actual_id)
            && consistent_ref_ids
                .is_none_or(|consistent_ref_ids| consistent_ref_ids.contains(&actual_id))
    } else {
        name == expected_name
    }
}

pub(super) fn analyze_unit_check_temp_binding_with_consistency(
    value: &PseudoExpr,
    consistent_ref_ids: Option<&HashSet<VarId>>,
) -> Option<String> {
    let PseudoExpr::When {
        subject, clauses, ..
    } = value
    else {
        return None;
    };
    if clauses.is_empty()
        || !clauses
            .iter()
            .any(|clause| expr_contains_fail(&clause.body))
    {
        return None;
    }

    let stem = match subject.as_ref() {
        PseudoExpr::Var { name, id } => {
            if subject_looks_like_constructor_variant_with_consistency(
                name,
                id.get(),
                clauses,
                consistent_ref_ids,
            ) {
                Some("variant".to_string())
            } else {
                generated_name_base(name)
            }
        }
        PseudoExpr::FieldAccess { record, .. } => match record.as_ref() {
            PseudoExpr::Var { name, .. } => generated_name_base(name),
            _ => None,
        },
        _ => None,
    }?;

    if stem.is_empty() {
        None
    } else {
        Some(format!("check_{stem}"))
    }
}

pub(super) fn subject_looks_like_constructor_variant_with_consistency(
    name: &str,
    subject_id: Option<VarId>,
    clauses: &[WhenClause],
    consistent_ref_ids: Option<&HashSet<VarId>>,
) -> bool {
    if clauses.iter().any(|clause| {
        clause_contains_var_field_access_with_consistency(
            clause,
            name,
            subject_id,
            consistent_ref_ids,
        )
    }) {
        return true;
    }

    (is_temporary_helper_name(name) || is_generic_name(name))
        && clauses.iter().all(|clause| {
            matches!(
                clause.pattern,
                WhenPattern::Constructor { .. } | WhenPattern::Wildcard
            )
        })
}

pub(super) fn clause_contains_var_field_access_with_consistency(
    clause: &WhenClause,
    var_name: &str,
    var_id: Option<VarId>,
    consistent_ref_ids: Option<&HashSet<VarId>>,
) -> bool {
    clause.guard.as_ref().is_some_and(|guard| {
        expr_contains_var_field_access_with_consistency(guard, var_name, var_id, consistent_ref_ids)
    }) || expr_contains_var_field_access_with_consistency(
        &clause.body,
        var_name,
        var_id,
        consistent_ref_ids,
    )
}

pub(super) fn expr_contains_var_field_access_with_consistency(
    expr: &PseudoExpr,
    var_name: &str,
    var_id: Option<VarId>,
    consistent_ref_ids: Option<&HashSet<VarId>>,
) -> bool {
    match expr {
        PseudoExpr::FieldAccess { record, .. } => {
            expr_matches_named_var_identity_with_consistency(
                record.as_ref(),
                var_name,
                var_id,
                consistent_ref_ids,
            ) || expr_contains_var_field_access_with_consistency(
                record,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }
        PseudoExpr::IndexAccess { collection, .. } => {
            expr_matches_named_var_identity_with_consistency(
                collection.as_ref(),
                var_name,
                var_id,
                consistent_ref_ids,
            ) || expr_contains_var_field_access_with_consistency(
                collection,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }
        PseudoExpr::Let { value, body, .. } => {
            expr_contains_var_field_access_with_consistency(
                value,
                var_name,
                var_id,
                consistent_ref_ids,
            ) || expr_contains_var_field_access_with_consistency(
                body,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }
        PseudoExpr::Apply { function, args } => {
            expr_contains_var_field_access_with_consistency(
                function,
                var_name,
                var_id,
                consistent_ref_ids,
            ) || args.iter().any(|arg| {
                expr_contains_var_field_access_with_consistency(
                    arg,
                    var_name,
                    var_id,
                    consistent_ref_ids,
                )
            })
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expr_contains_var_field_access_with_consistency(
                condition,
                var_name,
                var_id,
                consistent_ref_ids,
            ) || expr_contains_var_field_access_with_consistency(
                then_branch,
                var_name,
                var_id,
                consistent_ref_ids,
            ) || expr_contains_var_field_access_with_consistency(
                else_branch,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            expr_contains_var_field_access_with_consistency(
                subject,
                var_name,
                var_id,
                consistent_ref_ids,
            ) || clauses.iter().any(|clause| {
                clause.guard.as_ref().is_some_and(|guard| {
                    expr_contains_var_field_access_with_consistency(
                        guard,
                        var_name,
                        var_id,
                        consistent_ref_ids,
                    )
                }) || expr_contains_var_field_access_with_consistency(
                    &clause.body,
                    var_name,
                    var_id,
                    consistent_ref_ids,
                )
            })
        }
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
            expr_contains_var_field_access_with_consistency(
                body,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }
        PseudoExpr::BinOp { left, right, .. } => {
            expr_contains_var_field_access_with_consistency(
                left,
                var_name,
                var_id,
                consistent_ref_ids,
            ) || expr_contains_var_field_access_with_consistency(
                right,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }
        PseudoExpr::UnOp { operand, .. } => expr_contains_var_field_access_with_consistency(
            operand,
            var_name,
            var_id,
            consistent_ref_ids,
        ),
        PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => {
            expr_contains_var_field_access_with_consistency(
                inner,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }
        PseudoExpr::Trace { message, value } => {
            expr_contains_var_field_access_with_consistency(
                message,
                var_name,
                var_id,
                consistent_ref_ids,
            ) || expr_contains_var_field_access_with_consistency(
                value,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }
        PseudoExpr::List { elements, tail } => {
            elements.iter().any(|element| {
                expr_contains_var_field_access_with_consistency(
                    element,
                    var_name,
                    var_id,
                    consistent_ref_ids,
                )
            }) || tail.as_ref().is_some_and(|tail| {
                expr_contains_var_field_access_with_consistency(
                    tail,
                    var_name,
                    var_id,
                    consistent_ref_ids,
                )
            })
        }
        PseudoExpr::Tuple(elements) => elements.iter().any(|element| {
            expr_contains_var_field_access_with_consistency(
                element,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }),
        PseudoExpr::Pair(a, b) => {
            expr_contains_var_field_access_with_consistency(a, var_name, var_id, consistent_ref_ids)
                || expr_contains_var_field_access_with_consistency(
                    b,
                    var_name,
                    var_id,
                    consistent_ref_ids,
                )
        }
        PseudoExpr::Constr { fields, .. } => fields.iter().any(|field| {
            expr_contains_var_field_access_with_consistency(
                field,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }),
        PseudoExpr::BuiltinCall { args, .. } => args.iter().any(|arg| {
            expr_contains_var_field_access_with_consistency(
                arg,
                var_name,
                var_id,
                consistent_ref_ids,
            )
        }),
        _ => false,
    }
}

pub(super) fn analyze_arithmetic_temp_binding(value: &PseudoExpr) -> Option<String> {
    let PseudoExpr::BinOp { op, left, right } = value else {
        return None;
    };

    match op {
        BinaryOp::Add => {
            if matches!(left.as_ref(), PseudoExpr::Int(n) if *n == 1.into())
                || matches!(right.as_ref(), PseudoExpr::Int(n) if *n == 1.into())
            {
                Some("count".to_string())
            } else {
                Some("sum".to_string())
            }
        }
        _ => None,
    }
}

pub(super) fn analyze_extractor_temp_binding(value: &PseudoExpr) -> Option<String> {
    let PseudoExpr::BuiltinCall { name, args } = value else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }

    let stem = extractor_source_stem(&args[0]);
    let hint = if DATA_BYTES_EXTRACTORS
        .iter()
        .any(|builtin| *name == *builtin)
    {
        stem.map(|stem| format!("{stem}_bytes"))
            .unwrap_or_else(|| "bytes".to_string())
    } else if DATA_INT_EXTRACTORS.iter().any(|builtin| *name == *builtin) {
        stem.map(|stem| format!("{stem}_int"))
            .unwrap_or_else(|| "int_value".to_string())
    } else if DATA_MAP_EXTRACTORS.iter().any(|builtin| *name == *builtin) {
        stem.map(|stem| format!("{stem}_pairs"))
            .unwrap_or_else(|| "pairs".to_string())
    } else if DATA_LIST_EXTRACTORS.iter().any(|builtin| *name == *builtin) {
        stem.map(|stem| format!("{stem}_items"))
            .unwrap_or_else(|| "items".to_string())
    } else {
        return None;
    };

    Some(sanitize_hint_stem(&hint))
}

pub(super) fn analyze_option_wrapper_temp_binding(value: &PseudoExpr) -> Option<String> {
    let some_branch = match value {
        PseudoExpr::If {
            then_branch,
            else_branch,
            ..
        } => option_wrapper_some_branch(then_branch, else_branch)?,
        PseudoExpr::When { clauses, .. } if clauses.len() == 2 => {
            let first = &clauses[0].body;
            let second = &clauses[1].body;
            option_wrapper_some_branch(first, second)?
        }
        _ => return None,
    };

    let some_fields = extract_standard_option_some_fields(some_branch)?;
    let [payload] = some_fields.as_slice() else {
        return None;
    };

    let stem = match payload {
        PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::DataInt => {
            "int".to_string()
        }
        PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::DataMap => {
            "map".to_string()
        }
        PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::DataList => {
            "list".to_string()
        }
        PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::DataByteArray => {
            "bytes".to_string()
        }
        PseudoExpr::Var { name, .. } => sanitize_hint_stem(name),
        PseudoExpr::Apply { function, .. } => match function.as_ref() {
            PseudoExpr::Var { name, .. } => sanitize_hint_stem(name),
            _ => return None,
        },
        _ => return None,
    };

    if stem.is_empty() {
        return None;
    }

    Some(format!("{stem}_option"))
}

pub(super) fn option_wrapper_some_branch<'a>(
    first: &'a PseudoExpr,
    second: &'a PseudoExpr,
) -> Option<&'a PseudoExpr> {
    if is_standard_option_none_candidate(first) || is_bool_false_like(first) {
        return Some(second);
    }
    if is_standard_option_none_candidate(second) || is_bool_false_like(second) {
        return Some(first);
    }
    None
}

pub(super) fn extractor_source_stem(expr: &PseudoExpr) -> Option<String> {
    use crate::decompile::simplify::postprocess::ContextField;

    match expr {
        PseudoExpr::Var { name, .. }
            if !is_generic_name(name) && !is_temporary_helper_name(name) =>
        {
            Some(sanitize_hint_stem(name))
        }
        PseudoExpr::FieldAccess { selector, .. }
            if selector.is_pair_fst() || selector.is_pair_snd() =>
        {
            Some(selector.as_pretty_name().to_string())
        }
        PseudoExpr::FieldAccess { selector, .. } => {
            let field_name = selector.as_pretty_name();
            if ContextField::from_display_name(field_name).is_some() {
                Some(field_name.to_string())
            } else {
                None
            }
        }
        _ => None,
    }
}

pub(super) fn analyze_value_binding_with_known_renames(
    name: &str,
    value: &PseudoExpr,
    rename_map: &HashMap<String, String>,
) -> Option<String> {
    if !is_generic_name(name) && !is_temporary_helper_name(name) {
        return None;
    }

    let fn_name = applied_function_name_for_result_hint(value)?;
    if fn_name.starts_with("expect!") {
        return None;
    }

    let resolved_name = rename_map
        .get(fn_name)
        .map(String::as_str)
        .unwrap_or(fn_name);
    if resolved_name == fn_name && is_generic_name(fn_name) {
        return None;
    }

    Some(format!("{}_result", sanitize_hint_stem(resolved_name)))
}

// Peel Option wrappers (`if`/`when` to the Some-branch). Only ever one
// child is descended into per level, so this is a pointer loop.
pub(super) fn applied_function_name_for_result_hint(value: &PseudoExpr) -> Option<&str> {
    let mut current = value;
    loop {
        match current {
            PseudoExpr::Apply { function, .. } => {
                return match function.as_ref() {
                    PseudoExpr::Var { name, .. } => Some(name.as_str()),
                    _ => None,
                };
            }
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                current = option_wrapper_some_branch(then_branch, else_branch)?;
            }
            PseudoExpr::When { clauses, .. } if clauses.len() == 2 => {
                current = option_wrapper_some_branch(&clauses[0].body, &clauses[1].body)?;
            }
            _ => return None,
        }
    }
}
