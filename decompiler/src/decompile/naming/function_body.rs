//! Naming a function from its BODY: what the helper does, and what its
//! parameters should therefore be called.
//!
//! Covers plain helpers, rec-fns, the forwarded-wrapper indirection, and
//! the `when`-clause / constructor-pattern binder hints.

use super::*;

/// Analyze a function body to generate a descriptive name hint.
pub(super) fn analyze_function_body(
    name: &str,
    body: &PseudoExpr,
    param_count: usize,
) -> Option<String> {
    // Strategy 1: Boolean negation pattern
    if is_boolean_negation(body) {
        return Some("not".to_string());
    }

    // Strategy 2: Check for trace messages in body
    if let Some(hint) = hint_from_trace_messages(body) {
        return Some(hint);
    }

    // Strategy 3: Single when-expression body analysis
    if let Some(hint) = analyze_when_body(body, param_count) {
        return Some(hint);
    }

    // Strategy 4: let-wrapped recursive list helpers
    if let Some(hint) = analyze_list_rec_wrapper(body) {
        return Some(hint);
    }

    // Strategy 5: let-wrapped folds over map data
    if let Some(hint) = analyze_map_fold_wrapper(body) {
        return Some(hint);
    }

    // Strategy 6: let-wrapped nested map lookup wrappers
    if let Some(hint) = analyze_nested_map_lookup_wrapper(body) {
        return Some(hint);
    }

    // Strategy 7: two-level nested lookup wrappers returning an Int payload
    if let Some(hint) = analyze_nested_lookup_int_wrapper(body) {
        return Some(hint);
    }

    // Strategy 8: thin list-membership wrappers over any-like helpers
    if let Some(hint) = analyze_contains_wrapper(body) {
        return Some(hint);
    }

    // Strategy 9: thin any-like wrappers over data lists
    if let Some(hint) = analyze_any_data_list_wrapper(body) {
        return Some(hint);
    }

    // Strategy 10: expect Constr<0> + simple extraction
    if let Some(hint) = analyze_expect_extract(body) {
        return Some(hint);
    }

    // Strategy 11: expect Constr<0> + identity (validation)
    if is_expect_identity(body) {
        if name.contains("13") || name.contains("datum") {
            return Some("validate_datum".to_string());
        }
        if name.contains("14") || name.contains("redeemer") {
            return Some("validate_redeemer".to_string());
        }
        return Some("validate_constr".to_string());
    }

    // Strategy 12: Simple equality / comparison
    if is_simple_equality(body) {
        if body_contains_builtin(body, "equals_byte_string")
            || body_references_type(body, "ByteArray")
        {
            return Some("eq_bytes".to_string());
        }
        if body_contains_builtin(body, "equals_integer") {
            return Some("eq_int".to_string());
        }
        return Some("eq".to_string());
    }

    // Strategy 13: Simple less-than comparison
    if is_simple_less_than(body) {
        return Some("lt_int".to_string());
    }

    // Strategy 14: Other simple integer arithmetic/comparison helpers
    if let Some(hint) = analyze_simple_int_helper(body) {
        return Some(hint);
    }

    // Strategy 15: Pair construction / Constr<1> wrapper
    if is_constr_wrapper(body, 1) {
        return Some("cons_pair".to_string());
    }

    // Strategy 16: CPS membership check
    if param_count == 2 && is_cps_membership_check(body) {
        return Some("check_member".to_string());
    }

    None
}

/// Check if body matches the CPS membership shape
/// `f(fn(x) { g(fn(y) { x == y }, ...) }, ...)`, where
/// `f` and `g` are meant to be the two params — only the
/// shape is checked.
pub(super) fn is_cps_membership_check(body: &PseudoExpr) -> bool {
    let PseudoExpr::Apply { function: _, args } = body else {
        return false;
    };
    if args.is_empty() {
        return false;
    }
    let PseudoExpr::Lambda {
        params,
        body: lambda_body,
    } = &args[0]
    else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let PseudoExpr::Apply {
        args: inner_args, ..
    } = lambda_body.as_ref()
    else {
        return false;
    };
    if inner_args.is_empty() {
        return false;
    }
    matches!(
        &inner_args[0],
        PseudoExpr::Lambda { params: eq_params, body: eq_body }
            if eq_params.len() == 1
                && matches!(eq_body.as_ref(), PseudoExpr::BinOp { op: BinaryOp::Eq, .. })
    )
}

pub(super) fn analyze_rec_function_body(
    name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<String> {
    analyze_list_rec_behavior(name, rec_id, params, body)
        .or_else(|| analyze_bool_collapsed_list_rec_behavior(name, rec_id, params, body))
        .or_else(|| analyze_if_empty_list_rec_behavior(name, rec_id, params, body))
        .or_else(|| analyze_single_param_list_rec(name, rec_id, params, body))
        .or_else(|| analyze_list_index_rec_behavior(name, rec_id, params, body))
        .or_else(|| analyze_assoc_lookup_rec_behavior(name, rec_id, params, body))
        .or_else(|| analyze_assoc_lookup_then_rec_behavior(name, rec_id, params, body))
        .or_else(|| analyze_function_body(name, body, params.len()))
}

pub(super) fn analyze_rec_function_param_hints<'a>(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &'a [crate::pseudo::ast::Binder],
    body: &'a PseudoExpr,
) -> Vec<(&'a crate::pseudo::ast::Binder, &'static str)> {
    let direct_body = unwrap_lets(body);

    analyze_bool_collapsed_list_rec_param_hints(rec_name, rec_id, params, direct_body)
        .or_else(|| analyze_list_index_param_hints(rec_name, rec_id, params, direct_body))
        .or_else(|| analyze_assoc_lookup_param_hints(params, direct_body))
        .or_else(|| analyze_if_empty_list_rec_param_hints(rec_name, rec_id, params, direct_body))
        .or_else(|| analyze_list_accumulator_param_hints(rec_name, rec_id, params, direct_body))
        .or_else(|| {
            analyze_single_param_list_rec_param_hints(rec_name, rec_id, params, direct_body)
        })
        .or_else(|| analyze_forwarded_rec_wrapper_param_hints(params, body))
        .unwrap_or_default()
}

pub(super) fn analyze_bool_collapsed_list_rec_behavior(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<String> {
    if params.len() != 2 {
        return None;
    }

    for list_idx in 0..params.len() {
        let list_param = &params[list_idx];
        let pred_param = &params[1 - list_idx];

        if is_collapsed_all_list_body(
            body, rec_name, rec_id, params, list_idx, pred_param, list_param,
        ) {
            return Some("all".to_string());
        }

        if is_collapsed_any_list_body(
            body, rec_name, rec_id, params, list_idx, pred_param, list_param,
        ) {
            return Some("any".to_string());
        }
    }

    None
}

pub(super) fn analyze_bool_collapsed_list_rec_param_hints<'a>(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &'a [crate::pseudo::ast::Binder],
    body: &'a PseudoExpr,
) -> Option<Vec<(&'a crate::pseudo::ast::Binder, &'static str)>> {
    if params.len() != 2 {
        return None;
    }

    for list_idx in 0..params.len() {
        let list_param = &params[list_idx];
        let pred_param = &params[1 - list_idx];

        if is_collapsed_all_list_body(
            body, rec_name, rec_id, params, list_idx, pred_param, list_param,
        ) || is_collapsed_any_list_body(
            body, rec_name, rec_id, params, list_idx, pred_param, list_param,
        ) {
            return Some(vec![(list_param, "list"), (pred_param, "predicate")]);
        }
    }

    None
}

pub(super) fn analyze_forwarded_rec_wrapper_param_hints<'a>(
    params: &'a [crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<Vec<(&'a crate::pseudo::ast::Binder, &'static str)>> {
    let PseudoExpr::Let {
        name: helper_name,
        value,
        body: call_body,
        ..
    } = body
    else {
        return None;
    };

    let PseudoExpr::RecFn {
        name: inner_name,
        params: inner_params,
        body: inner_body,
    } = value.as_ref()
    else {
        return None;
    };
    if inner_name.as_str() != helper_name {
        return None;
    }

    let PseudoExpr::Apply { function, args } = call_body.as_ref() else {
        return None;
    };
    if !matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == helper_name)
        || args.len() != inner_params.len()
    {
        return None;
    }

    let inner_hints = analyze_rec_function_param_hints(
        inner_name.as_str(),
        Some(inner_name.var_id()),
        inner_params,
        inner_body,
    );
    if inner_hints.is_empty() {
        return None;
    }

    let mut outer_hints = Vec::new();
    for (inner_binder, hint) in inner_hints {
        let inner_index = inner_params
            .iter()
            .position(|binder| binder.id == inner_binder.id)?;
        let outer_binder = match &args[inner_index] {
            PseudoExpr::Var { name, id, .. } => params
                .iter()
                .find(|binder| Some(binder.id) == *id)
                .or_else(|| {
                    id.get()
                        .is_none()
                        .then(|| params.iter().find(|binder| binder.as_str() == name))
                        .flatten()
                }),
            _ => None,
        }?;
        outer_hints.push((outer_binder, hint));
    }

    if outer_hints.is_empty() {
        None
    } else {
        Some(outer_hints)
    }
}

pub(super) fn analyze_lambda_param_hints<'a>(
    params: &'a [crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Vec<(&'a crate::pseudo::ast::Binder, &'static str)> {
    analyze_nested_lookup_int_param_hints(params, body).unwrap_or_default()
}

pub(super) fn analyze_when_clause_pattern_hints<'a>(
    subject: &PseudoExpr,
    clause: &'a WhenClause,
) -> Vec<(&'a Binder, String)> {
    let WhenPattern::Constructor { fields, shape, .. } = &clause.pattern else {
        return Vec::new();
    };

    let is_some_pattern = matches!(shape, ConstructorShape::Known(KnownConstructor::Some));

    // Read `semantic_name()` (mint-time, stable) so the recognizer
    // fires regardless of any display-side disambiguation suffix
    // applied by helper/hoist or other passes.
    fields
        .iter()
        .filter(|binder| is_pattern_hint_candidate_name(binder.semantic_name()))
        .filter_map(|binder| {
            analyze_constructor_pattern_binder_hint(subject, clause, is_some_pattern, binder)
                .map(|hint| (binder, hint))
        })
        .collect()
}

pub(super) fn analyze_constructor_pattern_binder_hint(
    subject: &PseudoExpr,
    clause: &WhenClause,
    is_some_pattern: bool,
    binder: &Binder,
) -> Option<String> {
    if is_some_pattern && let Some(hint) = option_payload_subject_hint(subject) {
        return Some(hint.to_string());
    }

    if clause_contains_builtin_call_on_var(
        clause,
        DATA_MAP_EXTRACTORS,
        binder.as_str(),
        Some(binder.var_id()),
    ) {
        return Some("map".to_string());
    }
    if clause_contains_builtin_call_on_var(
        clause,
        DATA_LIST_EXTRACTORS,
        binder.as_str(),
        Some(binder.var_id()),
    ) {
        return Some("items".to_string());
    }
    if clause_contains_builtin_call_on_var(
        clause,
        DATA_BYTES_EXTRACTORS,
        binder.as_str(),
        Some(binder.var_id()),
    ) {
        return Some("bytes".to_string());
    }
    if clause_contains_builtin_call_on_var(
        clause,
        DATA_INT_EXTRACTORS,
        binder.as_str(),
        Some(binder.var_id()),
    ) {
        return Some("int_value".to_string());
    }
    if clause_uses_var_as_when_subject(clause, binder.as_str(), Some(binder.var_id())) {
        return Some("variant".to_string());
    }
    if clause_contains_var_comparison(clause, binder.as_str(), Some(binder.var_id())) {
        return Some("value".to_string());
    }
    if clause_contains_var_field_access(clause, binder.as_str(), Some(binder.var_id())) {
        return Some("payload".to_string());
    }
    if is_some_pattern {
        return Some("payload".to_string());
    }

    None
}

pub(super) fn option_payload_subject_hint(subject: &PseudoExpr) -> Option<&'static str> {
    match subject {
        PseudoExpr::Apply { function, .. } => match function.as_ref() {
            PseudoExpr::Var { name, .. } if name == "get_at" => Some("item"),
            PseudoExpr::Var { name, .. } if name.starts_with("lookup") => Some("value"),
            _ => None,
        },
        PseudoExpr::Var { name, .. } if name.starts_with("get_at_result") => Some("item"),
        PseudoExpr::Var { name, .. } if name.contains("lookup_result") => Some("value"),
        _ => None,
    }
}

pub(super) fn analyze_list_rec_wrapper(body: &PseudoExpr) -> Option<String> {
    let PseudoExpr::Let {
        name: rec_name,
        value,
        body: call_body,
        ..
    } = body
    else {
        return None;
    };

    let PseudoExpr::RecFn {
        name: inner_name,
        params,
        body: rec_body,
    } = value.as_ref()
    else {
        return None;
    };
    if inner_name.as_str() != rec_name {
        return None;
    }

    let PseudoExpr::Apply { function, args } = call_body.as_ref() else {
        return None;
    };
    if !expr_matches_named_var_identity(
        function.as_ref(),
        inner_name.as_str(),
        Some(inner_name.var_id()),
    ) || args.len() != params.len()
    {
        return None;
    }

    analyze_list_rec_behavior(
        inner_name.as_str(),
        Some(inner_name.var_id()),
        params,
        rec_body,
    )
    .or_else(|| {
        analyze_list_index_rec_behavior(
            inner_name.as_str(),
            Some(inner_name.var_id()),
            params,
            rec_body,
        )
    })
}

pub(super) fn analyze_contains_wrapper(body: &PseudoExpr) -> Option<String> {
    let PseudoExpr::Apply { args, .. } = body else {
        return None;
    };
    if args.len() != 2 || !body_contains_any_builtin_call(&args[0], DATA_LIST_EXTRACTORS) {
        return None;
    }

    let PseudoExpr::Lambda { params, body } = &args[1] else {
        return None;
    };
    let [item_param] = params.as_slice() else {
        return None;
    };

    if is_lambda_param_equality_predicate(body, item_param) {
        Some("contains".to_string())
    } else {
        None
    }
}

pub(super) fn analyze_any_data_list_wrapper(body: &PseudoExpr) -> Option<String> {
    let PseudoExpr::Apply { args, .. } = body else {
        return None;
    };
    if args.len() != 2 || !body_contains_any_builtin_call(&args[0], DATA_LIST_EXTRACTORS) {
        return None;
    }

    if matches!(&args[1], PseudoExpr::Var { .. }) {
        Some("any_data_list".to_string())
    } else {
        None
    }
}
