//! Fold / map recognition, and the nested-lookup wrappers built on it.
//!
//! A compiled `list.foldr`/`list.map` arrives as a rec-fn plus an
//! adapter lambda. `collect_fold_rec_candidates` indexes the rec-fns
//! that could be one; the `analyze_map_fold_*` pair confirms a candidate
//! against its call site before naming either.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct FoldRecCandidateKey {
    name: String,
    id: Option<VarId>,
}

impl FoldRecCandidateKey {
    fn new(name: &str, id: Option<VarId>) -> Self {
        Self {
            name: name.to_string(),
            id,
        }
    }
}

pub(super) fn collect_fold_rec_candidates(expr: &PseudoExpr) -> HashSet<FoldRecCandidateKey> {
    struct FoldRecCandidateVisitor {
        candidates: HashSet<FoldRecCandidateKey>,
    }

    impl FoldRecCandidateVisitor {
        fn record_if_fold_rec(
            &mut self,
            let_name: Option<(&str, VarId)>,
            rec_name: &Binder,
            params: &[Binder],
            rec_body: &PseudoExpr,
        ) {
            if !fold_rec_body_matches(rec_name.as_str(), Some(rec_name.var_id()), params, rec_body)
            {
                return;
            }

            self.candidates.insert(FoldRecCandidateKey::new(
                rec_name.as_str(),
                Some(rec_name.var_id()),
            ));
            if let Some((let_name, let_id)) = let_name {
                self.candidates
                    .insert(FoldRecCandidateKey::new(let_name, Some(let_id)));
            }
        }
    }

    impl ExprVisitor for FoldRecCandidateVisitor {
        fn visit_let(
            &mut self,
            name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            if let PseudoExpr::RecFn {
                name: rec_name,
                params,
                body,
            } = value
            {
                if let Some(vid) = *id {
                    self.record_if_fold_rec(Some((name, vid)), rec_name, params, body);
                } else {
                    self.record_if_fold_rec(None, rec_name, params, body);
                }
            }
        }

        fn visit_recfn(&mut self, name: &Binder, params: &[Binder], body: &PseudoExpr) {
            self.record_if_fold_rec(None, name, params, body);
        }
    }

    let mut visitor = FoldRecCandidateVisitor {
        candidates: HashSet::new(),
    };
    visitor.walk(expr);
    visitor.candidates
}

pub(super) fn fold_rec_candidates_match(
    fold_rec_candidates: &HashSet<FoldRecCandidateKey>,
    function: &PseudoExpr,
) -> bool {
    let PseudoExpr::Var { name, id } = function else {
        return false;
    };
    if !is_generic_name(name) && !is_temporary_helper_name(name) {
        return false;
    }
    let id = id.get();
    fold_rec_candidates.iter().any(|candidate| {
        candidate.name == *name && (id.is_none() || candidate.id.is_none() || candidate.id == id)
    })
}

pub(super) fn analyze_map_fold_forwarder(
    params: &[Binder],
    body: &PseudoExpr,
    fold_rec_candidates: &HashSet<FoldRecCandidateKey>,
) -> Option<String> {
    let [map_param, step_param, init_param] = params else {
        return None;
    };

    let PseudoExpr::Apply { function, args } = body else {
        return None;
    };
    if args.len() != 3
        || !fold_rec_candidates_match(fold_rec_candidates, function)
        || !map_fold_arg_extracts_map_param(&args[0], map_param)
        || !fold_map_adapter_lambda_calls_step(&args[1], step_param)
        || !expr_matches_binder_identity(&args[2], init_param)
    {
        return None;
    }

    Some("fold_map".to_string())
}

pub(super) fn map_fold_arg_extracts_map_param(expr: &PseudoExpr, map_param: &Binder) -> bool {
    matches!(
        expr,
        PseudoExpr::BuiltinCall { name, args }
            if DATA_MAP_EXTRACTORS.contains(&name.as_str())
                && args.len() == 1
                && expr_matches_binder_identity(&args[0], map_param)
    )
}

pub(super) fn fold_map_adapter_lambda_calls_step(expr: &PseudoExpr, step_param: &Binder) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    let [acc_param, entry_param] = params.as_slice() else {
        return false;
    };
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        return false;
    };

    expr_matches_binder_identity(function.as_ref(), step_param)
        && args.len() == 3
        && expr_matches_binder_identity(&args[0], acc_param)
        && is_pair_fst_access(&args[1], entry_param.as_str(), Some(entry_param.var_id()))
        && is_pair_snd_access(&args[2], entry_param.as_str(), Some(entry_param.var_id()))
}

pub(super) fn analyze_map_fold_wrapper(body: &PseudoExpr) -> Option<String> {
    let PseudoExpr::Let {
        name: rec_name,
        id: rec_id,
        value,
        body: call_body,
        ..
    } = body
    else {
        return None;
    };
    let rec_id = (*rec_id)?;

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

    if !fold_rec_body_matches(
        inner_name.as_str(),
        Some(inner_name.var_id()),
        params,
        rec_body,
    ) {
        return None;
    }

    let PseudoExpr::Apply { function, args } = call_body.as_ref() else {
        return None;
    };
    let calls_rec_fn =
        expr_matches_named_var_identity(
            function.as_ref(),
            inner_name.as_str(),
            Some(inner_name.var_id()),
        ) || expr_matches_named_var_identity(function.as_ref(), rec_name, Some(rec_id));
    if !calls_rec_fn || args.len() != 3 {
        return None;
    }

    if body_contains_any_builtin_call(&args[0], DATA_MAP_EXTRACTORS) {
        Some("fold_map".to_string())
    } else {
        None
    }
}

pub(super) fn fold_rec_body_matches(
    rec_name: &str,
    rec_id: Option<VarId>,
    params: &[Binder],
    rec_body: &PseudoExpr,
) -> bool {
    let [list_param, step_param, acc_param] = params else {
        return false;
    };

    let PseudoExpr::When {
        subject, clauses, ..
    } = rec_body
    else {
        return false;
    };
    if !expr_matches_binder_identity(subject.as_ref(), list_param) || clauses.len() != 2 {
        return false;
    }

    let Some(empty_clause) = clauses.iter().find(|c| {
        matches!(
            c.pattern,
            WhenPattern::List {
                ref elements,
                tail: None
            } if elements.is_empty()
        )
    }) else {
        return false;
    };
    if !expr_matches_binder_identity(&empty_clause.body, acc_param) {
        return false;
    }

    let Some((head_binder, tail_binder, cons_body)) =
        clauses.iter().find_map(|c| match &c.pattern {
            WhenPattern::List {
                elements,
                tail: Some(tail),
            } if elements.len() == 1 => Some((&elements[0], tail, &c.body)),
            _ => None,
        })
    else {
        return false;
    };

    let PseudoExpr::Apply { function, args } = cons_body else {
        return false;
    };
    if !expr_matches_named_var_identity(function.as_ref(), rec_name, rec_id)
        || args.len() != 3
        || !expr_matches_binder_identity(&args[0], tail_binder)
        || !expr_matches_binder_identity(&args[1], step_param)
    {
        return false;
    }

    let PseudoExpr::Apply { function, args } = &args[2] else {
        return false;
    };
    if !expr_matches_binder_identity(function.as_ref(), step_param)
        || args.len() != 2
        || !expr_matches_binder_identity(&args[0], acc_param)
        || !expr_matches_binder_identity(&args[1], head_binder)
    {
        return false;
    }

    true
}

pub(super) fn analyze_nested_map_lookup_wrapper(body: &PseudoExpr) -> Option<String> {
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
    if inner_name.as_str() != rec_name
        || analyze_assoc_lookup_then_rec_behavior(
            inner_name.as_str(),
            Some(inner_name.var_id()),
            params,
            rec_body,
        )
        .is_none()
    {
        return None;
    }

    let PseudoExpr::Apply { function, args } = call_body.as_ref() else {
        return None;
    };
    if !expr_matches_named_var_identity(
        function.as_ref(),
        inner_name.as_str(),
        Some(inner_name.var_id()),
    ) || args.len() != 2
    {
        return None;
    }

    let PseudoExpr::Lambda {
        params: lambda_params,
        body: lambda_body,
    } = &args[0]
    else {
        return None;
    };
    if !is_self_applied_lookup_lambda(lambda_params, lambda_body)
        || !body_contains_any_builtin_call(&args[1], DATA_MAP_EXTRACTORS)
    {
        return None;
    }

    Some("lookup_nested_map".to_string())
}

pub(super) fn analyze_nested_lookup_int_wrapper(body: &PseudoExpr) -> Option<String> {
    if is_nested_lookup_int_wrapper(body) {
        Some("lookup_nested_int".to_string())
    } else {
        None
    }
}

pub(super) fn analyze_nested_lookup_int_param_hints<'a>(
    params: &'a [crate::pseudo::ast::Binder],
    body: &PseudoExpr,
) -> Option<Vec<(&'a crate::pseudo::ast::Binder, &'static str)>> {
    let [pairs_param, needle_param, nested_needle_param] = params else {
        return None;
    };

    if is_nested_lookup_int_wrapper(body) {
        Some(vec![
            (pairs_param, "pairs"),
            (needle_param, "needle"),
            (nested_needle_param, "nested_needle"),
        ])
    } else {
        None
    }
}

pub(super) fn is_nested_lookup_int_wrapper(body: &PseudoExpr) -> bool {
    let PseudoExpr::Let {
        name: first_lookup_result,
        id: Some(first_lookup_result_id),
        value: first_lookup_value,
        body: after_first_lookup,
        ..
    } = body
    else {
        return false;
    };
    if !matches!(
        first_lookup_value.as_ref(),
        PseudoExpr::Apply { function, args }
            if matches!(function.as_ref(), PseudoExpr::Var { .. }) && args.len() == 2
    ) {
        return false;
    }

    let PseudoExpr::Let {
        name: inner_lookup_name,
        id: Some(inner_lookup_id),
        value: inner_lookup_value,
        body: after_inner_lookup,
        ..
    } = after_first_lookup.as_ref()
    else {
        return false;
    };
    let PseudoExpr::RecFn {
        name: rec_name,
        params,
        body: rec_body,
    } = inner_lookup_value.as_ref()
    else {
        return false;
    };
    if rec_name.as_str() != inner_lookup_name
        || analyze_rec_function_body(rec_name.as_str(), Some(rec_name.var_id()), params, rec_body)
            .as_deref()
            != Some("lookup")
    {
        return false;
    }

    let PseudoExpr::Let {
        name: nested_result_name,
        id: Some(nested_result_id),
        value: nested_result_value,
        body: final_body,
        ..
    } = after_inner_lookup.as_ref()
    else {
        return false;
    };

    is_nested_lookup_option_bridge(
        nested_result_value,
        first_lookup_result.as_str(),
        Some(*first_lookup_result_id),
        inner_lookup_name.as_str(),
        Some(*inner_lookup_id),
    ) && is_nested_lookup_int_finish(
        final_body,
        nested_result_name.as_str(),
        Some(*nested_result_id),
    )
}

pub(super) fn is_nested_lookup_option_bridge(
    expr: &PseudoExpr,
    first_lookup_result: &str,
    first_lookup_result_id: Option<VarId>,
    inner_lookup_name: &str,
    inner_lookup_id: Option<VarId>,
) -> bool {
    let PseudoExpr::When {
        subject, clauses, ..
    } = expr
    else {
        return false;
    };
    if !expr_matches_named_var_identity(
        subject.as_ref(),
        first_lookup_result,
        first_lookup_result_id,
    ) || clauses.len() != 2
    {
        return false;
    }

    let Some(_none_clause) = clauses
        .iter()
        .find(|clause| is_naming_none_like(&clause.body))
    else {
        return false;
    };
    let Some(some_clause) = clauses
        .iter()
        .find(|clause| !is_naming_none_like(&clause.body))
    else {
        return false;
    };

    is_nested_lookup_some_bridge_call(&some_clause.body, inner_lookup_name, inner_lookup_id)
}

pub(super) fn is_nested_lookup_some_bridge_call(
    expr: &PseudoExpr,
    inner_lookup_name: &str,
    inner_lookup_id: Option<VarId>,
) -> bool {
    matches!(
        expr,
        PseudoExpr::Apply { function, args }
            if expr_matches_named_var_identity(
                function.as_ref(),
                inner_lookup_name,
                inner_lookup_id,
            )
                && args.len() == 1
                && matches!(
                    &args[0],
                    PseudoExpr::BuiltinCall { name, args }
                        if DATA_MAP_EXTRACTORS.contains(&name.as_str())
                            && args.len() == 1
                            && is_zero_payload_access(&args[0])
                )
    )
}

pub(super) fn is_nested_lookup_int_finish(
    expr: &PseudoExpr,
    nested_result_name: &str,
    nested_result_id: Option<VarId>,
) -> bool {
    let PseudoExpr::When {
        subject, clauses, ..
    } = expr
    else {
        return false;
    };
    if !expr_matches_named_var_identity(subject.as_ref(), nested_result_name, nested_result_id)
        || clauses.len() != 2
    {
        return false;
    }

    let Some(_zero_clause) = clauses
        .iter()
        .find(|clause| matches!(&clause.body, PseudoExpr::Int(n) if *n == 0.into()))
    else {
        return false;
    };
    let Some(value_clause) = clauses
        .iter()
        .find(|clause| !matches!(&clause.body, PseudoExpr::Int(n) if *n == 0.into()))
    else {
        return false;
    };

    matches!(
        &value_clause.body,
        PseudoExpr::BuiltinCall { name, args }
            if DATA_INT_EXTRACTORS.contains(&name.as_str())
                && args.len() == 1
                && is_zero_payload_access(&args[0])
    )
}

pub(super) fn is_zero_payload_access(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::IndexAccess { collection, index }
            if *index == 0
                && matches!(
                    collection.as_ref(),
                    PseudoExpr::FieldAccess { record, selector, .. }
                        if selector.as_pretty_name() == "fields"
                            && matches!(record.as_ref(), PseudoExpr::Var { .. })
                )
    )
}
