//! Naming from a `when` body, plus the small `expect` / integer-helper
//! recognisers that share its shape analysis.

use super::*;

/// Analyze a function whose body is a single when expression.
pub(super) fn analyze_when_body(body: &PseudoExpr, _param_count: usize) -> Option<String> {
    let inner = unwrap_lets(body);

    let (clauses, subject) = match inner {
        PseudoExpr::When {
            clauses, subject, ..
        } => (clauses, subject),
        _ => return None,
    };

    let is_expect_style = has_wildcard_fail_branch(clauses);

    // Bare-param dispatch (`when x is …`) versus a derived subject
    // (`when x.snd is …`, `when f(x) is …`): only the direct case may
    // take the `extract_policy_id` name; derived subjects get a
    // shape-honest name so the two do not collide.
    let subject_is_bare_var = matches!(subject.as_ref(), PseudoExpr::Var { .. });

    // Expect-style (single real branch + wildcard fail): extraction patterns
    if is_expect_style && has_constr0_pattern(clauses) {
        let real_branches: Vec<_> = clauses
            .iter()
            .filter(|c| !matches!(&c.pattern, WhenPattern::Wildcard) && !is_fail_body(&c.body))
            .collect();

        // Expect Constr<0> + pair construction = decode_asset_pair
        // (check before Data.to_* since pair construction may also use those)
        if real_branches.len() == 1 && is_pair_construction_in_body(&real_branches[0].body) {
            return Some("decode_asset_pair".to_string());
        }

        // `extract_*` claims the function EXTRACTS one value, so the
        // shape has to be a single live branch — a `when` with several
        // live arms is a sum DECODER, and naming it `extract_policy_id`
        // states something about the script that is not there. The
        // wildcard-fail arm alone does not make a `when` an `expect`.
        //
        // The scan is likewise limited to that branch and to what it
        // RETURNS: an unrelated `un_i_data` inside a nested lambda
        // otherwise names a pair-building function `extract_int`.
        if let [only] = real_branches.as_slice() {
            let returns_bytes = returns_builtin_call(&only.body, DATA_BYTES_EXTRACTORS);
            let returns_int = returns_builtin_call(&only.body, DATA_INT_EXTRACTORS);

            // Pure extraction to bytes
            if returns_bytes && !returns_int {
                return Some(if subject_is_bare_var {
                    "extract_policy_id".to_string()
                } else {
                    "extract_tagged_bytes".to_string()
                });
            }

            // Pure extraction to int
            if returns_int && !returns_bytes {
                return Some(if subject_is_bare_var {
                    "extract_int".to_string()
                } else {
                    "extract_tagged_int".to_string()
                });
            }

            // Mixed extraction — the branch pulls both out of the record.
            if body_contains_any_builtin_call(&only.body, DATA_BYTES_EXTRACTORS)
                && body_contains_any_builtin_call(&only.body, DATA_INT_EXTRACTORS)
            {
                return Some("extract_fields".to_string());
            }
        }
    }

    // Non-expect patterns (multiple real branches)
    let real_branch_count = clauses
        .iter()
        .filter(|c| !matches!(&c.pattern, WhenPattern::Wildcard))
        .filter(|c| !is_fail_body(&c.body))
        .count();

    // These names describe the structural pattern only: a 2-branch
    // list walk with a `Data.to_bytes` call can equally be a filter
    // over pairs, so a name from Plutus semantics would overclaim.

    // 2-branch non-expect dispatch with `Data.to_bytes` in a branch.
    if real_branch_count == 2 && has_data_to_bytes_in_branches(clauses) && !is_expect_style {
        return Some("decode_pairs_bytes".to_string());
    }

    // 2-branch walk with `Data.to_int` plus `.fst`/`.snd` access;
    // the pair access separates it from the bytes case.
    if real_branch_count == 2
        && has_data_to_int_in_branches(clauses)
        && has_pair_access_in_branches(clauses)
        && !is_expect_style
    {
        return Some("decode_pairs_int".to_string());
    }

    // 4+ branch Constr dispatch with field extraction; 7+ arms is
    // "wide", 4-6 arms "narrow".
    if real_branch_count >= 4 && has_field_extraction_in_branches(clauses) {
        if real_branch_count >= 7 {
            return Some("decode_constr_wide".to_string());
        }
        return Some("decode_constr_dispatch".to_string());
    }

    // 2-4 branch decoder with Data.to_int or Data.to_bytes
    // Only when dispatching on constructors, not iterating over lists
    let has_list_pattern = clauses
        .iter()
        .any(|c| matches!(&c.pattern, WhenPattern::List { .. }));
    if (2..=4).contains(&real_branch_count)
        && !has_list_pattern
        && (body_contains_any_builtin_call(inner, DATA_BYTES_EXTRACTORS)
            || body_contains_any_builtin_call(inner, DATA_INT_EXTRACTORS))
    {
        // `OutputDatum` is `NoDatum | DatumHash(h) | InlineDatum(d)` —
        // three arms at tags 0/1/2 with arities 0/1/1. Any other narrow
        // Constr decoder (`Credential`, `StakingCredential`, a user sum)
        // gets a shape-honest name: naming it for a ledger type the
        // script never touches misleads harder than no name at all.
        if matches_output_datum_shape(clauses) {
            return Some("decode_output_datum".to_string());
        }
        return Some("decode_constr_narrow".to_string());
    }

    None
}

/// The prelude `OutputDatum` layout: tags 0/1/2 with arities 0/1/1.
///
/// A LIVE arm that is not one of those three — a wildcard with a real
/// body, a list or literal pattern — means the subject is something
/// wider, so the layout match does not settle it. Only a failing arm is
/// ignored: that is the exhaustiveness tail, not a fourth case.
pub(super) fn matches_output_datum_shape(clauses: &[WhenClause]) -> bool {
    let mut seen: Vec<(usize, usize)> = Vec::new();
    for clause in clauses {
        match &clause.pattern {
            WhenPattern::Constructor { tag, fields, .. } => seen.push((*tag, fields.len())),
            _ if is_fail_body(&clause.body) => {}
            _ => return false,
        }
    }
    seen.sort_unstable();
    seen.dedup();
    seen == vec![(0, 0), (1, 1), (2, 1)]
}

/// Analyze expect+extract patterns like `expect Constr<0>(field_0) = x; Data.to_bytes(field_0)`
pub(super) fn analyze_expect_extract(body: &PseudoExpr) -> Option<String> {
    // Single-clause Constr<0> `when` whose branch extracts bytes or int
    if let PseudoExpr::When { clauses, .. } = body
        && clauses.len() == 1
        && has_constr0_pattern(clauses)
    {
        let branch_body = &clauses[0].body;
        if body_contains_any_builtin_call(branch_body, DATA_BYTES_EXTRACTORS) {
            return Some("extract_policy_id".to_string());
        }
        if body_contains_any_builtin_call(branch_body, DATA_INT_EXTRACTORS) {
            return Some("extract_int".to_string());
        }
    }

    // A `let` (lowered `expect`) whose body constructs a pair
    if let PseudoExpr::Let {
        body: inner_body, ..
    } = body
        && is_pair_construction(inner_body)
    {
        return Some("decode_asset_pair".to_string());
    }

    None
}

/// Check if body is `expect Constr<0> = x; fn(x) { x }` (identity after validation)
pub(super) fn is_expect_identity(body: &PseudoExpr) -> bool {
    let inner = unwrap_lets_and_whens(body);
    match inner {
        PseudoExpr::Lambda {
            params,
            body: fn_body,
        } => {
            if params.len() == 1
                && let PseudoExpr::Var { name, .. } = fn_body.as_ref()
            {
                return name == &params[0];
            }
            false
        }
        _ => false,
    }
}

/// Unwrap both Let bindings and expect-style When patterns to get inner expression.
/// Handles: single-clause When, or 2-clause When where one is wildcard/fail.
pub(super) fn unwrap_lets_and_whens(expr: &PseudoExpr) -> &PseudoExpr {
    let mut current = expr;
    loop {
        current = match current {
            PseudoExpr::Let { body, .. } => body,
            PseudoExpr::When { clauses, .. } if clauses.len() == 1 => &clauses[0].body,
            PseudoExpr::When { clauses, .. } if clauses.len() == 2 => {
                // Expect pattern: one real branch + one wildcard/fail branch
                let real_branch = clauses.iter().find(|c| {
                    !matches!(&c.pattern, WhenPattern::Wildcard) && !is_fail_body(&c.body)
                });
                let Some(branch) = real_branch else {
                    return current;
                };
                let other_is_fail = clauses.iter().any(|c| {
                    (matches!(&c.pattern, WhenPattern::Wildcard) || is_fail_body(&c.body))
                        && !std::ptr::eq(c, branch)
                });
                if !other_is_fail {
                    return current;
                }
                &branch.body
            }
            _ => return current,
        };
    }
}

/// Check if body is `x == y` (simple equality check).
pub(super) fn is_simple_equality(body: &PseudoExpr) -> bool {
    matches!(
        body,
        PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Eq,
            ..
        }
    )
}

/// Check if body is `x < y` (simple less-than check).
pub(super) fn is_simple_less_than(body: &PseudoExpr) -> bool {
    matches!(
        body,
        PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Lt,
            ..
        }
    )
}

pub(super) fn analyze_simple_int_helper(body: &PseudoExpr) -> Option<String> {
    if let Some(op) = extract_data_int_binop(body) {
        return Some(
            match op {
                BinaryOp::Add => "add_int",
                BinaryOp::Sub => "sub_int",
                BinaryOp::Mul => "mul_int",
                BinaryOp::Div => "div_int",
                BinaryOp::Mod => "mod_int",
                _ => return None,
            }
            .to_string(),
        );
    }

    if let Some(op) = extract_comparison_binop(body) {
        return Some(
            match op {
                BinaryOp::Lte => "lte_int",
                BinaryOp::Gt => "gt_int",
                BinaryOp::Gte => "gte_int",
                _ => return None,
            }
            .to_string(),
        );
    }

    if let PseudoExpr::Let {
        name,
        value,
        body: let_body,
        ..
    } = body
        && let Some(op) = extract_comparison_binop(value)
        && matches!(
            let_body.as_ref(),
            PseudoExpr::UnOp {
                op: crate::pseudo::ast::UnaryOp::Not,
                operand,
            } if matches!(operand.as_ref(), PseudoExpr::Var { name: var_name, .. } if var_name == name)
        )
    {
        return Some(
            match op {
                BinaryOp::Lt => "gte_int",
                BinaryOp::Lte => "gt_int",
                BinaryOp::Gt => "lte_int",
                BinaryOp::Gte => "lt_int",
                _ => return None,
            }
            .to_string(),
        );
    }

    None
}

pub(crate) fn extract_data_int_binop(body: &PseudoExpr) -> Option<BinaryOp> {
    let PseudoExpr::BuiltinCall { name, args } = body else {
        return None;
    };
    if !matches!(name.as_str(), "Data.Int" | "IData" | "i_data") || args.len() != 1 {
        return None;
    }

    let PseudoExpr::BinOp { op, left, right } = &args[0] else {
        return None;
    };
    if body_contains_any_builtin_call(left, DATA_INT_EXTRACTORS)
        && body_contains_any_builtin_call(right, DATA_INT_EXTRACTORS)
    {
        Some(*op)
    } else {
        None
    }
}

pub(crate) fn extract_comparison_binop(body: &PseudoExpr) -> Option<BinaryOp> {
    let PseudoExpr::BinOp { op, left, right } = body else {
        return None;
    };

    match op {
        BinaryOp::Lt | BinaryOp::Lte | BinaryOp::Gt | BinaryOp::Gte => {
            if body_contains_any_builtin_call(left, DATA_INT_EXTRACTORS)
                && body_contains_any_builtin_call(right, DATA_INT_EXTRACTORS)
            {
                Some(*op)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Check if body is a `Constr` with tag.
pub(super) fn is_constr_wrapper(body: &PseudoExpr, tag: usize) -> bool {
    matches!(
        body,
        PseudoExpr::Constr {
            tag: t,
            ..
        } if *t == tag
    )
}
