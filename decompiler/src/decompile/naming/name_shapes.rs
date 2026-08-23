//! Judging NAMES rather than trees: which are generic
//! (`x`, `v_12`, `arg_3`), which are compiler temporaries, which may
//! carry a param or pattern hint, and how to reduce one to a stem.
//!
//! Plus the two whole-expression probes the naming decisions gate on —
//! whether a body can fail, and whether it references another binding by
//! name.

use super::*;

/// Check if a name is a generic decompiler-generated name.
pub(crate) fn is_generic_name(name: &str) -> bool {
    // `fn` / `rec_fn` placeholders from the early rename pass.
    // `helper` is the multi-param Lambda hint — `fn` is an surface
    // keyword that `sanitize_identifier` renders as `fn_` — and
    // `helper_<N>` carries a disambiguation suffix.
    if name == "fn" || name == "rec_fn" || name == "helper" {
        return true;
    }
    if name.starts_with("helper_") && name[7..].chars().all(|c| c.is_ascii_digit()) {
        return true;
    }
    // f_N (top-level functions)
    if name.starts_with("f_") && name[2..].chars().all(|c| c.is_ascii_digit()) {
        return true;
    }
    // fn_N (inner functions)
    if name.starts_with("fn_") && name[3..].chars().all(|c| c.is_ascii_digit()) {
        return true;
    }
    // rec_fn_N (recursive helpers)
    if name.starts_with("rec_fn_") && name[7..].chars().all(|c| c.is_ascii_digit()) {
        return true;
    }
    if name.starts_with("fold_result_") && name[12..].chars().all(|c| c.is_ascii_digit()) {
        return true;
    }
    // fn_result / rec_fn_result and uniquified variants
    if name == "fn_result" || name == "rec_fn_result" {
        return true;
    }
    if (name.starts_with("fn_result_") && name[10..].chars().all(|c| c.is_ascii_digit()))
        || (name.starts_with("rec_fn_result_") && name[14..].chars().all(|c| c.is_ascii_digit()))
    {
        return true;
    }
    if (name.starts_with("f_") || name.starts_with("fn_") || name.starts_with("rec_fn_"))
        && name.ends_with("_result")
    {
        return true;
    }
    false
}

/// Check if a helper name is obviously temporary and still worth readability renaming.
pub(crate) fn is_temporary_helper_name(name: &str) -> bool {
    if name.len() == 1 && name.chars().all(|c| c.is_ascii_lowercase()) {
        return true;
    }

    if name.len() > 1
        && name.as_bytes()[0].is_ascii_lowercase()
        && name[1..].chars().all(|c| c.is_ascii_digit())
    {
        return true;
    }

    if let Some((stem, suffix)) = name.rsplit_once('_') {
        if stem.len() == 1
            && stem.chars().all(|c| c.is_ascii_lowercase())
            && !suffix.is_empty()
            && suffix.chars().all(|c| c.is_ascii_digit())
        {
            return true;
        }

        if !stem.is_empty()
            && stem.starts_with("decode_")
            && !suffix.is_empty()
            && suffix.chars().all(|c| c.is_ascii_digit())
        {
            return true;
        }

        if stem == "check" && !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()) {
            return true;
        }
    }

    name.ends_with("_partial") || name.ends_with("_forced")
}

pub(super) fn is_param_hint_candidate_name(name: &str) -> bool {
    if is_generic_name(name) || is_temporary_helper_name(name) {
        return true;
    }

    if has_generated_numeric_suffix_segments(name) {
        return true;
    }

    name.rsplit_once('_').is_some_and(|(stem, suffix)| {
        !stem.is_empty()
            && !suffix.is_empty()
            && suffix.chars().all(|c| c.is_ascii_digit())
            && stem.chars().all(|c| c.is_ascii_lowercase())
    })
}

pub(super) fn has_generated_numeric_suffix_segments(name: &str) -> bool {
    let mut segments = name.split('_');
    let Some(stem) = segments.next() else {
        return false;
    };
    if stem.is_empty() || !stem.chars().all(|c| c.is_ascii_lowercase()) {
        return false;
    }

    let mut saw_numeric_suffix = false;
    for segment in segments {
        if segment.is_empty() || !segment.chars().all(|c| c.is_ascii_digit()) {
            return false;
        }
        saw_numeric_suffix = true;
    }

    saw_numeric_suffix
}

pub(super) fn is_pattern_hint_candidate_name(name: &str) -> bool {
    if is_param_hint_candidate_name(name) {
        return true;
    }

    if name.starts_with("fields_") || name.starts_with("item_") {
        return true;
    }

    let Some((stem, suffix)) = name.rsplit_once('_') else {
        return false;
    };

    !suffix.is_empty()
        && suffix.chars().all(|c| c.is_ascii_digit())
        && !stem.is_empty()
        && stem.len() <= 4
        && stem
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit())
        && stem.chars().any(|c| c.is_ascii_digit())
}

pub(super) fn sanitize_hint_stem(name: &str) -> String {
    let mut out = String::new();
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
        } else if ch == '_' && !out.ends_with('_') {
            out.push('_');
        }
    }
    out.trim_matches('_').to_string()
}

pub(super) fn generated_name_base(name: &str) -> Option<String> {
    let mut parts: Vec<&str> = name.split('_').collect();
    while parts
        .last()
        .is_some_and(|segment| !segment.is_empty() && segment.chars().all(|c| c.is_ascii_digit()))
    {
        parts.pop();
    }

    let base = parts.join("_");
    let sanitized = sanitize_hint_stem(&base);
    if sanitized.is_empty() {
        None
    } else {
        Some(sanitized)
    }
}

pub(super) fn scoped_reusable_hint(hint: &str) -> Option<String> {
    match hint {
        "item" | "map" | "payload" | "variant" => Some(hint.to_string()),
        _ => None,
    }
}

pub(super) fn expr_contains_fail(expr: &PseudoExpr) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if is_fail_body(expr) {
            return true;
        }
        let kids: Vec<&PseudoExpr> = match expr {
            PseudoExpr::Let { value, body, .. } => vec![value, body],
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => vec![condition, then_branch, else_branch],
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                let mut v = vec![subject.as_ref()];
                for clause in clauses {
                    if let Some(g) = &clause.guard {
                        v.push(g);
                    }
                    v.push(&clause.body);
                }
                v
            }
            PseudoExpr::Apply { function, args } => {
                let mut v = vec![function.as_ref()];
                v.extend(args.iter());
                v
            }
            PseudoExpr::BinOp { left, right, .. } => vec![left, right],
            PseudoExpr::UnOp { operand, .. } => vec![operand],
            PseudoExpr::Trace { message, value } => vec![message, value],
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => vec![inner],
            PseudoExpr::List { elements, tail } => {
                let mut v: Vec<&PseudoExpr> = elements.iter().collect();
                if let Some(tail) = tail {
                    v.push(tail);
                }
                v
            }
            PseudoExpr::Tuple(elements) => elements.iter().collect(),
            PseudoExpr::Pair(left, right) => vec![left, right],
            PseudoExpr::Constr { fields, .. } => fields.iter().collect(),
            PseudoExpr::FieldAccess { record, .. } => vec![record],
            PseudoExpr::IndexAccess { collection, .. } => vec![collection],
            PseudoExpr::BuiltinCall { args, .. } => args.iter().collect(),
            _ => vec![],
        };
        pending.extend(kids.into_iter().rev());
    }
    false
}

pub(super) fn expr_references_other_var_named(
    expr: &PseudoExpr,
    name: &str,
    current_id: VarId,
) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        let kids: Vec<&PseudoExpr> = match expr {
            PseudoExpr::Var {
                name: var_name, id, ..
            } => {
                if var_name == name && *id != Some(current_id) {
                    return true;
                }
                vec![]
            }
            PseudoExpr::Let { value, body, .. } => vec![value, body],
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => vec![condition, then_branch, else_branch],
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                let mut v = vec![subject.as_ref()];
                for clause in clauses {
                    if let Some(g) = &clause.guard {
                        v.push(g);
                    }
                    v.push(&clause.body);
                }
                v
            }
            PseudoExpr::Apply { function, args } => {
                let mut v = vec![function.as_ref()];
                v.extend(args.iter());
                v
            }
            PseudoExpr::BinOp { left, right, .. } => vec![left, right],
            PseudoExpr::UnOp { operand, .. } => vec![operand],
            PseudoExpr::Trace { message, value } => vec![message, value],
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => vec![inner],
            PseudoExpr::List { elements, tail } => {
                let mut v: Vec<&PseudoExpr> = elements.iter().collect();
                if let Some(tail) = tail {
                    v.push(tail);
                }
                v
            }
            PseudoExpr::Tuple(elements) => elements.iter().collect(),
            PseudoExpr::Pair(left, right) => vec![left, right],
            PseudoExpr::Constr { fields, .. } => fields.iter().collect(),
            PseudoExpr::FieldAccess { record, .. } => vec![record],
            PseudoExpr::IndexAccess { collection, .. } => vec![collection],
            PseudoExpr::BuiltinCall { args, .. } => args.iter().collect(),
            _ => vec![],
        };
        pending.extend(kids.into_iter().rev());
    }
    false
}
