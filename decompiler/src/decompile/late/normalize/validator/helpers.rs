use std::collections::HashMap;

use crate::pseudo::ast::{Binder, WhenPattern};
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

pub(in crate::decompile::late::normalize) fn collect_pattern_binders(
    pattern: &WhenPattern,
    out: &mut Vec<String>,
) {
    match pattern {
        WhenPattern::Constructor { fields, .. } => {
            out.extend(
                fields
                    .iter()
                    .filter(|binder| binder.name != "_")
                    .map(|binder| binder.name.clone()),
            );
        }
        WhenPattern::List { elements, tail } => {
            out.extend(
                elements
                    .iter()
                    .filter(|binder| binder.name != "_")
                    .map(|binder| binder.name.clone()),
            );
            if let Some(tail) = tail
                && tail.name != "_"
            {
                out.push(tail.name.clone());
            }
        }
        WhenPattern::Tuple(elements) => {
            out.extend(
                elements
                    .iter()
                    .filter(|binder| binder.name != "_")
                    .map(|binder| binder.name.clone()),
            );
        }
        WhenPattern::Pair(left, right) => {
            if left.name != "_" {
                out.push(left.name.clone());
            }
            if right.name != "_" {
                out.push(right.name.clone());
            }
        }
        WhenPattern::Var(binder) => {
            if binder.name != "_" {
                out.push(binder.name.clone());
            }
        }
        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
    }
}

pub(in crate::decompile::late::normalize) fn list_pattern_head(
    pattern: &WhenPattern,
) -> Option<Binder> {
    match pattern {
        WhenPattern::List { elements, .. } => {
            elements.iter().find(|binder| binder.name != "_").cloned()
        }
        _ => None,
    }
}

pub(in crate::decompile::late::normalize) fn is_generated_payload_name(name: &str) -> bool {
    if name.starts_with("fields_") {
        return true;
    }
    let mut seen_digit = false;
    let mut seen_underscore = false;
    for ch in name.chars() {
        if ch.is_ascii_digit() {
            seen_digit = true;
        } else if ch == '_' {
            seen_underscore = true;
        }
    }
    seen_digit && seen_underscore
}

/// Orphan generated-payload predicate for validator constructor recovery.
/// Delegates to the shared
/// [`crate::decompile::varkind_recovery::is_orphan_payload_ref_typed_or_legacy`]
/// helper with this pass's legacy predicate (`is_generated_payload_name`).
pub(in crate::decompile::late::normalize) fn is_orphan_generated_payload_ref(
    name: &str,
    id: Option<VarId>,
    kind_annotations: &HashMap<VarId, VarKind>,
    use_varkind_recovery: bool,
) -> bool {
    let id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
    crate::decompile::varkind_recovery::is_orphan_payload_ref_typed_or_legacy(
        name,
        id,
        kind_annotations,
        use_varkind_recovery,
        is_generated_payload_name,
        "validator",
    )
}

pub(in crate::decompile::late::normalize) fn generated_subject_prefix(name: &str) -> Option<&str> {
    let underscore = name.rfind('_')?;
    Some(&name[..=underscore])
}

pub(in crate::decompile::late::normalize) fn generated_field_index(name: &str) -> Option<usize> {
    fn parse_leading_index(suffix: &str) -> Option<usize> {
        let digits: String = suffix
            .chars()
            .take_while(|ch| ch.is_ascii_digit())
            .collect();
        (!digits.is_empty()).then(|| digits.parse().ok()).flatten()
    }

    name.strip_prefix("fields_")
        .and_then(parse_leading_index)
        .or_else(|| name.strip_prefix("field_").and_then(parse_leading_index))
}
