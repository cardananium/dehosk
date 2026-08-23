use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

use super::aliases::{
    choose_generated_record_subject_alias, is_authoritative_same_name_different_id,
};
use super::collectors::{
    collect_local_generated_payload_binders, collect_nested_generated_field_record_binders,
    collect_subject_field_access_indices, recovered_generated_payload_binder,
};
use super::field0::{contains_subject_field0_access, extract_subject_field0_binder};
use super::helpers::generated_subject_prefix;
use super::payload_rewrite::PayloadRewriteCtx;
use super::rebind::rewrite_free_generated_var_to_binder;
use super::scope::ScopeFrame;

pub(in crate::decompile::late::normalize) fn try_recover_generated_constructor_fields(
    pattern: WhenPattern,
    subject_name: Option<&Binder>,
    subject_supports_fields: bool,
    body: PseudoExpr,
    scopes: &[ScopeFrame],
    kind_annotations: &HashMap<VarId, VarKind>,
    use_varkind_recovery: bool,
) -> (WhenPattern, PseudoExpr) {
    let WhenPattern::Constructor {
        type_hint,
        tag,
        fields,
        shape,
    } = pattern
    else {
        return (pattern, body);
    };
    if !fields.is_empty() {
        return (
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            },
            body,
        );
    }
    if !subject_supports_fields {
        return (
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            },
            body,
        );
    }
    let Some(subject_name) = subject_name else {
        return (
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            },
            body,
        );
    };
    let mut bound = HashSet::new();
    let mut bound_ids = HashSet::new();
    for scope in scopes {
        bound.extend(scope.bound.iter().cloned());
        bound_ids.extend(scope.binders.iter().map(|binder| binder.id));
    }
    bound.insert(subject_name.name.clone());
    bound_ids.insert(subject_name.id);
    let mut normalized_body = body;
    let mut generated_record_binders = Vec::new();
    collect_nested_generated_field_record_binders(
        &normalized_body,
        &bound_ids,
        &mut generated_record_binders,
        kind_annotations,
        use_varkind_recovery,
    );
    if let Some(alias_binder) =
        choose_generated_record_subject_alias(&generated_record_binders, subject_name)
    {
        normalized_body = rewrite_free_generated_var_to_binder(
            normalized_body,
            &alias_binder,
            subject_name,
            &bound_ids,
        );
    }

    let extracted = extract_subject_field0_binder(normalized_body.clone(), subject_name.id);

    let direct_field0_fallback = extracted.is_none()
        && tag != 0
        && contains_subject_field0_access(&normalized_body, subject_name.id);

    let generated_scan_body = extracted
        .as_ref()
        .map(|(_, stripped_body)| stripped_body)
        .unwrap_or(&normalized_body);
    let mut generated_binders = Vec::new();
    if direct_field0_fallback {
        collect_nested_generated_field_record_binders(
            generated_scan_body,
            &bound_ids,
            &mut generated_binders,
            kind_annotations,
            use_varkind_recovery,
        );
    } else {
        collect_local_generated_payload_binders(
            generated_scan_body,
            &bound_ids,
            &mut generated_binders,
            kind_annotations,
            use_varkind_recovery,
        );
        if let Some(prefix) = generated_subject_prefix(subject_name.as_str()) {
            generated_binders.retain(|binder| {
                binder.name.starts_with("fields_") || binder.name.starts_with(prefix)
            });
        } else {
            generated_binders.retain(|binder| binder.name.starts_with("fields_"));
        }
    }
    generated_binders
        .retain(|binder| !is_authoritative_same_name_different_id(binder, subject_name));

    let mut direct_subject_field_indices = BTreeSet::new();
    if direct_field0_fallback {
        let mut subject_field_bound = bound_ids.clone();
        subject_field_bound.remove(&subject_name.id);
        collect_subject_field_access_indices(
            generated_scan_body,
            subject_name.id,
            &subject_field_bound,
            &mut direct_subject_field_indices,
        );
        direct_subject_field_indices.remove(&0);
    }

    let has_recoverable_generated_fields =
        !generated_binders.is_empty() || !direct_subject_field_indices.is_empty();

    let Some((field0_binder, stripped_body)) = extracted.or_else(|| {
        (direct_field0_fallback && has_recoverable_generated_fields).then(|| {
            (
                Binder::new("field_0", VarId::fresh_binding()),
                normalized_body.clone(),
            )
        })
    }) else {
        return (
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            },
            normalized_body,
        );
    };

    bound.insert(field0_binder.name.clone());

    let mut field_binders = BTreeMap::new();
    field_binders.insert(0usize, field0_binder.clone());
    let mut generated_var_fields = HashMap::new();
    let mut next_index = 1usize;

    for binder in generated_binders {
        if let Some(index) = binder
            .name
            .strip_prefix("fields_")
            .and_then(|suffix| suffix.parse::<usize>().ok())
        {
            field_binders
                .entry(index)
                .or_insert_with(|| recovered_generated_payload_binder(&binder));
            generated_var_fields.insert(binder.id, index);
            next_index = next_index.max(index + 1);
        } else {
            let index = next_index;
            next_index += 1;
            field_binders.insert(index, recovered_generated_payload_binder(&binder));
            generated_var_fields.insert(binder.id, index);
        }
    }

    for index in direct_subject_field_indices {
        field_binders
            .entry(index)
            .or_insert_with(|| Binder::new(format!("fields_{index}"), VarId::fresh_binding()));
    }

    if field_binders.len() == 1 {
        let fields = vec![field0_binder];
        let shape = ConstructorShape::from_name_and_tag(shape.pretty_name(), tag, fields.len());
        return (
            WhenPattern::Constructor {
                type_hint: None,
                tag,
                fields,
                shape,
            },
            stripped_body,
        );
    }

    let condition_binder = field_binders.get(&0);
    let rewritten_body = PayloadRewriteCtx {
        subject_name: subject_name.as_str(),
        subject_id: subject_name.id,
        field_binders: &field_binders,
        generated_var_fields: &generated_var_fields,
        condition_binder,
        kind_annotations,
        use_varkind_recovery,
    }
    .rewrite(stripped_body);

    let max_index = field_binders.keys().max().copied().unwrap_or(0);
    let fields: Vec<Binder> = (0..=max_index)
        .map(|index| {
            field_binders
                .get(&index)
                .cloned()
                .unwrap_or_else(|| Binder::new("_", VarId::fresh_binding()))
        })
        .collect();
    let shape = ConstructorShape::from_name_and_tag(shape.pretty_name(), tag, fields.len());
    (
        WhenPattern::Constructor {
            type_hint: None,
            tag,
            fields,
            shape,
        },
        rewritten_body,
    )
}
