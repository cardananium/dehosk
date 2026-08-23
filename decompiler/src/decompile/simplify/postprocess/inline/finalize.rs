use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::decompile::ScriptVersion;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{BinaryOp, PseudoExpr, UnaryOp};
use crate::pseudo::var_id::VarId;

use super::super::context::{context_field_at, context_field_type_from_display_name};
use super::super::context_schema::{ContextType, FieldTypeRef};
use super::rebuild::pop_result;
use super::scope::{
    expr_has_binder, has_any_var_named, is_generic_field_binding, is_semantic_field_name,
};
use super::{
    ByIdNames, InlineNames, InlineOverrides, InlineTypes, resolve_expr_inline_context_name,
};

fn inline_semantic_var(parent: &str, field_names_by_id: &ByIdNames) -> PseudoExpr {
    let mut ids = field_names_by_id
        .iter()
        .filter_map(|(id, semantic)| (semantic == parent).then_some(*id));

    let Some(id) = ids.next() else {
        return PseudoExpr::var(parent);
    };

    if ids.next().is_some() {
        PseudoExpr::var(parent)
    } else {
        PseudoExpr::var_with_id(parent, id)
    }
}

pub(super) fn resolve_inline_index_access(
    resolved_collection: PseudoExpr,
    index: usize,
    context_names: &InlineNames,
    context_types: &InlineTypes,
    sum_field_overrides: &InlineOverrides,
    field_names_by_id: &ByIdNames,
    version: ScriptVersion,
) -> PseudoExpr {
    if let PseudoExpr::Var {
        ref name, ref id, ..
    } = resolved_collection
    {
        let by_id_sem = id.get().and_then(|vid| field_names_by_id.get(&vid));
        let by_name_sem = context_names.get(name);
        let resolved_by_id = by_id_sem.is_some();
        if let Some(semantic) = by_id_sem.or(by_name_sem)
            && let Some(parent) = semantic.strip_suffix("_fields")
        {
            let record = if resolved_by_id {
                inline_semantic_var(parent, field_names_by_id)
            } else {
                PseudoExpr::var(parent)
            };
            if let Some(field_name) = ContextType::from_display_name(parent)
                .and_then(|t| context_field_at(t, index, version))
            {
                return PseudoExpr::field_access(record, field_name.display_name());
            }
            if let Some(fields) = sum_field_overrides.get(parent)
                && let Some(field_name) = fields.get(index)
            {
                return PseudoExpr::field_access(record, field_name.clone());
            }
            if let Some(parent_type) = context_types.get(parent)
                && let Some(field_name) = ContextType::from_display_name(parent_type)
                    .and_then(|t| context_field_at(t, index, version))
            {
                return PseudoExpr::field_access(record, field_name.display_name());
            }
        }
    }

    if let PseudoExpr::FieldAccess {
        ref record,
        ref selector,
        ..
    } = resolved_collection
        && selector.as_pretty_name() == "fields"
        && let Some(semantic) = resolve_expr_inline_context_name(
            record.as_ref(),
            context_names,
            context_types,
            Some(field_names_by_id),
        )
    {
        if let Some(field_name) = ContextType::from_display_name(&semantic)
            .and_then(|t| context_field_at(t, index, version))
        {
            return PseudoExpr::field_access((**record).clone(), field_name.display_name());
        }
        if let Some(fields) = sum_field_overrides.get(semantic.as_str())
            && let Some(field_name) = fields.get(index)
        {
            return PseudoExpr::field_access((**record).clone(), field_name.clone());
        }
        if let Some(var_type) = context_types.get(semantic.as_str())
            && let Some(field_name) = ContextType::from_display_name(var_type)
                .and_then(|t| context_field_at(t, index, version))
        {
            return PseudoExpr::field_access((**record).clone(), field_name.display_name());
        }
    }

    PseudoExpr::IndexAccess {
        collection: PBox::new(resolved_collection),
        index,
    }
}

pub(super) fn finalize_inline_let_binding(
    name: String,
    id: VarId,
    resolved_value: PseudoExpr,
    resolved_body: PseudoExpr,
    used_let_names: &mut HashSet<String>,
) -> (String, PseudoExpr, PseudoExpr) {
    let (final_name, final_body) = if is_generic_field_binding(&name) {
        if let PseudoExpr::FieldAccess { ref selector, .. } = resolved_value {
            let field = selector.as_pretty_name();
            if is_semantic_field_name(field)
                && field != name.as_str()
                && !used_let_names.contains(field)
                && !has_any_var_named(&resolved_body, field)
            {
                let renamed = crate::decompile::simplify::Simplifier::rename_var_binding(
                    &resolved_body,
                    &name,
                    id.get(),
                    field,
                );
                used_let_names.insert(field.to_string());
                (field.to_string(), renamed)
            } else {
                (name, resolved_body)
            }
        } else {
            (name, resolved_body)
        }
    } else {
        (name, resolved_body)
    };

    (final_name, resolved_value, final_body)
}

pub(super) fn finalize_index_access_from_results(
    results: &mut Vec<PseudoExpr>,
    index: usize,
    context_names: &InlineNames,
    context_types: &InlineTypes,
    sum_field_overrides: &InlineOverrides,
    field_names_by_id: &ByIdNames,
    version: ScriptVersion,
) -> PseudoExpr {
    let resolved_collection = pop_result(results);
    resolve_inline_index_access(
        resolved_collection,
        index,
        context_names,
        context_types,
        sum_field_overrides,
        field_names_by_id,
        version,
    )
}

pub(super) fn finalize_let_from_results(
    results: &mut Vec<PseudoExpr>,
    name: String,
    id: VarId,
    used_let_names: &mut HashSet<String>,
) -> PseudoExpr {
    let resolved_body = pop_result(results);
    let resolved_value = pop_result(results);
    let (final_name, final_value, final_body) =
        finalize_inline_let_binding(name, id, resolved_value, resolved_body, used_let_names);

    PseudoExpr::Let {
        name: final_name,
        id: id.get(),
        value: PBox::new(final_value),
        body: PBox::new(final_body),
    }
}

pub(super) fn finalize_binop_from_results(
    results: &mut Vec<PseudoExpr>,
    op: BinaryOp,
    version: ScriptVersion,
) -> PseudoExpr {
    let right = pop_result(results);
    let left = pop_result(results);

    if matches!(op, BinaryOp::Eq | BinaryOp::Neq) {
        if let Some(expanded) = try_expand_fields_eq(&left, &right, &op, version) {
            return expanded;
        }
        if let Some(expanded) = try_expand_fields_eq(&right, &left, &op, version) {
            return expanded;
        }
    }

    PseudoExpr::BinOp {
        op,
        left: PBox::new(left),
        right: PBox::new(right),
    }
}

pub(super) fn finalize_unop_from_results(results: &mut Vec<PseudoExpr>, op: UnaryOp) -> PseudoExpr {
    let operand = pop_result(results);
    PseudoExpr::UnOp {
        op,
        operand: PBox::new(operand),
    }
}

/// Try to expand `record.fields == [a, b, ...]` into field-by-field comparisons
/// when `record` has a known context type.
///
/// e.g. `out_ref.fields == [Data.Constr(0,[hash]),1]` →
///      `out_ref.tx_id == Data.Constr(0,[hash]) && out_ref.output_index == 1`
fn try_expand_fields_eq(
    fields_side: &PseudoExpr,
    list_side: &PseudoExpr,
    op: &BinaryOp,
    version: ScriptVersion,
) -> Option<PseudoExpr> {
    let PseudoExpr::FieldAccess {
        record, selector, ..
    } = fields_side
    else {
        return None;
    };
    if selector.as_pretty_name() != "fields" {
        return None;
    }

    let PseudoExpr::List { elements, tail } = list_side else {
        return None;
    };
    if tail.is_some() || elements.is_empty() {
        return None;
    }

    // Only record types (ContextType) expose positional fields - sum types bail.
    let record_type = match record.as_ref() {
        PseudoExpr::Var { name, .. } => context_field_type_from_display_name(name, version),
        PseudoExpr::FieldAccess { selector, .. } => {
            context_field_type_from_display_name(selector.as_pretty_name(), version)
        }
        _ => None,
    }
    .and_then(|t| match t {
        FieldTypeRef::Context(ct) => Some(ct),
        FieldTypeRef::Sum(_) => None,
    })?;

    let field_count = (0..)
        .take_while(|i| context_field_at(record_type, *i, version).is_some())
        .count();

    if elements.len() != field_count {
        return None;
    }
    if field_count > 1 && expr_has_binder(record) {
        return None;
    }

    let comparisons: Vec<PseudoExpr> = (0..field_count)
        .map(|i| {
            let field_name = context_field_at(record_type, i, version).unwrap();
            PseudoExpr::BinOp {
                op: *op,
                left: PBox::new(PseudoExpr::field_access(
                    (**record).clone(),
                    field_name.display_name(),
                )),
                right: PBox::new(elements[i].clone()),
            }
        })
        .collect();

    let combine_op = if *op == BinaryOp::Eq {
        BinaryOp::And
    } else {
        BinaryOp::Or
    };
    Some(
        comparisons
            .into_iter()
            .reduce(|acc, cmp| PseudoExpr::BinOp {
                op: combine_op,
                left: PBox::new(acc),
                right: PBox::new(cmp),
            })
            .unwrap(),
    )
}
