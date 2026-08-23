//! Post-processing and context field resolution for the simplifier.

mod context;
mod context_schema;
mod inline;
mod passes;

pub(super) use context::seed_context_field_names;
pub(crate) use context::{
    ListCombinatorShape, builtin_cardano_return, context_field_at, context_field_type,
    context_field_type_from_display_name, context_field_type_full, detect_sum_type_overrides,
    list_combinator_element_param_index, singular_of_list_field, sum_type_constructor_fields,
    sum_type_constructor_names,
};
pub(crate) use context_schema::{
    CardanoTypeRef, ContextField, ContextType, FieldTypeRef, SumTypeId,
};
pub(crate) use inline::resolve_inline_field_accesses;
pub(crate) use passes::convert_expect_tag_to_constr_when;
pub(crate) use passes::{
    bool_constr_collapse, cancel_force_delay_vars, normalize_list_cons_literals,
    strip_cosmetic_delays,
};
