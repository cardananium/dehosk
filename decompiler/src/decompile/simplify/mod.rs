//! Simplification passes for PseudoExpr, making the AST
//! readable: force/delay cancellation, builtin application
//! patterns, Y-combinator recursion, if-chain to `when`
//! conversion, and && / || recovery.

mod analysis;
mod apply;
mod builtin_simplify;
mod builtins;
mod clone_hygiene;
mod control_flow;
pub(crate) mod cps_eliminate;
mod force;
mod helpers;
mod identity;
mod lambda;
mod let_binding;
mod patterns;
pub(crate) mod postprocess;
mod rename;
mod selectors;
mod state;
#[cfg(test)]
mod tests;
mod transform;

pub use crate::builtins::BuiltinId;
pub(crate) use cps_eliminate::eliminate_cps_selectors;
pub(crate) use postprocess::{
    cancel_force_delay_vars, normalize_list_cons_literals, strip_cosmetic_delays,
};
pub(crate) use state::Simplifier;
pub(crate) use state::{SimplifyOutput, SimplifyState};
pub(crate) use transform::simplify_with_state_opts;
#[cfg(test)]
pub(crate) use transform::{simplify, simplify_with_options, simplify_with_state};

// Re-export post-processing functions (called from run_pipeline)
pub(crate) use postprocess::{
    convert_expect_tag_to_constr_when, detect_sum_type_overrides, resolve_inline_field_accesses,
};
#[cfg(test)]
pub(crate) use rename::rename_validator_params;
pub(crate) use rename::{
    is_protected_validator_param_name, rename_validator_params_with_var_kinds,
    rename_validator_params_with_var_kinds_authoritative,
};
