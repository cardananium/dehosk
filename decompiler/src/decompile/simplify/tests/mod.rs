pub(crate) use super::*;
use crate::decompile::name_orphan_audit::audit_id_orphans;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

pub(super) fn assert_local_simplifier_binder(binder: &Binder, name: &str) {
    assert_eq!(binder.as_str(), name);
    assert!(
        binder.id.as_u32() < 1_000_000_000,
        "expected {name} to use the per-Simplifier id allocator, got {}",
        binder.id
    );
}

mod basics;

mod selector_identity;

mod var_id_identity_guards;

mod selector_dethunk_var_id;

mod readability_recfn_regressions;

mod builtin_alias_identity;

mod lambda_identity;

mod recfn_identity;

mod delay_or;

mod expect_delay;

mod force_basic;

mod force_builtin_alias;

pub(super) fn assert_helper_symbol(expr: &PseudoExpr, expected_name: &str) {
    // `fix` emits as
    // `PseudoExpr::HelperSymbol(HelperIntrinsic::Fix)`; other
    // helpers (e.g. `expect!`) are a `Var` with no id or a
    // compat-placeholder id.
    if expected_name == "fix" {
        assert!(
            matches!(
                expr,
                PseudoExpr::HelperSymbol(crate::pseudo::ast::HelperIntrinsic::Fix)
            ),
            "expected fix HelperSymbol(Fix), got: {expr:?}"
        );
    } else {
        assert!(
            matches!(
                expr,
                PseudoExpr::Var { name, id, .. }
                    if name == expected_name && id.is_none_or(|v| v.is_compat_placeholder())
            ),
            "expected {expected_name} helper symbol with compat-placeholder id, got: {expr:?}"
        );
    }
}

pub(super) fn assert_expect_helper_head(expr: &PseudoExpr) {
    assert_helper_symbol(expr, "expect!");
}

mod helper_symbols;

mod lazy_choose_list;

mod when_constr_collapse;

mod force_scott;

mod partial_apply_recfn;

mod y_fix;

mod inlining_basics;

mod simplify_state_metadata;

mod simplify_state_identity;

mod simplify_state_recursion;

mod apply_distribution;
mod bool_constant_folding;
mod bool_list_when_rewrites;
mod boolean_if_delay_rewrites;
mod branch_freshening;
mod cancel_force_delay_vars;
mod constructor_option_naming;
mod cps_scott_constructor_rewrites;
mod data_apply_roundtrip;
mod data_constr_folding;
mod data_field_access;
mod data_roundtrip_unconstr;
mod delayed_force_depth_dethunk;
mod delayed_rec_force_expansion;
mod force_delay_dethunk;
mod force_dethunk_selector;
mod force_scott_case_inline;
mod generated_binding_ids;
mod identity_function_elimination;
mod inline_list_reconstruction;
mod inlining_extended;
mod list_destructure;
mod list_subject_reconstruction;
mod multi_use_helper_inlining;
mod nested_lambda_merge;
mod nested_when_same_subject;
mod pair_constr_projection;
mod readability_aliasing;
mod recfn_curried_arity_safety;
mod recfn_nonempty_list_search;
mod recfn_normalization;
mod recfn_wrapper_promotion;
mod residual_if_handling;
mod scott_bool_iife;
mod selector_when_eta_hoist;
mod single_use_delay_inlining;
mod single_use_nonlambda_inlining;
mod tail_chain_index_access;

mod constructor_when_fields_destructure;
mod expect_constructor_field_destructure;
mod expect_fail_message;

mod walker_adapter;

mod let_capture_alias_hygiene;

mod expect_when_return_binder;

mod readability_regressions;

mod binding_table_scan_order;
