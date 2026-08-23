//! The render-prep chain's ORDER, as data.
//!
//! `prepare_for_render` runs ~140 passes whose sequence is load-bearing:
//! the modules carry 60-odd prose notes of the form "Runs AFTER `x`" /
//! "must run before `y`", and nothing checked any of them. The core
//! pipeline one layer up has had machine-checked pass contracts
//! (`requires` / `produces` / `invalidates`) since it was written; this
//! is the render half catching up.
//!
//! Two things are pinned here:
//!
//! * [`PREP_PASS_ORDER`] — the exact sequence. `order_matches_the_chain`
//!   fails if a pass is inserted, removed or moved, so a reorder has to
//!   be a deliberate edit to this list rather than a silent side effect
//!   of editing `prepare_for_render`.
//! * [`MUST_RUN_AFTER`] — the dependencies the modules state in prose,
//!   transcribed. `PrepRun::step` checks each one as the chain runs, so
//!   a violation names the pass and the dependency it jumped.
//!
//! The list below is deliberately NOT alphabetised: it is the running
//! order, and reading it top to bottom is reading the chain.

/// Every render-prep pass, in the order `prepare_for_render` runs it.
pub(super) const PREP_PASS_ORDER: &[&str] = &[
    "uniquify_duplicate_binders",
    "render_improve_variable_names",
    "deduplicate_constr_pattern_binders",
    "prefix_bare_extractor_lets_with_field_name",
    "inline_slice_chain_aliases",
    "repair_underscore_lambda_params_with_dangling_uses",
    "disambiguate_shadowed_lets",
    "disambiguate_shadowed_pattern_binders",
    "drop_dead_fail_labels",
    "strip_stray_thunk_wrappers",
    "inline_expect_subjects",
    "rewrite_expect_when_bool",
    "lift_let_through_expect",
    "rewrite_expect_three_arg_conditional",
    "rewrite_expect_field_access",
    "collapse_church_pair_eliminator_ast",
    "undo_pair_when_on_lambda_subject",
    "unfold_y_comb_through_let_pair_when",
    "collapse_bool_identity_when",
    "rename_synthetic_field_let_binders",
    "fold_force_on_lambda_var",
    "strip_force_under_member_access",
    "inline_identity_helpers",
    "inline_cps_identity_helpers",
    "strip_all_traces",
    "collapse_dead_fail_chain",
    "rename_unused_lambda_params",
    "flag_orphan_fix",
    "collapse_script_context_when",
    "cse_y_comb_consts",
    "recover_church_list_literals",
    "unfold_y_comb_applications",
    "unfold_y_comb_helper_applications",
    "relabel_option_producer_leaves",
    "relabel_option_consumer_args",
    "relabel_stub_consumer_args",
    "curry_split_partial_helpers",
    "cse_church_cons_helpers",
    "rename_church_n_pack_helpers",
    "rewrite_church_bool_in_list_fold",
    "inline_pattern_field_access",
    "uniquify_duplicate_binders",
    "unify_constructor_pattern_arity",
    "rebind_pattern_field_slices",
    "strip_void_apply_on_constr",
    "hoist_church_bool_selectors",
    "reduce_applied_church_pair_pack",
    "hoist_church_pair_pack",
    "rename_tx_info_binders",
    "resolve_tx_info_field_indices",
    "schema_param_provenance",
    "bind_cardano_sum_when_payload",
    "name_cardano_sum_arms",
    "lift_list_fold_to_when",
    "cse_church_list_map_helpers",
    "rename_church_list_helper_binders",
    "const_fold_church_bytestring",
    "collapse_trace_fail_let",
    "drop_dead_pure_lets",
    "fold_arith_identity",
    "fold_data_eq_roundtrip",
    "fold_un_data_scalar_const",
    "fold_if_to_logical",
    "inline_partial_binop",
    "replace_inline_pack_with_pack_n",
    "cse_inline_y_comb",
    "collapse_identity_option_when",
    "fold_when_option_to_is_some",
    "hoist_entry_param_chain_calls",
    "uniquify_duplicate_binders",
    "hoist_pure_multi_arg_calls",
    "uniquify_duplicate_binders",
    "decode_church_to_native",
    "rewrite_native_list_map",
    "rename_module_shadowing_lets",
    "fold_identity_pair_map",
    "inline_pair_identity_arg",
    "inline_constructor_helpers",
    "recover_scott_list_builder",
    "complete_church_nil_to_empty_list",
    "inline_pack_call_use_sites",
    "resolve_pack_ordinal_projection",
    "drop_dead_pure_lets",
    "normalize_tuple_field_ordinals",
    "eta_reduce_pair_aliases",
    "decode_church_list_fold_partial",
    "cse_alpha_equivalent_lambda_helpers",
    "undo_if_on_function_condition",
    "decode_church_pair_application",
    "collapse_church_pair_eliminator_ast",
    "resolve_scott_eliminator",
    "beta_reduce_lambda_apply",
    "eta_reduce_lambda_forwarder",
    "extract_repeated_subexpr",
    "uniquify_duplicate_binders",
    "disambiguate_shadowed_lets",
    "build_cardano_type_env",
    "bind_cardano_sum_when_payload",
    "name_cardano_sum_arms",
    "name_cardano_sum_values",
    "resolve_cardano_field_indices",
    "rename_let_to_cardano_field",
    "recfn_self_ref_probe",
    "collapse_identity_self_receiver",
    "clarify_rec_self_value_use",
    "flatten_recfn_unused_self",
    "rename_semantic_helpers",
    "recover_church_booleans",
    "recover_inverted_church_or",
    "recover_ordering_comparator",
    "inline_always_fail_helpers",
    "collapse_over_applied_fail",
    "saturate_dead_param_knot",
    "collapse_empty_when",
    "fix_option_false_to_none",
    "relabel_bool_none_to_false",
    "recover_if_from_bool_option_when",
    "recover_inverse_cip_nil_as_true",
    "normalize_church_false_arm_to_native",
    "promote_validator_entry_first",
    "decode_safe_pair_pack",
    "bind_list_cons_head_tail",
    "underscore_unused_pattern_binders",
    "strip_void_apply_on_noncallable_result",
    "rename_list_element_binders_late",
    "inline_identity_params",
    "disambiguate_shadowed_pattern_binders",
    "clarify_recfn_tail_return",
    "copy_propagate_var_aliases",
    "fold_const_recfn_alias",
    "recover_constr_cons_spread",
    "recover_recursive_list_builder",
    "lower_constr_field_sugar",
    "split_over_applied_helper_calls",
    "drop_unreferenced_helper_fns",
    "name_context_field_peel",
    "unname_discarded_check",
];

/// `(pass, passes that must already have run)`.
///
/// Transcribed from the modules' own doc comments — each entry has a
/// sentence next to the pass explaining WHY.
///
/// Only dependencies that hold for EVERY run of the dependant are here.
/// Seven passes run more than once (`uniquify_duplicate_binders` five
/// times, after each cloning pass; `drop_dead_pure_lets` twice), so a
/// note like "before the `drop_dead_pure_lets` RE-RUN" is a claim about
/// one occurrence, not about the pass, and there is nothing to check
/// against here. Notes of the form "runs after the other rewrites have
/// settled" are likewise not a checkable claim.
pub(super) const MUST_RUN_AFTER: &[(&str, &[&str])] = &[
    (
        "beta_reduce_lambda_apply",
        &[
            "cse_alpha_equivalent_lambda_helpers",
            "undo_if_on_function_condition",
        ],
    ),
    (
        "drop_unreferenced_helper_fns",
        &["promote_validator_entry_first"],
    ),
    ("fold_identity_pair_map", &["rewrite_native_list_map"]),
    (
        "hoist_church_pair_pack",
        &["reduce_applied_church_pair_pack"],
    ),
    ("name_cardano_sum_arms", &["bind_cardano_sum_when_payload"]),
    (
        "normalize_tuple_field_ordinals",
        &["resolve_pack_ordinal_projection"],
    ),
    (
        "promote_validator_entry_first",
        &["const_fold_church_bytestring"],
    ),
    (
        "rename_church_list_helper_binders",
        &["lift_list_fold_to_when"],
    ),
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::render_prep::{RenderCtx, prepare_for_render_with_notes};
    use crate::pseudo::ast::PseudoExpr;

    /// The chain must run exactly [`PREP_PASS_ORDER`].
    ///
    /// This is what makes the sequence an artifact instead of an
    /// accident: inserting, dropping or moving a `prep.step(..)` in
    /// `prepare_for_render` fails here until the list is updated to
    /// match, which is the moment to check the "Runs AFTER `x`" notes on
    /// the passes either side of the move.
    #[test]
    fn order_matches_the_chain() {
        // The tree is irrelevant — every step runs, most as a no-op.
        let prepared = prepare_for_render_with_notes(&PseudoExpr::Unit, &RenderCtx::default());
        let ran = prepared.profile.pass_names();
        assert_eq!(
            ran, PREP_PASS_ORDER,
            "the render-prep chain no longer matches `PREP_PASS_ORDER`; update the list \
             in the same commit that reorders the chain",
        );
    }

    /// Every dependency named in [`MUST_RUN_AFTER`] must be a real pass,
    /// and must actually precede its dependant in [`PREP_PASS_ORDER`].
    ///
    /// The runtime check in `PrepRun::step` only fires for passes that
    /// run; this proves the table itself is consistent, including for
    /// dependencies whose pass short-circuits on a given tree.
    #[test]
    fn declared_dependencies_are_real_and_ordered() {
        let position = |name: &str| PREP_PASS_ORDER.iter().position(|p| *p == name);
        for (pass, deps) in MUST_RUN_AFTER {
            let at =
                position(pass).unwrap_or_else(|| panic!("`{pass}` is not a pass in the chain"));
            for dep in *deps {
                let dep_at = position(dep)
                    .unwrap_or_else(|| panic!("`{pass}` depends on `{dep}`, which is not a pass"));
                assert!(
                    dep_at < at,
                    "`{pass}` declares it runs after `{dep}`, but the chain runs \
                     `{dep}` at {dep_at} and `{pass}` at {at}",
                );
            }
        }
    }

    /// A pass that runs more than once must have a REASON, and the
    /// reason is the same in each case: an earlier pass cloned or
    /// renamed something the later one has to see again.
    ///
    /// The list is here so that a NEW repeat is a deliberate entry
    /// rather than an accidental second `prep.step` with the same name —
    /// which would also make `MUST_RUN_AFTER` ambiguous for it.
    #[test]
    fn only_the_declared_passes_repeat() {
        /// `(pass, times, why)`.
        const EXPECTED_REPEATS: &[(&str, usize, &str)] = &[
            (
                "uniquify_duplicate_binders",
                5,
                "re-uniquify after each pass that clones a binder-bearing subtree",
            ),
            (
                "disambiguate_shadowed_lets",
                2,
                "re-run once the late passes have minted their own bindings",
            ),
            (
                "disambiguate_shadowed_pattern_binders",
                2,
                "same, for `when`-pattern binders",
            ),
            (
                "collapse_church_pair_eliminator_ast",
                2,
                "the second run catches shapes the intervening rewrites expose",
            ),
            (
                "bind_cardano_sum_when_payload",
                2,
                "name-only first, then type-directed once the env is built",
            ),
            (
                "name_cardano_sum_arms",
                2,
                "pairs with each `bind_cardano_sum_when_payload` run",
            ),
            (
                "drop_dead_pure_lets",
                2,
                "re-run after the late passes strand more bindings",
            ),
        ];

        let mut counts = std::collections::HashMap::new();
        for name in PREP_PASS_ORDER {
            *counts.entry(*name).or_insert(0usize) += 1;
        }
        for (name, times, why) in EXPECTED_REPEATS {
            assert_eq!(
                counts.get(name).copied().unwrap_or(0),
                *times,
                "`{name}` should run {times}× ({why})",
            );
        }
        let declared: std::collections::HashSet<&str> =
            EXPECTED_REPEATS.iter().map(|(n, _, _)| *n).collect();
        for (name, n) in counts {
            assert!(
                n == 1 || declared.contains(name),
                "`{name}` runs {n}× but is not in `EXPECTED_REPEATS` — a repeat needs a \
                 reason, and it makes `MUST_RUN_AFTER` ambiguous for that pass",
            );
        }
    }
}
