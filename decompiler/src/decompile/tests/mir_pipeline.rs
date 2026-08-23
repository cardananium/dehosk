//! MIR pipeline skip guards — the MIR-native pipeline must not
//! schedule late repair passes that exist only to clean up
//! artifacts of the legacy Scott-encoded path. Each test wraps
//! `collect_mir_passes` in a `!passes.contains` assertion, so a
//! pass sneaking back in via a scheduling change fails here.

#![cfg(test)]

use crate::decompile::pipeline::run_pipeline_with_artifacts_opts;
use crate::decompile::tests::{
    MIR_SHARED_PIPELINE_PASSES, MIR_SHARED_SEMANTIC_RECOVERY_PASSES,
    MIR_SHARED_STRUCTURAL_NORMALIZATION_PASSES, MIR_SHARED_TYPE_AND_NAMING_PASSES,
    MIR_V2_SMOKE_HEX, MIR_V3_SMOKE_HEX, collect_mir_passes, collect_pipeline_passes,
    collect_pipeline_telemetry, decompile_program_with_mir, mir_shared_classified_passes,
    pipeline_parity_test_lock,
};
use crate::decompile::{
    decode_hex_to_program, decompile_program, render_decompiled_expr_with_registry_and_final_types,
};
use crate::{DecompileOptions, ScriptVersion};
use std::collections::BTreeSet;
use uplc::ast::{NamedDeBruijn, Program};

#[test]
fn test_decompile_to_ast_matches_program_rendering() {
    let _guard = pipeline_parity_test_lock().lock().unwrap();

    let program: Program<NamedDeBruijn> =
        decode_hex_to_program(MIR_V2_SMOKE_HEX).expect("expected valid test program");
    let mut opts = DecompileOptions::default();
    opts.script_version = Some(ScriptVersion::PlutusV2);

    let pipeline_output =
        run_pipeline_with_artifacts_opts(&program, opts.clone(), |_, _| {}, false)
            .expect("pipeline should succeed");

    // `decompile_program` dresses the pipeline AST with the synthetic
    // stub-ADT declarations before rendering. Go through the very same
    // helper it uses, so this parity check pins the wiring around it
    // rather than a copy of it that silently drifts.
    let (plan_version, render_field_version) =
        crate::decompile::resolve_render_versions(&program, opts.script_version);
    let (expr_for_render, registry_for_render, stub_prefix) = crate::decompile::dress_stub_adts(
        pipeline_output.expr.clone(),
        pipeline_output.blueprint_registry.clone(),
        &crate::decompile::StubAdtRenderContext {
            synthesize_stub_adts: opts.synthesize_stub_adts,
            decode_church: opts.decode_church_to_native,
            compilable_data_access: opts.compilable_data_access,
            strip_all_traces: opts.strip_all_traces,
            strip_plutustx_traces: opts.strip_plutustx_traces,
            render_field_version,
            plan_version,
            version_guessed: false,
        },
    );

    // `decompile_program` renders under the same `RenderCtx`: it gates the
    // church->native rewrite and the ScriptContext / TxInfo field naming, so
    // the render is only comparable under an identical one.
    let (rendered, _spans) = {
        let render_ctx = crate::decompile::RenderCtx::new(render_field_version, plan_version)
            .with_version_guessed(false)
            .with_decode_church(opts.decode_church_to_native)
            .with_compilable_data_access(opts.compilable_data_access)
            .with_strip_all_traces(opts.strip_all_traces)
            .with_strip_plutustx_traces(opts.strip_plutustx_traces)
            .with_expect_or_fail(opts.expect_or_fail);
        render_decompiled_expr_with_registry_and_final_types(
            &expr_for_render,
            opts.type_passes.any_enabled(),
            &registry_for_render,
            &pipeline_output.final_types,
            &render_ctx,
        )
    };
    // `decompile_program` wraps the renderer output in a
    // `validator NAME { ... }` block, so route through
    // `validator_shape::build_plan` + `wrap_rendered` to pick up
    // the same diagnostic comments.
    let validator_shape_options = opts.validator_shape.clone();
    let script_version_for_plan = opts.script_version;
    let dispatch = crate::decompile::validator_shape::detect_dispatch(&expr_for_render);
    let outer = crate::decompile::validator_shape::inspect_outer(&program);
    let plan = crate::decompile::validator_shape::build_plan(
        crate::decompile::validator_shape::PlanInput {
            meta: opts.validator_meta.as_ref(),
            options: &validator_shape_options,
            script_version: script_version_for_plan,
            outer: &outer,
            dispatch: &dispatch,
            detected_single_purpose: None,
            observed_script_info_purposes: Vec::new(),
            version_inferred_ambiguous: false,
        },
    );
    let (diagnostics, rendered_wrapped) =
        crate::decompile::validator_shape::wrap_rendered_separated(&rendered, &plan);
    // mirror `decompile_program`'s
    // const-annotation pass so the parity diff stays clean.
    let compile_count_for_annotate = outer.applied_params.len().saturating_sub(
        crate::decompile::validator_shape::param_surface_runtime_count(
            validator_shape_options.applied_kind,
            &outer,
            crate::decompile::validator_shape::runtime_arity_for(
                script_version_for_plan,
                validator_shape_options.purpose,
            ),
        ),
    );
    let (rendered_wrapped, mut annotated_param_indices) =
        crate::decompile::validator_shape::annotate_hoisted_consts_with_param_origin(
            &rendered_wrapped,
            &outer.applied_params,
            compile_count_for_annotate,
            &outer.compiler_binding_indices,
        );
    // Mirror `decompile_program`'s hoist pass so the parity
    // diff stays clean.
    let (rendered_wrapped, hoisted_param_indices) =
        crate::decompile::validator_shape::hoist_compile_param_lets(
            &rendered_wrapped,
            &outer.applied_params,
            compile_count_for_annotate,
            &outer.compiler_binding_indices,
        );
    annotated_param_indices.extend(hoisted_param_indices.iter().copied());
    let hoisted_param_indices = annotated_param_indices;
    // Mirror `decompile_program`'s applied-params prefix: same
    // calling-convention runtime arity for the split logic, and
    // no prefix for `PlainFn` wraps.
    let is_plain = matches!(
        plan.wrap_form,
        crate::decompile::validator_shape::WrapForm::PlainFn
    );
    let param_prefix = if is_plain {
        String::new()
    } else {
        let runtime_arity_for_prefix = crate::decompile::validator_shape::runtime_arity_for(
            script_version_for_plan,
            validator_shape_options.purpose,
        );
        // skip hoisted params from prefix.
        crate::decompile::validator_shape::format_applied_params_prefix_with_skip(
            &outer,
            validator_shape_options.applied_kind,
            runtime_arity_for_prefix,
            &hoisted_param_indices,
        )
        .unwrap_or_default()
    };
    // Order: diagnostics → param prefix → stub ADTs → wrap.
    let rendered_wrapped_with_prefix =
        format!("{diagnostics}{param_prefix}{stub_prefix}{rendered_wrapped}");
    let rendered_program =
        decompile_program(&program, opts).expect("program decompile should succeed");

    assert_eq!(rendered_wrapped_with_prefix, rendered_program);
}

#[test]
fn test_mir_shared_pass_classification_is_exhaustive_and_disjoint() {
    let shared_pipeline: BTreeSet<&'static str> =
        MIR_SHARED_PIPELINE_PASSES.iter().copied().collect();
    let structural: BTreeSet<&'static str> = MIR_SHARED_STRUCTURAL_NORMALIZATION_PASSES
        .iter()
        .copied()
        .collect();
    let semantic: BTreeSet<&'static str> = MIR_SHARED_SEMANTIC_RECOVERY_PASSES
        .iter()
        .copied()
        .collect();
    let type_and_naming: BTreeSet<&'static str> =
        MIR_SHARED_TYPE_AND_NAMING_PASSES.iter().copied().collect();

    let overlap = |left: &BTreeSet<&'static str>,
                   right: &BTreeSet<&'static str>|
     -> Vec<&'static str> { left.intersection(right).copied().collect() };

    assert!(
        overlap(&shared_pipeline, &structural).is_empty(),
        "shared pipeline and structural buckets should not overlap"
    );
    assert!(
        overlap(&shared_pipeline, &semantic).is_empty(),
        "shared pipeline and semantic buckets should not overlap"
    );
    assert!(
        overlap(&shared_pipeline, &type_and_naming).is_empty(),
        "shared pipeline and type/naming buckets should not overlap"
    );
    assert!(
        overlap(&structural, &semantic).is_empty(),
        "structural and semantic buckets should not overlap"
    );
    assert!(
        overlap(&structural, &type_and_naming).is_empty(),
        "structural and type/naming buckets should not overlap"
    );
    assert!(
        overlap(&semantic, &type_and_naming).is_empty(),
        "semantic and type/naming buckets should not overlap"
    );

    let classified = mir_shared_classified_passes();
    let expected: BTreeSet<&'static str> = [
        "lower_mir",
        "rename_variables",
        "simplify_1",
        "inline_single_use",
        "simplify_2",
        "inline_fp",
        "simplify_fp",
        "uniquify_final",
        "eliminate_dead_lets",
        "inline_post_readability",
        "simplify_post_readability",
        "collapse_tail_chains",
        "strip_cosmetic_delays",
        "cancel_force_delay_vars",
        "normalize_list_cons_literals",
        "resolve_scott_constructor_lambdas",
        "lift_unpack_tag_when_subjects",
        "simplify_z_combinator",
        "simplify_double_rec_fn",
        "destructure_when_fields",
        "extract_complex_when_subjects",
        "collapse_eta_pair_selector_when_subjects",
        "collapse_eta_pair_selector_when_subjects_post_readability",
        "flatten_let_chains",
        "flatten_let_chains_post_inline",
        "flatten_let_chains_post_readability",
        "hoist_local_helpers",
        "extract_heavy_constants",
        "normalize_display_rewrites",
        "hoist_local_helpers_post_normalize",
        "convert_expect_tag",
        "resolve_field_accesses",
        "eliminate_cps_selectors",
        "disambiguate_constructors",
        "simplify_boolean_and_identity",
        "simplify_boolean_and_identity_late",
        "simplify_boolean_and_identity_post_readability",
        "eliminate_cps_selectors_post_readability",
        "resolve_cardano_field_names",
        "resolve_cardano_field_names_late",
        "rename_validator_params",
        "deduplicate_var_ids_for_type_refinement",
        "solve_type_constraints",
        "solve_type_constraints_late",
        "solve_type_constraints_post_late_structural",
        "solve_type_constraints_final",
        // collapse Bool↔Constr<0|1>
        // immediately after the final type solve, before propagation.
        "bool_constr_collapse_final",
        "propagate_types",
        "propagate_types_late",
        "propagate_types_post_late_structural",
        "propagate_types_final",
        "resolve_cardano_field_names_post_late_structural",
        "resolve_cardano_field_names_final",
        "improve_variable_names",
        "improve_variable_names_post_late",
        "retarget_refs_by_scope",
        "structural_final_cleanup",
        "deduplicate_var_ids_final",
        "inline_dangling_field_aliases",
        "default_nameless_post_pipeline",
    ]
    .into_iter()
    .collect();

    assert_eq!(
        classified, expected,
        "shared MIR pass classification should stay explicit and exhaustive"
    );
}

#[test]
fn test_mir_pipeline_identity_stays_simple_without_legacy_repair_stage() {
    let output = decompile_program_with_mir("46010000200101", None);

    assert_eq!(output.trim(), "fn(x) { x }");
}

#[test]
fn test_run_pipeline_uses_mir_seed() {
    let passes = collect_pipeline_passes("46010000200101", None);

    assert!(
        passes.contains(&"lower_mir"),
        "pipeline should start from MIR lowering: {passes:?}"
    );
    assert!(
        !passes.contains(&"decompile"),
        "pipeline should not use the removed direct seed: {passes:?}"
    );
}

#[test]
fn test_default_nameless_post_pipeline_is_emitted_after_final_cleanup() {
    let passes = collect_pipeline_passes("46010000200101", None);
    let nameless_pos = passes
        .iter()
        .position(|pass| *pass == "default_nameless_post_pipeline")
        .unwrap_or_else(|| panic!("default nameless post-pipeline should be emitted: {passes:?}"));
    let final_cleanup_pos = passes
        .iter()
        .position(|pass| *pass == "structural_final_cleanup")
        .unwrap_or_else(|| panic!("structural final cleanup should be emitted: {passes:?}"));

    assert!(
        nameless_pos > final_cleanup_pos,
        "default nameless post-pipeline should run after structural final cleanup: {passes:?}"
    );
    if let Some(final_retarget_pos) = passes
        .iter()
        .rposition(|pass| *pass == "retarget_refs_by_scope")
    {
        assert!(
            nameless_pos > final_retarget_pos,
            "default nameless post-pipeline should run after the final ref-retarget boundary: {passes:?}"
        );
    }
}

#[test]
fn test_pipeline_fixed_point_telemetry_reports_convergence() {
    let telemetry = collect_pipeline_telemetry("46010000200101", None, false);

    assert!(
        telemetry.fixed_point.attempted_iterations > 0,
        "optimized pipeline should attempt the fixed-point loop: {:?}",
        telemetry.fixed_point
    );
    assert!(
        telemetry.fixed_point.attempted_iterations <= telemetry.fixed_point.max_iterations,
        "fixed-point loop should not exceed its configured cap: {:?}",
        telemetry.fixed_point
    );
    assert!(
        telemetry.fixed_point.converged,
        "identity program should converge before the iteration cap: {:?}",
        telemetry.fixed_point
    );
    assert!(
        !telemetry.fixed_point.hit_iteration_limit,
        "identity program should not hit the iteration cap: {:?}",
        telemetry.fixed_point
    );
}

#[test]
fn test_pipeline_fixed_point_telemetry_stays_idle_in_safe_mode() {
    let telemetry = collect_pipeline_telemetry("46010000200101", None, true);

    assert_eq!(telemetry.fixed_point.attempted_iterations, 0);
    assert!(telemetry.fixed_point.converged);
    assert!(!telemetry.fixed_point.hit_iteration_limit);
}

#[test]
fn test_mir_pipeline_v3_has_no_legacy_repair_artifacts() {
    let output = decompile_program_with_mir(MIR_V3_SMOKE_HEX, Some(ScriptVersion::PlutusV3));

    assert!(
        !output.contains("Data.Constr("),
        "unexpected Data.Constr artifact: {output}"
    );
    assert!(
        !output.contains("delay("),
        "unexpected delay artifact: {output}"
    );
}

#[test]
fn test_mir_pipeline_v2_has_no_legacy_repair_artifacts() {
    let output = decompile_program_with_mir(MIR_V2_SMOKE_HEX, Some(ScriptVersion::PlutusV2));

    assert!(
        !output.contains("Data.Constr("),
        "unexpected Data.Constr artifact: {output}"
    );
    assert!(
        !output.contains("fn_call("),
        "unexpected fn_call artifact: {output}"
    );
    assert!(
        !output.contains("acc_2(acc_2"),
        "unexpected self-application artifact: {output}"
    );
}

#[test]
fn test_pipeline_skips_removed_scott_ballast_passes() {
    let passes = collect_mir_passes(MIR_V2_SMOKE_HEX, Some(ScriptVersion::PlutusV2));

    assert!(
        !passes.contains(&"resolve_scott_encoding"),
        "pipeline should not reference removed Scott encoding ballast: {passes:?}"
    );
    assert!(
        !passes.contains(&"repair_legacy_scott_if_dispatch"),
        "pipeline should not reference removed Scott-if ballast: {passes:?}"
    );
    assert!(
        !passes.contains(&"cleanup_recursive_self_applications"),
        "pipeline should not reference removed recursive self-application ballast: {passes:?}"
    );
}

#[test]
fn test_mir_pipeline_skips_late_data_constr_repair_pass() {
    let passes = collect_mir_passes(MIR_V2_SMOKE_HEX, Some(ScriptVersion::PlutusV2));

    assert!(
        !passes.contains(&"resolve_data_constr"),
        "MIR path should only use Data.Constr cleanup as a fallback when artifacts remain: {passes:?}"
    );
}

#[test]
fn test_mir_pipeline_skips_late_data_case_repair_pass() {
    let passes = collect_mir_passes(MIR_V2_SMOKE_HEX, Some(ScriptVersion::PlutusV2));

    assert!(
        !passes.contains(&"resolve_data_case"),
        "MIR path should not rely on late Data.case cleanup after MIR choose_data recognition: {passes:?}"
    );
}

#[test]
fn test_mir_pipeline_skips_late_expect_unpack_repair_pass() {
    let passes = collect_mir_passes(MIR_V2_SMOKE_HEX, Some(ScriptVersion::PlutusV2));

    assert!(
        !passes.contains(&"resolve_expect_constr_unpack"),
        "MIR path should not rely on late expect/unpack cleanup when no standalone expect! unpack-tag check survives lowering: {passes:?}"
    );
}

#[test]
fn test_mir_pipeline_skips_double_rec_fn_repair_pass() {
    let passes = collect_mir_passes(MIR_V2_SMOKE_HEX, Some(ScriptVersion::PlutusV2));

    assert!(
        !passes.contains(&"simplify_double_rec_fn"),
        "MIR path should not rely on late nested-rec cleanup when no double-rec artifact survives lowering: {passes:?}"
    );
}

#[test]
fn test_mir_pipeline_skips_when_field_destructure_repair_pass() {
    let passes = collect_mir_passes(MIR_V2_SMOKE_HEX, Some(ScriptVersion::PlutusV2));

    assert!(
        !passes.contains(&"destructure_when_fields"),
        "MIR path should not rely on late when-field destructuring when no unpack(subject) field-access pattern survives lowering: {passes:?}"
    );
}

#[test]
fn test_mir_pipeline_skips_complex_when_subject_extraction_pass() {
    let passes = collect_mir_passes(MIR_V2_SMOKE_HEX, Some(ScriptVersion::PlutusV2));

    assert!(
        !passes.contains(&"extract_complex_when_subjects"),
        "MIR path should not rely on late complex-when subject extraction when no complex subject survives lowering: {passes:?}"
    );
}

#[test]
fn test_mir_pipeline_skips_immediate_lambda_application_resolution_pass() {
    let passes = collect_mir_passes(MIR_V2_SMOKE_HEX, Some(ScriptVersion::PlutusV2));

    assert!(
        !passes.contains(&"resolve_immediate_applications"),
        "MIR path should not rely on late immediate-lambda application resolution when no saturated Apply(Lambda, args) survives lowering: {passes:?}"
    );
    assert!(
        !passes.contains(&"resolve_immediate_applications_late"),
        "MIR path should not rely on late immediate-lambda application resolution when no saturated Apply(Lambda, args) survives lowering: {passes:?}"
    );
}
