use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

use super::blueprint_registry::BlueprintHintRegistry;
use super::final_type_table::FinalTypeTable;
use super::late::normalize::{run_display_polish_layer, run_structural_final_cleanup};
use super::pipeline_passes::PipelinePassId;
use super::pipeline_runtime::{FixedPointTelemetry, MAX_FIXED_POINT_ITERATIONS, PipelineExecutor};
use super::type_solver::solve_type_constraints_with_final_table_versioned;
use super::*;

pub(in crate::decompile) fn apply_if_changed<F>(
    expr: &mut PseudoExpr,
    updated: PseudoExpr,
    pass: PipelinePassId,
    executor: &mut PipelineExecutor<'_, F>,
) -> bool
where
    F: FnMut(&'static str, &PseudoExpr),
{
    if updated.structural_eq(expr) {
        return false;
    }
    *expr = updated;
    executor.emit(pass, expr);
    true
}

fn uniquify_simplify_contract_output(expr: PseudoExpr) -> PseudoExpr {
    uniquify_let_names(expr)
}

fn retarget_scope_refs_if_needed(expr: PseudoExpr) -> PseudoExpr {
    if crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr) {
        crate::decompile::ref_retarget::retarget_refs_by_scope(expr)
    } else {
        expr
    }
}

fn normalize_simplify_contract_output(expr: PseudoExpr) -> PseudoExpr {
    retarget_scope_refs_if_needed(uniquify_simplify_contract_output(expr))
}

pub(in crate::decompile) fn run_late_pattern_recovery_cluster<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    let polish = &options.display_polish_passes;
    let structural = &options.structural_recovery_passes;

    expr = executor.ensure_consistent_ref_ids(expr);

    if polish.resolve_scott_constructor_lambdas_late {
        let late_scott = resolve_scott_constructor_lambdas(expr.clone());
        apply_if_changed(
            &mut expr,
            late_scott,
            PipelinePassId::ResolveScottConstructorLambdasLate,
            executor,
        );
    }

    if structural.resolve_immediate_applications && contains_immediate_lambda_application(&expr) {
        let resolved =
            normalize_simplify_contract_output(resolve_immediate_applications(expr.clone()));
        apply_if_changed(
            &mut expr,
            resolved,
            PipelinePassId::ResolveImmediateApplicationsLate,
            executor,
        );
    }

    if polish.resolve_data_case_late && contains_builtin_call_named(&expr, "Data.case") {
        let resolved = resolve_data_case(expr.clone());
        apply_if_changed(
            &mut expr,
            resolved,
            PipelinePassId::ResolveDataCaseLate,
            executor,
        );
    }

    if polish.simplify_boolean_and_identity {
        let late_bool = simplify_boolean_and_identity(expr.clone(), env);
        apply_if_changed(
            &mut expr,
            late_bool,
            PipelinePassId::SimplifyBooleanAndIdentityLate,
            executor,
        );
    }

    expr
}

#[cfg(test)]
mod tests;

#[derive(Clone, Copy)]
pub(in crate::decompile) struct TypeRefinementPasses {
    pub deduplicate: PipelinePassId,
    pub solve: PipelinePassId,
    pub propagate: PipelinePassId,
    pub resolve_cardano_fields: PipelinePassId,
}

#[derive(Clone, Copy)]
pub(in crate::decompile) struct PostReadabilityPasses {
    pub cps: PipelinePassId,
    pub boolean: PipelinePassId,
    pub eta: PipelinePassId,
    pub flatten: PipelinePassId,
}

#[derive(Default)]
pub(in crate::decompile) struct SimplifyContextArtifacts {
    pub field_names: std::collections::HashMap<String, String>,
    pub var_types: std::collections::HashMap<String, String>,
    pub field_names_by_id: std::collections::HashMap<crate::pseudo::var_id::VarId, String>,
    pub var_types_by_id: std::collections::HashMap<crate::pseudo::var_id::VarId, String>,
}

impl SimplifyContextArtifacts {
    fn absorb(&mut self, output: simplify::SimplifyOutput) -> PseudoExpr {
        self.field_names = output.context_field_names;
        self.var_types = output.context_var_types;
        self.field_names_by_id = output.context_field_names_by_id;
        self.var_types_by_id = output.context_var_types_by_id;
        output.expr
    }
}

#[allow(dead_code, clippy::too_many_arguments)]
pub(in crate::decompile) fn run_type_refinement_stage<F>(
    expr: PseudoExpr,
    script_version: Option<ScriptVersion>,
    env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    passes: TypeRefinementPasses,
    type_passes: &crate::decompile::TypePasses,
    kind_annotations: &mut std::collections::HashMap<VarId, VarKind>,
    blueprint_registry: &mut BlueprintHintRegistry,
    final_types: &mut Option<FinalTypeTable>,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    run_type_refinement_stage_with_blueprint(
        expr,
        script_version,
        env,
        passes,
        type_passes,
        kind_annotations,
        blueprint_registry,
        None,
        final_types,
        executor,
    )
}

/// Variant taking optional `DecompileOptions::blueprint_hints`.
#[allow(clippy::too_many_arguments)]
pub(in crate::decompile) fn run_type_refinement_stage_with_blueprint<F>(
    mut expr: PseudoExpr,
    script_version: Option<ScriptVersion>,
    _env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    passes: TypeRefinementPasses,
    type_passes: &crate::decompile::TypePasses,
    kind_annotations: &mut std::collections::HashMap<VarId, VarKind>,
    blueprint_registry: &mut BlueprintHintRegistry,
    blueprint_hints: Option<&crate::cardano::BlueprintHints>,
    final_types: &mut Option<FinalTypeTable>,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    if has_duplicate_binding_ids(&expr) {
        // dedup is a sanity prerequisite for solve; runs unconditionally
        // but its emit is gated by solve_type_constraints.
        expr = crate::decompile::varid_dedup::deduplicate_var_ids_with_annotations(
            expr,
            kind_annotations,
        );
        if type_passes.solve_type_constraints {
            executor.emit(passes.deduplicate, &expr);
        }
        expr = executor.ensure_consistent_ref_ids(expr);
    }
    if type_passes.solve_type_constraints {
        let (next_expr, solved) =
            solve_type_constraints_with_final_table_versioned(expr, script_version);
        expr = next_expr;
        *final_types = Some(solved);
        executor.emit(passes.solve, &expr);
    }

    if let Some(version) = script_version {
        if type_passes.propagate_types {
            expr = propagate_types_and_name_constructors_with_blueprint(
                expr,
                version,
                blueprint_registry,
                blueprint_hints,
                kind_annotations,
            );
            executor.emit(passes.propagate, &expr);
        }
        if type_passes.resolve_cardano_field_names {
            expr = resolve_cardano_field_names_with_var_kinds(expr, version, kind_annotations);
            executor.emit(passes.resolve_cardano_fields, &expr);
        }
    }

    expr
}

pub(in crate::decompile) fn run_initial_simplify_fixed_point_stage<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    sstate: &mut simplify::SimplifyState,
    preserved: &std::collections::HashSet<crate::pseudo::var_id::VarId>,
    env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    executor: &mut PipelineExecutor<'_, F>,
) -> (PseudoExpr, SimplifyContextArtifacts)
where
    F: FnMut(&'static str, &PseudoExpr),
{
    let mut artifacts = SimplifyContextArtifacts::default();
    let simplify_passes = &options.simplify_passes;

    if simplify_passes.simplify_fp_initial {
        let output = simplify::simplify_with_state_opts(
            expr,
            env,
            options.safe_mode,
            options.script_version,
            options.use_varkind_recovery,
            sstate,
        );
        expr = artifacts.absorb(output);
        expr = normalize_simplify_contract_output(expr);
        executor.emit(PipelinePassId::Simplify1, &expr);
    }

    if !options.safe_mode {
        let mut fixed_point = FixedPointTelemetry::default();

        if simplify_passes.inline_single_use {
            expr = inline_single_use_preserving(expr, preserved);
            executor.emit(PipelinePassId::InlineSingleUse, &expr);

            if simplify_passes.simplify_fp_initial {
                let output = simplify::simplify_with_state_opts(
                    expr,
                    env,
                    options.safe_mode,
                    options.script_version,
                    options.use_varkind_recovery,
                    sstate,
                );
                expr = artifacts.absorb(output);
                expr = normalize_simplify_contract_output(expr);
                executor.emit(PipelinePassId::Simplify2, &expr);
            }
        }

        if simplify_passes.inline_fp && simplify_passes.simplify_fp_initial {
            for iteration in 0..MAX_FIXED_POINT_ITERATIONS {
                fixed_point.attempted_iterations = iteration + 1;
                let unique = uniquify_let_names(expr.clone());
                let inlined = inline_single_use_preserving(unique, preserved);
                if !inlined.structural_eq(&expr) {
                    executor.emit(PipelinePassId::InlineFp, &inlined);
                }
                let output = simplify::simplify_with_state_opts(
                    inlined,
                    env,
                    options.safe_mode,
                    options.script_version,
                    options.use_varkind_recovery,
                    sstate,
                );
                let repaired = artifacts.absorb(output);
                let repaired = normalize_simplify_contract_output(repaired);
                if repaired.structural_eq(&expr) {
                    fixed_point.converged = true;
                    break;
                }
                expr = repaired;
                executor.emit(PipelinePassId::SimplifyFp, &expr);
                if iteration + 1 == MAX_FIXED_POINT_ITERATIONS {
                    fixed_point.converged = false;
                    fixed_point.hit_iteration_limit = true;
                }
            }
            executor.set_fixed_point_telemetry(fixed_point);
        }
    }

    (expr, artifacts)
}

pub(in crate::decompile) fn run_safe_mode_post_simplify_recovery_stage<F>(
    mut expr: PseudoExpr,
    structural: &StructuralRecoveryPasses,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    expr = executor.ensure_consistent_ref_ids(expr);
    expr = simplify::convert_expect_tag_to_constr_when(expr);
    executor.emit(PipelinePassId::ConvertExpectTag, &expr);

    if structural.recover_let_bound_tag_dispatch {
        let recovered = recover_let_bound_tag_if_dispatch(expr.clone());
        apply_if_changed(
            &mut expr,
            recovered,
            PipelinePassId::RecoverLetBoundTagIfDispatch,
            executor,
        );
    }

    expr
}

pub(in crate::decompile) fn run_context_field_resolution_stage<F>(
    mut expr: PseudoExpr,
    script_version: Option<ScriptVersion>,
    artifacts: &SimplifyContextArtifacts,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    expr = executor.ensure_consistent_ref_ids(expr);

    if let Some(version) = script_version {
        let sum_overrides = simplify::detect_sum_type_overrides(
            &expr,
            version,
            &artifacts.field_names,
            &artifacts.field_names_by_id,
        );
        expr = simplify::resolve_inline_field_accesses(
            expr,
            version,
            &artifacts.field_names,
            &artifacts.var_types,
            &sum_overrides,
            &artifacts.field_names_by_id,
            &artifacts.var_types_by_id,
        );
        executor.emit(PipelinePassId::ResolveFieldAccesses, &expr);
    }

    expr
}

pub(in crate::decompile) fn run_initial_postprocess_stage<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    kind_annotations: &mut std::collections::HashMap<VarId, VarKind>,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    expr = simplify::rename_validator_params_with_var_kinds_authoritative(
        expr,
        options.script_version,
        kind_annotations,
        options
            .blueprint_hints
            .as_ref()
            .map(|h| h.param_names.as_slice()),
        options.validator_shape.purpose,
    );
    executor.emit(PipelinePassId::RenameValidatorParams, &expr);

    expr = uniquify_let_names(expr);
    executor.emit(PipelinePassId::UniquifyFinal, &expr);

    expr = executor.ensure_consistent_ref_ids(expr);
    expr = collapse_tail_chains(expr);
    executor.emit(PipelinePassId::CollapseTailChains, &expr);

    expr
}

fn run_base_readability_cleanup<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    let polish = &options.display_polish_passes;

    if polish.eliminate_cps_selectors {
        expr = executor.ensure_consistent_ref_ids(expr);
        expr = simplify::eliminate_cps_selectors(expr, env);
        executor.emit(PipelinePassId::EliminateCpsSelectors, &expr);
    }
    if polish.simplify_boolean_and_identity {
        expr = executor.ensure_consistent_ref_ids(expr);
        expr = simplify_boolean_and_identity(expr, env);
        executor.emit(PipelinePassId::SimplifyBooleanAndIdentity, &expr);
    }
    if polish.collapse_eta_pair_selectors {
        expr = executor.ensure_consistent_ref_ids(expr);
        if contains_eta_pair_selector_when_subjects(&expr) {
            expr = collapse_eta_pair_selector_when_subjects(expr);
            executor.emit(PipelinePassId::CollapseEtaPairSelectorWhenSubjects, &expr);
        }
    }

    expr
}

fn run_post_inline_simplify_if_changed<F>(
    baseline: &PseudoExpr,
    options: &DecompileOptions,
    preserved: &std::collections::HashSet<crate::pseudo::var_id::VarId>,
    env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    simplify_state: &mut simplify::SimplifyState,
    use_varkind_recovery: bool,
    executor: &mut PipelineExecutor<'_, F>,
) -> Option<PseudoExpr>
where
    F: FnMut(&'static str, &PseudoExpr),
{
    let simplify_passes = &options.simplify_passes;

    if !simplify_passes.inline_post_readability {
        return None;
    }

    let late_unique = uniquify_let_names(baseline.clone());
    let late_inlined = inline_single_use_preserving(late_unique, preserved);
    if late_inlined.structural_eq(baseline) {
        return None;
    }

    executor.emit(PipelinePassId::InlinePostReadability, &late_inlined);
    // Thread `use_varkind_recovery` into this post-readability
    // simplify pass too so `single_field_collapse` dispatches by
    // VarKind here just like in the main simplify stages.
    let mut expr = if simplify_passes.simplify_fp_post_readability {
        let expr = simplify::simplify_with_state_opts(
            late_inlined,
            env,
            false,
            None,
            use_varkind_recovery,
            simplify_state,
        )
        .expr;
        executor.emit(PipelinePassId::SimplifyPostReadability, &expr);
        expr
    } else {
        late_inlined
    };
    expr = executor.ensure_consistent_ref_ids(expr);

    Some(run_base_readability_cleanup(expr, options, env, executor))
}

fn run_post_inline_post_flatten_cleanup<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    let polish = &options.display_polish_passes;
    let readability = &options.readability_passes;

    if readability.flatten_let_chains {
        expr = executor.ensure_consistent_ref_ids(expr);
        expr = flatten_let_chains(expr);
        executor.emit(PipelinePassId::FlattenLetChainsPostInline, &expr);
    }
    if polish.collapse_eta_pair_selectors && contains_eta_pair_selector_when_subjects(&expr) {
        expr = collapse_eta_pair_selector_when_subjects(expr);
        executor.emit(PipelinePassId::CollapseEtaPairSelectorWhenSubjects, &expr);
    }

    if polish.eliminate_cps_selectors {
        expr = executor.ensure_consistent_ref_ids(expr);
        let post_flatten_cps = simplify::eliminate_cps_selectors(expr.clone(), env);
        if !post_flatten_cps.structural_eq(&expr) {
            expr = post_flatten_cps;
            executor.emit(PipelinePassId::EliminateCpsSelectors, &expr);
            if polish.simplify_boolean_and_identity {
                expr = simplify_boolean_and_identity(expr, env);
                executor.emit(PipelinePassId::SimplifyBooleanAndIdentity, &expr);
            }
            if polish.collapse_eta_pair_selectors && contains_eta_pair_selector_when_subjects(&expr)
            {
                expr = collapse_eta_pair_selector_when_subjects(expr);
                executor.emit(PipelinePassId::CollapseEtaPairSelectorWhenSubjects, &expr);
            }
        }
    }

    expr
}

pub(in crate::decompile) fn run_post_inline_readability_cluster<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    preserved: &std::collections::HashSet<crate::pseudo::var_id::VarId>,
    env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    simplify_state: &mut simplify::SimplifyState,
    use_varkind_recovery: bool,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    if let Some(post_inline) = run_post_inline_simplify_if_changed(
        &expr,
        options,
        preserved,
        env,
        simplify_state,
        use_varkind_recovery,
        executor,
    ) {
        expr = run_post_inline_post_flatten_cleanup(post_inline, options, env, executor);
    }

    expr
}

pub(in crate::decompile) fn run_post_readability_cleanup_cluster<F>(
    mut expr: PseudoExpr,
    passes: PostReadabilityPasses,
    options: &DecompileOptions,
    env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    let polish = &options.display_polish_passes;
    let readability = &options.readability_passes;

    if polish.eliminate_cps_selectors {
        expr = executor.ensure_consistent_ref_ids(expr);
        let post_readability_cps = simplify::eliminate_cps_selectors(expr.clone(), env);
        if !post_readability_cps.structural_eq(&expr) {
            expr = post_readability_cps;
            executor.emit(passes.cps, &expr);
        }
    }

    if polish.simplify_boolean_and_identity {
        expr = executor.ensure_consistent_ref_ids(expr);
        let post_readability_bool = simplify_boolean_and_identity(expr.clone(), env);
        if !post_readability_bool.structural_eq(&expr) {
            expr = post_readability_bool;
            executor.emit(passes.boolean, &expr);
        }
    }

    if polish.collapse_eta_pair_selectors {
        expr = executor.ensure_consistent_ref_ids(expr);
        if contains_eta_pair_selector_when_subjects(&expr) {
            let collapsed = collapse_eta_pair_selector_when_subjects(expr.clone());
            if !collapsed.structural_eq(&expr) {
                expr = collapsed;
                executor.emit(passes.eta, &expr);
            }
        }
    }

    if readability.flatten_let_chains {
        expr = executor.ensure_consistent_ref_ids(expr);
        let post_readability_flattened = flatten_let_chains(expr.clone());
        if !post_readability_flattened.structural_eq(&expr) {
            expr = post_readability_flattened;
            executor.emit(passes.flatten, &expr);
        }
    }

    expr
}

pub(in crate::decompile) fn run_display_polish_cluster<F>(
    expr: PseudoExpr,
    options: &DecompileOptions,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    run_display_polish_layer(expr, options, executor)
}

pub(in crate::decompile) fn run_cleanup_normalization_cluster<F>(
    mut expr: PseudoExpr,
    polish: &crate::decompile::DisplayPolishPasses,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    if polish.strip_cosmetic_delays {
        expr = executor.ensure_consistent_ref_ids(expr);
        expr = strip_cosmetic_delays(expr);
        executor.emit(PipelinePassId::StripCosmeticDelays, &expr);
    }

    if polish.cancel_force_delay_vars {
        expr = executor.ensure_consistent_ref_ids(expr);
        expr = cancel_force_delay_vars(expr);
        executor.emit(PipelinePassId::CancelForceDelayVars, &expr);
    }

    if polish.normalize_list_cons_literals {
        expr = normalize_list_cons_literals(expr);
        executor.emit(PipelinePassId::NormalizeListConsLiterals, &expr);
    }

    expr
}

pub(in crate::decompile) fn run_pre_type_structural_recovery_cluster<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    blueprint_registry: &mut BlueprintHintRegistry,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    let structural = &options.structural_recovery_passes;
    let polish = &options.display_polish_passes;

    if polish.eliminate_cps_selectors {
        expr = executor.ensure_consistent_ref_ids(expr);
        expr = simplify::eliminate_cps_selectors(expr, env);
        executor.emit(PipelinePassId::EliminateCpsSelectors, &expr);
    }

    if polish.resolve_scott_constructor_lambdas_late {
        expr = executor.ensure_consistent_ref_ids(expr);
        let resolved = resolve_scott_constructor_lambdas(expr.clone());
        apply_if_changed(
            &mut expr,
            resolved,
            PipelinePassId::ResolveScottConstructorLambdas,
            executor,
        );
    }

    // resolve_data_constr is correctness-critical (Data.Constr lowering),
    // gate it under resolve_data_case which covers the broader Data.* family.
    if structural.resolve_data_case && contains_builtin_call_named(&expr, "Data.Constr") {
        expr = resolve_data_constr(expr);
        executor.emit(PipelinePassId::ResolveDataConstr, &expr);
    }

    if contains_builtin_call_named(&expr, "Constr.unpack")
        || contains_builtin_call_named(&expr, "Data.un_constr")
    {
        expr = executor.ensure_consistent_ref_ids(expr);
    }

    // lift_unpack_tag_when_subjects and destructure_when_fields are part of the
    // when-subject extraction surface — gate under extract_complex_when_subjects.
    if structural.extract_complex_when_subjects && contains_unpack_tag_when_subjects(&expr) {
        expr = lift_unpack_tag_when_subjects(
            expr,
            options.blueprint_hints.as_ref(),
            Some(blueprint_registry),
        );
        executor.emit(PipelinePassId::LiftUnpackTagWhenSubjects, &expr);
    }

    if structural.extract_complex_when_subjects && contains_destructurable_when_fields(&expr) {
        expr = destructure_when_fields(
            expr,
            options.blueprint_hints.as_ref(),
            Some(blueprint_registry),
        );
        executor.emit(PipelinePassId::DestructureWhenFields, &expr);
    }

    if structural.simplify_double_rec_fn && contains_nested_recfn_body(&expr) {
        expr = executor.ensure_consistent_ref_ids(expr);
        expr = simplify_double_rec_fn(expr);
        executor.emit(PipelinePassId::SimplifyDoubleRecFn, &expr);
    }

    // Must run BEFORE simplify_z_combinator — the pair U-comb
    // template anchors on the named 2-param RecFn knot shape the
    // Z-combinator rewrites would consume. Fail-closed: anything
    // but the exact church-pair fixpoint template is left alone.
    if structural.recover_pair_fixpoint {
        expr = executor.ensure_consistent_ref_ids(expr);
        // Emit only on an actual recovery, so pass-tracking tests don't see
        // this inert pass "fire" on inputs it leaves untouched.
        let updated = recover_pair_fixpoint(expr.clone());
        apply_if_changed(
            &mut expr,
            updated,
            PipelinePassId::RecoverPairFixpoint,
            executor,
        );
    }

    if structural.simplify_z_combinator {
        expr = simplify_z_combinator(expr);
        executor.emit(PipelinePassId::SimplifyZCombinator, &expr);
    }

    if structural.extract_complex_when_subjects && contains_complex_when_subjects(&expr) {
        expr = normalize_simplify_contract_output(extract_complex_when_subjects(expr));
        executor.emit(PipelinePassId::ExtractComplexWhenSubjects, &expr);
    }

    if polish.collapse_eta_pair_selectors {
        expr = executor.ensure_consistent_ref_ids(expr);
        if contains_eta_pair_selector_when_subjects(&expr) {
            expr = collapse_eta_pair_selector_when_subjects(expr);
            executor.emit(PipelinePassId::CollapseEtaPairSelectorWhenSubjects, &expr);
        }
    }

    // resolve_expect_constr_unpack is part of the structural recovery family.
    if structural.resolve_data_case && contains_expect_unpack_tag_check(&expr) {
        expr = resolve_expect_constr_unpack(expr, options.script_version);
        executor.emit(PipelinePassId::ResolveExpectConstrUnpack, &expr);
    }

    // disambiguate_constructors is correctness-critical for blueprint-aware ADTs;
    // gate under resolve_data_case (the cluster anchor for Data.*-shaped passes).
    if structural.resolve_data_case {
        expr = executor.ensure_consistent_ref_ids(expr);
        expr = disambiguate_constructors(
            expr,
            options.blueprint_hints.as_ref(),
            blueprint_registry,
            options.ordering_names,
        );
        executor.emit(PipelinePassId::DisambiguateConstructors, &expr);
    }

    if polish.simplify_boolean_and_identity {
        expr = simplify_boolean_and_identity(expr, env);
        executor.emit(PipelinePassId::SimplifyBooleanAndIdentity, &expr);
    }

    if structural.resolve_immediate_applications && contains_immediate_lambda_application(&expr) {
        expr = normalize_simplify_contract_output(resolve_immediate_applications(expr));
        executor.emit(PipelinePassId::ResolveImmediateApplications, &expr);
    }

    if structural.resolve_data_case && contains_builtin_call_named(&expr, "Data.case") {
        expr = executor.ensure_consistent_ref_ids(expr);
        expr = resolve_data_case(expr);
        executor.emit(PipelinePassId::ResolveDataCase, &expr);
    }

    expr
}

pub(in crate::decompile) fn run_structural_final_cleanup_stage<F>(
    mut expr: PseudoExpr,
    env: Option<&crate::decompile::mid::type_env::TypeEnvironment>,
    options: &DecompileOptions,
    kind_annotations: &mut std::collections::HashMap<VarId, VarKind>,
    blueprint_registry: &mut BlueprintHintRegistry,
    final_types: &mut Option<FinalTypeTable>,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    expr = run_structural_final_cleanup(expr, env, options, kind_annotations);
    executor.emit(PipelinePassId::StructuralFinalCleanup, &expr);

    if options.type_passes.any_enabled() {
        if has_duplicate_binding_ids(&expr) {
            expr = crate::decompile::varid_dedup::deduplicate_var_ids_with_annotations(
                expr,
                kind_annotations,
            );
            executor.emit(PipelinePassId::DeduplicateVarIdsFinal, &expr);
        }
        let (next_expr, solved) =
            solve_type_constraints_with_final_table_versioned(expr, options.script_version);
        expr = next_expr;
        executor.emit(PipelinePassId::SolveTypeConstraintsFinal, &expr);
        *final_types = Some(solved);

        // Collapse `when X is { Constr<1> -> T; _ -> E }` to
        // `if X { T } else { E }` when X is provably Bool. Runs
        // immediately after the final type-solve so `final_types`
        // is authoritative; runs before `propagate_types_final` so
        // downstream propagation sees the collapsed If shape.
        if let Some(table) = final_types.as_ref() {
            expr = crate::decompile::simplify::postprocess::bool_constr_collapse(expr, table);
            executor.emit(PipelinePassId::BoolConstrCollapseFinal, &expr);
        }

        if let Some(version) = options.script_version {
            expr = propagate_types_and_name_constructors_with_blueprint(
                expr,
                version,
                blueprint_registry,
                options.blueprint_hints.as_ref(),
                kind_annotations,
            );
            executor.emit(PipelinePassId::PropagateTypesFinal, &expr);
            expr = resolve_cardano_field_names_with_var_kinds(expr, version, kind_annotations);
            executor.emit(PipelinePassId::ResolveCardanoFieldNamesFinal, &expr);
            // Helper hoist + single-use inlining can drop the aliases
            // `introduce_field_index_aliases` bound, stranding uses of
            // names no longer in scope. Inline those back to a chained
            // access through the closest in-scope Cardano context anchor.
            expr = executor.ensure_consistent_ref_ids(expr);
            expr = inline_dangling_field_aliases(
                expr,
                version,
                kind_annotations,
                options.use_varkind_recovery,
            );
            executor.emit(PipelinePassId::InlineDanglingFieldAliases, &expr);
        }
    }

    // Final retarget after late transforms that invalidate `ConsistentRefIds`,
    // such as `inline_dangling_field_aliases`. Passes after the display-polish
    // boundary that only preserve the property must not lean on this call: the
    // executor skips retargeting while the property bit is still satisfied.
    expr = executor.ensure_consistent_ref_ids(expr);

    expr
}

#[allow(clippy::too_many_arguments)]
pub(in crate::decompile) fn run_readability_pipeline_stage<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    simplify_state: &mut simplify::SimplifyState,
    preserved: &std::collections::HashSet<crate::pseudo::var_id::VarId>,
    type_env: &crate::decompile::mid::type_env::TypeEnvironment,
    blueprint_registry: &mut BlueprintHintRegistry,
    final_types: &mut Option<FinalTypeTable>,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    if options.simplify_passes.dead_let_elim {
        expr = executor.ensure_consistent_ref_ids(expr);
        expr = eliminate_dead_lets_pseudo(expr);
        executor.emit(PipelinePassId::EliminateDeadLets, &expr);
    }

    let readability = &options.readability_passes;
    if !options.safe_mode {
        if readability.improve_variable_names {
            expr = semantic_improve_variable_names(expr);
            annotate_post_naming_call_results(
                &expr,
                &mut simplify_state.var_kinds.kind_annotations,
            );
            executor.emit(PipelinePassId::ImproveVariableNames, &expr);
        }
        if readability.flatten_let_chains {
            expr = executor.ensure_consistent_ref_ids(expr);
            expr = flatten_let_chains(expr);
            executor.emit(PipelinePassId::FlattenLetChains, &expr);
        }
        if options.simplify_passes.inline_post_readability
            || options.simplify_passes.simplify_fp_post_readability
            || options.display_polish_passes.eliminate_cps_selectors
            || options.display_polish_passes.simplify_boolean_and_identity
            || options.display_polish_passes.collapse_eta_pair_selectors
        {
            expr = run_post_inline_readability_cluster(
                expr,
                options,
                preserved,
                Some(type_env),
                simplify_state,
                options.use_varkind_recovery,
                executor,
            );
        }
    }

    if !options.safe_mode && options.display_polish_passes.any_enabled() {
        expr = run_post_readability_cleanup_cluster(
            expr,
            PostReadabilityPasses {
                cps: PipelinePassId::EliminateCpsSelectorsPostReadability,
                boolean: PipelinePassId::SimplifyBooleanAndIdentityPostReadability,
                eta: PipelinePassId::CollapseEtaPairSelectorWhenSubjectsPostReadability,
                flatten: PipelinePassId::FlattenLetChainsPostReadability,
            },
            options,
            Some(type_env),
            executor,
        );
    }

    if !options.safe_mode && options.display_polish_passes.any_enabled() {
        expr = run_display_polish_cluster(expr, options, executor);
    }

    if options.type_passes.any_enabled() {
        expr = run_type_refinement_stage_with_blueprint(
            expr,
            options.script_version,
            Some(type_env),
            TypeRefinementPasses {
                deduplicate: PipelinePassId::DeduplicateVarIdsForTypeRefinement,
                solve: PipelinePassId::SolveTypeConstraintsLate,
                propagate: PipelinePassId::PropagateTypesLate,
                resolve_cardano_fields: PipelinePassId::ResolveCardanoFieldNamesLate,
            },
            &options.type_passes,
            &mut simplify_state.var_kinds.kind_annotations,
            blueprint_registry,
            options.blueprint_hints.as_ref(),
            final_types,
            executor,
        );
    }

    if !options.safe_mode && options.structural_recovery_passes.any_enabled() {
        expr = run_late_pattern_recovery_cluster(expr, options, Some(type_env), executor);

        if options.type_passes.any_enabled() {
            expr = run_type_refinement_stage_with_blueprint(
                expr,
                options.script_version,
                Some(type_env),
                TypeRefinementPasses {
                    deduplicate: PipelinePassId::DeduplicateVarIdsForTypeRefinement,
                    solve: PipelinePassId::SolveTypeConstraintsPostLateStructural,
                    propagate: PipelinePassId::PropagateTypesPostLateStructural,
                    resolve_cardano_fields:
                        PipelinePassId::ResolveCardanoFieldNamesPostLateStructural,
                },
                &options.type_passes,
                &mut simplify_state.var_kinds.kind_annotations,
                blueprint_registry,
                options.blueprint_hints.as_ref(),
                final_types,
                executor,
            );
        }
    }

    expr
}

/// Annotate every `<callee>_result(_<N>)?`-named Let binder with
/// `VarKind::CallResult { callee }` when the value matches
/// `Apply(Var(callee), ...)`. Name matching goes through
/// `Simplifier::call_result_callee_for_binding_name`, which
/// strips disambiguation suffixes, so `lookup_result_2` counts.
///
/// `semantic_improve_variable_names` mints these display names
/// without annotating the binder's VarKind, leaving downstream
/// recovery passes with no `kind_annotations` entry.
fn annotate_post_naming_call_results(
    expr: &PseudoExpr,
    kind_annotations: &mut std::collections::HashMap<VarId, VarKind>,
) {
    fn walk(expr: &PseudoExpr, kind_annotations: &mut std::collections::HashMap<VarId, VarKind>) {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(cur) = pending.pop() {
            if let PseudoExpr::Let {
                name, id, value, ..
            } = cur
                && let Some(vid) = id.get()
                && let std::collections::hash_map::Entry::Vacant(entry) =
                    kind_annotations.entry(vid)
                && let Some(callee) =
                    crate::decompile::simplify::Simplifier::call_result_callee_for_binding_name(
                        name, value,
                    )
            {
                entry.insert(VarKind::CallResult { callee });
            }
            match cur {
                PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                    pending.push(body);
                }
                PseudoExpr::Apply { function, args } => {
                    pending.extend(args.iter().rev());
                    pending.push(function);
                }
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(body);
                    pending.push(value);
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(else_branch);
                    pending.push(then_branch);
                    pending.push(condition);
                }
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    let mut order: Vec<&PseudoExpr> = Vec::new();
                    order.push(subject);
                    for c in clauses {
                        if let Some(g) = &c.guard {
                            order.push(g);
                        }
                        order.push(&c.body);
                    }
                    pending.extend(order.into_iter().rev());
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        pending.push(t);
                    }
                    pending.extend(elements.iter().rev());
                }
                PseudoExpr::Tuple(items) => pending.extend(items.iter().rev()),
                PseudoExpr::Pair(a, b) => {
                    pending.push(b);
                    pending.push(a);
                }
                PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter().rev()),
                PseudoExpr::FieldAccess { record, .. } => pending.push(record),
                PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                PseudoExpr::UnOp { operand, .. } => pending.push(operand),
                PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter().rev()),
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
                PseudoExpr::Trace { message, value } => {
                    pending.push(value);
                    pending.push(message);
                }
                _ => {}
            }
        }
    }
    walk(expr, kind_annotations);
}
