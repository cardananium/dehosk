use crate::error::{DecompileError, Result};
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;
use std::collections::HashMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use uplc::ast::{NamedDeBruijn, Program};

// Submodules of `pipeline/`. They live solely as children of `pipeline`
// and are NOT cross-mounted into `decompile/` via `#[path]`, which would
// compile the same files twice. Outside callers reach them via the
// re-export `decompile::{pipeline_passes, pipeline_runtime, pipeline_stages}`.
pub(crate) mod pipeline_passes;
pub(crate) mod pipeline_runtime;
pub(crate) mod pipeline_stages;

use self::pipeline_passes::PipelinePassId;
use self::pipeline_runtime::{PipelineExecutor, PipelineTelemetry};
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::decompile) use self::pipeline_stages::run_type_refinement_stage;
use self::pipeline_stages::{
    TypeRefinementPasses, run_cleanup_normalization_cluster, run_context_field_resolution_stage,
    run_initial_postprocess_stage, run_initial_simplify_fixed_point_stage,
    run_pre_type_structural_recovery_cluster, run_readability_pipeline_stage,
    run_safe_mode_post_simplify_recovery_stage, run_structural_final_cleanup_stage,
    run_type_refinement_stage_with_blueprint,
};
use super::blueprint_registry::BlueprintHintRegistry;
use super::final_type_table::FinalTypeTable;
use super::nameless_post_pipeline::{
    NamelessPostPipelineGuardReport, run_default_nameless_post_pipeline_preserving,
};
use super::pseudo_lineage::{project_chained_pseudo_to_mid_with_heirs, snapshot_expr};
use super::type_invariants::validate_type_invariants;
use super::*;

struct PipelineSeed {
    expr: PseudoExpr,
    simplify_state: simplify::SimplifyState,
    mir_source_map: Option<crate::decompile::mid::source_map::SourceMap>,
    mir_var_registry: Option<crate::decompile::mid::var_registry::VarRegistry>,
    type_env: std::rc::Rc<crate::decompile::mid::type_env::TypeEnvironment>,
    /// VarIds of Let-bound lambdas whose MIR signature was recorded.
    /// Computed once from the seed expression and shared with every pass
    /// that might inline or hoist Let-bound helpers.
    preserved_helper_ids: std::collections::HashSet<crate::pseudo::var_id::VarId>,
    /// Constructor display names for rendering, seeded with canonical
    /// Cardano-schema names and extended by structural passes with
    /// user-ADT constructors from blueprint hints, so the render layer
    /// resolves names without the inline `display_name` field.
    blueprint_registry: BlueprintHintRegistry,
}

// The debugger is this item's only consumer and is not in this
// build; the plumbing is still produced in full.
#[allow(dead_code)]
pub(crate) struct PipelineOutput {
    pub expr: PseudoExpr,
    pub mir_source_map: Option<crate::decompile::mid::source_map::SourceMap>,
    pub mir_var_registry: Option<crate::decompile::mid::var_registry::VarRegistry>,
    pub telemetry: PipelineTelemetry,
    /// Guard outcomes from the default nameless post-pipeline run that
    /// produced `expr`.
    #[allow(dead_code)] // public API — exposed for tests/diagnostics
    pub nameless_guard_report: NamelessPostPipelineGuardReport,
    /// Mint-site VarKind annotations from
    /// `SimplifyState::var_kinds.kind_annotations`; authoritative for kinds
    /// set at simplifier mint sites (e.g. `introduce_field_index_aliases` →
    /// `FieldIndexAlias`). Empty until a mint-site populator fires.
    #[allow(dead_code)]
    pub kind_annotations:
        std::collections::HashMap<crate::pseudo::var_id::VarId, crate::pseudo::nameless::VarKind>,
    /// Frozen type environment from MIR lowering, indexed by canonical
    /// MIR `VarId`s. Use it for MIR-keyed lookups only; types anchored
    /// to the final AST live in `final_types`.
    #[allow(dead_code)]
    pub type_env: std::rc::Rc<crate::decompile::mid::type_env::TypeEnvironment>,
    /// Constructor display names for rendering: canonical
    /// Cardano-schema names plus user-defined ADTs that
    /// `adt_disambiguation` resolves from blueprint hints, so the
    /// rendering API resolves names without reading the inline
    /// `display_name` field.
    pub blueprint_registry: std::rc::Rc<BlueprintHintRegistry>,
    /// Solved types anchored to the last AST the type solver saw in the core
    /// pipeline; later display/render-prep rewrites can still change
    /// declaration ids, so covering those outputs needs an explicit remap or
    /// re-solve. When no solve fired (e.g. `options.infer_types` off) this is
    /// an empty+frozen table, not an `Option`, so consumers always get a
    /// well-formed handle. Distinct from `TypeEnvironment` on purpose: the
    /// solver-boundary table for typed-output consumers, where `type_env`
    /// stays the frozen MIR-keyed env.
    #[allow(dead_code)]
    pub final_types: std::rc::Rc<FinalTypeTable>,
    /// Route provenance of every mid. `Some` only when
    /// `options.record_lineage_routes` is set, which no production path does.
    pub lineage_routes: Option<crate::decompile::pseudo_lineage::RouteRecorder>,
    /// The program's church-bool convention plus the three structural
    /// signals behind the verdict, detected ONCE on the freshly-lowered
    /// seed. The pipeline consumed the verdict itself (via
    /// `SimplifyState`); the render half needs it for its `RenderCtx`
    /// and the `--emit polarity-report` layer renders the signals.
    pub church_polarity_signals: crate::decompile::church_polarity::ChurchPolaritySignals,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
// `Pseudo` postfix is intentional — these stages run on PseudoExpr (the
// IR named in pseudo::ast). Stripping it would conflate them with
// nameless / mid stages elsewhere in the pipeline.
#[allow(clippy::enum_variant_names)]
enum CorePipelineStageId {
    InitialPseudo,
    CleanupPseudo,
    StructuralPseudo,
}

impl CorePipelineStageId {
    fn validation_stage(self) -> &'static str {
        match self {
            Self::InitialPseudo => "initial_pseudo_pipeline",
            Self::CleanupPseudo => "cleanup_pseudo_pipeline",
            Self::StructuralPseudo => "structural_pseudo_pipeline",
        }
    }
}

const CORE_PIPELINE_STAGES: &[CorePipelineStageId] = &[
    CorePipelineStageId::InitialPseudo,
    CorePipelineStageId::CleanupPseudo,
    CorePipelineStageId::StructuralPseudo,
];

fn build_pipeline_seed<F>(
    program: &Program<NamedDeBruijn>,
    options: &DecompileOptions,
    executor: &mut PipelineExecutor<'_, F>,
) -> Result<PipelineSeed>
where
    F: FnMut(&'static str, &PseudoExpr),
{
    let mid::lower::MirDecompileOutput {
        pseudo,
        source_map,
        var_registry,
        mut simplify_state,
        type_env,
    } = mid::lower::decompile_via_mir_output_with_options(
        program,
        options.script_version,
        options.safe_mode,
        // The pseudo -> mid map the lowering builds is read only by the
        // final-pseudo lineage projection, which is itself a no-op unless
        // snapshots are collected.
        executor.collects_snapshots(),
    )?;
    executor.emit(PipelinePassId::LowerMir, &pseudo);

    // Collect user-declared helpers while type_env is still the frozen MIR
    // output and every Let-bound signature-bearing lambda is visible. The set
    // reaches the three post-MIR `inline_single_use_preserving` call sites via
    // the seed's `preserved_helper_ids`, and `let_binding.rs`'s small-function
    // inlining guard via `simplify_state.helpers.preserved_helper_ids`, copied
    // into every `Simplifier` by `simplify_with_state`. Only fully-concrete
    // signatures qualify, so synthesized closures (CPS, Scott clauses,
    // curry-lifted args) stay out.
    let preserved_helper_ids = super::preserved_helper_ids(&pseudo, type_env.as_ref());
    simplify_state.helpers.preserved_helper_ids = preserved_helper_ids.clone();

    Ok(PipelineSeed {
        expr: pseudo,
        simplify_state,
        mir_source_map: Some(source_map),
        mir_var_registry: Some(var_registry),
        type_env,
        preserved_helper_ids,
        blueprint_registry: BlueprintHintRegistry::with_cardano_seed(options.script_version),
    })
}

/// Structural walk kept as the pipeline's per-stage validation hook.
pub(crate) fn validate_known_builtins(expr: &PseudoExpr, _stage: &'static str) -> Result<()> {
    // `_stage` is intentional: the walk threads it through but never reads it,
    // keeping the caller's stage available for the diagnostics a restored check
    // would emit.
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        pending.extend(crate::decompile::render_prep::scope_recurse::children(
            current,
        ));
    }
    Ok(())
}

fn run_initial_pseudo_pipeline<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    sstate: &mut simplify::SimplifyState,
    preserved: &std::collections::HashSet<crate::pseudo::var_id::VarId>,
    type_env: &crate::decompile::mid::type_env::TypeEnvironment,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    // Seed validator-entrypoint parameter names (`script_context`, `datum`,
    // `redeemer`) on the freshly-lowered MIR tree so the simplify fixed
    // point treats them as protected; otherwise later inlining beta-reduces
    // the outer lambda away and the name never reaches the output.
    expr = simplify::rename_validator_params_with_var_kinds(
        expr,
        options.script_version,
        &mut sstate.var_kinds.kind_annotations,
        options
            .blueprint_hints
            .as_ref()
            .map(|h| h.param_names.as_slice()),
        options.validator_shape.purpose,
    );
    executor.emit(PipelinePassId::RenameValidatorParams, &expr);

    if options.readability_passes.rename_variables {
        expr = crate::decompile::rename::rename_variables_with_kind_annotations(
            expr,
            &mut sstate.var_kinds.kind_annotations,
        );
        executor.emit(PipelinePassId::RenameVariables, &expr);
    }

    if options.simplify_passes.any_enabled() {
        let (next_expr, artifacts) = run_initial_simplify_fixed_point_stage(
            expr,
            options,
            sstate,
            preserved,
            Some(type_env),
            executor,
        );
        expr = next_expr;

        if !options.safe_mode {
            expr = run_safe_mode_post_simplify_recovery_stage(
                expr,
                &options.structural_recovery_passes,
                executor,
            );
        }

        expr =
            run_context_field_resolution_stage(expr, options.script_version, &artifacts, executor);

        expr = run_initial_postprocess_stage(
            expr,
            options,
            &mut sstate.var_kinds.kind_annotations,
            executor,
        );
    }

    expr
}

fn run_cleanup_pseudo_pipeline<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    if !options.safe_mode && options.display_polish_passes.any_enabled() {
        expr = run_cleanup_normalization_cluster(expr, &options.display_polish_passes, executor);
    }

    expr
}

#[allow(clippy::too_many_arguments)]
fn run_structural_pseudo_pipeline<F>(
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
    if !options.safe_mode && options.structural_recovery_passes.any_enabled() {
        expr = run_pre_type_structural_recovery_cluster(
            expr,
            options,
            Some(type_env),
            blueprint_registry,
            executor,
        );
    }

    if options.type_passes.any_enabled() {
        expr = run_type_refinement_stage_with_blueprint(
            expr,
            options.script_version,
            Some(type_env),
            TypeRefinementPasses {
                deduplicate: PipelinePassId::DeduplicateVarIdsForTypeRefinement,
                solve: PipelinePassId::SolveTypeConstraints,
                propagate: PipelinePassId::PropagateTypes,
                resolve_cardano_fields: PipelinePassId::ResolveCardanoFieldNames,
            },
            &options.type_passes,
            &mut simplify_state.var_kinds.kind_annotations,
            blueprint_registry,
            options.blueprint_hints.as_ref(),
            final_types,
            executor,
        );
    }

    expr = run_readability_pipeline_stage(
        expr,
        options,
        simplify_state,
        preserved,
        type_env,
        blueprint_registry,
        final_types,
        executor,
    );

    // Populate kind_annotations BEFORE structural_final_cleanup runs
    // its recovery passes (`recover_missing_option_payload_binders`,
    // `try_recover_generated_constructor_fields`, etc.) so they see a
    // complete table. The later post-pipeline call still matters for
    // binders minted in between; the populator is idempotent, so both
    // runs end at the same table.
    sync_late_var_kind_annotations(&expr, &mut simplify_state.var_kinds.kind_annotations);

    expr = run_structural_final_cleanup_stage(
        expr,
        Some(type_env),
        options,
        &mut simplify_state.var_kinds.kind_annotations,
        blueprint_registry,
        final_types,
        executor,
    );

    expr
}

#[allow(clippy::too_many_arguments)]
fn run_core_pipeline_stage<F>(
    stage: CorePipelineStageId,
    expr: PseudoExpr,
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
    match stage {
        CorePipelineStageId::InitialPseudo => run_initial_pseudo_pipeline(
            expr,
            options,
            simplify_state,
            preserved,
            type_env,
            executor,
        ),
        CorePipelineStageId::CleanupPseudo => run_cleanup_pseudo_pipeline(expr, options, executor),
        CorePipelineStageId::StructuralPseudo => run_structural_pseudo_pipeline(
            expr,
            options,
            simplify_state,
            preserved,
            type_env,
            blueprint_registry,
            final_types,
            executor,
        ),
    }
}

fn extract_panic_message(panic_info: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = panic_info.downcast_ref::<&str>() {
        (*message).to_string()
    } else if let Some(message) = panic_info.downcast_ref::<String>() {
        message.clone()
    } else {
        "unknown panic".to_string()
    }
}

fn catch_internal_stage_panic<T, F>(stage: &'static str, f: F) -> Result<T>
where
    F: FnOnce() -> T,
{
    catch_unwind(AssertUnwindSafe(f)).map_err(|panic_info| {
        DecompileError::internal(format!(
            "core pipeline stage `{stage}` panicked: {}",
            extract_panic_message(panic_info)
        ))
    })
}

#[allow(clippy::too_many_arguments)]
fn run_core_pseudo_pipeline<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    simplify_state: &mut simplify::SimplifyState,
    preserved: &std::collections::HashSet<crate::pseudo::var_id::VarId>,
    type_env: &crate::decompile::mid::type_env::TypeEnvironment,
    blueprint_registry: &mut BlueprintHintRegistry,
    final_types: &mut Option<FinalTypeTable>,
    executor: &mut PipelineExecutor<'_, F>,
) -> Result<PseudoExpr>
where
    F: FnMut(&'static str, &PseudoExpr),
{
    for stage in CORE_PIPELINE_STAGES {
        expr = catch_internal_stage_panic(stage.validation_stage(), || {
            run_core_pipeline_stage(
                *stage,
                expr,
                options,
                simplify_state,
                preserved,
                type_env,
                blueprint_registry,
                final_types,
                executor,
            )
        })?;
        validate_known_builtins(&expr, stage.validation_stage())?;
    }

    Ok(expr)
}

pub(crate) fn run_pipeline_with_artifacts<F>(
    program: &Program<NamedDeBruijn>,
    options: DecompileOptions,
    on_pass: F,
) -> Result<PipelineOutput>
where
    F: FnMut(&'static str, &PseudoExpr),
{
    // Collects per-pass snapshots, which downstream callers (debug bundle,
    // stepping bridge, unit tests) need for final-pseudo lineage.
    run_pipeline_with_artifacts_opts(program, options, on_pass, true)
}

/// Variant of [`run_pipeline_with_artifacts`] that lets the caller opt out of
/// per-pass snapshot collection. Skipping them is a large win on big scripts,
/// where every pass otherwise deep-flattens the full AST for lineage tracking;
/// the cost is that `source_map.final_pseudo_to_mid` stays empty. Safe for call
/// sites that consume only `PipelineOutput.expr` and/or `blueprint_registry`.
pub(crate) fn run_pipeline_with_artifacts_opts<F>(
    program: &Program<NamedDeBruijn>,
    options: DecompileOptions,
    mut on_pass: F,
    collect_snapshots: bool,
) -> Result<PipelineOutput>
where
    F: FnMut(&'static str, &PseudoExpr),
{
    let mut executor = PipelineExecutor::new(&mut on_pass, collect_snapshots);
    let PipelineSeed {
        expr,
        mut simplify_state,
        mut mir_source_map,
        mir_var_registry,
        type_env,
        preserved_helper_ids,
        mut blueprint_registry,
    } = build_pipeline_seed(program, &options, &mut executor)?;
    validate_known_builtins(&expr, "pipeline_seed")?;
    // Filled in only by the lineage projection below, and only when
    // `options.record_lineage_routes` is set. Declared here because the
    // projection is inside an `if let` over the source map.
    let mut lineage_routes: Option<crate::decompile::pseudo_lineage::RouteRecorder> = None;

    // Detect church-bool polarity on the freshly-lowered seed, the only
    // point where the signals are intact: simplify folds the inverse-CIP
    // `if c {Constr<0>} else {Constr<1>}` producers into native Bool once
    // is_true/is_false recognise them, so a later re-detect on the render
    // input would wrongly report `Cip`. Seeded into `SimplifyState` (from
    // which every `Simplifier` picks it up) and returned on
    // `PipelineOutput` for the render half. Detected BEFORE the
    // `RawPseudo` early return so both exits carry a verdict measured on
    // THIS program's seed. Fail-safe to `Cip`.
    let church_polarity_signals = crate::decompile::church_polarity::detect_church_polarity(&expr);
    simplify_state.church_polarity = church_polarity_signals.verdict();

    // Raw pseudo layer: stop BEFORE the structural pseudo pipeline and
    // return the lowering seed as `expr`. A forward return on a
    // well-formed seed, not an abort mid-iteration, so every
    // PipelineOutput field is clean: no type solve ran, hence an
    // empty+frozen `final_types`; source map and var registry are the
    // lowering artifacts as-is; the guard report is the default, the
    // nameless post-pipeline never having run. Callers render `expr`
    // with the bare pretty-printer and consult none of them.
    if options.output_layer == OutputLayer::RawPseudo {
        let mut seed_types = FinalTypeTable::new();
        seed_types.freeze();
        return Ok(PipelineOutput {
            expr,
            mir_source_map,
            mir_var_registry,
            telemetry: executor.into_telemetry(),
            nameless_guard_report: NamelessPostPipelineGuardReport::default(),
            type_env,
            blueprint_registry: std::rc::Rc::new(blueprint_registry),
            final_types: std::rc::Rc::new(seed_types),
            kind_annotations: simplify_state.var_kinds.kind_annotations.clone(),
            // RawPseudo returns before the lineage projection runs, so `None`
            // means "no projection happened", not "the recorder was off".
            lineage_routes: None,
            church_polarity_signals,
        });
    }

    // Slot populated by every `solve_type_constraints_with_final_table`
    // call in the pipeline. The last solve wins; the table is anchored
    // to the AST passed to that solve, before later nameless/render-prep
    // rewrites that may still change declaration ids.
    let mut final_types_slot: Option<FinalTypeTable> = None;

    let expr = run_core_pseudo_pipeline(
        expr,
        &options,
        &mut simplify_state,
        &preserved_helper_ids,
        type_env.as_ref(),
        &mut blueprint_registry,
        &mut final_types_slot,
        &mut executor,
    )?;

    sync_late_var_kind_annotations(&expr, &mut simplify_state.var_kinds.kind_annotations);
    let (expr, nameless_guard_report) = run_default_nameless_post_pipeline_preserving(
        expr,
        &simplify_state.var_kinds.kind_annotations,
        &preserved_helper_ids,
    );
    executor.emit(PipelinePassId::DefaultNamelessPostPipeline, &expr);
    // Wrap the validator entry Lambda in a synthetic `Let { name:
    // "decompiled", kind: ValidatorEntry, ... }` so the renderer emits
    // `fn decompiled(args) { body }` through the existing `let X = Lambda`
    // path, and so the entry is identified by kind annotation rather than by
    // name-pattern matching an anonymous `fn(...)` line. `decompiled` avoids
    // the keyword `validator`, which renders with a trailing `_`.
    // Sync this thread's fresh-id counter ABOVE every id already in the tree
    // before minting the synthetic binder: the tree can carry fresh-range
    // ids from another counter epoch, and an unsynced mint re-uses a live id.
    crate::pseudo::var_id::VarId::ensure_binding_counter_above(
        crate::decompile::render_prep::alpha_uniquify::max_fresh_range_id(&expr),
    );
    let expr =
        wrap_validator_entry_for_render(expr, &mut simplify_state.var_kinds.kind_annotations);
    // V1/V2 validators return Bool; rewrite tail-position
    // `Unit` to `Bool(true)` inside the validator-entry lambda body. No-op for
    // V3 (which expects Unit) and when `script_version` is `None`. The entry
    // is identified by `VarKind::ValidatorEntry` on its binder.

    let expr = crate::decompile::lower_v2_tail_unit_to_true(
        expr,
        options.script_version,
        &simplify_state.var_kinds.kind_annotations,
    );
    if options.type_passes.any_enabled() {
        // Validate against the same solved table the render path consults,
        // falling back to the frozen MIR env when no solve fired.
        validate_type_invariants(&expr, final_types_slot.as_ref(), type_env.as_ref())?;
    }
    if let Some(source_map) = mir_source_map.as_mut() {
        // Two chained projections. `wrap_validator_entry_for_render` shifted
        // the node-id path hash of everything under the entry lambda, so the
        // second projection cannot re-find the first's nodes by id: it is
        // seeded from `lineage_carry` (the first projection's last snapshot
        // plus its owned map) and bridges the gap structurally. ONE recorder
        // across BOTH projections, so window indices stay continuous and the
        // spliced bridge window sits between the last pass window and the
        // render-prep window instead of restarting the count. `None` in
        // production — the flag defaults off.
        let mut route_recorder = options
            .record_lineage_routes
            .then(crate::decompile::pseudo_lineage::RouteRecorder::new);
        let (final_pseudo_to_mid, lineage_carry) =
            executor.project_final_pseudo_lineage(source_map, route_recorder.as_mut());
        // The lineage projection's view of the render tree. It carries the
        // church polarity — which the detection above pinned for THIS
        // program, and which the inverse-CIP recoverers gate on — but is
        // otherwise the faithful default: the version channels and the
        // opt-in transforms are the render half's stance, decided in
        // `decompile_program_to_ast` from options the pipeline no longer
        // holds. (Before the render context was a value, this call read
        // whatever the ambient thread-locals happened to hold: these same
        // defaults on a fresh process, the previous request's leftovers on
        // a reused `spawn_blocking` thread.)
        let lineage_ctx = crate::decompile::RenderCtx::default()
            .with_church_polarity(church_polarity_signals.verdict());
        let prepared_for_render = prepare_for_render(&expr, &lineage_ctx);
        let (render_prepared_pseudo_to_mid, heirs) = project_chained_pseudo_to_mid_with_heirs(
            &[snapshot_expr(&expr), snapshot_expr(&prepared_for_render)],
            &final_pseudo_to_mid,
            lineage_carry,
            route_recorder.as_mut(),
        );
        lineage_routes = route_recorder;
        // Every mid the projection could not carry to a node that survived to
        // the rendered tree. Recorded here, beside the projection that knows
        // it, rather than re-derived downstream from a snapshot chain nobody
        // else keeps. Its consumer is the abstain channel in `SourceMap`.
        source_map.heirless_mids = source_map
            .mid_to_uplc
            .keys()
            .copied()
            .filter(|mid| heirs.heir_mids.binary_search(mid).is_err())
            .collect();
        source_map.set_final_pseudo_to_mid(render_prepared_pseudo_to_mid);
    }

    // Normalize "no solve fired" into an empty+frozen table so the public
    // output shape needs no `Option`.
    let final_types = final_types_slot.unwrap_or_else(|| {
        let mut t = FinalTypeTable::new();
        t.freeze();
        t
    });

    Ok(PipelineOutput {
        expr,
        mir_source_map,
        mir_var_registry,
        telemetry: executor.into_telemetry(),
        nameless_guard_report,
        type_env,
        blueprint_registry: std::rc::Rc::new(blueprint_registry),
        final_types: std::rc::Rc::new(final_types),
        kind_annotations: simplify_state.var_kinds.kind_annotations.clone(),
        lineage_routes,
        church_polarity_signals,
    })
}

pub(crate) fn run_pipeline<F>(
    program: &Program<NamedDeBruijn>,
    options: DecompileOptions,
    on_pass: F,
) -> Result<PseudoExpr>
where
    F: FnMut(&'static str, &PseudoExpr),
{
    // `run_pipeline` discards everything but `expr`, so it never consumes
    // `source_map.final_pseudo_to_mid` — the per-pass snapshot work is pure
    // overhead here. Skipping it gives ~10x on large scripts.
    Ok(run_pipeline_with_artifacts_opts(program, options, on_pass, false)?.expr)
}

/// Wrap the validator entry Lambda **in place** as a synthetic
/// `Let { name: "decompiled", kind: ValidatorEntry, value: <entry>, body: Unit }`
/// at the chain's terminal position, so the renderer emits
/// `fn decompiled(args) { body }` instead of an anonymous `fn(args) { body }`
/// and downstream consumers identify the entry by `VarKind::ValidatorEntry`
/// instead of name-pattern matching. The binder avoids `validator`, an surface
/// keyword that renders with a trailing `_`.
///
/// **The entry is NOT moved to the top of the chain at AST level.** That would
/// create forward references that violate PseudoExpr's lexical scope
/// invariants, stranding hundreds of ids as orphans (bounded by the
/// `regression_guard_residual_orphan_bounds` test). Top-level reordering
/// happens purely at the rendering layer in
/// `decompile/mod.rs::move_validator_entry_first`, where declarations are
/// top-level and surface syntax allows forward references.
///
/// **Identification:** the entry Lambda is detected by VarKind, not by name —
/// a param carries `VarKind::CardanoContext { context_type: "script_context" }`
/// from `rename_validator_params_with_var_kinds` — with a name check on
/// `"script_context"` as a fallback for validators that never get the
/// annotation. Returns the expression unchanged if no entry-like Lambda is
/// found.
fn wrap_validator_entry_for_render(
    expr: PseudoExpr,
    kind_annotations: &mut HashMap<VarId, VarKind>,
) -> PseudoExpr {
    use crate::pseudo::ast::Binder;

    fn is_entry_lambda(params: &[Binder], kind_annotations: &HashMap<VarId, VarKind>) -> bool {
        params.iter().any(|p| {
            matches!(
                kind_annotations.get(&p.var_id()),
                Some(VarKind::CardanoContext { context_type }) if context_type == "script_context"
            ) || p.as_str() == "script_context"
        })
    }

    fn wrap_terminal(
        expr: PseudoExpr,
        kind_annotations: &mut HashMap<VarId, VarKind>,
    ) -> PseudoExpr {
        let mut frames = Vec::new();
        let mut current = expr;
        loop {
            match current {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    frames.push((name, id, value));
                    current = body.into_inner();
                }
                other => {
                    current = other;
                    break;
                }
            }
        }

        let mut result = match current {
            PseudoExpr::Lambda { params, body } if is_entry_lambda(&params, kind_annotations) => {
                let validator_id = VarId::fresh_binding();
                kind_annotations.insert(validator_id, VarKind::ValidatorEntry);
                // `decompiled` is not an keyword, so the
                // renderer's `sanitize_identifier` keyword guard leaves
                // it alone. A later pass swaps in the real validator
                // name when blueprint metadata is available.
                PseudoExpr::Let {
                    name: "decompiled".to_string(),
                    id: Some(validator_id),
                    value: PBox::new(PseudoExpr::Lambda { params, body }),
                    body: PBox::new(PseudoExpr::Unit),
                }
            }
            other => other,
        };

        for (name, id, value) in frames.into_iter().rev() {
            result = PseudoExpr::Let {
                name,
                id,
                value,
                body: PBox::new(result),
            };
        }

        result
    }

    let wrapped = wrap_terminal(expr, kind_annotations);

    // If the terminal-position wrap found no entry Lambda — the entry
    // sits in a let *value*, not the chain's terminal body, as after
    // a helper-hoist or naming pass moves the binding earlier — scan
    // let values for a Lambda whose params signal a validator entry
    // (named `script_context` or tagged with the `CardanoContext`
    // VarKind). The match promotes the enclosing Let's binder to
    // `decompiled` and tags its id with `VarKind::ValidatorEntry`, so
    // the renderer and wrap_rendered treat it like the terminal path.
    if !contains_validator_entry(&wrapped, kind_annotations) {
        return promote_let_bound_entry(wrapped, kind_annotations);
    }
    wrapped
}

/// True if any `Let` binder anywhere in the tree is already tagged
/// with `VarKind::ValidatorEntry`.
fn contains_validator_entry(expr: &PseudoExpr, kind_annotations: &HashMap<VarId, VarKind>) -> bool {
    struct EntryFinder<'a> {
        kinds: &'a HashMap<VarId, VarKind>,
        found: bool,
    }
    impl ExprVisitor for EntryFinder<'_> {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, _value: &PseudoExpr) {
            if let Some(id) = id
                && matches!(self.kinds.get(id), Some(VarKind::ValidatorEntry))
            {
                self.found = true;
            }
        }
    }
    let mut finder = EntryFinder {
        kinds: kind_annotations,
        found: false,
    };
    finder.walk(expr);
    finder.found
}

/// Promote the first `Let { value: Lambda }` whose Lambda satisfies
/// the validator-entry heuristic to `name = "decompiled"` tagged with
/// `VarKind::ValidatorEntry`; later matches in the chain stay helpers.
///
/// Covers the post-helper-hoist shape where the entry was lifted into
/// a `let helper_N = Lambda(redeemer, script_context, body)` binding
/// rather than left as the terminal Lambda of the chain.
fn promote_let_bound_entry(
    expr: PseudoExpr,
    kind_annotations: &mut HashMap<VarId, VarKind>,
) -> PseudoExpr {
    use crate::pseudo::ast::Binder;

    fn is_entry_lambda(params: &[Binder], kind_annotations: &HashMap<VarId, VarKind>) -> bool {
        params.iter().any(|p| {
            matches!(
                kind_annotations.get(&p.var_id()),
                Some(VarKind::CardanoContext { context_type }) if context_type == "script_context"
            ) || p.as_str() == "script_context"
        })
    }

    // Descends through `Let.body` ONLY, never into `Let.value`,
    // `Lambda.body`, or `RecFn.body`: promoting a nested helper as
    // `ValidatorEntry` would mislead `promote_validator_entry_first`
    // and the V1/V2 tail-Unit lowering, both of which assume the entry
    // sits on the top-level let chain. A non-`Let` node ends the walk.
    fn walk(
        expr: PseudoExpr,
        kind_annotations: &mut HashMap<VarId, VarKind>,
        promoted: &mut bool,
    ) -> PseudoExpr {
        let mut frames: Vec<(String, Option<VarId>, PBox)> = Vec::new();
        let mut current = expr;
        let mut result = loop {
            if *promoted {
                break current;
            }
            match current {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    // Inspect the let's value for an entry-shaped
                    // Lambda, without recursing into the value or the
                    // lambda body: promote here, or move on.
                    match value.into_inner() {
                        PseudoExpr::Lambda {
                            params,
                            body: lam_body,
                        } => {
                            if is_entry_lambda(&params, kind_annotations) {
                                let new_id = id.unwrap_or_else(VarId::fresh_binding);
                                kind_annotations.insert(new_id, VarKind::ValidatorEntry);
                                *promoted = true;
                                break PseudoExpr::Let {
                                    name: "decompiled".to_string(),
                                    id: Some(new_id),
                                    value: PBox::new(PseudoExpr::Lambda {
                                        params,
                                        body: lam_body,
                                    }),
                                    body,
                                };
                            }
                            // Not the entry: keep the let's value untouched
                            // (no recursion into lam_body) and continue down
                            // the body.
                            frames.push((
                                name,
                                id,
                                PBox::new(PseudoExpr::Lambda {
                                    params,
                                    body: lam_body,
                                }),
                            ));
                            current = body.into_inner();
                        }
                        // Non-Lambda value — leave it alone, recurse into body.
                        value => {
                            frames.push((name, id, PBox::new(value)));
                            current = body.into_inner();
                        }
                    }
                }
                // Terminal — any non-Let node ends the top-level chain.
                other => break other,
            }
        };

        for (name, id, value) in frames.into_iter().rev() {
            result = PseudoExpr::Let {
                name,
                id,
                value,
                body: PBox::new(result),
            };
        }

        result
    }

    let mut promoted = false;
    walk(expr, kind_annotations, &mut promoted)
}

fn sync_late_var_kind_annotations(expr: &PseudoExpr, annotations: &mut HashMap<VarId, VarKind>) {
    sync_late_slice_tail_kind_annotations(expr, annotations);
    sync_late_call_result_kind_annotations(expr, annotations);
    // Records `VarKind::ConstrPayload` for binders in
    // `WhenPattern::Constructor` patterns. The `assign_names`
    // ConstrPayload arm emits `item_{index}` only for unnamed binders,
    // so user-meaningful renames survive.
    sync_late_constr_payload_kind_annotations(expr, annotations);
}

fn sync_late_slice_tail_kind_annotations(
    expr: &PseudoExpr,
    annotations: &mut HashMap<VarId, VarKind>,
) {
    struct LateSliceTailVisitor<'a> {
        annotations: &'a mut HashMap<VarId, VarKind>,
    }

    impl ExprVisitor for LateSliceTailVisitor<'_> {
        fn visit_let(
            &mut self,
            _name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            let Some(alias_id) = id.get() else {
                return;
            };
            if self.annotations.contains_key(&alias_id) {
                return;
            }
            let Some((parent, depth)) = late_slice_tail_alias_for_value(value, self.annotations)
            else {
                return;
            };
            self.annotations
                .insert(alias_id, VarKind::SliceTailAlias { parent, depth });
        }
    }

    LateSliceTailVisitor { annotations }.walk(expr);
}

fn late_slice_tail_alias_for_value(
    value: &PseudoExpr,
    annotations: &HashMap<VarId, VarKind>,
) -> Option<(VarId, usize)> {
    let mut current = value;
    let mut depth = 0usize;
    while let Some(inner) = strip_late_list_tail(current) {
        depth += 1;
        current = inner;
    }

    match current {
        PseudoExpr::Var { id, .. } if depth == 0 => {
            let real_id = id.get()?;
            slice_tail_annotation(annotations, real_id)
        }
        PseudoExpr::Var { id, .. } => {
            let real_id = id.get()?;
            slice_tail_annotation(annotations, real_id)
                .map(|(parent, existing_depth)| (parent, depth + existing_depth))
                .or(Some((real_id, depth)))
        }
        _ => None,
    }
}

fn slice_tail_annotation(
    annotations: &HashMap<VarId, VarKind>,
    id: VarId,
) -> Option<(VarId, usize)> {
    match annotations.get(&id)? {
        VarKind::SliceTailAlias { parent, depth } => Some((*parent, *depth)),
        _ => None,
    }
}

fn strip_late_list_tail(expr: &PseudoExpr) -> Option<&PseudoExpr> {
    let PseudoExpr::Apply { function, args } = expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let PseudoExpr::BuiltinCall {
        name,
        args: builtin_args,
    } = function.as_ref()
    else {
        return None;
    };
    if *name == crate::BuiltinId::ListTail && builtin_args.is_empty() {
        Some(&args[0])
    } else {
        None
    }
}

fn sync_late_call_result_kind_annotations(
    expr: &PseudoExpr,
    annotations: &mut HashMap<VarId, VarKind>,
) {
    struct LateCallResultVisitor<'a> {
        annotations: &'a mut HashMap<VarId, VarKind>,
    }

    impl ExprVisitor for LateCallResultVisitor<'_> {
        fn visit_let(
            &mut self,
            name: &str,
            id: &Option<VarId>,
            value: &PseudoExpr,
            _body: &PseudoExpr,
        ) {
            let Some(result_id) = id.get() else {
                return;
            };
            let Some(callee) =
                simplify::Simplifier::call_result_callee_for_binding_name(name, value)
                    .and_then(|callee| callee.get())
            else {
                return;
            };
            match self.annotations.get(&result_id) {
                // New CallResult binding — record it.
                None => {
                    self.annotations
                        .insert(result_id, VarKind::CallResult { callee });
                }
                // RE-SYNC a stale CallResult callee: a late rename/inline can re-id
                // the callee binder without updating this annotation, leaving `callee`
                // pointing at a dead id the kind verifier rejects. Re-derive from the
                // final tree; NEVER clobber a non-CallResult kind.
                Some(VarKind::CallResult { callee: existing }) if *existing != callee => {
                    self.annotations
                        .insert(result_id, VarKind::CallResult { callee });
                }
                _ => {}
            }
        }
    }

    LateCallResultVisitor { annotations }.walk(expr);
}

/// Record `VarKind::ConstrPayload { pattern_id, index }` for binders in
/// `WhenPattern::Constructor { fields, .. }` patterns.
///
/// `pattern_id` is the first field's `VarId` — stable and unique without
/// a separate counter, and shared by every binder in the pattern.
/// Patterns with no fields produce no annotations.
fn sync_late_constr_payload_kind_annotations(
    expr: &PseudoExpr,
    annotations: &mut HashMap<VarId, VarKind>,
) {
    struct LateConstrPayloadVisitor<'a> {
        annotations: &'a mut HashMap<VarId, VarKind>,
    }

    impl ExprVisitor for LateConstrPayloadVisitor<'_> {
        fn visit_when_clause_pre(
            &mut self,
            _subject_name: Option<&crate::pseudo::ast::Binder>,
            clause: &crate::pseudo::ast::WhenClause,
        ) {
            let WhenPattern::Constructor { fields, .. } = &clause.pattern else {
                return;
            };
            let Some(first_field_id) = fields.first().and_then(|b| b.var_id().get()) else {
                return;
            };
            let pattern_id = first_field_id.as_u32() as usize;
            for (index, binder) in fields.iter().enumerate() {
                let Some(binder_id) = binder.var_id().get() else {
                    continue;
                };
                if self.annotations.contains_key(&binder_id) {
                    continue;
                }
                self.annotations
                    .insert(binder_id, VarKind::ConstrPayload { pattern_id, index });
            }
        }
    }

    LateConstrPayloadVisitor { annotations }.walk(expr);
}

#[cfg(test)]
mod tests;
