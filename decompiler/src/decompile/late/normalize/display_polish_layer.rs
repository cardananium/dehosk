use crate::decompile::DecompileOptions;
use crate::decompile::display::polish::extract_heavy_constants;
use crate::decompile::display::rewrite::normalize_display_rewrites;
use crate::decompile::helper::hoist::hoist_local_helpers;
use crate::decompile::naming::render_improve_variable_names;
use crate::decompile::pipeline_passes::PipelinePassId;
use crate::decompile::pipeline_runtime::PipelineExecutor;
use crate::pseudo::ast::PseudoExpr;

/// Run the late display/naming layer.
///
/// The transforms live in dedicated modules; the sequencing contract
/// lives here rather than in `pipeline_stages.rs`.
pub(crate) fn run_display_polish_layer<F>(
    mut expr: PseudoExpr,
    options: &DecompileOptions,
    executor: &mut PipelineExecutor<'_, F>,
) -> PseudoExpr
where
    F: FnMut(&'static str, &PseudoExpr),
{
    let polish = &options.display_polish_passes;
    let readability = &options.readability_passes;

    expr = executor.ensure_consistent_ref_ids(expr);

    if readability.hoist_local_helpers {
        let mut apply = |expr: &mut PseudoExpr, pass, updated: PseudoExpr| {
            if !updated.structural_eq(expr) {
                *expr = updated;
                executor.emit(pass, expr);
            }
        };

        let updated = hoist_local_helpers(expr.clone());
        apply(&mut expr, PipelinePassId::HoistLocalHelpers, updated);
    }

    if readability.extract_heavy_constants {
        let mut apply = |expr: &mut PseudoExpr, pass, updated: PseudoExpr| {
            if !updated.structural_eq(expr) {
                *expr = updated;
                executor.emit(pass, expr);
            }
        };

        let updated = extract_heavy_constants(expr.clone());
        apply(&mut expr, PipelinePassId::ExtractHeavyConstants, updated);
    }

    // Retarget refs to in-scope binder ids BEFORE display_rewrite:
    // corrects stale refs whose binder was inlined away while a
    // same-name binder was minted nearby, so downstream id-only
    // renames see the right targets. `structural_eq` ignores VarIds,
    // so this pass skips the `apply` guard. Without it,
    // `NormalizeDisplayRewrites` fails its `ConsistentRefIds`
    // contract and the pipeline panics with
    // "missing required properties".
    expr = executor.ensure_consistent_ref_ids(expr);

    if polish.normalize_display_rewrites {
        let mut apply = |expr: &mut PseudoExpr, pass, updated: PseudoExpr| {
            if !updated.structural_eq(expr) {
                *expr = updated;
                executor.emit(pass, expr);
            }
        };

        let updated = normalize_display_rewrites(expr.clone());
        apply(&mut expr, PipelinePassId::NormalizeDisplayRewrites, updated);
    }
    // Display rewrites can hoist same-name lets and invalidate ref ids.
    // Keep repair at the executor boundary instead of hiding it inside the
    // display helper.
    expr = executor.ensure_consistent_ref_ids(expr);

    let mut apply = |expr: &mut PseudoExpr, pass, updated: PseudoExpr| {
        if !updated.structural_eq(expr) {
            *expr = updated;
            executor.emit(pass, expr);
        }
    };

    if readability.hoist_local_helpers {
        let updated = hoist_local_helpers(expr.clone());
        apply(
            &mut expr,
            PipelinePassId::HoistLocalHelpersPostNormalize,
            updated,
        );
    }

    if readability.improve_variable_names {
        let updated = render_improve_variable_names(expr.clone());
        apply(
            &mut expr,
            PipelinePassId::ImproveVariableNamesPostLate,
            updated,
        );
    }

    expr
}
