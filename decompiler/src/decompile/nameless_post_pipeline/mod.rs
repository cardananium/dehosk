use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::nameless::convert::{nameless_to_pseudo, pseudo_to_nameless};
use crate::pseudo::nameless::invariants::{
    nameless_free_var_id_set, nameless_introduces_new_free_var_ids, nameless_live_var_id_set,
    nameless_render_binder_name_set, nameless_render_orphan_name_set, nameless_render_var_name_set,
};
use crate::pseudo::nameless::{NamelessExpr, VarKind, VarMetadata, VarOrigin, VarTable};
use crate::pseudo::var_id::VarId;

use super::dead_let_nameless::eliminate_dead_lets_nameless;
use super::inline::nameless::inline_single_use_nameless_preserving;
#[cfg(debug_assertions)]
use super::kind_inference::verify_var_kinds;
use super::naming::{
    collect_arithmetic_temp_display_name_hints, collect_check_temp_display_name_hints,
    collect_data_list_temp_display_name_hints, collect_extractor_temp_display_name_hints,
    collect_field_payload_temp_display_name_hints, collect_option_wrapper_temp_display_name_hints,
    collect_when_pattern_binder_display_name_hints,
};
use super::slice_chain_nameless::inline_slice_chain_nameless;

/// Canonical nameless post-pipeline: lower to NamelessExpr, merge
/// mint-site VarKind metadata, run the nameless leaf passes, and raise
/// back to PseudoExpr.
///
/// Test-only convenience that takes no preserved helper ids; production
/// calls `run_default_nameless_post_pipeline_preserving`.
#[cfg(test)]
pub(crate) fn run_default_nameless_post_pipeline(
    expr: PseudoExpr,
    kind_annotations: &HashMap<VarId, VarKind>,
) -> (PseudoExpr, NamelessPostPipelineGuardReport) {
    run_default_nameless_post_pipeline_preserving(expr, kind_annotations, &HashSet::new())
}

pub(crate) fn run_default_nameless_post_pipeline_preserving(
    expr: PseudoExpr,
    kind_annotations: &HashMap<VarId, VarKind>,
    preserved_helper_ids: &HashSet<VarId>,
) -> (PseudoExpr, NamelessPostPipelineGuardReport) {
    run_nameless_post_pipeline_with_annotations_and_guard_report_preserving(
        expr,
        kind_annotations,
        preserved_helper_ids,
    )
}

/// Safety outcome for a nameless leaf pass guarded by the render-orphan
/// checks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NamelessPassGuardOutcome {
    Accepted,
    RevertedNewFreeVarIds,
    RevertedLostBinderNameMasksOrphan,
    RevertedNewOrphanName,
}

/// Safety outcome for the late nameless `assign_names` display pass.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NamelessAssignNamesGuardOutcome {
    Accepted,
    RevertedNewOrphanName,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct NamelessPostPipelineGuardReport {
    pub(crate) inline_single_use: NamelessPassGuardOutcome,
    pub(crate) dead_lets: NamelessPassGuardOutcome,
    pub(crate) slice_chain: NamelessPassGuardOutcome,
    pub(crate) assign_names: NamelessAssignNamesGuardOutcome,
}

impl NamelessPostPipelineGuardReport {
    /// Test-only convenience to check that no guard tripped. Production
    /// pipeline reads individual fields when handling the report.
    #[cfg(test)]
    pub(crate) fn all_accepted(&self) -> bool {
        self.inline_single_use == NamelessPassGuardOutcome::Accepted
            && self.dead_lets == NamelessPassGuardOutcome::Accepted
            && self.slice_chain == NamelessPassGuardOutcome::Accepted
            && self.assign_names == NamelessAssignNamesGuardOutcome::Accepted
    }
}

impl Default for NamelessPostPipelineGuardReport {
    fn default() -> Self {
        Self {
            inline_single_use: NamelessPassGuardOutcome::Accepted,
            dead_lets: NamelessPassGuardOutcome::Accepted,
            slice_chain: NamelessPassGuardOutcome::Accepted,
            assign_names: NamelessAssignNamesGuardOutcome::Accepted,
        }
    }
}

fn apply_render_display_hints(after_pseudo: &PseudoExpr, after_table: &mut VarTable) {
    for (id, hint) in collect_check_temp_display_name_hints(after_pseudo) {
        if let Some(metadata) = after_table.get_mut(id) {
            metadata.display_name_hint = Some(hint);
        }
    }
    for (id, hint) in collect_arithmetic_temp_display_name_hints(after_pseudo) {
        if let Some(metadata) = after_table.get_mut(id) {
            metadata.display_name_hint = Some(hint);
        }
    }
    for (id, hint) in collect_option_wrapper_temp_display_name_hints(after_pseudo) {
        if let Some(metadata) = after_table.get_mut(id) {
            metadata.display_name_hint = Some(hint);
        }
    }
    for (id, hint) in collect_extractor_temp_display_name_hints(after_pseudo) {
        if let Some(metadata) = after_table.get_mut(id) {
            metadata.display_name_hint = Some(hint);
        }
    }
    for (id, hint) in collect_field_payload_temp_display_name_hints(after_pseudo) {
        if let Some(metadata) = after_table.get_mut(id) {
            metadata.display_name_hint = Some(hint);
        }
    }
    for (id, hint) in collect_when_pattern_binder_display_name_hints(after_pseudo) {
        if let Some(metadata) = after_table.get_mut(id) {
            metadata.display_name_hint = Some(hint);
        }
    }
    for (id, hint) in collect_data_list_temp_display_name_hints(after_pseudo) {
        if let Some(metadata) = after_table.get_mut(id) {
            metadata.display_name_hint = Some(hint);
        }
    }
}

/// Annotation-aware nameless post-pipeline: lowers to NamelessExpr,
/// populates kinds, runs the leaf passes (`inline_single_use_nameless`,
/// `eliminate_dead_lets_nameless`, `inline_slice_chain_nameless`), raises
/// back, and reports each pass's guard outcome.
///
/// **Safety guard**: every pass runs, then two invariants decide whether
/// to keep it:
///
///   1. The free-var (orphan) VarId set has not grown.
///   2. Every rendered name still has a binder above the references to it.
///
/// For guard 2, a pass that drops a binder whose render name equals the
/// render name of a *free* Var in the body would render "field_0
/// referenced but no `let field_0 = ...` above" — a render-time orphan on
/// top of the PseudoExpr pipeline's same-name/different-VarId orphans;
/// the pass is reverted in that case.
///
/// Mint-site VarKind annotations from
/// [`crate::decompile::simplify::SimplifyState::var_kinds`] are merged
/// into the VarTable before `kind_inference` runs, so verifier shape arms
/// can check a kind without acting as fallback producers.
///
/// Test-only entry; production calls
/// `run_default_nameless_post_pipeline_preserving` directly.
#[cfg(test)]
pub(crate) fn run_nameless_post_pipeline_with_annotations_and_guard_report(
    expr: PseudoExpr,
    kind_annotations: &HashMap<VarId, VarKind>,
) -> (PseudoExpr, NamelessPostPipelineGuardReport) {
    run_nameless_post_pipeline_with_annotations_and_guard_report_preserving(
        expr,
        kind_annotations,
        &HashSet::new(),
    )
}

pub(crate) fn run_nameless_post_pipeline_with_annotations_and_guard_report_preserving(
    expr: PseudoExpr,
    kind_annotations: &HashMap<VarId, VarKind>,
    preserved_helper_ids: &HashSet<VarId>,
) -> (PseudoExpr, NamelessPostPipelineGuardReport) {
    let (mut nameless, mut table) = pseudo_to_nameless(&expr);
    for (id, kind) in kind_annotations {
        let name_hint = table.get(*id).and_then(|m| m.name_hint.clone());
        let display_name_hint = table.get(*id).and_then(|m| m.display_name_hint.clone());
        table.insert(
            *id,
            VarMetadata {
                origin: VarOrigin::Synthetic {
                    producer_pass: "mint_site",
                },
                name_hint,
                display_name_hint,
                kind: kind.clone(),
            },
        );
    }
    // The verifier walk feeds only the `debug_assert!` below, a no-op
    // without debug assertions, and costs a full AST shape-match
    // against every mint-site arm on large programs.
    #[cfg(debug_assertions)]
    {
        let kind_report = verify_var_kinds(&expr, &table);
        debug_assert!(
            kind_report.conflicts.is_empty(),
            "kind verifier disagreed with existing VarKind annotations: {:?}",
            kind_report.conflicts
        );
    }

    let baseline_orphan_ids = nameless_free_var_id_set(&nameless);
    let baseline_orphan_names = nameless_render_orphan_name_set(&nameless, &table);
    let baseline_binder_names = nameless_render_binder_name_set(&nameless, &table);
    let mut guard_report = NamelessPostPipelineGuardReport::default();

    let try_pass = |before: NamelessExpr,
                    after: NamelessExpr,
                    table: &VarTable|
     -> (NamelessExpr, NamelessPassGuardOutcome) {
        // Guard 1: no new orphan VarIds, even if the orphan count stays stable.
        if nameless_introduces_new_free_var_ids(&after, &baseline_orphan_ids) {
            return (before, NamelessPassGuardOutcome::RevertedNewFreeVarIds);
        }
        let after_orphan_names = nameless_render_orphan_name_set(&after, table);
        let after_binder_names = nameless_render_binder_name_set(&after, table);
        // Guard 2a: if the pass dropped a binder whose render name also
        // appears as an orphan render name in the after tree, the rendered
        // output will reference that name without a binding above it.
        let lost_binder_names: Vec<&String> = baseline_binder_names
            .difference(&after_binder_names)
            .collect();
        for lost_name in &lost_binder_names {
            if after_orphan_names.contains(*lost_name) {
                return (
                    before,
                    NamelessPassGuardOutcome::RevertedLostBinderNameMasksOrphan,
                );
            }
        }
        // Guard 2b: even if no binder was lost, no new orphan name should
        // appear.
        let after_var_names = nameless_render_var_name_set(&after, table);
        for var_name in &after_var_names {
            if !after_binder_names.contains(var_name) && !baseline_orphan_names.contains(var_name) {
                return (before, NamelessPassGuardOutcome::RevertedNewOrphanName);
            }
        }
        (after, NamelessPassGuardOutcome::Accepted)
    };

    let after_inline =
        inline_single_use_nameless_preserving(nameless.clone(), preserved_helper_ids);
    let (next, outcome) = try_pass(nameless, after_inline, &table);
    nameless = next;
    guard_report.inline_single_use = outcome;

    let after_dce = eliminate_dead_lets_nameless(nameless.clone());
    let (next, outcome) = try_pass(nameless, after_dce, &table);
    nameless = next;
    guard_report.dead_lets = outcome;

    let after_slice = inline_slice_chain_nameless(nameless.clone(), &table);
    let (next, outcome) = try_pass(nameless, after_slice, &table);
    nameless = next;
    guard_report.slice_chain = outcome;

    // Assign canonical names from VarKind metadata; revert the whole
    // rename if it introduces new render-time orphans.
    //
    // LIVE-ONLY allocation: the table holds entries for ids long dead in
    // the AST (simplifier temporaries, dropped aliases), and unfiltered
    // they consume `field_0`, `field_0_2`, ... in `fresh_name`'s global
    // used set, so the live binder renders with a spurious suffix. Only
    // ids present in the final nameless AST participate; dead entries
    // keep their hints — they cannot render. An empty live set falls
    // back to unfiltered naming inside `assign_names_live`.
    let live_ids = nameless_live_var_id_set(&nameless);
    let mut after_table = table.clone();
    let after_pseudo = nameless_to_pseudo(&nameless, &after_table);
    apply_render_display_hints(&after_pseudo, &mut after_table);
    crate::decompile::assign_names::assign_names_live(&mut after_table, &live_ids);
    let after_orphan_names = nameless_render_orphan_name_set(&nameless, &after_table);
    let introduced_orphan = after_orphan_names
        .iter()
        .any(|name| !baseline_orphan_names.contains(name));
    if !introduced_orphan {
        table = after_table;
    } else {
        guard_report.assign_names = NamelessAssignNamesGuardOutcome::RevertedNewOrphanName;
    }

    (nameless_to_pseudo(&nameless, &table), guard_report)
}

#[cfg(test)]
mod tests;
