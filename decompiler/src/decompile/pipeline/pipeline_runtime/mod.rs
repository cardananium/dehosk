use crate::pseudo::ast::{PseudoExpr, PseudoNodeId};
use crate::pseudo::mid::expr_id::MidExprId;

use super::pipeline_passes::{PassContract, PipelinePassId, PipelineProperty, PipelinePropertySet};
use super::pseudo_lineage::{
    LineageCarry, PseudoSnapshot, project_pseudo_to_mid_carrying, snapshot_expr,
};

pub(in crate::decompile) const MAX_FIXED_POINT_ITERATIONS: usize = 16;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FixedPointTelemetry {
    pub max_iterations: usize,
    pub attempted_iterations: usize,
    pub converged: bool,
    pub hit_iteration_limit: bool,
}

impl Default for FixedPointTelemetry {
    fn default() -> Self {
        Self {
            max_iterations: MAX_FIXED_POINT_ITERATIONS,
            attempted_iterations: 0,
            converged: true,
            hit_iteration_limit: false,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct PipelineTelemetry {
    pub fixed_point: FixedPointTelemetry,
}

/// The pipeline's optional per-pass self-checks — developer diagnostics,
/// not user options, so they are a process-wide switch rather than a
/// [`DecompileOptions`] field.
///
/// Debug builds only, and off by default: each check walks the whole tree
/// after EVERY pass, which is far too expensive to leave on.
///
/// [`DecompileOptions`]: crate::decompile::DecompileOptions
#[cfg(debug_assertions)]
pub(in crate::decompile) mod self_checks {
    use std::sync::atomic::{AtomicBool, Ordering};

    /// Panic when a pass violates its declared `consistent_ref_ids`
    /// producer/preserver contract.
    static REF_ID_PROPERTY_BOUNDARIES: AtomicBool = AtomicBool::new(false);
    /// Panic when a pass leaves a stranded id-orphan behind, naming the
    /// pass — which is what localizes the regression to one pass instead
    /// of to "somewhere in the pipeline".
    static ORPHAN_ASSERT: AtomicBool = AtomicBool::new(false);

    pub(in crate::decompile) fn ref_id_property_boundaries() -> bool {
        REF_ID_PROPERTY_BOUNDARIES.load(Ordering::Relaxed)
    }

    pub(in crate::decompile) fn orphan_assert() -> bool {
        ORPHAN_ASSERT.load(Ordering::Relaxed)
    }

    /// Turn the orphan assert on for the lifetime of the returned guard.
    ///
    /// Process-wide, so callers must serialize themselves — the tests do
    /// it through `pipeline_parity_test_lock`.
    #[cfg(test)]
    pub(in crate::decompile) fn orphan_assert_enabled() -> OrphanAssertGuard {
        OrphanAssertGuard(ORPHAN_ASSERT.swap(true, Ordering::Relaxed))
    }

    /// Restores the previous setting on drop, panic included.
    #[cfg(test)]
    pub(in crate::decompile) struct OrphanAssertGuard(bool);

    #[cfg(test)]
    impl Drop for OrphanAssertGuard {
        fn drop(&mut self) {
            ORPHAN_ASSERT.store(self.0, Ordering::Relaxed);
        }
    }
}

pub(in crate::decompile) struct PipelineExecutor<'a, F>
where
    F: FnMut(&'static str, &PseudoExpr),
{
    on_pass: &'a mut F,
    collect_snapshots: bool,
    pass_snapshots: Vec<PseudoSnapshot>,
    properties: PipelinePropertySet,
    telemetry: PipelineTelemetry,
}

impl<'a, F> PipelineExecutor<'a, F>
where
    F: FnMut(&'static str, &PseudoExpr),
{
    /// Whether per-pass snapshots are being collected — equivalently, whether
    /// anything will read the lineage maps the lowering can build.
    pub(in crate::decompile) fn collects_snapshots(&self) -> bool {
        self.collect_snapshots
    }

    pub(in crate::decompile) fn new(on_pass: &'a mut F, collect_snapshots: bool) -> Self {
        Self {
            on_pass,
            collect_snapshots,
            pass_snapshots: Vec::new(),
            properties: PipelinePropertySet::default(),
            telemetry: PipelineTelemetry::default(),
        }
    }

    pub(in crate::decompile) fn emit(&mut self, pass: PipelinePassId, expr: &PseudoExpr) {
        let name = pass.label();
        let contract = pass.contract();
        let had_consistent_ref_ids = self
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds]);
        if !self.properties.satisfies(contract.requires) {
            let missing = self.properties.missing_labels(contract.requires);
            panic!(
                "pipeline pass `{name}` missing required properties: {}",
                missing.join(", ")
            );
        }
        self.properties.remove_all(contract.invalidates);
        self.properties.insert_all(contract.produces);
        if self.collect_snapshots {
            self.pass_snapshots.push(snapshot_expr(expr));
        }
        Self::enforce_ref_id_property_contract(name, expr, contract, had_consistent_ref_ids);
        Self::enforce_ref_id_hygiene(name, expr);
        (self.on_pass)(name, expr);
    }

    /// Pipeline-owned `ConsistentRefIds` repair boundary — the only
    /// retarget emitted as a pipeline pass. The remaining direct
    /// `retarget_refs_by_scope` calls are local repair adapters owned by
    /// their enclosing pass helpers:
    ///
    /// `pipeline_stages::normalize_simplify_contract_output`: normalizes
    ///   broad simplify outputs before emitting their pass snapshots.
    /// `late_normalize::{retarget_final_scope_refs,
    ///   repair_forward_let_dependencies}`: structural final cleanup
    ///   internals, run before the executor emits the owning cleanup pass.
    pub(in crate::decompile) fn ensure_consistent_ref_ids(
        &mut self,
        expr: PseudoExpr,
    ) -> PseudoExpr {
        if self
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
        {
            return expr;
        }
        if !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr) {
            self.properties.insert(PipelineProperty::ConsistentRefIds);
            return expr;
        }
        let expr = crate::decompile::ref_retarget::retarget_refs_by_scope(expr);
        self.emit(PipelinePassId::RetargetRefsByScope, &expr);
        expr
    }

    /// Debug-only pass-boundary checks, each opt-in via an env var
    /// because it walks the whole expression once per pass: the
    /// producer/preserver `consistent_ref_ids` contract
    /// (`DEHOSK_VALIDATE_REF_PROPERTY_BOUNDARIES`) and the
    /// zero-stranded-ref audit (`DEHOSK_ENFORCE_ORPHAN_ASSERT`). A
    /// stranded ref is a `Var { id }` whose id belongs to a binder
    /// elsewhere in the tree but outside the ref's scope chain.
    ///
    /// Enabling a flag reports benign intermediate residue too:
    /// some inputs carry stranded refs through the early simplify
    /// passes. `regression_guard_residual_orphan_bounds` asserts
    /// zero stranded refs on final output unconditionally.
    #[cfg(any(debug_assertions, test))]
    fn consistent_ref_id_contract_violation(
        expr: &PseudoExpr,
        contract: PassContract,
        had_consistent_ref_ids: bool,
    ) -> Option<&'static str> {
        let invalidates_consistent_ref_ids = contract
            .invalidates
            .contains(&PipelineProperty::ConsistentRefIds);
        let produces_consistent_ref_ids = contract
            .produces
            .contains(&PipelineProperty::ConsistentRefIds);
        let requires_check = produces_consistent_ref_ids
            || (had_consistent_ref_ids && !invalidates_consistent_ref_ids);

        if !requires_check || !crate::decompile::ref_retarget::refs_need_retarget_by_scope(expr) {
            return None;
        }

        Some(if produces_consistent_ref_ids {
            "producer"
        } else {
            "preserver"
        })
    }

    #[cfg(debug_assertions)]
    fn enforce_ref_id_property_contract(
        pass: &'static str,
        expr: &PseudoExpr,
        contract: PassContract,
        had_consistent_ref_ids: bool,
    ) {
        if !self_checks::ref_id_property_boundaries() {
            return;
        }
        if let Some(kind) =
            Self::consistent_ref_id_contract_violation(expr, contract, had_consistent_ref_ids)
        {
            panic!("pipeline pass `{pass}` violated `consistent_ref_ids` {kind} contract");
        }
    }

    #[cfg(not(debug_assertions))]
    fn enforce_ref_id_property_contract(
        _pass: &'static str,
        _expr: &PseudoExpr,
        _contract: PassContract,
        _had_consistent_ref_ids: bool,
    ) {
    }

    #[cfg(debug_assertions)]
    fn enforce_ref_id_hygiene(pass: &'static str, expr: &PseudoExpr) {
        use crate::decompile::name_orphan_audit::audit_id_orphans;
        if !self_checks::orphan_assert() {
            return;
        }
        let root_params: Vec<(String, crate::pseudo::var_id::VarId)> =
            if let PseudoExpr::Lambda { params, .. } = expr {
                params
                    .iter()
                    .map(|b| (b.as_str().to_string(), b.var_id()))
                    .collect()
            } else {
                Vec::new()
            };
        let report = audit_id_orphans(expr, &root_params);
        assert_eq!(
            report.stranded, 0,
            "pipeline pass `{pass}` emitted {} stranded ref(s). Top: {:?}",
            report.stranded, report.stranded_by_name
        );
    }

    #[cfg(not(debug_assertions))]
    fn enforce_ref_id_hygiene(_pass: &'static str, _expr: &PseudoExpr) {}

    pub(in crate::decompile) fn set_fixed_point_telemetry(
        &mut self,
        telemetry: FixedPointTelemetry,
    ) {
        self.telemetry.fixed_point = telemetry;
    }

    pub(in crate::decompile) fn into_telemetry(self) -> PipelineTelemetry {
        self.telemetry
    }

    /// Project the collected pass snapshots, returning the lineage map and
    /// the [`LineageCarry`] the chained render-prep projection needs.
    ///
    /// The caller owns the carry and must hand it to
    /// `project_chained_pseudo_to_mid`; `None` means there was no projection
    /// to carry from, so the chained call falls back to exact-id seeding.
    ///
    /// `recorder` is the diagnostic route recorder, `None` in production,
    /// threaded from the caller so ONE recorder spans both chained
    /// projections and its window indices stay continuous across the bridge;
    /// a recorder created here would restart numbering at the wrap.
    pub(in crate::decompile) fn project_final_pseudo_lineage(
        &self,
        source_map: &crate::decompile::mid::source_map::SourceMap,
        recorder: Option<&mut crate::decompile::pseudo_lineage::RouteRecorder>,
    ) -> (
        std::collections::HashMap<PseudoNodeId, Vec<MidExprId>>,
        Option<LineageCarry>,
    ) {
        if !self.collect_snapshots || self.pass_snapshots.is_empty() {
            return (std::collections::HashMap::new(), None);
        }
        project_pseudo_to_mid_carrying(
            &self.pass_snapshots,
            &source_map.initial_pseudo_to_mid,
            recorder,
        )
    }
}

#[cfg(test)]
mod tests;
