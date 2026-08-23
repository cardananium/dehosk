//! Generic AST traversal for MidExpr: `MidCollector` (read-only) and the
//! `rewrite_bottom_up` family (owned rewrites). All of it is iterative.

use crate::pseudo::mid::expr::MidExpr;
use crate::pseudo::mid::expr_id::{ProvenanceBuilder, refresh_mid_ids};
pub(crate) use crate::pseudo::mid::rewrite::{
    Descend, Rewritten, rewrite_bottom_up, rewrite_bottom_up_fixpoint, rewrite_bottom_up_selective,
};

// =============================================================================
// MidCollector — read-only traversal collecting data
// =============================================================================

/// Read-only AST visitor for MidExpr.
///
/// Override `inspect_expr`; recurse through `walk`, not `walk_inner` —
/// that is where the stack grows.
pub(crate) trait MidCollector {
    /// Inspect a node (read-only). Called for every node in the tree.
    fn inspect_expr(&mut self, _expr: &MidExpr) {}

    /// Walk the whole tree, pre-order, iteratively.
    ///
    /// Children are pushed in reverse so they pop in source order.
    fn walk(&mut self, expr: &MidExpr) {
        let mut pending: Vec<&MidExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            self.inspect_expr(current);
            pending.extend(current.children().into_iter().rev());
        }
    }
}

// =============================================================================
// Substitute helper — generic variable substitution using MidFolder
// =============================================================================

use crate::pseudo::var_id::VarId;

/// Replace every free occurrence of `target` with `replacement`, cloned
/// with fresh ids at each site. The descent stops at a Let/Closure/Case
/// binder that shadows `target`.
pub(crate) fn substitute_var(
    expr: MidExpr,
    target: VarId,
    replacement: &MidExpr,
    provenance: &mut ProvenanceBuilder,
) -> MidExpr {
    rewrite_bottom_up_selective(
        expr,
        // Stop at any binder that SHADOWS `target`: past it the name refers to
        // something else, so an occurrence there is not the one being replaced.
        &mut |node| match node {
            // The occurrence itself — replaced whole, nothing below it to walk.
            MidExpr::Var { var, .. } if *var == target => Descend::None,
            // `let target = value in body`: the value is evaluated BEFORE the
            // binding exists, so it still sees the outer `target`; the body
            // does not. Children are `[value, body]`.
            MidExpr::Let { var, .. } if *var == target => Descend::Only(vec![0]),
            // A lambda that rebinds it shadows the whole body.
            MidExpr::Closure { params, .. } if params.contains(&target) => Descend::None,
            // Per-arm: the scrutinee (child 0) is always outside the arms'
            // binders; an arm that rebinds `target` is skipped. Arm `i` sits at
            // child `i + 1`.
            MidExpr::Case { branches, .. } => Descend::Only(
                std::iter::once(0)
                    .chain(
                        branches
                            .iter()
                            .enumerate()
                            .filter(|(_, b)| !b.binders.contains(&target))
                            .map(|(i, _)| i + 1),
                    )
                    .collect(),
            ),
            _ => Descend::All,
        },
        &mut |node| {
            let MidExpr::Var { id, ref var, .. } = node else {
                return node;
            };
            if *var != target {
                return node;
            }
            // Cloned with fresh ids at each site, so two substitutions of the
            // same replacement never share a `MidExprId`.
            let mut replacement = replacement.clone();
            refresh_mid_ids(&mut replacement, provenance);
            provenance.absorb_mid(replacement.id(), id);
            replacement
        },
    )
}
