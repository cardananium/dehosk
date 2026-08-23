//! Variable use counting pass for MidExpr.
//!
//! Counts references per VarId and writes the totals into
//! `Let.use_count`.

use std::collections::HashMap;

use crate::pseudo::mid::expr::MidExpr;
use crate::pseudo::var_id::VarId;

pub(crate) fn count_uses(expr: &MidExpr) -> HashMap<VarId, u32> {
    let mut counts: HashMap<VarId, u32> = HashMap::new();
    count_uses_rec(expr, &mut counts);
    counts
}

/// Tally every `Var` occurrence in the tree.
///
/// Every node is visited and only `Var` does anything, so the child set
/// comes from [`MidExpr::children`].
fn count_uses_rec(expr: &MidExpr, counts: &mut HashMap<VarId, u32>) {
    let mut pending: Vec<&MidExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let MidExpr::Var { var, .. } = current {
            *counts.entry(*var).or_insert(0) += 1;
        }
        pending.extend(current.children().into_iter().rev());
    }
}

/// Apply use counts to the MidExpr tree, writing into `Let.use_count` fields.
pub(crate) fn apply_use_counts(expr: &mut MidExpr) {
    let counts = count_uses(expr);
    apply_counts_rec(expr, &counts);
}

/// Write each `Let`'s tallied use count into its `use_count` field.
fn apply_counts_rec(expr: &mut MidExpr, counts: &HashMap<VarId, u32>) {
    let mut pending: Vec<&mut MidExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let MidExpr::Let { var, use_count, .. } = current {
            *use_count = counts.get(var).copied().unwrap_or(0);
        }
        pending.extend(current.children_mut().into_iter().rev());
    }
}

#[cfg(test)]
mod tests;
