//! MIR invariant validation helpers.

use std::collections::BTreeSet;
use std::collections::HashSet;

use crate::error::{DecompileError, Result as DecompileResult};
use crate::pseudo::mid::expr::MidExpr;
use crate::pseudo::mid::expr_id::{MidExprId, ProvenanceBuilder};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MidInvariantError {
    DuplicateId { id: MidExprId },
    MissingProvenance { id: MidExprId },
}

pub(crate) fn validate_mid_invariants(
    expr: &MidExpr,
    provenance: &ProvenanceBuilder,
) -> std::result::Result<(), Vec<MidInvariantError>> {
    let mut seen_ids: HashSet<MidExprId> = HashSet::new();
    let mut duplicate_ids: BTreeSet<MidExprId> = BTreeSet::new();
    let mut missing_provenance: BTreeSet<MidExprId> = BTreeSet::new();

    let mut pending: Vec<&MidExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        let id = current.id();
        if !seen_ids.insert(id) {
            duplicate_ids.insert(id);
        }
        if provenance.uplc_ids(id).is_empty() {
            missing_provenance.insert(id);
        }
        pending.extend(current.children().into_iter().rev());
    }

    let mut errors = Vec::new();
    errors.extend(
        duplicate_ids
            .into_iter()
            .map(|id| MidInvariantError::DuplicateId { id }),
    );
    errors.extend(
        missing_provenance
            .into_iter()
            .map(|id| MidInvariantError::MissingProvenance { id }),
    );

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

pub(crate) fn enforce_mid_invariants(
    stage: &str,
    expr: &MidExpr,
    provenance: &ProvenanceBuilder,
) -> DecompileResult<()> {
    if let Err(errors) = validate_mid_invariants(expr, provenance) {
        let details = errors
            .iter()
            .map(|error| match error {
                MidInvariantError::DuplicateId { id } => {
                    format!("duplicate MidExprId detected: {}", id)
                }
                MidInvariantError::MissingProvenance { id } => {
                    format!("missing provenance for {}", id)
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        return Err(DecompileError::internal(format!(
            "MIR invariants violated after {stage}: {details}"
        )));
    }

    Ok(())
}

#[cfg(test)]
mod tests;
