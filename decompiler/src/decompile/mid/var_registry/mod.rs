//! Variable lifecycle registry.
//!
//! Tracks the variable metadata that is still consumed after MIR lowering:
//! Display name, DeBruijn binding, origin, and stepping-facing role/type hints.

use std::collections::HashMap;

use crate::pseudo::abstract_value::AbstractType;
use crate::pseudo::mid::expr_id::SourceSpan;
use crate::pseudo::var_id::{VarId, VarInterner};

/// Complete information about a variable throughout the pipeline.
#[derive(Debug, Clone)]
pub(crate) struct VarEntry {
    pub id: VarId,
    /// Display name in decompiled code.
    pub display_name: String,
    /// Original DeBruijn info (for runtime env lookup during stepping).
    pub debruijn: Option<DebruijnBinding>,
    /// Optional type hint surfaced to stepping/debug output.
    pub tipo: Option<AbstractType>,
    /// Where this variable is declared in decompiled source.
    pub declaration_span: Option<SourceSpan>,
    /// Where this variable is used in decompiled source.
    pub use_spans: Vec<SourceSpan>,
    /// How this variable was created in UPLC.
    pub origin: VarOrigin,
    /// Semantic role (e.g., "datum", "redeemer", "script_context").
    pub semantic_role: Option<String>,
}

/// DeBruijn binding information for runtime environment inspection.
/// Connects a VarId to the specific Lambda that binds it in UPLC.
#[derive(Debug, Clone)]
pub(crate) struct DebruijnBinding {
    /// `uniq_id` of the Lambda term that introduces this variable.
    pub binder_term_id: isize,
    /// DeBruijn index relative to that Lambda (always 0 for the param itself).
    pub index: usize,
}

/// How a variable was created in UPLC.
#[derive(Debug, Clone)]
pub(crate) enum VarOrigin {
    /// Lambda parameter at a given position.
    LambdaParam {
        lambda_term_id: isize,
        position: usize,
    },
    /// Reconstructed let binding (from Apply(Lambda, value)).
    LetBinding { apply_term_id: isize },
    /// Y-combinator self-reference.
    RecursiveSelf { y_comb_term_id: isize },
    /// Constructor field destructuring.
    ConstrField {
        case_term_id: isize,
        tag: usize,
        field: usize,
    },
    /// Synthetic (created by analysis, no direct UPLC counterpart).
    Synthetic,
}

/// Registry tracking all variables and their metadata.
pub(crate) struct VarRegistry {
    entries: HashMap<VarId, VarEntry>,
    /// Reverse index: UPLC binder_term_id → VarId.
    term_to_var: HashMap<isize, Vec<VarId>>,
    /// Reverse index: DeBruijn (binder_term_id, index) → VarId.
    debruijn_to_var: HashMap<(isize, usize), VarId>,
}

impl VarRegistry {
    pub(crate) fn new() -> Self {
        Self {
            entries: HashMap::new(),
            term_to_var: HashMap::new(),
            debruijn_to_var: HashMap::new(),
        }
    }

    pub(crate) fn register(&mut self, id: VarId, display_name: String, origin: VarOrigin) {
        let term_id = match &origin {
            VarOrigin::LambdaParam { lambda_term_id, .. } => Some(*lambda_term_id),
            VarOrigin::LetBinding { apply_term_id } => Some(*apply_term_id),
            VarOrigin::RecursiveSelf { y_comb_term_id } => Some(*y_comb_term_id),
            VarOrigin::ConstrField { case_term_id, .. } => Some(*case_term_id),
            VarOrigin::Synthetic => None,
        };

        if let Some(tid) = term_id {
            self.term_to_var.entry(tid).or_default().push(id);
        }

        self.entries.insert(
            id,
            VarEntry {
                id,
                display_name,
                debruijn: None,
                tipo: None,
                declaration_span: None,
                use_spans: Vec::new(),
                origin,
                semantic_role: None,
            },
        );
    }

    /// Record DeBruijn binding information for runtime env inspection.
    pub(crate) fn record_debruijn(&mut self, id: VarId, binder_term_id: isize, index: usize) {
        if let Some(entry) = self.entries.get_mut(&id) {
            entry.debruijn = Some(DebruijnBinding {
                binder_term_id,
                index,
            });
        }
        self.debruijn_to_var.insert((binder_term_id, index), id);
    }

    pub(crate) fn set_semantic_role(&mut self, id: VarId, role: String) {
        if let Some(entry) = self.entries.get_mut(&id) {
            entry.semantic_role = Some(role);
        }
    }

    pub(crate) fn get(&self, id: VarId) -> Option<&VarEntry> {
        self.entries.get(&id)
    }

    pub(crate) fn get_mut(&mut self, id: VarId) -> Option<&mut VarEntry> {
        self.entries.get_mut(&id)
    }

    pub(crate) fn find_by_origin_term(&self, term_id: isize) -> &[VarId] {
        self.term_to_var
            .get(&term_id)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Return the unique variable created from a specific UPLC term, if and
    /// only if there is exactly one such variable.
    pub(crate) fn unique_by_origin_term(&self, term_id: isize) -> Option<&VarEntry> {
        let mut ids = self.find_by_origin_term(term_id).iter().copied();
        let first = ids.next()?;
        if ids.next().is_some() {
            return None;
        }
        self.get(first)
    }

    /// Find VarId by DeBruijn binding (for runtime env inspection).
    pub(crate) fn find_by_debruijn(&self, binder_term_id: isize, index: usize) -> Option<VarId> {
        self.debruijn_to_var.get(&(binder_term_id, index)).copied()
    }

    pub(crate) fn all_vars(&self) -> impl Iterator<Item = &VarEntry> {
        self.entries.values()
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Refresh display names from the current VarInterner state after any
    /// cosmetic renaming/disambiguation pass.
    pub(crate) fn sync_display_names(&mut self, interner: &VarInterner) {
        for (var_id, entry) in &mut self.entries {
            entry.display_name = interner.resolve(*var_id).to_string();
        }
    }
}

impl Default for VarRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
