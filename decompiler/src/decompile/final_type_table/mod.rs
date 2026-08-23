//! Side table of solved types anchored to the latest pseudo AST passed to the
//! type solver.
//!
//! `mid::type_env::TypeEnvironment` is populated during MIR lower, keyed by
//! canonical MIR `VarId`s, and frozen before post-MIR rewrites run — any
//! downstream `VarId` rewrite breaks its lookups, so it cannot be the source
//! of truth for output produced from the *final* AST.
//!
//! `FinalTypeTable` is keyed by the declaration ids present in the AST the
//! solver was given. Later display/render-prep rewrites may still remove,
//! rename, or remap ids, so it is a complete map of the render-prepared AST
//! only if the pipeline re-solves or remaps it afterwards. It is deliberately
//! a distinct type from `TypeEnvironment` so a consumer needing final-AST
//! types cannot be handed the frozen MIR env by accident.
//!
//! Final ids are not assumed to coincide with MIR ids: a caller seeding
//! entries from a MIR-keyed env must translate ids before `bind_var`, which
//! stores exactly what it is given. Construct late for the current solver
//! input, populate via `bind_var`, then `freeze` (further mutation panics)
//! before sharing with render / invariant-validation consumers.

use std::collections::HashMap;
use std::rc::Rc;

use crate::pseudo::ast::PseudoType;
use crate::pseudo::var_id::VarId;

#[derive(Debug, Clone, Default)]
pub(crate) struct FinalTypeTable {
    var_types: HashMap<VarId, Rc<PseudoType>>,
    frozen: bool,
}

impl FinalTypeTable {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Test-only accessor: the pipeline drives the table through
    /// `freeze`/`type_of_var`, so this exists for assertions.
    #[cfg(test)]
    pub(crate) fn is_frozen(&self) -> bool {
        self.frozen
    }

    pub(crate) fn freeze(&mut self) {
        self.frozen = true;
    }

    fn assert_mutable(&self, op: &'static str) {
        if self.frozen {
            panic!(
                "FinalTypeTable: attempted `{op}` after freeze(); entries must be written before the table is handed to consumers"
            );
        }
    }

    pub(crate) fn bind_var(&mut self, id: VarId, ty: Rc<PseudoType>) {
        self.assert_mutable("bind_var");
        self.var_types.insert(id, ty);
    }

    pub(crate) fn type_of_var(&self, id: VarId) -> Option<Rc<PseudoType>> {
        self.var_types.get(&id).cloned()
    }

    /// Test-only accessor: the pipeline drives the table through
    /// `freeze`/`type_of_var`, so this exists for assertions.
    #[cfg(test)]
    pub(crate) fn contains_var(&self, id: VarId) -> bool {
        self.var_types.contains_key(&id)
    }

    /// Test-only accessor: the pipeline drives the table through
    /// `freeze`/`type_of_var`, so this exists for assertions.
    #[cfg(test)]
    pub(crate) fn var_type_count(&self) -> usize {
        self.var_types.len()
    }
}

#[cfg(test)]
mod tests;
