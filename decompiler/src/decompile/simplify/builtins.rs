//! Builtin helpers scoped to the simplify pipeline.

use crate::builtins::BuiltinId;

use super::Simplifier;

impl Simplifier {
    /// Check if a builtin needs 2 forces (polymorphic builtins).
    pub(crate) fn is_force2_builtin(name: impl Into<BuiltinId>) -> bool {
        name.into().force_count() == 2
    }

    /// Check if a builtin needs 1 force.
    pub(crate) fn is_force1_builtin(name: impl Into<BuiltinId>) -> bool {
        name.into().force_count() == 1
    }

    /// Get a nicer name for a builtin.
    pub(crate) fn nice_builtin_name(name: impl Into<BuiltinId>) -> BuiltinId {
        name.into()
    }
}
