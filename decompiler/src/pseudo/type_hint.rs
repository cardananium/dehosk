//! [`TypeHintId`] — the ADT-name key a `PseudoExpr::Constr` carries.
//!
//! It lives here because the AST NODE carries it: both `Constr` and
//! `WhenPattern::Constructor` hold an `Option<TypeHintId>`. It had been
//! declared up in `decompile::blueprint_registry`, beside the registry
//! that resolves it, which made the AST layer depend on the decompiler
//! layer — `pseudo::ast`, `pseudo::fold` and `pseudo::nameless` all
//! reached upward for this one newtype.
//!
//! It is deliberately just a NAME. Resolving one to a display string
//! needs the `BlueprintHintRegistry`, which stays up in `decompile`
//! because it is seeded from the Cardano schema and from the project's
//! `plutus.json`.

use std::rc::Rc;

/// Newtype identifier for a user-defined ADT.
///
/// Wraps the type-name string used as the lookup key in
/// [`crate::cardano::BlueprintHints::constructor_names`], keeping the
/// user-ADT namespace distinct from other stringly-typed identifiers
/// so a constructor name cannot be passed where a type name is
/// expected.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub(crate) struct TypeHintId(Rc<str>);

impl TypeHintId {
    /// Build a [`TypeHintId`] from any string-like value.
    pub(crate) fn new(name: impl Into<Rc<str>>) -> Self {
        Self(name.into())
    }

    /// Borrow the underlying type-name string.
    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }
}

impl<S: Into<Rc<str>>> From<S> for TypeHintId {
    fn from(name: S) -> Self {
        Self::new(name)
    }
}
