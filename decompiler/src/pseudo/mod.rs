//! The pseudo-code AST: nodes, folds, identifiers, and the nameless
//! form.
//!
//! Strictly BELOW `decompile`. The printer used to live here as
//! `pseudo::pretty`, which made this layer depend on the one above it
//! for the render context, the type table and `prepare_for_render`; it
//! now lives at `decompile::render`, where its dependencies point
//! downward like everything else.
//!
//! `PseudoExpr` is the decompiler's high-level intermediate representation.

pub mod abstract_value;
pub mod ast;
pub mod constructor;
pub mod field_selector;
pub mod fold;
mod layering;
pub mod mid;
/// Nameless IR definitions. `nameless::convert` carries the
/// round-trip converters; `nameless::invariants` carries the
/// invariant validator.
pub mod nameless;
pub(crate) mod pbox;
pub mod root_layout;
pub mod type_hint;
pub mod var_id;
pub mod walker;

pub(crate) use var_id::OptionVarIdGet;

// Kept only because the test suites name them at this path.
#[cfg(test)]
pub(crate) use constructor::ConstructorShape;
#[cfg(test)]
pub(crate) use field_selector::FieldSelector;
