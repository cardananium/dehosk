//! Canonical walker abstraction for `PseudoExpr` transformations.
//!
//! Import the walker trait from here (`use crate::pseudo::walker::Walker;`)
//! rather than reaching into `super::fold` directly; this re-export is the
//! single public entry point, and `ExprFolder` remains the concrete
//! implementation target (hooks, stack safety, scope tracking).
//!
//! All hooks have identity default implementations, so `impl Walker for
//! MyPass {}` reconstructs the tree unchanged.

pub(crate) use super::fold::{ExprFolder as Walker, ExprVisitor as WalkVisitor, FoldAction};

#[cfg(test)]
mod tests;
