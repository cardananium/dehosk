//! Non-render helper functions used by `pretty.rs`.
//!
//! They inspect `PseudoExpr` nodes to make formatting decisions (force
//! multi-line rendering, recognize a single-branch `expect!` `when`),
//! feeding booleans, complexity scores, and pattern projections back to
//! the renderer; they render no output themselves.

pub(super) mod dispatch;
pub(super) mod formatting;
pub(super) mod list_proof;
pub(super) mod optional;
pub(super) mod sizing;
pub(super) mod spans;
pub(super) mod traversal;
