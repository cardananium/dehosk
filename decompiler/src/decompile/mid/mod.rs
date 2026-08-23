//! Mid-level IR pipeline: UPLC → MidExpr → analysis → PseudoExpr.
//!
//! MidExpr preserves UPLC semantics for analysis and
//! pre-computation before lowering to the high-level PseudoExpr.

pub mod analyze;
pub mod bool_orientation;
pub mod fold;
pub mod free_vars;
pub mod lower;
pub mod patterns;
pub mod precompute;
pub mod source_map;
pub mod translate;
pub mod type_env;
pub mod use_count;
pub mod validate;
pub mod var_registry;
