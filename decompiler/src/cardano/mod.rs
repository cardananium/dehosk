//! Cardano-specific functionality: blueprint (`plutus.json`) parsing.
//!
//! Two sibling modules — `patterns` (context-access / purpose / validation
//! shape recognition) and `stdlib` (builtin → Aiken-like stdlib name
//! mapping) — were deleted: nothing in the crate, the CLI or the web app
//! referenced them, and the decompiler had grown its own recognisers for
//! both jobs (`decompile::simplify::postprocess::context` and
//! `builtins::display_name`). They had been invisible to `dead_code`
//! only because they were `pub`.

pub mod blueprint;

pub use blueprint::{Blueprint, BlueprintHints};
