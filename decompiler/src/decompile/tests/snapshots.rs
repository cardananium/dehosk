//! Snapshot tests for the full decompile pipeline.
//!
//! Pin the rendered pseudocode for the synthetic smoke programs so
//! any pipeline change that perturbs the output shows up as a
//! test-time diff. Review the diff, then accept an intended
//! improvement with `cargo insta accept` (requires `cargo-insta`).
//!
//! Corpus-driven snapshots live in the overlay beside the corpus.

#![cfg(test)]

use super::{MIR_V2_SMOKE_HEX, MIR_V3_SMOKE_HEX, decompile_program_with_mir};
use crate::decompile::{decode_hex_to_program, decompile_program};
use crate::{DecompileOptions, ScriptVersion};

/// Decompile with `--decode-church-to-native` ON. This is the
/// primary path the render-prep passes target.
pub(crate) fn decompile_with_church_decode(hex: &str, version: Option<ScriptVersion>) -> String {
    let program = decode_hex_to_program(hex).expect("hex decode");
    let mut opts = DecompileOptions::default();
    opts.script_version = version;
    opts.decode_church_to_native = true;
    decompile_program(&program, opts).expect("decompile")
}

#[test]
fn snapshot_mir_v2_smoke() {
    let rendered = decompile_program_with_mir(MIR_V2_SMOKE_HEX, Some(ScriptVersion::PlutusV2));
    insta::assert_snapshot!("mir_v2_smoke", rendered);
}

#[test]
fn snapshot_mir_v3_smoke() {
    let rendered = decompile_program_with_mir(MIR_V3_SMOKE_HEX, Some(ScriptVersion::PlutusV3));
    insta::assert_snapshot!("mir_v3_smoke", rendered);
}
