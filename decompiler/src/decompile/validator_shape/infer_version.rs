//! Refine `ScriptVersion` from the UPLC binary header plus a builtin
//! lower-bound scan.
//!
//! Builtin presence proves a lower bound on the required Plutus
//! protocol version; absence proves nothing — a V3 script that uses
//! no V2/V3-only builtin is indistinguishable from a V1 one.
//! `(1, 1, _)` is V3; `(1, 0, _)` plus a V2-only builtin is V2;
//! `(1, 0, _)` with no V2/V3 builtins is V1 or V2 (ambiguous).
//!
//! `builtin_level` classifies each builtin: V2-only are
//! `SerialiseData` and the two secp256k1 verifications; V3-only are
//! the BLS12-381 ops, `Keccak_256` / `Blake2b_224` / `Ripemd_160`,
//! integer ↔ bytestring conversion, and the CIP-122 bit/byte ops.
//!
//! A V3-only builtin under a `(1, 0, _)` header is inconsistent —
//! such a script would be rejected on-chain — so it yields
//! `InconsistentV3BuiltinInV1V2` for the caller to surface.

use uplc::ast::{NamedDeBruijn, Program, Term};
use uplc::builtins::DefaultFunction;

use crate::decompile::ScriptVersion;

/// Result of version inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum VersionDecision {
    /// Definitively V3 — from `(1,1,_)` UPLC header.
    DefinitelyV3,
    /// Definitively V2 — `(1,0,_)` UPLC header + V2-only builtin
    /// usage observed.
    DefinitelyV2,
    /// `(1, 0, _)` header, no V2/V3 signal. `to_script_version`
    /// defaults to V2; V1 is deprecated and virtually unused.
    AmbiguousV1OrV2,
    /// `(1, 0, _)` header but a V3-only builtin was observed — the
    /// script would fail on-chain. Surface as a warning.
    InconsistentV3BuiltinInV1V2,
    /// Unknown UPLC header version (not `(1,0,_)` or `(1,1,_)`).
    /// Modern UPLC only emits these two; anything else is opaque.
    UnknownUplcVersion { version: (usize, usize, usize) },
}

impl VersionDecision {
    /// Convert to a concrete `ScriptVersion`, defaulting where the
    /// decision is ambiguous. `None` for an unknown UPLC header
    /// version; an explicit `--script-version` bypasses inference.
    pub(crate) fn to_script_version(&self) -> Option<ScriptVersion> {
        match self {
            Self::DefinitelyV3 => Some(ScriptVersion::PlutusV3),
            Self::DefinitelyV2 => Some(ScriptVersion::PlutusV2),
            Self::AmbiguousV1OrV2 => Some(ScriptVersion::PlutusV2),
            Self::InconsistentV3BuiltinInV1V2 => Some(ScriptVersion::PlutusV2),
            Self::UnknownUplcVersion { .. } => None,
        }
    }
}

/// Infer the Plutus version from a UPLC program. Combines the
/// binary header version with a scan of builtin usage in the
/// program term.
pub(crate) fn infer_version(program: &Program<NamedDeBruijn>) -> VersionDecision {
    let (major, minor, _patch) = program.version;
    match (major, minor) {
        (1, 1) => VersionDecision::DefinitelyV3,
        (1, 0) => {
            let signal = scan_builtin_signal(&program.term);
            match signal {
                BuiltinSignal::V3OnlyObserved => VersionDecision::InconsistentV3BuiltinInV1V2,
                BuiltinSignal::V2OnlyObserved => VersionDecision::DefinitelyV2,
                BuiltinSignal::V1Compatible => VersionDecision::AmbiguousV1OrV2,
            }
        }
        _ => VersionDecision::UnknownUplcVersion {
            version: program.version,
        },
    }
}

/// Tristate signal from a builtin scan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BuiltinSignal {
    /// Only V1-compatible builtins were observed.
    V1Compatible,
    /// At least one V2-only builtin observed (no V3-only).
    V2OnlyObserved,
    /// At least one V3-only builtin observed.
    V3OnlyObserved,
}

/// Walk the term, collecting the strongest builtin signal seen.
fn scan_builtin_signal(term: &Term<NamedDeBruijn>) -> BuiltinSignal {
    use BuiltinSignal::*;
    let mut signal = V1Compatible;
    let mut stack: Vec<&Term<NamedDeBruijn>> = vec![term];
    while let Some(t) = stack.pop() {
        match t {
            Term::Builtin { fun, .. } => {
                let level = builtin_level(*fun);
                signal = match (signal, level) {
                    (V3OnlyObserved, _) => V3OnlyObserved,
                    (_, V3OnlyObserved) => V3OnlyObserved,
                    (V2OnlyObserved, _) => V2OnlyObserved,
                    (_, V2OnlyObserved) => V2OnlyObserved,
                    _ => V1Compatible,
                };
            }
            Term::Apply {
                function, argument, ..
            } => {
                stack.push(function.as_ref());
                stack.push(argument.as_ref());
            }
            Term::Delay { body, .. } | Term::Force { body, .. } | Term::Lambda { body, .. } => {
                stack.push(body.as_ref())
            }
            Term::Constr { fields, .. } => {
                for f in fields {
                    stack.push(f);
                }
            }
            Term::Case {
                constr, branches, ..
            } => {
                stack.push(constr.as_ref());
                for b in branches {
                    stack.push(b);
                }
            }
            Term::Var { .. } | Term::Constant { .. } | Term::Error { .. } => {}
        }
    }
    signal
}

/// Classify a builtin by the minimum Plutus version that exposes it.
fn builtin_level(fun: DefaultFunction) -> BuiltinSignal {
    use DefaultFunction as F;
    match fun {
        // V2-only builtins (CIP-42, CIP-49).
        F::SerialiseData
        | F::VerifyEcdsaSecp256k1Signature
        | F::VerifySchnorrSecp256k1Signature => BuiltinSignal::V2OnlyObserved,
        // V3-only builtins (PV9, PV10).
        F::Bls12_381_G1_Add
        | F::Bls12_381_G1_Neg
        | F::Bls12_381_G1_ScalarMul
        | F::Bls12_381_G1_Equal
        | F::Bls12_381_G1_Compress
        | F::Bls12_381_G1_Uncompress
        | F::Bls12_381_G1_HashToGroup
        | F::Bls12_381_G2_Add
        | F::Bls12_381_G2_Neg
        | F::Bls12_381_G2_ScalarMul
        | F::Bls12_381_G2_Equal
        | F::Bls12_381_G2_Compress
        | F::Bls12_381_G2_Uncompress
        | F::Bls12_381_G2_HashToGroup
        | F::Bls12_381_MillerLoop
        | F::Bls12_381_MulMlResult
        | F::Bls12_381_FinalVerify
        | F::Keccak_256
        | F::Blake2b_224
        | F::IntegerToByteString
        | F::ByteStringToInteger
        | F::AndByteString
        | F::OrByteString
        | F::XorByteString
        | F::ComplementByteString
        | F::ReadBit
        | F::WriteBits
        | F::ReplicateByte
        | F::ShiftByteString
        | F::RotateByteString
        | F::CountSetBits
        | F::FindFirstSetBit
        | F::Ripemd_160 => BuiltinSignal::V3OnlyObserved,
        // Everything else is V1-compatible.
        _ => BuiltinSignal::V1Compatible,
    }
}
