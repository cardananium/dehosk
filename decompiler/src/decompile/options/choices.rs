//! The choice lists for the six enum-valued options, each sitting
//! directly under the `wire_token` match that names its variants.
//!
//! A choice list is a hand-written list beside a Rust enum — the shape
//! of defect this module exists to remove — so every enum is guarded
//! twice:
//!
//! * `wire_token` is non-test code with NO `_` arm, so a new variant
//!   fails the BUILD rather than reaching the wire unnamed;
//! * a test in [`super::tests`] asserts the token set equals the
//!   offered-choice set, so a variant that is tokenised but not offered
//!   fails the SUITE.
//!
//! A variant deliberately not offered is named in that test, with its
//! reason.

use crate::decompile::validator_meta::ValidatorPurpose;
use crate::decompile::validator_shape::{AppliedKind, ScriptKind, SplitPurposes};
use crate::decompile::{OutputLayer, ScriptVersion};

use super::catalogue::{ChoicePayload, OptionChoice};

impl ScriptVersion {
    /// Every version, once.
    pub const ALL: [ScriptVersion; 3] = [Self::PlutusV1, Self::PlutusV2, Self::PlutusV3];

    /// The wire tag for this version. No `_` arm.
    pub const fn wire_token(self) -> &'static str {
        match self {
            Self::PlutusV1 => "PlutusV1",
            Self::PlutusV2 => "PlutusV2",
            Self::PlutusV3 => "PlutusV3",
        }
    }
}

pub const SCRIPT_VERSION_CHOICES: &[OptionChoice] = &[
    OptionChoice {
        value: "PlutusV1",
        label: "Plutus V1",
        summary: "Spend takes datum, redeemer and script_context; non-spend takes redeemer and \
                  script_context. Its TxInfo layout diverges from V2 at index 1 (`outputs` vs \
                  `reference_inputs`), so field naming needs the version to be certain.",
        payload: None,
    },
    OptionChoice {
        value: "PlutusV2",
        label: "Plutus V2",
        summary: "Same calling convention as V1 — spend takes datum, redeemer and \
                  script_context; non-spend takes redeemer and script_context. V1 and V2 share \
                  the `(1,0,_)` header, so auto-detect settles on V2 for it by default; V1 is \
                  chosen only when V1-only evidence appears.",
        payload: None,
    },
    OptionChoice {
        value: "PlutusV3",
        label: "Plutus V3",
        summary: "One script_context argument for every purpose; the purpose is carried inside \
                  `script_info`. Auto-detect reads this straight off a `(1,1,_)` UPLC header.",
        payload: None,
    },
];

impl OutputLayer {
    /// Every layer, once.
    pub const ALL: [OutputLayer; 7] = [
        Self::Decompiled,
        Self::Uplc,
        Self::UplcCanonical,
        Self::RawPseudo,
        Self::PostPipeline,
        Self::PolarityReport,
        Self::PrepProfile,
    ];

    /// The wire tag for this layer. No `_` arm.
    pub const fn wire_token(self) -> &'static str {
        match self {
            Self::Decompiled => "Decompiled",
            Self::Uplc => "Uplc",
            Self::UplcCanonical => "UplcCanonical",
            Self::RawPseudo => "RawPseudo",
            Self::PostPipeline => "PostPipeline",
            Self::PolarityReport => "PolarityReport",
            Self::PrepProfile => "PrepProfile",
        }
    }
}

pub const OUTPUT_LAYER_CHOICES: &[OptionChoice] = &[
    OptionChoice {
        value: "Decompiled",
        label: "Full decompilation",
        summary: "Full decompilation to readable pseudocode.",
        payload: None,
    },
    OptionChoice {
        value: "Uplc",
        label: "UPLC (flattened, readable)",
        summary: "Echo the decoded input as UPLC, readable spine-flattened layout `[f a b c]` \
                  with unique variable names — runs no decompilation.",
        payload: None,
    },
    OptionChoice {
        value: "UplcCanonical",
        label: "UPLC (canonical, binary-nested)",
        summary: "The same echo in the uplc crate's own binary-nested layout `[[[f a] b] c]`.",
        payload: None,
    },
    OptionChoice {
        value: "RawPseudo",
        label: "Raw pseudo (MIR seed, pre-passes)",
        summary: "The pseudo-AST seed straight out of MIR lowering, before any of the structural \
                  passes — the closest view of the 'MIR layer' (still shows church / Scott / \
                  Z-combinator shapes).",
        payload: None,
    },
    OptionChoice {
        value: "PostPipeline",
        label: "Post-pipeline (pre render-prep)",
        summary: "The pseudo-AST after all structural passes, before the render-prep dressing \
                  (stub-ADT synthesis, validator-shape wrap, church->native rewrite).",
        payload: None,
    },
    OptionChoice {
        value: "PrepProfile",
        label: "Render-prep profile (cost diagnostic)",
        summary: "What each of the ~140 render-prep steps cost on this program, slowest \
                  first. Reports instead of emitting code. Use it to find which pass is \
                  expensive on a specific script — a full render prepares the tree several \
                  times over, so the shares matter more than the absolute milliseconds.",
        payload: None,
    },
    OptionChoice {
        value: "PolarityReport",
        label: "Polarity report (church-bool diagnostic)",
        summary: "A church-bool polarity diagnostic — the detected convention (Cip/InverseCip), \
                  the structural signals behind it, and a heuristic-caveat warning. Useful when \
                  a script's `True`/`False`/`!` look suspect (PlutusTx-compiled scripts use the \
                  inverse convention).",
        payload: None,
    },
];

impl ValidatorPurpose {
    /// The wire tag for this purpose. No `_` arm.
    ///
    /// Distinct from [`ValidatorPurpose::keyword`], the surface
    /// word (`spend`) at a handler declaration; this is the serde tag
    /// (`Spend`), as `purposes_serialise_as_their_wire_token` asserts.
    pub const fn wire_token(self) -> &'static str {
        match self {
            Self::Spend => "Spend",
            Self::Mint => "Mint",
            Self::Withdraw => "Withdraw",
            Self::Certificate => "Certificate",
            Self::Vote => "Vote",
            Self::Propose => "Propose",
            Self::Else => "Else",
        }
    }
}

/// Test-only: the purposes the catalogue deliberately does NOT offer.
/// `Else` is deliberately not offered: it is the universal FALLBACK
/// entry the renderer synthesises (`else(_) { fail }`), not a purpose
/// a user can force a single-purpose interpretation to.
#[cfg(test)]
pub const PURPOSE_NOT_OFFERED: &[&str] = &["Else"];

pub const PURPOSE_CHOICES: &[OptionChoice] = &[
    OptionChoice {
        value: "Spend",
        label: "spend",
        summary: "Renders a `spend(...)` handler; matches the `Spending` script-info \
                  constructor.",
        payload: None,
    },
    OptionChoice {
        value: "Mint",
        label: "mint",
        summary: "Renders a `mint(...)` handler; matches the `Minting` script-info constructor.",
        payload: None,
    },
    OptionChoice {
        value: "Withdraw",
        label: "withdraw",
        summary: "Renders a `withdraw(...)` handler; matches the `Rewarding` script-info \
                  constructor.",
        payload: None,
    },
    OptionChoice {
        value: "Certificate",
        label: "certificate",
        summary: "Renders a `certificate(...)` handler; matches the `Certifying` script-info \
                  constructor.",
        payload: None,
    },
    OptionChoice {
        value: "Vote",
        label: "vote",
        summary: "Renders a `vote(...)` handler; matches the `Voting` script-info constructor.",
        payload: None,
    },
    OptionChoice {
        value: "Propose",
        label: "propose",
        summary: "V3-only governance purpose (`ScriptInfo::Proposing`); renders a \
                  `propose(...)` handler. V1/V2 have no Proposing purpose.",
        payload: None,
    },
];

impl SplitPurposes {
    /// Every policy, once.
    pub const ALL: [SplitPurposes; 3] = [Self::Auto, Self::Always, Self::Never];

    /// The wire tag for this policy. No `_` arm.
    pub const fn wire_token(self) -> &'static str {
        match self {
            Self::Auto => "Auto",
            Self::Always => "Always",
            Self::Never => "Never",
        }
    }
}

pub const SPLIT_PURPOSES_CHOICES: &[OptionChoice] = &[
    OptionChoice {
        value: "Auto",
        label: "Auto (split V3 dispatch; flat-wrap V1/V2)",
        summary: "Split when V3 multi-purpose dispatch is detected. V1/V2 multi-validator splits \
                  are not supported yet, so dispatch on V1/V2 falls back to flat wrap.",
        payload: None,
    },
    OptionChoice {
        value: "Always",
        label: "Always (warn on V1/V2 splits)",
        summary: "Same as Auto for V3. On V1/V2 with two or more detected arms, the decompiler \
                  still flat-wraps but emits a warning saying you asked for a split that the \
                  current pipeline can't honor.",
        payload: None,
    },
    OptionChoice {
        value: "Never",
        label: "Never (keep body intact)",
        summary: "Keep the body intact (flat wrap with a single entry). Useful for \
                  round-tripping or when the auto-detected split produces awkward output.",
        payload: None,
    },
];

impl ScriptKind {
    /// Every kind, once.
    pub const ALL: [ScriptKind; 2] = [Self::Validator, Self::Plain];

    /// The wire tag for this kind. No `_` arm.
    pub const fn wire_token(self) -> &'static str {
        match self {
            Self::Validator => "Validator",
            Self::Plain => "Plain",
        }
    }
}

pub const SCRIPT_KIND_CHOICES: &[OptionChoice] = &[
    OptionChoice {
        value: "Validator",
        label: "Validator (force wrap)",
        summary: "Keep the `validator NAME { ... }` wrap on borderline inputs, and emit the \
                  purpose diagnostics that go with it.",
        payload: None,
    },
    OptionChoice {
        value: "Plain",
        label: "Plain Plutus script (`pub fn ...`)",
        summary: "Emit `pub fn NAME(...) { ... }` for library helpers, debug snapshots, or any \
                  UPLC that isn't a real on-chain entry point — skips purpose diagnostics \
                  entirely.",
        payload: None,
    },
];

impl AppliedKind {
    /// Every interpretation, once. `RuntimeCount` stands for the whole
    /// family of explicit splits, so the representative carries 0.
    pub const ALL: [AppliedKind; 4] = [
        Self::Auto,
        Self::Compile,
        Self::Runtime,
        Self::RuntimeCount(0),
    ];

    /// The wire discriminator for this interpretation. No `_` arm.
    ///
    /// `Auto` / `Compile` / `Runtime` are serde tags; `Explicit` is
    /// not: the explicit split goes on the wire as the object
    /// `{"runtime_count": N}`, and `Explicit` is only the discriminator
    /// a UI selects it by. Its choice carries [`ChoicePayload::Count`]
    /// with the JSON key, so a consumer builds that object from the
    /// descriptor.
    pub const fn wire_token(self) -> &'static str {
        match self {
            Self::Auto => "Auto",
            Self::Compile => "Compile",
            Self::Runtime => "Runtime",
            Self::RuntimeCount(_) => "Explicit",
        }
    }
}

pub const APPLIED_KIND_CHOICES: &[OptionChoice] = &[
    OptionChoice {
        value: "Auto",
        label: "Auto (classify by structural fit)",
        summary: "Treat every outer Apply as a pre-applied runtime arg when `applied_count + \
                  lambda_chain_length == runtime_arity` for the version and purpose; otherwise \
                  fall back to all-compile-time.",
        payload: None,
    },
    OptionChoice {
        value: "Compile",
        label: "All compile-time params (CLI default)",
        summary: "All outer Apply nodes are compile-time params (the values baked in when the \
                  validator was parameterized). This is the right answer for any deployed \
                  validator.",
        payload: None,
    },
    OptionChoice {
        value: "Runtime",
        label: "Runtime args pre-applied (datum/redeemer/script_context)",
        summary: "The LAST `runtime_arity_for(version, purpose)` outer Apply nodes are runtime \
                  args (script_context, datum, redeemer) that were pre-applied. Use when \
                  decompiling a debug snapshot of a validator already evaluated against a \
                  specific tx.",
        payload: None,
    },
    OptionChoice {
        value: "Explicit",
        label: "Explicit split (last N runtime)",
        summary: "Split the outer Apply chain manually: the last N applications are runtime \
                  args; everything before is compile-time. N = 0 is the same as all \
                  compile-time.",
        payload: Some(ChoicePayload::Count {
            key: "runtime_count",
            min: 0,
            default: 1,
        }),
    },
];
