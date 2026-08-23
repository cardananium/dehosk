//! Validator-shape detection.
//!
//! Owns the analysis of a UPLC validator's outer structure and the
//! resulting "shape" that drives the renderer's wrap decision.
//!
//! ## Background
//!
//! The compiler compiles every validator — V1/V2/V3, single-purpose or
//! multi-purpose — as a single UPLC term of shape:
//!
//! ```text
//! Lambda(p1, Lambda(p2, ..., Lambda(pN, Lambda(ctx, body))))
//! ```
//!
//! The outer `N` lambdas are the compile-time params of the `validator
//! <NAME>(p1, p2, ...)` header; the last lambda takes the runtime arg
//! (`ctx` for V3, the datum-redeemer-ctx chain for the legacy V1/V2
//! calling convention). Compile-time params may already be applied in
//! the script bytes, as an outer `Apply(<curried>, const)` chain;
//! peeling it leaves the curried function.
//!
//! ## Detection signals
//!
//! UPLC binary version (`Program::version`):
//!   `(1, 0, _)` → V1 or V2 (ambiguous from bytes alone).
//!   `(1, 1, _)` → V3 (Plutus Core 1.1 introduces SOP `Constr`/`Case`).
//! V2/V3-only builtins (lower-bound proof — see `infer_version`).
//! Body internal dispatch on `script_context.script_info` (V3 multi).
//! Outer Apply/Lambda chain (`inspect_outer`).

use uplc::ast::{Constant, NamedDeBruijn, Program};

use crate::decompile::ScriptVersion;
use crate::decompile::options;
use crate::decompile::options::macros::define_options;
use crate::decompile::options::{Exposure, GroupId, OptionKind};
use crate::decompile::validator_meta::{ValidatorEntry, ValidatorMeta, ValidatorPurpose};

mod build_plan;
pub(crate) mod detect_dispatch;
mod infer_version;
mod inspect_outer;
mod param_surface;
mod wrap_rendered;

pub(crate) use build_plan::{build_plan_impl, runtime_arity_for};
pub(crate) use detect_dispatch::purpose_from_unknown_tag;
pub(crate) use detect_dispatch::{PurposeDispatch, detect_dispatch};
pub(crate) use infer_version::{VersionDecision, infer_version};
pub(crate) use inspect_outer::inspect_outer;
pub(crate) use param_surface::{
    annotate_hoisted_consts_with_param_origin, format_applied_params_prefix_with_skip,
    hoist_compile_param_lets, resolve_runtime_count as param_surface_runtime_count,
};
pub(crate) use wrap_rendered::wrap_rendered_separated_with_bodies;
// The multi-purpose wrap is exercised directly by the pipeline-parity
// test, which builds the plan itself.
#[cfg(test)]
pub(crate) use wrap_rendered::wrap_rendered_separated;

#[cfg(test)]
mod tests;

// CLI / DecompileOptions input

// The four wrap-shape options: the struct AND its catalogue entries
// out of ONE list — see `crate::decompile::options`.
//
// `label` is the web panel's control label, a field's first doc line
// its one-line description, and the remaining doc lines that
// control's long hint.
define_options! {
    /// Options that disambiguate validator shapes the bytecode alone
    /// can't distinguish.
    #[derive(Debug, Clone, Default, PartialEq, Eq)]
    ValidatorShapeOptions, path ["validator_shape"] {
        /// Use when V1/V2 non-spend or V3 single-purpose is ambiguous
        /// Force a single-purpose interpretation: use it on a V1/V2 non-spend validator — UPLC alone can't tell mint from withdraw from certificate, only the calling convention can — or on a V3 single-purpose script with no dispatch block. Without it, ambiguous V1/V2 non-spend inputs render with a generic signature and a warning. A purpose plus Split Purposes = Always behaves DIFFERENTLY on the two front-ends: the CLI refuses the pair up front (`--purpose` and `--split-purposes always` are mutually exclusive there), while the HTTP API accepts it and the explicit purpose wins outright, on every version, with the split setting dropped silently. The `SplitAlwaysIgnoredForV1V2` warning is a separate path that does not fire there: it requires NO purpose set, Split Purposes = Always, two or more detected purpose arms, and a version gate that refuses the split.
        ///
        /// Example (default — V1/V2 non-spend, ambiguous):
        ///   // Warning: V1/V2 non-spend purpose is ambiguous from bytecode
        ///   validator decompiled(redeemer, script_context) { ... }
        ///
        /// Example (--purpose mint):
        ///   validator decompiled {
        ///     mint(redeemer, script_context) { ... }
        ///     else(_) { fail }
        ///   }
        purpose: Option<ValidatorPurpose> = Exposure::Ui {
            label: "Validator Purpose",
            group: GroupId::ValidatorWrapShape,
            kind: OptionKind::Choice {
                choices: options::PURPOSE_CHOICES,
                unset: Some("Auto / not specified"),
            },
            cli_flag: Some("--purpose"),
        },

        /// How to handle V3 multi-purpose dispatch
        /// Every mode first needs the AST dispatch detector to find two or more purpose arms; this setting decides what happens then. AUTO (default): split a detected V3 dispatch — V1/V2 multivalidator splits are unsupported, so V1/V2 falls back to flat wrap. ALWAYS: as Auto on V3; on V1/V2 with two or more detected arms, flat-wrap and warn that the split can't be honored. NEVER: keep the body intact regardless.
        split_purposes: SplitPurposes = Exposure::Ui {
            label: "Split Purposes",
            group: GroupId::ValidatorWrapShape,
            kind: OptionKind::Choice {
                choices: options::SPLIT_PURPOSES_CHOICES,
                unset: None,
            },
            cli_flag: Some("--split-purposes"),
        },

        /// Auto-detect treats 1/2/3-lambda inputs as validators
        /// Render the program as a Cardano validator block (`validator NAME { ... }`) or as a plain function (`pub fn NAME(...) { ... }`). Auto-detect (the default) picks validator when a V3 dispatch is detected or the lambda arity is 1/2/3, plain otherwise. Force "Validator" to keep the wrap — and its purpose diagnostics — on a borderline input; force "Plain" for library helpers, debug snapshots, or any UPLC that isn't a real on-chain entry point, which skips purpose diagnostics entirely.
        ///
        /// Example (Auto / Validator):
        ///   validator decompiled(datum, redeemer, script_context) { ... }
        ///
        /// Example (Plain):
        ///   pub fn decompiled(datum, redeemer, script_context) { ... }
        script_kind: Option<ScriptKind> = Exposure::Ui {
            label: "Script Kind",
            group: GroupId::ValidatorWrapShape,
            kind: OptionKind::Choice {
                choices: options::SCRIPT_KIND_CHOICES,
                unset: Some("Auto-detect"),
            },
            cli_flag: Some("--script-kind"),
        },

        /// How to interpret the outer Apply chain
        /// COMPILE (the CLI and HTTP API default): every outer Apply node is a compile-time param baked in by compilation — the right answer for a deployed validator. RUNTIME: the LAST `runtime_arity_for(version, purpose)` Apply nodes are pre-applied runtime args (script_context, datum, redeemer) — use when decompiling a debug snapshot of an already-evaluated validator. EXPLICIT (N): split manually — the last N applications are runtime, everything before is compile-time. AUTO: label the whole chain runtime only when `applied_count + lambda_chain_length == runtime_arity`, otherwise fall back to compile-time.
        ///
        /// Example header (Compile):
        ///   // Applied compile-time params (from outer Apply chain) — applied first (innermost):
        ///   // param_0: <non-constant: force builtin.tailList>
        ///
        /// Example header (Runtime, same input):
        ///   // Info: All 2 outer Apply node(s) labeled as pre-applied runtime args (--applied-as).
        ///   // Pre-applied runtime args (datum / redeemer / script_context) — applied last (outermost):
        ///   // runtime_arg_0: <non-constant: force builtin.tailList>
        applied_kind: AppliedKind = Exposure::Ui {
            label: "Outer Apply Args",
            group: GroupId::ValidatorWrapShape,
            kind: OptionKind::Choice {
                choices: options::APPLIED_KIND_CHOICES,
                unset: None,
            },
            cli_flag: Some("--applied-as"),
        },
    }
}

/// How to interpret the outer-Apply chain that's already baked into
/// the program. Drives [`format_applied_params_prefix`]'s labeling.
///
/// Bytecode cannot distinguish a top-level `Apply(curried, const)`
/// that pre-applies a compile-time param from one that pre-applies a
/// runtime arg (datum / redeemer / script_context for V1/V2,
/// script_context for V3), so the user picks with `--applied-as`.
///
/// Per-arg split rule: the LAST `runtime_count` outer Apply nodes
/// are runtime args (they are applied AFTER compile params on the
/// curried lambda chain); the first `applied_count - runtime_count`
/// are compile-time params.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum AppliedKind {
    /// Default: treat every outer Apply as a pre-applied runtime
    /// arg when `applied_count + lambda_chain_length` equals the
    /// calling convention's `runtime_arity`; any other ratio falls
    /// back to the all-compile-time reading `Compile` produces.
    #[default]
    Auto,
    /// Explicit override: all outer Apply nodes are compile-time
    /// params (`runtime_count = 0`). Disables the auto heuristic.
    Compile,
    /// The LAST `runtime_arity_for(version, purpose)` outer
    /// Apply nodes are runtime args; those before them are
    /// compile-time params. Use for a debug snapshot whose
    /// runtime args (datum / redeemer / script_context) were
    /// pre-applied.
    Runtime,
    /// Explicit per-arg split — the LAST `N` outer Apply nodes are
    /// runtime args; the first `applied_count - N` are compile-time
    /// params. `N = 0` is equivalent to `Compile`; `N >= applied_count`
    /// saturates to "all runtime".
    RuntimeCount(usize),
}

/// What kind of Plutus script the input is. Drives the wrap form
/// and whether validator-specific diagnostics fire.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScriptKind {
    /// Cardano on-chain validator (spend/mint/withdraw/certificate/vote
    /// or V3 multi-purpose). Wraps as a validator block, or as
    /// flat-wrap with purpose-ambiguity diagnostics.
    Validator,
    /// Plain Plutus script — a library function, debug snapshot, or
    /// off-chain computation kernel. Emit `pub fn name(args) { body }`
    /// without validator-block wrap or purpose diagnostics.
    Plain,
}

/// How aggressive should the multi-purpose split be.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum SplitPurposes {
    /// Auto: split when a V3 dispatch shape is detected (≥2 known
    /// purpose constructors). Otherwise leave body intact.
    #[default]
    Auto,
    /// Always split — like `Auto`, but emits
    /// `SplitAlwaysIgnoredForV1V2` when the version gate refuses
    /// the split. Both need ≥2 detected purposes.
    Always,
    /// Never split — emit the flat-wrap form regardless of detected
    /// dispatch (the user wants the raw `when` visible).
    Never,
}

// Outer-structure analysis (raw UPLC peel)

/// The outer structure of a raw UPLC program after peeling the
/// `Apply` chain (applied compile params) and `Lambda` chain
/// (unapplied compile params + runtime args).
///
/// The compiler's compiled UPLC always has the shape:
///
/// ```text
/// Apply^M (Lambda^N body) (const_1) ... (const_M)
/// ```
///
/// Where `M ≤ N`. `inspect_outer` separates these and exposes the
/// counts.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct OuterStructure {
    /// Constants applied to the outermost lambdas (compile-time
    /// params already baked into the script bytes).
    pub applied_params: Vec<AppliedParam>,

    /// Positions in `applied_params` whose argument binds the
    /// compiler's own top-level `let` chain rather than a surface
    /// lambda — PlutusTx's shared-builtin hoisting puts its outermost
    /// binding on the same spine as the real params. Ascending, and
    /// empty for the plain `Apply^M (Lambda^N body)` shape.
    ///
    /// Labeling only: these positions are still counted in
    /// `applied_params`, so every plan decision keyed on the spine
    /// length is unaffected. The param surface skips them rather than
    /// calling a compiled-in binding `param_N`.
    pub compiler_binding_indices: Vec<usize>,

    /// Total number of lambdas in the curried inner term — the WHOLE
    /// chain: the Apply chain consumed `applied_params.len()` of
    /// them, the rest are unapplied (compile params + runtime args)
    /// at the surface. Use [`OuterStructure::truly_unapplied`]
    /// rather than open-coding that subtraction.
    pub lambda_chain_length: usize,

    /// Expected runtime arity per Cardano calling convention:
    /// V3: 1 (single `ctx` arg).
    /// V1/V2 spend: 3 (`datum, redeemer, ctx`).
    /// V1/V2 non-spend: 2 (`redeemer, ctx`).
    ///
    /// Defaults to 1 (V3-style); adjusted downstream from the
    /// inferred version + purpose.
    pub runtime_arity: usize,

    /// Non-zero when the Apply chain over-applied (more args than
    /// the lambda chain expects) — pre-applied runtime args, e.g. a
    /// debug snapshot with `script_context` already applied. The
    /// renderer falls back to flat-wrap with a diagnostic.
    pub pre_applied_runtime_args: usize,
}

impl OuterStructure {
    /// Lambdas left at the surface after the Apply chain consumed
    /// `applied_params.len()` of them — the count callers want
    /// when reasoning about V3 / V1/V2 calling-convention arity.
    pub(crate) fn truly_unapplied(&self) -> usize {
        self.lambda_chain_length
            .saturating_sub(self.applied_params.len())
    }
}

/// A compile-time param value applied to the outer lambda chain.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum AppliedParam {
    /// A literal UPLC constant (most common — bytestring, integer,
    /// list, pair, etc.). Suitable for rendering as a
    /// `const NAME = <value>` block at the top of the output.
    Constant(Constant),
    /// A non-constant argument was applied (e.g. another term).
    /// `summary` names it (`force builtin.tailList`, `var foo`,
    /// `<apply chain>`) instead of a bare `<non-constant>`. The
    /// common case is `Force(Builtin(TailList))` — surface
    /// pre-applies head/tail list builtins as innermost compile
    /// args to avoid repeated `force` in the body. Indicates a
    /// non-trivial parameterization or pre-applied runtime args;
    /// the renderer falls back to flat-wrap with a diagnostic.
    NonConstant { summary: String },
}

// Validator shape (the post-analysis classification)

/// The detected shape of the validator after all signals are
/// considered. Drives [`build_plan`].
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ValidatorShape {
    /// V3 multi-purpose: 1-arg lambda + internal dispatch on
    /// `script_info`. The detected purposes appear in body order.
    MultiPurposeV3 { purposes: Vec<ValidatorPurpose> },

    /// V3 single-purpose: 1-arg lambda, no detected dispatch. The
    /// purpose name is unknown from bytecode (Cardano's dispatch is
    /// external); the caller may supply it via
    /// `ValidatorShapeOptions::purpose`.
    SinglePurposeV3 { purpose: Option<ValidatorPurpose> },

    /// V1/V2 single-purpose. Outer lambda arity determines the
    /// `kind` (3-arg → spend; 2-arg → mint/withdraw/certificate). The
    /// specific non-spend purpose is unknown from bytecode; the
    /// caller may supply it via `ValidatorShapeOptions::purpose`.
    SinglePurposeV1V2 {
        purpose: Option<ValidatorPurpose>,
        kind: V1V2Kind,
    },

    /// Pre-Aug 2024 surface "multivalidator" wrap (outer Constr-index
    /// branching between a 2-arg and 3-arg lambda). Nothing constructs
    /// this variant — there is no detector for the shape.
    LegacyV1V2MultiValidator,

    /// Could not classify — emit flat-wrap with diagnostic.
    Unknown { reason: String },
}

/// V1/V2 calling convention kind (derived from outer lambda arity).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum V1V2Kind {
    /// 3-arg lambda: `(datum, redeemer, ctx)`. Always spending.
    Spend3Arg,
    /// 2-arg lambda: `(redeemer, ctx)`. mint / withdraw / certificate
    /// indistinguishable from bytecode.
    NonSpend2Arg,
}

// Plan + WrapForm (the renderer's directive)

/// The final wrap plan emitted by `build_plan`. The renderer's
/// `wrap_rendered` consumes this and produces the final output string.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ValidatorPlan {
    /// Validator block name. Defaults to `"decompiled"` when no
    /// blueprint metadata is available.
    pub name: String,
    /// How the body should be wrapped.
    pub wrap_form: WrapForm,
    /// Plutus script version, propagated from `PlanInput` so the
    /// renderer can re-classify based on the rendered arg count
    /// (e.g. 3-arg V1/V2 → auto-spend when the AST-level classifier
    /// returned `Plain`).
    pub script_version: Option<crate::decompile::ScriptVersion>,
    /// Whether `--purpose` was explicitly set. If false, the
    /// wrap_rendered post-processor may upgrade `PlainFn` → spend
    /// based on rendered arg count.
    pub purpose_was_explicit: bool,
    /// Non-fatal warnings to surface in the rendered output as
    /// `// Warning:` comments.
    pub diagnostics: Vec<ValidatorDiagnostic>,
}

/// How the validator body should be wrapped in the final output.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum WrapForm {
    /// Blueprint metadata wins — use the purpose-arm form
    /// (`validator NAME { spend(args) {...} mint(args) {...}
    /// else(_) { fail } }`).
    BlueprintBlock(ValidatorMeta),

    /// Synthesized purpose block: one entry per detected/declared
    /// purpose. Used for V3 multi-purpose splits or
    /// `--purpose`-forced single-purpose.
    PurposeBlock { entries: Vec<ValidatorEntry> },

    /// Flat-wrap form: `validator NAME(<args>) { <body> }` with
    /// optional `// Inferred purposes:` comment.
    Flat {
        inferred_purposes: Vec<ValidatorPurpose>,
    },

    /// Plain Plutus script — emit `pub fn <name>(<args>) { <body> }`
    /// with NO validator-block wrap and NO purpose-ambiguity
    /// diagnostics. Used when the script isn't a Cardano on-chain
    /// validator (library function, off-chain kernel, debug
    /// snapshot).
    PlainFn,
}

/// A non-fatal diagnostic to surface in the rendered output. Used
/// for ambiguity warnings (e.g. "V1/V2 non-spend purpose not
/// specified — pass `--purpose` to disambiguate").
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ValidatorDiagnostic {
    /// Severity tier — `Warning` for ambiguity / shape issues the
    /// user should be aware of, `Info` for purely informational
    /// notes (e.g. auto-detected V3 purpose, outer Apply labeled
    /// as runtime).
    pub severity: DiagnosticSeverity,
    /// Diagnostic kind — drives the universality classification in
    /// `wrap_rendered`, so rewording `message` can't flip a
    /// diagnostic between wrap-gated and universal emission.
    pub kind: DiagnosticKind,
    /// Human-readable message. Rendered as `// <severity>:
    /// <message>` in the output.
    pub message: String,
}

/// Diagnostic kind. Drives the `wrap_rendered` universality check:
/// `UnknownPlutusVersion` and `OuterApplyLabeled` are structural
/// signals about the program itself and emit regardless of whether
/// the validator-block wrap was applied; the other kinds are
/// purpose / shape diagnostics that are only actionable inside a
/// real wrap.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DiagnosticKind {
    /// V1/V2 non-spend purpose can't be recovered from bytecode.
    /// Pass `--purpose <mint|withdraw|certificate>` to disambiguate.
    V1V2NonSpendPurposeAmbiguous,
    /// V3 single-purpose name can't be recovered from bytecode.
    /// Pass `--purpose <name>` to specify.
    V3SinglePurposeAmbiguous,
    /// `Program::version` UPLC header reports an unknown
    /// `(major, minor, _)` shape. Pass `--script-version` to set
    /// the Plutus version explicitly.
    UnknownPlutusVersion,
    /// Some outer Apply nodes were labeled as pre-applied runtime
    /// args (`--applied-as` or the Auto heuristic). Informational
    /// count of that split — not a shape warning.
    OuterApplyLabeled,
    /// `--split-purposes always` was requested but the inferred
    /// version has no supported split (V1/V2 multivalidator
    /// detection is not implemented).
    SplitAlwaysIgnoredForV1V2,
    /// The V3 single purpose was AUTO-detected from a
    /// `script_info` assertion on the prepared entry-body spine
    /// (informational — explains why no `--purpose` flag was needed).
    AutoDetectedSinglePurpose,
    /// The version was inferred as V2 from the (1, 0) UPLC header that
    /// V1 shares, with no V2-only builtin evidence — a guess the user
    /// can pin with `--script-version` (affects context field naming).
    V1V2VersionAssumed,
}

/// Diagnostic severity tier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DiagnosticSeverity {
    Info,
    Warning,
}

// `build_plan` input

/// Input to `build_plan`.
#[derive(Debug)]
pub(crate) struct PlanInput<'a> {
    pub meta: Option<&'a ValidatorMeta>,
    pub options: &'a ValidatorShapeOptions,
    pub script_version: Option<ScriptVersion>,
    pub outer: &'a OuterStructure,
    pub dispatch: &'a PurposeDispatch,
    /// A V3 single purpose PROVEN by a `script_info` assertion
    /// on the prepared entry-body spine (`detect_single_purpose_v3`).
    /// `None` when undetected, multi-purpose, or not explicitly V3.
    /// Lower precedence than blueprint metadata and explicit
    /// `--purpose`; bypasses the Plain early-return like an explicit
    /// purpose does (deep helper nesting fools the structural
    /// classifier on exactly these scripts).
    pub detected_single_purpose: Option<ValidatorPurpose>,

    /// Purposes observed from the `ScriptInfo` tags the body matches
    /// (`observe_script_info_purposes`). Diagnostic input only — it
    /// reports what the bytecode discriminates on where the dominating
    /// single-purpose assertion is absent, and never selects a wrap.
    pub observed_script_info_purposes: Vec<ValidatorPurpose>,
    /// The (1, 0) UPLC header is shared by V1 and V2; `true` when the
    /// version was INFERRED as V2 without builtin evidence (no explicit
    /// `--script-version`, no V2-only builtins). Surfaces an Info line.
    pub version_inferred_ambiguous: bool,
}

/// Build a `ValidatorPlan` from analysis inputs. See
/// [`build_plan::build_plan_impl`].
pub(crate) fn build_plan(input: PlanInput<'_>) -> ValidatorPlan {
    build_plan_impl(input)
}

/// Alias for `inspect_outer`.
pub(crate) fn analyze_program(program: &Program<NamedDeBruijn>) -> OuterStructure {
    inspect_outer(program)
}
