//! The per-decompilation render context.
//!
//! [`RenderCtx::default`] is the faithful view — no script version on
//! either channel, CIP polarity, every opt-in off — which is what
//! non-pipeline callers (tests, debug bundles, the bare
//! `PseudoExpr::to_pretty`) get. Every version-gated pass and every
//! inverse-CIP recoverer is a no-op under it, so the default output is
//! the positional, CIP one.
//!
//! Read by `prepare_for_render`'s passes AND by the pretty-printer,
//! which carries it in [`PrettyConfig::render_ctx`] — the two must agree
//! on `compilable_data_access`, since the pass lowers the AST and the
//! printer renders what it produced.
//!
//! [`PrettyConfig::render_ctx`]: crate::decompile::render::PrettyConfig::render_ctx

use crate::decompile::ScriptVersion;
use crate::decompile::church_polarity::ChurchPolarity;

/// Render-time inputs shared by the `render_prep` passes and the printer.
///
/// The two version channels have DIFFERENT soundness contracts and are
/// deliberately not collapsed into one:
/// - [`version`](RenderCtx::version) is STRICT — `None` whenever V1-vs-V2
///   is unsettled — and gates every position whose schema layout differs
///   across that band (TxInfo `.fields[N]`, the version-dependent sums).
/// - [`sc_version`](RenderCtx::sc_version) is the plan version, `Some`
///   even under that ambiguity, and gates only the band-INVARIANT
///   ScriptContext top level (`[tx_info, purpose]` in both V1 and V2,
///   slot 0 `tx_info` in V3 too), which no coercion can mislabel.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct RenderCtx {
    /// Strict field-naming version; `None` under V1/V2 ambiguity.
    version: Option<ScriptVersion>,
    /// ScriptContext-level (plan) version; `Some` even under ambiguity.
    sc_version: Option<ScriptVersion>,
    /// The version is a GUESS: the `(1, 0)` UPLC header is shared by V1
    /// and V2 and nothing in the program settled it. Passes that name a
    /// schema position hold back where the two layouts disagree.
    version_guessed: bool,
    /// Opt-in church→native decode (`DecompileOptions::decode_church_to_native`).
    decode_church: bool,
    /// Opt-in compilable `builtin` surface for the un-recovered raw-`Data`
    /// access spine (`DecompileOptions::compilable_data_access`). Read on
    /// BOTH sides of the render: `lower_constr_field_sugar` rewrites the
    /// AST and the printer names the builtins to match.
    compilable_data_access: bool,
    /// Opt-in `expect P = X or fail @"msg"` rendering
    /// (`DecompileOptions::expect_or_fail`). Printer-only.
    expect_or_fail: bool,
    /// Opt-in: drop EVERY `trace` from the render
    /// (`DecompileOptions::strip_all_traces`). Semantically log-dropping.
    strip_all_traces: bool,
    /// Opt-in: drop the PlutusTx per-call-site enter/exit trace pairs
    /// (`DecompileOptions::strip_plutustx_traces`).
    strip_plutustx_traces: bool,
    /// The program's church-bool convention, detected once on the
    /// lowering seed and carried here from `PipelineOutput`. It cannot be
    /// re-detected at render time: simplify has already folded the
    /// producer signals, so a fresh detection would wrongly report `Cip`.
    church_polarity: ChurchPolarity,
}

impl RenderCtx {
    /// The two version channels; every opt-in starts off. Chain the
    /// `with_*` setters for the rest — they are named, so the four
    /// independent booleans cannot be transposed at a call site.
    pub(crate) fn new(version: Option<ScriptVersion>, sc_version: Option<ScriptVersion>) -> Self {
        Self {
            version,
            sc_version,
            ..Self::default()
        }
    }

    /// Mark the version a GUESS — the V1/V2-ambiguous `(1, 0)` header
    /// with nothing in the program to settle it.
    pub(crate) fn with_version_guessed(mut self, value: bool) -> Self {
        self.version_guessed = value;
        self
    }

    /// Turn on the church→native value decode.
    pub(crate) fn with_decode_church(mut self, value: bool) -> Self {
        self.decode_church = value;
        self
    }

    /// Turn on the compilable `builtin.*` data-access surface.
    pub(crate) fn with_compilable_data_access(mut self, value: bool) -> Self {
        self.compilable_data_access = value;
        self
    }

    /// Turn on `expect P = X or fail @"msg"` rendering.
    pub(crate) fn with_expect_or_fail(mut self, value: bool) -> Self {
        self.expect_or_fail = value;
        self
    }

    /// Turn on the log-dropping strip of every `trace`.
    pub(crate) fn with_strip_all_traces(mut self, value: bool) -> Self {
        self.strip_all_traces = value;
        self
    }

    /// Turn on the strip of PlutusTx enter/exit trace pairs.
    pub(crate) fn with_strip_plutustx_traces(mut self, value: bool) -> Self {
        self.strip_plutustx_traces = value;
        self
    }

    /// Carry the pipeline's church-bool verdict into the render.
    pub(crate) fn with_church_polarity(mut self, value: ChurchPolarity) -> Self {
        self.church_polarity = value;
        self
    }

    /// The strict field-naming version — `None` under V1/V2 ambiguity,
    /// which makes every layout-divergent relabel a no-op.
    pub(crate) fn version(&self) -> Option<ScriptVersion> {
        self.version
    }

    /// The strict version coerced to V2 when unset. Safe only where V1
    /// and V2 share the layout; V3-only sums must gate on
    /// [`version`](RenderCtx::version) being an EXPLICIT V3 instead.
    pub(crate) fn version_or_v2(&self) -> ScriptVersion {
        self.version.unwrap_or(ScriptVersion::PlutusV2)
    }

    /// The ScriptContext-level version, falling back to the strict
    /// channel — read ONLY for positions whose schema name is identical
    /// across the V1/V2 band.
    pub(crate) fn sc_version(&self) -> Option<ScriptVersion> {
        self.sc_version.or(self.version)
    }

    /// True when either channel is set — either can produce a named
    /// accessor, and the binder-rename pass keys off those accessors, so
    /// it must run whenever either fired.
    pub(crate) fn any_version_set(&self) -> bool {
        self.version.is_some() || self.sc_version.is_some()
    }

    /// Whether a pass should hold back on positions where the V1 and V2
    /// layouts disagree.
    pub(crate) fn version_is_guessed(&self) -> bool {
        self.version_guessed
    }

    /// Whether the opt-in church→native decode is enabled for this run.
    pub(crate) fn decode_church(&self) -> bool {
        self.decode_church
    }

    /// Whether the un-recovered raw-`Data` access spine renders (and
    /// lowers) as the compilable `builtin.*` surface.
    pub(crate) fn compilable_data_access(&self) -> bool {
        self.compilable_data_access
    }

    /// Whether the expect-sugar keeps its fail message as `or fail @"…"`.
    pub(crate) fn expect_or_fail(&self) -> bool {
        self.expect_or_fail
    }

    /// Whether every `trace` is dropped from the render.
    pub(crate) fn strip_all_traces(&self) -> bool {
        self.strip_all_traces
    }

    /// Whether the PlutusTx enter/exit trace pairs are dropped.
    pub(crate) fn strip_plutustx_traces(&self) -> bool {
        self.strip_plutustx_traces
    }

    /// The program's church-bool convention. `Cip` — the default — for
    /// non-pipeline callers, which is the fail-safe: the inverse-CIP
    /// recoverers are complete no-ops under it.
    pub(crate) fn church_polarity(&self) -> ChurchPolarity {
        self.church_polarity
    }
}

#[cfg(test)]
impl RenderCtx {
    /// Both version channels pinned to `version` — the shape a pass test
    /// wants when it only cares that a version is active. `None` is the
    /// version-agnostic view every version-gated pass no-ops under.
    pub(crate) fn at(version: Option<ScriptVersion>) -> Self {
        Self::new(version, version)
    }

    /// Shorthand for [`with_version_guessed(true)`](RenderCtx::with_version_guessed).
    pub(crate) fn guessed(self) -> Self {
        self.with_version_guessed(true)
    }
}
