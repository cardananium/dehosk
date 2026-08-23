//! Decompilation from UPLC to PseudoExpr.
//!
//! Declares the pass modules and holds the public
//! surface: `ScriptVersion`, `OutputLayer`,
//! `DecompileOptions`, and the `decompile` /
//! `decompile_program` entry points that drive the
//! pipeline and the render-prep dressing around it.

mod adt_disambiguation;
/// Walks the VarTable and computes each `VarId`'s canonical
/// `display_name_hint` from its `VarKind`, dedup by suffix.
mod assign_names;
pub(crate) mod basic;
mod blueprint_registry;
mod boolean_cleanup;
mod cardano_context_naming;
pub(crate) mod church_polarity;
mod constructor_data;
mod dangling_field_alias;
mod data_resolution;
/// Dead-let elimination on NamelessExpr.
mod dead_let_nameless;
mod display;
pub(crate) mod final_type_table;
mod fix_combinator;
mod helper;
/// `inline_single_use` on NamelessExpr, in `inline::nameless`.
mod inline;
/// VarKind verifier. Walks PseudoExpr shapes to check existing
/// mint-site VarKind entries without populating missing kinds.
/// Only a `debug_assert!` consumes it, hence the `cfg`.
#[cfg(any(debug_assertions, test))]
mod kind_inference;
mod late;
mod let_flatten;
mod list_traversal;
pub mod mid;
/// diagnostic walker that counts same-name-different-
/// VarId orphan references.
pub(crate) mod name_orphan_audit;
mod nameless_post_pipeline;
mod naming;
/// The option catalogue: what the decompilation options are, what each
/// one does, and which panel section it belongs in — as data, so a UI
/// renders its panel from the crate instead of keeping a copy of the
/// list. Catalogue entries and option structs are generated from one
/// source text, so the two cannot disagree.
pub mod options;
mod pair_patterns;
mod pipeline;
pub(crate) mod polarity_oracle;
mod varkind_recovery;
// Convenience re-exports so callers can use `decompile::pipeline_passes::*`
// instead of `decompile::pipeline::pipeline_passes::*`. `pipeline_stages`
// is used only from inside `pipeline/`, so it isn't re-exported.
pub(in crate::decompile) use pipeline::{pipeline_passes, pipeline_runtime};
pub(crate) mod pseudo_lineage;
mod purpose_dispatch;
mod ref_retarget;
mod rename;
pub(crate) mod render;
pub(crate) mod render_prep;
use purpose_dispatch::*;
mod expect_constr_unpack;
use expect_constr_unpack::*;
mod expr_probes;
use expr_probes::*;
mod simplify;
/// slice-chain inlining driven by `VarKind::SliceTailAlias`.
mod slice_chain_nameless;
mod type_invariants;
mod type_solver;
mod uniquify;
mod uplc_render;
/// V1/V2 validator return-type lowering: tail-position `Unit` →
/// `Bool(true)` in the validator-entry lambda body.
mod v2_validator_return;
/// Validator-block metadata for emitting `validator NAME { spend(...)
/// {...} mint(...) {...} else(_) { fail } }` syntax instead of the bare
/// `fn decompiled(...)` form.
pub mod validator_meta;
pub mod validator_shape;
#[cfg(test)]
mod value_hint;
/// Centralized `Var`/`Binder` matching helpers
/// over `Option<VarId>` ids.
mod var_match;
mod varid_dedup;
mod when_destructure;

pub(crate) use adt_disambiguation::disambiguate_constructors;
// Legacy basic-translation surface: production lowering runs through
// `mid::lower`. `basic` exposes only `convert_plutus_data`, consumed
// by `mid::lower::lower_plutus_data`, plus the two normalization
// rules it is built from — `constructor_index` and
// `convert_pallas_bigint` — which the stepping render calls directly
// to print a `uplc::PlutusData` without converting the tree.
pub(crate) use blueprint_registry::{BlueprintHintRegistry, TypeHintId};
pub(crate) use boolean_cleanup::simplify_boolean_and_identity;
#[cfg(test)]
#[allow(unused_imports)]
pub(crate) use cardano_context_naming::propagate_types_and_name_constructors;
pub(crate) use cardano_context_naming::{
    propagate_types_and_name_constructors_with_blueprint,
    resolve_cardano_field_names_with_var_kinds,
};
pub(crate) use dangling_field_alias::inline_dangling_field_aliases;
pub(crate) use data_resolution::{resolve_data_case, resolve_data_constr};
pub(crate) use fix_combinator::{
    recover_pair_fixpoint, simplify_double_rec_fn, simplify_z_combinator,
};
pub(crate) use helper::preserve::preserved_helper_ids;
pub(crate) use inline::inline_single_use_preserving;
pub(crate) use let_flatten::flatten_let_chains;
#[cfg(test)]
pub(crate) use naming::improve_variable_names;
pub(crate) use naming::semantic_improve_variable_names;
pub use polarity_oracle::OracleTxBundle;
// Re-exported for the pipeline-runtime tests, which drive each pass
// through `PipelineExecutor::emit` by name from this module. Production
// code calls them through their own modules.
#[cfg(test)]
pub(crate) use display::polish::extract_heavy_constants;
pub(crate) use pipeline::{
    run_pipeline, run_pipeline_with_artifacts, run_pipeline_with_artifacts_opts,
};
pub(crate) use pipeline_runtime::PipelineTelemetry;
pub(crate) use render_prep::RenderCtx;
pub(crate) use render_prep::prepare_for_render;
pub(crate) use v2_validator_return::lower_v2_tail_unit_to_true;
pub use validator_meta::{ValidatorMeta, ValidatorPurpose};
#[cfg(test)]
pub(crate) use varid_dedup::deduplicate_var_ids;
// Re-exported at this path for the OVERLAY test suite, which the
// published tree does not carry (`build.rs` pulls it in only when
// `.dehosk-overlay` points at one). Without the overlay nothing in-tree
// names them here — hence the `allow`, rather than a re-export that
// makes `cargo test` fail on a fresh clone.
#[cfg(test)]
#[allow(unused_imports)]
pub(crate) use render_prep::{debug_disambiguate_shadowed_lets, debug_rename_render_var_in_expr};
#[cfg(test)]
pub(crate) use simplify::simplify;
pub(crate) use simplify::{
    cancel_force_delay_vars, normalize_list_cons_literals, strip_cosmetic_delays,
};
pub(crate) use uniquify::{collapse_tail_chains, uniquify_let_names};
pub(crate) use varid_dedup::has_duplicate_binding_ids;
pub(crate) use when_destructure::{
    collapse_eta_pair_selector_when_subjects, contains_complex_when_subjects,
    contains_destructurable_when_fields, contains_eta_pair_selector_when_subjects,
    contains_unpack_tag_when_subjects, destructure_when_fields, extract_complex_when_subjects,
    lift_unpack_tag_when_subjects,
};

use crate::decompile::options::macros::{define_options, define_pass_group};
use crate::decompile::options::{Exposure, GroupId, OptionKind};
use crate::error::{DecompileError, Result};
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
#[allow(unused_imports)]
use crate::pseudo::var_id::OptionVarIdGet;
use uplc::ast::{FakeNamedDeBruijn, NamedDeBruijn, Program};

/// Plutus script version, used to determine parameter naming and field mappings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScriptVersion {
    PlutusV1,
    PlutusV2,
    PlutusV3,
}

/// Resolve the script version for two render purposes from an optional
/// explicit version plus the program's inferred version.
///
/// Returns `(plan_version, field_naming_version)`:
/// - `plan_version` — what the pipeline / validator-shape plan commits to
///   (ambiguous `(1,0)` headers default to V2); seeds
///   `options.script_version`.
/// - `field_naming_version` — gates
///   `render_prep::resolve_tx_info_field_indices`, which relabels
///   positional `tx_info.fields[N]` to schema-named fields. `None` unless
///   V1-vs-V2 is certain (explicit, or `DefinitelyV2` / `DefinitelyV3`).
///
/// The second value is EVIDENCE, not a render gate. Withholding names
/// under the ambiguous `(1, 0)` band does not make the output safe: the
/// pipeline's own Cardano naming runs on the coerced version and names
/// `tx_info.withdrawals` regardless, so gating only the render side
/// produced one output that mixed a guessed name with an abstained
/// `tx_info.fields[4]` — neither complete nor sound, and measurably
/// worse to read. Both halves now name under the plan version, and the
/// guess is disclosed once, at the top, by the `V1V2VersionAssumed`
/// diagnostic this same flag drives.
pub(crate) fn resolve_render_versions(
    program: &Program<NamedDeBruijn>,
    explicit: Option<ScriptVersion>,
) -> (Option<ScriptVersion>, Option<ScriptVersion>) {
    if let Some(v) = explicit {
        // User asserted the version — trust it for both purposes.
        return (Some(v), Some(v));
    }
    let decision = validator_shape::infer_version(program);
    let plan = decision.to_script_version();
    let field_safe = matches!(
        decision,
        validator_shape::VersionDecision::DefinitelyV2
            | validator_shape::VersionDecision::DefinitelyV3
    );
    (plan, if field_safe { plan } else { None })
}

/// Which pipeline layer to render as the decompiler's output.
///
/// The decompiler lowers UPLC → MIR → pseudo-AST → structural
/// passes → render-prep → surface text. [`Decompiled`](OutputLayer::Decompiled),
/// the default, is the full-pipeline output; every other variant
/// stops the pipeline early and renders the intermediate
/// representation with the plain pseudo pretty-printer, WITHOUT the
/// render-prep dressing (stub-ADT synthesis, validator-shape
/// wrapping, prelude downgrade, and the church→native /
/// `expect ... or fail` toggles). That output is a faithful view of
/// the intermediate AST, NOT valid surface syntax —
/// callers/UI must not treat it as compilable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OutputLayer {
    /// Echo the decoded input as UPLC text with the readable spine-flattened
    /// application layout (`[f a b c]`) and unique variable names. No
    /// decompilation runs — the parsed view of CBOR/Flat hex input.
    Uplc,
    /// Same echo as [`Uplc`](OutputLayer::Uplc) but in the `uplc` crate's
    /// canonical binary-nested application layout (`[[[f a] b] c]`).
    UplcCanonical,
    /// The pseudo-AST seed straight out of MIR lowering, before any of
    /// the structural pipeline passes run — the closest user-facing
    /// view of the "MIR layer".
    RawPseudo,
    /// The pseudo-AST after all structural pipeline passes, before the
    /// render-prep dressing (stub-ADT synthesis, validator-shape wrap,
    /// church→native rewrite).
    PostPipeline,
    /// A church-bool **polarity** diagnostic: the detected convention
    /// (Cip / InverseCip), the structural signals behind it, and a warning
    /// that the verdict is a heuristic. Runs the pipeline (so detection
    /// fires) but emits the report instead of the rendered program.
    PolarityReport,
    /// A render-prep **cost** diagnostic: what each of `prepare_for_render`'s
    /// ~140 steps took on this program, slowest first. Runs the full
    /// decompilation and then reports instead of emitting the code — the
    /// answer to "which pass is expensive on THIS script".
    PrepProfile,
    /// Full decompilation to readable pseudocode (default).
    #[default]
    Decompiled,
}

// `DecompileOptions`: the struct AND its catalogue entries out of ONE
// list. Each field must declare how it is exposed, so a new field
// cannot slip in unclassified — see `decompile::options`.
define_options! {
    /// Options for decompilation.
    ///
    /// `safe_mode` and the `*_passes` group toggles BOTH gate whether a
    /// cluster runs:
    /// * `safe_mode == true` skips the structural-recovery cluster, several
    ///   display-polish stages, and a handful of MIR-level recoveries,
    ///   regardless of the group flags.
    /// * Each `*_passes` group gates its own cluster independently — e.g.
    ///   `type_passes.all_off()` skips the type pipeline.
    ///
    /// Inside a cluster that runs, per-pass leaf `bool`s fine-tune behavior
    /// for debugging / regression bisection.
    #[derive(Debug, Clone)]
    DecompileOptions, path [] {
        // Declared FIRST because `ENTRIES` is declaration order and the
        // catalogue is the UI's only ordering authority: the
        // `PipelineSurface` group's prose says "The layer comes first
        // because it decides whether the rest applies at all", so the
        // layer selector must render above that group's toggles.
        // Order-only — `DecompileOptions` derives no serde, so no wire
        // format depends on field position.
        /// Stop early to inspect an intermediate representation (not valid surface syntax)
        /// Intermediate layers are a faithful view of the AST — NOT valid surface syntax, so don't paste one into a build. The other options here (stub-ADTs, validator shape, prelude / church rewrites) only affect the full-decompilation layer: the UPLC layers ignore them entirely, and Raw pseudo / Post-pipeline render the bare AST.
        output_layer: OutputLayer = Exposure::Ui {
            label: "Output Layer",
            group: GroupId::PipelineSurface,
            kind: OptionKind::Choice {
                choices: options::OUTPUT_LAYER_CHOICES,
                unset: None,
            },
            cli_flag: Some("--emit"),
        },

        /// Skip aggressive recovery / polish stages
        /// ON: the pipeline skips the structural-recovery cluster (Z-combinator collapse, when-subject extraction, immediate-apply resolution, ...), several display-polish stages, and a handful of MIR-level recoveries; simplification and the type pipeline still run. OFF (default) is equally correct — "safer" only means more literal and less normalized. Turn it on when the default rendering looks suspicious, or to bisect a misbehaving recovery pass.
        ///
        /// Visible differences include:
        ///   * Constructor disambiguation runs less aggressively, so the same tag can land on a different stub-variant — `Unknown_S_1_2(Data)` (default) vs `Unknown_S_1_0` (safe mode).
        ///   * Hoisted constants get plain names (`const list`) instead of disambiguated ones (`const list_2`).
        ///   * Some `when` subjects are not extracted into intermediate lets, leaving longer subject expressions inline.
        safe_mode: bool = Exposure::Ui {
            label: "Safe Mode",
            group: GroupId::PipelineSurface,
            kind: OptionKind::Toggle,
            cli_flag: Some("--safe-mode"),
        },

        /// Plutus script version (v1, v2, or v3). Enables semantic field naming.
        /// Plutus version that produced the bytecode. Drives the runtime calling convention (V1/V2 spend = datum+redeemer+ctx; non-spend = redeemer+ctx; V3 = single ctx) and Cardano-domain field naming (`tx_info`, `signatories`, ... vs `fields[0]`). Auto-detect (the default) reads the UPLC header — `(1,1,_)` = V3; `(1,0,_)` is V1 or V2, refined by scanning for V2/V3-only builtins (serialise_data, BLS, keccak_256) and falling back to V2 when none is found. Set it explicitly mainly to disambiguate V1 from V2 spend (3 args vs 2).
        ///
        /// Calling-convention example:
        ///   V1/V2 spend  -> validator decompiled(datum, redeemer, script_context) { ... }
        ///   V1/V2 mint   -> validator decompiled(redeemer, script_context) { ... }
        ///   V3 (any)     -> validator decompiled(script_context) { ... }
        ///
        /// Cardano-domain naming (`script_context.tx_info.signatories` rather than `script_context.fields[0].fields[0]`) needs a known version and survives `--no-types`, which only drops the `: Type` annotations. Naming inside `tx_info` additionally needs V1-vs-V2 to be certain: the two share the `(1,0,_)` header and their TxInfo layouts differ, so an ambiguous script keeps positional `fields[N]` until the version is set.
        script_version: Option<ScriptVersion> = Exposure::Ui {
            label: "Script Version",
            group: GroupId::ScriptIdentification,
            kind: OptionKind::Choice {
                choices: options::SCRIPT_VERSION_CHOICES,
                unset: Some("Auto-detect"),
            },
            cli_flag: Some("--script-version"),
        },

        /// Blueprint type hints extracted from plutus.json.
        /// Enables constructor and field naming from the blueprint's
        /// type definitions; purely additive — `None` changes nothing.
        blueprint_hints: Option<crate::cardano::BlueprintHints> = Exposure::Internal {
            reason: "set from the `blueprint` subcommand, not chosen by the user",
        },

        /// Validator-block metadata for the `validator NAME { ... }` surface form.
        /// Renders `validator NAME { spend(...) {...} mint(...) {...}
        /// else(_) { fail } }`; `None` falls back to the single-entry
        /// `validator decompiled { else(_) { body } }` stub.
        validator_meta: Option<ValidatorMeta> = Exposure::Internal {
            reason: "set from the `blueprint` subcommand, not chosen by the user",
        },

        /// Regression-bisection knob for late name recovery; must stay `true` in production.
        /// Late name-recovery passes dispatch on VarKind annotations
        /// unioned with the name-pattern predicate — a strict superset
        /// of name patterns alone.
        use_varkind_recovery: bool = Exposure::Internal {
            reason: "regression-bisection knob; a strict superset of the legacy behaviour that \
                     must stay `true` in production",
        },

        /// Emit `pub type Unknown_S_<n>` declarations for `Constr<tag>` (valid surface syntax)
        /// ON (the CLI default): synthesize `pub type Unknown_S_<N> { Unknown_S_<N>_<tag>(...) }` declarations for constructors that map to no known type, so the output is legal surface syntax. OFF (the web default): raw `Constr<tag>` placeholders survive — they round-trip back to UPLC more cleanly but are not valid surface syntax.
        ///
        /// Example (ON):
        ///   pub type Unknown_S_2 { Unknown_S_2_0(Data) }
        ///   when v_249 is { Unknown_S_2_0(value) -> ... }
        ///
        /// Example (OFF, web default):
        ///   when v_249 is { Constr<0>(value) -> ... }
        synthesize_stub_adts: bool = Exposure::Ui {
            label: "Synthesize Stub ADTs",
            group: GroupId::PipelineSurface,
            kind: OptionKind::Toggle,
            cli_flag: Some("--no-stub-adts"),
        },

        /// Wrap-shape choices the bytecode alone cannot settle.
        /// Populated by `--purpose`, `--split-purposes`, `--script-kind`
        /// and `--applied-as`; blueprint metadata outranks the purpose
        /// and split choices.
        validator_shape: crate::decompile::validator_shape::ValidatorShapeOptions =
            Exposure::Nested {
                members: crate::decompile::validator_shape::ValidatorShapeOptions::ENTRIES,
            },

        /// OFF: prelude ctors become raw `Constr<N>`, except purpose anchors
        /// ON (default): True/False, Some/None, Void, Ok/Error, the constructor-encoded Pair, list constructors, ordering, etc. render by name. OFF: they downgrade to raw `Constr<N>`, except the Cardano purpose anchors (Spend/Mint/Withdraw/Publish/Vote/Propose), which stay named because purpose-dispatch detection needs them. Pairs arriving as the UPLC builtin pair type render through a separate `Pair(a, b)` path this flag does not affect.
        ///
        /// Example (ON, default):
        ///   [] -> False
        ///   True
        ///   Some(payload) -> ...
        ///
        /// Example (OFF):
        ///   [] -> Constr<0>
        ///   Constr<1>
        ///   Constr<0>(payload) -> ...
        recognize_prelude_constructors: bool = Exposure::Ui {
            label: "Recognize Prelude Constructors",
            group: GroupId::PipelineSurface,
            kind: OptionKind::Toggle,
            cli_flag: Some("--no-prelude-constructors"),
        },

        /// Rewrite Church-encoded values to native types, marked `// church-X`
        /// ON: Church-encoded helper bodies surface as their native equivalents (`fn(x) { x(a, b) }` becomes `Pair(a, b)`, `fn(t, _) { t }` becomes `True`, `fn(_, f) { f }` becomes `False`), and each rewritten let-binding carries a trailing `// church-{pair|true|false}` so the reader knows the compiled UPLC still uses Church encoding. OFF (default): the raw Lambda form, faithful to the bytecode.
        ///
        /// Each shape is gated on a strict VarId-identity check that the inner Var(s) are the Lambda's own params. The rewrite is value-level, so `.fst`/`.snd` call sites keep working — the Pair builtin uses the same accessors.
        ///
        /// Example (ON):
        ///   fn pair_pack(a, b) {
        ///     Pair(a, b)
        ///   }  // church-pair
        ///
        /// Example (OFF, default):
        ///   fn pair_pack(a, b) {
        ///     fn(x) { x(a, b) }
        ///   }
        decode_church_to_native: bool = Exposure::Ui {
            label: "Decode Church Encodings",
            group: GroupId::PipelineSurface,
            kind: OptionKind::Toggle,
            cli_flag: Some("--decode-church-to-native"),
        },

        /// Preserve the fail message the default `expect` sugar drops
        /// ON: a single-branch `when X is { P -> body  _ -> fail @"msg" }` renders as `expect P = X or fail @"msg"`. NOT valid surface syntax — real `expect` has no `or fail` clause, so this is a read-not-compile annotation. OFF (default): the plain `expect P = X` sugar, with the custom fail message lost.
        ///
        /// Example (ON):
        ///   expect Spending(output_reference, datum) =
        ///     script_context.script_info or fail @"PT1"
        ///
        /// Example (OFF, default):
        ///   expect Spending(output_reference, datum) = script_context.script_info
        expect_or_fail: bool = Exposure::Ui {
            label: "Expect-or-fail Annotations",
            group: GroupId::PipelineSurface,
            kind: OptionKind::Toggle,
            cli_flag: Some("--expect-or-fail"),
        },

        /// Lower the raw Data-access spine to valid `builtin` surface
        /// ON: `X.tag`/`X.fields` become `builtin.un_constr_data(X).1st`/`.2nd`, `Constr.unpack(X)` becomes `builtin.un_constr_data(X)`, `List.head`/`List.tail`/`List.is_empty` become `builtin.head_list`/`tail_list`/`null_list`, `coll[N]` becomes `builtin.head_list(builtin.tail_list^N(coll))`, `coll[N..]` becomes nested `builtin.tail_list`, and `.head` becomes `builtin.head_list(...)`. Render-only — the recovered semantics are unchanged. OFF (default): the readable pseudo forms, which are NOT valid surface syntax.
        ///
        /// Example (ON):
        ///   let unpack = builtin.un_constr_data(redeemer).2nd
        ///
        /// Example (OFF, default):
        ///   let unpack = redeemer.fields
        compilable_data_access: bool = Exposure::Ui {
            label: "Compilable Data Access",
            group: GroupId::PipelineSurface,
            kind: OptionKind::Toggle,
            cli_flag: Some("--compilable-data-access"),
        },

        /// Drop every `trace` from the rendered output
        /// ON: all `trace @"msg"` expressions are removed, keeping only the traced value. Semantically LOG-DROPPING: the compiled script still emits those traces, so the render no longer says everything the program does. Useful when a PlutusTx-compiled script is more trace than logic. OFF (default): traces are preserved verbatim.
        ///
        /// This was an undocumented `DEHOSK_STRIP_TRACES` environment variable, which meant a process-wide switch nobody could see from the request, and a value one test could leave behind for another. It is an option because it changes the output.
        ///
        /// Example (ON):
        ///   let ok = check(x)
        ///
        /// Example (OFF, default):
        ///   let ok = trace @"checking": check(x)
        strip_all_traces: bool = Exposure::Ui {
            label: "Strip All Traces",
            group: GroupId::PipelineSurface,
            kind: OptionKind::Toggle,
            cli_flag: Some("--strip-all-traces"),
        },

        /// Drop the PlutusTx per-call-site enter/exit trace pairs
        /// ON: strips the `trace("entering X", fn(_) { trace("exiting X", body, _) }, _)` instrumentation PlutusTx wraps around every call. Narrower than `strip_all_traces`: only that mechanical pair shape goes, user-facing `trace @"msg"` stays. OFF (default): the pairs are kept — they name the original Haskell functions, which usually tells the reader more than the noise costs.
        strip_plutustx_traces: bool = Exposure::Ui {
            label: "Strip PlutusTx Call Traces",
            group: GroupId::PipelineSurface,
            kind: OptionKind::Toggle,
            cli_flag: Some("--strip-plutustx-traces"),
        },

        /// Name 3-nullary-variant `when` shapes as the prelude `Ordering`
        /// Arms become `Less`/`Equal`/`Greater`. The producer-side comparator relabel additionally requires the comparator's branch CONDITIONS to match the canonical semantics (`==` gives `Equal`, `<` gives `Less`, else `Greater`); a scrambled-tag comparator keeps its stub names even with the flag ON.
        ///
        /// Default off — the signature `{(0,0),(1,0),(2,0)}` matches ANY 3-variant nullary enum (governance parameter kinds, state tags, ...), and prelude comparison names on a non-comparison enum read as semantics the program does not have.
        ordering_names: bool = Exposure::Ui {
            label: "Ordering Names",
            group: GroupId::PipelineSurface,
            kind: OptionKind::Toggle,
            cli_flag: Some("--ordering-names"),
        },

        /// Inlining + fixed-point simplify
        simplify_passes: SimplifyPasses = Exposure::Nested {
            members: SimplifyPasses::ENTRIES,
        },

        /// Recover idiomatic patterns
        structural_recovery_passes: StructuralRecoveryPasses = Exposure::Nested {
            members: StructuralRecoveryPasses::ENTRIES,
        },

        /// Names, flattening, hoisting
        readability_passes: ReadabilityPasses = Exposure::Nested {
            members: ReadabilityPasses::ENTRIES,
        },

        /// Cosmetic rewrites
        display_polish_passes: DisplayPolishPasses = Exposure::Nested {
            members: DisplayPolishPasses::ENTRIES,
        },

        /// HM solver + propagation
        type_passes: TypePasses = Exposure::Nested {
            members: TypePasses::ENTRIES,
        },

        /// Runtime data arguments applied by the `--emit polarity-report` oracle.
        /// In calling-convention order: `[datum, redeemer, script_context]`
        /// for a spend validator, `[redeemer, script_context]` /
        /// `[script_context]` otherwise. Empty (the default) leaves the
        /// oracle with only its closed church-lambda pass, so the data-tag
        /// convention stays unresolved. Ignored outside the polarity
        /// report.
        oracle_data_args: Vec<uplc::PlutusData> = Exposure::Internal {
            reason: "polarity-report oracle input, not a render option",
        },

        /// A full transaction plus its resolved inputs.
        /// When set, the `--emit polarity-report` data-tag oracle runs the
        /// transaction under phase-2 rules — the ledger rebuilds each
        /// ScriptContext, so real transactions work without hand-assembled
        /// args — instead of applying `oracle_data_args` alone.
        oracle_tx: Option<polarity_oracle::OracleTxBundle> = Exposure::Internal {
            reason: "polarity-report oracle input, not a render option",
        },

        /// DIAGNOSTIC opt-in: record which lineage route carried each mid's ownership.
        ///
        /// Records, for every mid, which of the six
        /// [`crate::decompile::pseudo_lineage::Route`]s carried its ownership from
        /// snapshot to snapshot, and hands the recorder out as
        /// `PipelineOutput::lineage_routes`.
        ///
        /// Setting it CANNOT change the emitted lineage map or the heirless set: the
        /// recorder is written to and never read by the projection.
        ///
        /// OUTPUT-inert, not COST-inert. `matches` is `Vec<(u32, u32, Route)>` rather
        /// than `Vec<(u32, u32)>`, and a `Route` is stamped on every match WHETHER OR
        /// NOT the recorder is on, plus one `Option` test per match — 4 bytes per
        /// match to padding, no extra allocation, on a path that runs once per
        /// decompile. One match path that always produces the tag beats two that can
        /// diverge: a recorder-free copy of this code is how a diagnostic stops
        /// describing the thing it diagnoses.
        record_lineage_routes: bool = Exposure::Internal {
            reason: "diagnostics only; must stay off on the served path",
        },
    }
}

// The five pass groups. Each struct AND its catalogue entries come out
// of ONE list, so a leaf that is not in the catalogue does not exist.

define_pass_group! {
    /// Initial + fixed-point simplification and inlining.
    ///
    /// All leaves default to `true`; `SimplifyPasses::all_off()` skips
    /// the simplify cluster entirely.
    #[derive(Debug, Clone, Copy)]
    SimplifyPasses in GroupId::Simplify, path ["simplify_passes"] {
        /// Pre-readability simplify loop
        /// Beta-reduces, folds known builtins and propagates constants to a fixed point, before the readability passes run. Produces the `ConsistentRefIds` pipeline property; disabling it REQUIRES also disabling `inline_single_use`, which consumes it.
        simplify_fp_initial => "Initial simplify fixpoint",
        /// Re-run simplify after naming/flatten
        /// Readability rewrites (naming, let-flatten) unlock further simplification: a `let foo = bar in foo` produced by naming inlines here. Runs only when `inline_post_readability` is on and changed the tree.
        simplify_fp_post_readability => "Post-readability simplify",
        /// Drop bindings used exactly once
        /// Inline `let x = e in body` wherever `x` is used exactly once. Consumes the `ConsistentRefIds` property, so it cannot be enabled while `simplify_fp_initial` is off.
        inline_single_use => "Inline single-use lets",
        /// Iterate inline + simplify until stable
        /// Loops inlining + simplification to a fixed point or the iteration cap. Inert unless `simplify_fp_initial` is on.
        inline_fp => "Inline fixed-point",
        /// Inline pass after readability stage
        /// Picks up trivial let bindings exposed by naming/flatten/hoist that the earlier inline rounds missed.
        inline_post_readability => "Late inline",
        /// Drop unused let bindings
        /// Remove `let x = e in body` where `e` is pure and `x` is never used in `body`. Most well-simplified scripts have no dead bindings left, so it usually changes nothing.
        dead_let_elim => "Dead let elimination",
        /// Fold list/tail patterns
        /// Collapse a chain of single-use `List.tail` lets into nested calls, which the printer renders as one slice (`xs[3..]`). Fires only on tail chains that survive simplify.
        collapse_tail_chains => "Collapse tail chains",
    }
}

define_pass_group! {
    /// Structural pattern recovery (Z-combinator, when-subject
    /// extraction, immediate-apply collapse, etc.).
    #[derive(Debug, Clone, Copy)]
    StructuralRecoveryPasses in GroupId::StructuralRecovery, path ["structural_recovery_passes"] {
        /// Intentional no-op stub (compatibility seam)
        /// Does nothing: the `let bound_tag = subject.tag in if bound_tag == ...` dispatch normalization it hooks now happens in earlier MIR passes, so turning this leaf off cannot change the output.
        recover_let_bound_tag_dispatch => "Let-bound tag dispatch",
        /// Inner rec fn becomes a plain fn
        /// Demote a `rec fn` nested directly inside another `rec fn` to a plain `fn` when its body never references its own name — the only shape it fires on.
        simplify_double_rec_fn => "Double-rec fn simplify",
        /// Recover U-comb pair as two named rec fns
        /// The U-combinator church-pair fixpoint — a 2-param self-applying fn whose tail builds a pair of injector continuations over an inner knot — becomes two named mutually-recursive functions (`fix_combinator::pair_fix`), with the pair-first-projection call sites rewritten to match. Fail-closed: inert on anything but that exact template.
        recover_pair_fixpoint => "Church-pair fixpoint → named fns",
        /// Recover named recursion
        /// The Z-combinator UPLC uses to encode recursion (`(lambda f. (lambda x. f (lambda v. x x v)) (lambda x. f (lambda v. x x v)))`) becomes a named `rec fn`. Fires only on inputs that still contain a Z-combinator after simplify.
        simplify_z_combinator => "Z-combinator → fn rec",
        /// Pull complex subjects into a let
        /// Hoist a `when ... is { ... }` subject that is a complex expression rather than a simple variable into a `let`, so the arms read cleanly. Three sub-passes, each gated by a contains-check.
        extract_complex_when_subjects => "Extract when subjects",
        /// (fn x -> ...)(arg) becomes let x = arg
        /// `(lambda x. body) arg` becomes `let x = arg in body`. Most well-simplified inputs have already reduced these, so it often changes nothing.
        resolve_immediate_applications => "Resolve immediate apps",
        /// Data.case becomes a when expression
        /// `Data.case(subject, on_constr, on_map, on_list, on_int, on_bytes)` chains become `when subject is { ... }`. Also gates `Data.Constr` lowering, expect-unpack tag recovery and constructor disambiguation, so it changes output with no `Data.case` present.
        resolve_data_case => "Resolve Data.case",
    }
}

define_pass_group! {
    /// Readability passes (variable naming, let-chain flattening,
    /// helper hoisting, constant extraction).
    #[derive(Debug, Clone, Copy)]
    ReadabilityPasses in GroupId::Readability, path ["readability_passes"] {
        /// Synthesize meaningful names
        /// Rename generic binders from what they do: a helper that walks a list becomes `any` / `all` / `count` / `find`, one that scans a map becomes `lookup`, and lambda params take hints from the calls they feed. OFF: binders keep their `v_<NN>` names.
        improve_variable_names => "Improve variable names",
        /// Block-style let layout
        /// Collapse nested `let a = ... in let b = ... in let c = ... in body` into a flat block of `let a = ...; let b = ...; let c = ...; body`. OFF: deeply nested input renders as deeply nested let-in chains.
        flatten_let_chains => "Flatten let chains",
        /// Rename binders to unique names
        /// Alpha-rename every binder to a program-unique name — a let from its value (`unpack`, `head`), a param from its position (`x`, `y`, `z`), a clash with `_2`. Validator-entry names survive.
        rename_variables => "Rename via VarKind",
        /// Lambdas become top-level fns
        /// Lift `let`-bound `fn` / `rec fn` values to top-level `fn <name>(...) { ... }`; a captured enclosing binding becomes an extra parameter.
        hoist_local_helpers => "Hoist local helpers",
        /// Lift large literals into bindings
        /// Pull a static literal operand of a binary operation into a `bytes_const_N` / `data_const_N` binding — a module-level `const` when it lands at the top. Only above six AST nodes, or a 20-byte bytestring.
        extract_heavy_constants => "Extract heavy constants",
    }
}

define_pass_group! {
    /// Late display polish (cosmetic delays/forces, list-cons
    /// literal normalization, eta-pair-selector collapse, etc.).
    #[derive(Debug, Clone, Copy)]
    DisplayPolishPasses in GroupId::DisplayPolish, path ["display_polish_passes"] {
        /// Remove no-op delay() wrappers
        /// Drop the `delay(...)` wrapper around a plain value — an integer, a builtin call, a constructor. A wrapper around a `fn`, `rec fn`, `let`, `when` or `if` body is left in place.
        strip_cosmetic_delays => "Strip cosmetic delays",
        /// force(delay(x)) becomes x
        /// Where `let x = delay(body)` and every use of `x` is `force(x)`, rewrite to `let x = body` and each use to `x` — cancelling both without copying `body`.
        cancel_force_delay_vars => "Cancel force/delay vars",
        /// cons chains become [1, 2, 3]
        /// Fold `cons(a, cons(b, []))` chains into `[a, b]`; a cons onto a non-literal tail becomes the spread `[a, ..xs]`.
        normalize_list_cons_literals => "Normalize list cons",
        /// Late visual cleanup
        /// Small structural rewrites run to a fixpoint: int-operator helpers back to operators, identical `let`s merged, pair binders renamed, CPS option adapters inlined.
        normalize_display_rewrites => "Display rewrites",
        /// Selector bools become if/else
        /// Some scripts return a Scott selector for a `Bool` — `fn(x, _) { x }` is `True`, `fn(_, y) { y }` is `False` — then over-apply it. Rewrite the returns to `True` / `False` and those call sites to `if`/`else`.
        eliminate_cps_selectors => "Eliminate CPS selectors",
        /// Boolean identity cleanup
        /// Boolean residue becomes booleans: `choose_fst` returned as a value becomes `True`, a bare `Constr<0>`/`Constr<1>` in a `Bool` branch becomes `True`/`False`, `if c { True } else { False }` becomes `c`.
        simplify_boolean_and_identity => "Simplify booleans",
        /// Unwrap eta'd pair subjects
        /// A `when` whose subject is the eta-expanded pair `fn(sel, y) { sel(first, y) }` and whose single unguarded arm is `Pair(a, b)` collapses to that arm's body, with `a` bound to `first`.
        collapse_eta_pair_selectors => "Eta pair selectors",
        /// Recover Scott-encoded constructors
        /// A lambda of two or more params whose body uses exactly one of them is a Scott-encoded constructor: `fn(c0, c1) { c1(x, y) }` becomes `Constr<1>(x, y)`. Runs after readability, so the recovery still gets named.
        resolve_scott_constructor_lambdas_late => "Late Scott constructors",
        /// Data.case recovery, late stage
        /// Same idea as Structural recovery's "Resolve Data.case" but at the late stage, catching `case_data` shapes exposed by readability rewrites.
        resolve_data_case_late => "Late Data.case",
    }
}

define_pass_group! {
    /// Type pipeline (HM constraint solving, propagation, Cardano
    /// field naming).
    #[derive(Debug, Clone, Copy)]
    TypePasses in GroupId::TypeInference, path ["type_passes"] {
        /// Run HM constraint solver
        /// Gather type constraints from builtin signatures and run the Hindley-Milner solver. Produces the `TypeConstraintsSolved` property — disabling REQUIRES disabling both downstream passes ("Propagate types" and "Cardano field names").
        solve_type_constraints => "Solve constraints",
        /// Annotate vars with solved types
        /// Walk the AST and annotate every var/let binder with the type the solver inferred. Required for Cardano field-name resolution. Cannot be enabled without "Solve constraints".
        propagate_types => "Propagate types",
        /// Map ScriptContext fields to names
        /// Recognize Cardano context types (`script_context`, `tx_info`, `tx_out`, ...) and rewrite `fields[N]` accesses to real field names (`tx_info`, `signatories`, `outputs`, ...). Cannot be enabled without "Propagate types".
        resolve_cardano_field_names => "Cardano field names",
    }
}

impl Default for DecompileOptions {
    fn default() -> Self {
        Self {
            safe_mode: false,
            script_version: None,
            blueprint_hints: None,
            validator_meta: None,
            use_varkind_recovery: true,
            synthesize_stub_adts: true,
            validator_shape: Default::default(),
            recognize_prelude_constructors: true,
            decode_church_to_native: false,
            expect_or_fail: false,
            compilable_data_access: false,
            strip_all_traces: false,
            strip_plutustx_traces: false,
            ordering_names: false,
            output_layer: OutputLayer::Decompiled,
            simplify_passes: SimplifyPasses::all_on(),
            structural_recovery_passes: StructuralRecoveryPasses::all_on(),
            readability_passes: ReadabilityPasses::all_on(),
            display_polish_passes: DisplayPolishPasses::all_on(),
            type_passes: TypePasses::all_on(),
            oracle_data_args: Vec::new(),
            oracle_tx: None,
            record_lineage_routes: false,
        }
    }
}

impl DecompileOptions {
    /// Check that the leaf-pass toggles don't violate any
    /// pipeline-internal dependency invariant. The dependencies run
    /// between leaves WITHIN a pass-group, never between groups — so
    /// `all_off()` on a whole group is always safe, while toggling one
    /// leaf can break e.g. `inline_single_use`, which needs the
    /// `consistent_ref_ids` that `simplify_fp_initial` produces.
    ///
    /// `decompile_program` calls this at its top, so callers see a
    /// `DecompileError::InvalidOptions` rather than a panic from the
    /// pipeline contract checker.
    pub(crate) fn validate(&self) -> crate::error::Result<()> {
        // Each rule: when the FIRST leaf is off, the DEPENDENT leaf must be off
        // too, because the dependent reads a property only the first produces.
        let s = &self.simplify_passes;
        let t = &self.type_passes;
        if !s.simplify_fp_initial && s.inline_single_use {
            return Err(crate::error::DecompileError::invalid_options(
                "`simplify_passes.simplify_fp_initial=false` requires \
                 `simplify_passes.inline_single_use=false` — \
                 the simplify-fp pass produces the `consistent_ref_ids` \
                 property that inline_single_use requires.",
            ));
        }
        if !t.solve_type_constraints && t.propagate_types {
            return Err(crate::error::DecompileError::invalid_options(
                "`type_passes.solve_type_constraints=false` requires \
                 `type_passes.propagate_types=false` — \
                 solve produces the `type_constraints_solved` property \
                 that propagate_types requires.",
            ));
        }
        if !t.propagate_types && t.resolve_cardano_field_names {
            return Err(crate::error::DecompileError::invalid_options(
                "`type_passes.propagate_types=false` requires \
                 `type_passes.resolve_cardano_field_names=false` — \
                 propagate produces the `types_propagated` property \
                 that resolve_cardano_field_names requires.",
            ));
        }
        Ok(())
    }

    /// Raw decompilation — only correctness-critical passes run.
    pub fn raw() -> Self {
        Self {
            safe_mode: true,
            script_version: None,
            blueprint_hints: None,
            validator_meta: None,
            use_varkind_recovery: true,
            // Raw mode preserves the raw `Constr<tag>` placeholders.
            synthesize_stub_adts: false,
            validator_shape: Default::default(),
            // Raw mode also disables prelude-constructor naming
            // (True/False/None/Some/Void) — show the raw shape.
            recognize_prelude_constructors: false,
            decode_church_to_native: false,
            expect_or_fail: false,
            // Raw mode keeps the readable pseudo Data-access spine.
            compilable_data_access: false,
            // Raw mode is the faithful view: every trace the script emits
            // stays in the render.
            strip_all_traces: false,
            strip_plutustx_traces: false,
            ordering_names: false,
            // `raw()` is about WHICH passes run, not WHERE the pipeline
            // stops — layer selection stays orthogonal.
            output_layer: OutputLayer::Decompiled,
            simplify_passes: SimplifyPasses::all_off(),
            structural_recovery_passes: StructuralRecoveryPasses::all_off(),
            readability_passes: ReadabilityPasses::all_off(),
            display_polish_passes: DisplayPolishPasses::all_off(),
            type_passes: TypePasses::all_off(),
            oracle_data_args: Vec::new(),
            oracle_tx: None,
            record_lineage_routes: false,
        }
    }
}

/// Decompile a UPLC hex string (CBOR-wrapped Flat or raw
/// Flat) to readable pseudocode.
pub fn decompile(hex_code: &str, options: DecompileOptions) -> Result<String> {
    let program = decode_hex_to_program(hex_code)?;
    decompile_program(&program, options)
}

/// If input starts with a CBOR `bytes` major type (0b010), return:
/// `(header_bytes, declared_payload_len)`.
fn cbor_bytes_header_info(bytes: &[u8]) -> Option<(usize, usize)> {
    let first = *bytes.first()?;
    let major = first >> 5;
    if major != 2 {
        return None;
    }

    let addl = first & 0x1f;
    match addl {
        0..=23 => Some((1, addl as usize)),
        24 => {
            if bytes.len() < 2 {
                None
            } else {
                Some((2, bytes[1] as usize))
            }
        }
        25 => {
            if bytes.len() < 3 {
                None
            } else {
                Some((3, u16::from_be_bytes([bytes[1], bytes[2]]) as usize))
            }
        }
        26 => {
            if bytes.len() < 5 {
                None
            } else {
                Some((
                    5,
                    u32::from_be_bytes([bytes[1], bytes[2], bytes[3], bytes[4]]) as usize,
                ))
            }
        }
        27 => {
            if bytes.len() < 9 {
                None
            } else {
                let len64 = u64::from_be_bytes([
                    bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7], bytes[8],
                ]);
                usize::try_from(len64).ok().map(|n| (9, n))
            }
        }
        _ => None,
    }
}

fn decode_failure_diagnostic(bytes: &[u8]) -> String {
    const BASE_MSG: &str = "Failed to decode as exact CBOR-wrapped Flat or exact Flat";

    if let Some((header_len, payload_len)) = cbor_bytes_header_info(bytes) {
        let expected_total = header_len.saturating_add(payload_len);
        if bytes.len() < expected_total {
            let missing = expected_total - bytes.len();
            return format!(
                "{}; CBOR bytes header declares {} payload bytes ({} total), but input has {} bytes (missing {})",
                BASE_MSG,
                payload_len,
                expected_total,
                bytes.len(),
                missing
            );
        }
        if bytes.len() > expected_total {
            let extra = bytes.len() - expected_total;
            return format!(
                "{}; CBOR bytes header declares {} payload bytes ({} total), but input has {} bytes (extra {})",
                BASE_MSG,
                payload_len,
                expected_total,
                bytes.len(),
                extra
            );
        }
    }

    BASE_MSG.to_string()
}

pub(crate) fn decode_hex_to_program(hex_code: &str) -> Result<Program<NamedDeBruijn>> {
    let bytes = hex::decode(hex_code)?;

    // Decode exactly as either CBOR-wrapped Flat or raw Flat; round-trip
    // byte equality is required, to reject ambiguous prefix decodes.
    let mut cbor_buffer = Vec::new();
    let cbor_program: Option<Program<FakeNamedDeBruijn>> =
        Program::from_cbor(&bytes, &mut cbor_buffer)
            .ok()
            .and_then(|p| match p.to_cbor() {
                Ok(encoded) if encoded == bytes => Some(p),
                _ => None,
            });

    let flat_program: Option<Program<FakeNamedDeBruijn>> = Program::from_flat(&bytes)
        .ok()
        .and_then(|p| match p.to_flat() {
            Ok(encoded) if encoded == bytes => Some(p),
            _ => None,
        });

    if cbor_program.is_none() && flat_program.is_none() {
        return Err(DecompileError::decode(decode_failure_diagnostic(&bytes)));
    }

    let program = select_exact_program(cbor_program, flat_program)?;

    Ok(program.into())
}

pub(crate) fn select_exact_program(
    cbor_program: Option<Program<FakeNamedDeBruijn>>,
    flat_program: Option<Program<FakeNamedDeBruijn>>,
) -> Result<Program<FakeNamedDeBruijn>> {
    match (cbor_program, flat_program) {
        (Some(cbor), Some(flat)) => {
            let cbor_flat = cbor
                .to_flat()
                .map_err(|e| DecompileError::decode(format!("CBOR round-trip failed: {:?}", e)))?;
            let flat_flat = flat
                .to_flat()
                .map_err(|e| DecompileError::decode(format!("Flat round-trip failed: {:?}", e)))?;

            if cbor_flat == flat_flat {
                Ok(cbor)
            } else {
                Err(DecompileError::decode(
                    "Ambiguous UPLC encoding: input decodes as both CBOR and Flat with different programs".to_string(),
                ))
            }
        }
        (Some(cbor), None) => Ok(cbor),
        (None, Some(flat)) => Ok(flat),
        (None, None) => Err(DecompileError::decode(
            "Failed to decode as exact CBOR-wrapped Flat or exact Flat".to_string(),
        )),
    }
}

/// Infer a [`ScriptVersion`] from a UPLC program's binary version
/// triple:
/// `(1, 0, _)` → Plutus V1 / V2 (one UPLC version for both; **not
///   distinguishable** from the bytecode alone — defaults to V2, the
///   more common modern Plutus baseline).
/// `(1, 1, _)` → Plutus V3 (new builtins — BLS, ed25519 verify
///   variants — plus the V3 ScriptContext layout).
/// Anything else → `None` (unknown — stay version-agnostic).
///
/// The pipeline itself goes through `validator_shape::infer_version`,
/// which also weighs builtin evidence.
pub(crate) fn infer_script_version_from_program<T>(program: &Program<T>) -> Option<ScriptVersion> {
    match (program.version.0, program.version.1) {
        (1, 0) => Some(ScriptVersion::PlutusV2),
        (1, 1) => Some(ScriptVersion::PlutusV3),
        _ => None,
    }
}

/// Inputs the post-pipeline stub-ADT dressing reads off the options.
pub(crate) struct StubAdtRenderContext {
    pub(crate) synthesize_stub_adts: bool,
    pub(crate) decode_church: bool,
    pub(crate) compilable_data_access: bool,
    pub(crate) strip_all_traces: bool,
    pub(crate) strip_plutustx_traces: bool,
    pub(crate) render_field_version: Option<ScriptVersion>,
    pub(crate) plan_version: Option<ScriptVersion>,
    /// The version is a GUESS — the `(1, 0)` header is shared by V1 and
    /// V2 and nothing in the program settled it.
    pub(crate) version_guessed: bool,
}

impl StubAdtRenderContext {
    /// The render-prep context for the analysis preps below. Both version
    /// channels carry the same stance as the final render, so a prepared
    /// tree measured here cannot be named differently from the rendered one.
    fn render_ctx(&self) -> RenderCtx {
        RenderCtx::new(self.render_field_version, self.plan_version)
            .with_version_guessed(self.version_guessed)
            .with_decode_church(self.decode_church)
            .with_compilable_data_access(self.compilable_data_access)
            .with_strip_all_traces(self.strip_all_traces)
            .with_strip_plutustx_traces(self.strip_plutustx_traces)
    }
}

/// Dress a pipeline AST for rendering: synthesize `pub type Unknown_S_*`
/// declarations for the unresolved `Constr<N>` shapes, give the Cardano
/// ones their canonical names, merge the isomorphic ones and drop the
/// unreferenced ones.
///
/// Shared so the one-shot [`decompile_program`] and any caller that
/// assembles the render from [`decompile_program_to_ast`] cannot drift
/// apart — the parity test in `tests::mir_pipeline` pins that.
pub(crate) fn dress_stub_adts(
    expr: PseudoExpr,
    blueprint_registry: std::rc::Rc<BlueprintHintRegistry>,
    ctx: &StubAdtRenderContext,
) -> (PseudoExpr, std::rc::Rc<BlueprintHintRegistry>, String) {
    let mut expr = expr;
    if ctx.synthesize_stub_adts {
        expr = render_prep::relabel_stub_producer_leaves::relabel_stub_producer_leaves(expr);
    }
    let groups = if ctx.synthesize_stub_adts {
        render_prep::stub_adt::collect_unresolved_constr_shapes(&expr)
    } else {
        Default::default()
    };
    if groups.is_empty() {
        // Fast path: no unresolved constructors → no stub-ADT work.
        // (Also the path when `synthesize_stub_adts == false`.)
        (expr, blueprint_registry, String::new())
    } else {
        let ordinals = render_prep::stub_adt::assign_class_ordinals(&groups);
        let mut registry: BlueprintHintRegistry = (*blueprint_registry).clone();
        let mut names = render_prep::stub_adt::register_stub_adts_in_registry(
            &groups,
            &ordinals,
            &mut registry,
        );
        // Override `Unknown_S_N` synthetic names with canonical
        // Cardano type names (`TxInfo`, `ScriptContext`, ...) when
        // the scrutinee binder is a recognized Cardano context
        // binder.
        let cardano_roots = render_prep::stub_adt::override_cardano_stub_adt_names(
            &expr,
            &mut names,
            &mut registry,
        );
        let mut rewritten = render_prep::stub_adt::rewrite_unresolved_constrs(expr, &names);
        // List-element provenance needs the `rec fn` iteration shapes
        // that only exist after prepare's y-comb unfolds, so re-run
        // the schema descent on a PREPARED, pre-merge view of the
        // tree: a class named here (TxOut/Address) is then excluded
        // from soft-merging with same-shape data pairs. Separate from
        // the DCE prepare below, whose referenced-hint set must come
        // from the POST-merge tree the render preps.
        // Payload arities per pre-merge stub class, measured on the
        // prepared view below and consumed by the merge further down.
        let observed_arities;
        let cardano_sum_scrutinees;
        {
            // `render_ctx()` keeps this analysis view identical to the final
            // render's (sc = plan version, same opt-in transforms) so
            // provenance keys off the same prepared tree.
            let provenance_ast = render_prep::prepare_for_render(&rewritten, &ctx.render_ctx());
            observed_arities = render_prep::stub_adt::collect_stub_pattern_arities(&provenance_ast);
            cardano_sum_scrutinees =
                render_prep::cardano_sum_scrutinees(&provenance_ast, &ctx.render_ctx());
            let typed_records = render_prep::stub_adt::override_list_element_stub_adts(
                &rewritten,
                &provenance_ast,
                &mut names,
                &mut registry,
                &cardano_roots,
            );
            // Give the typed record destructures their schema field
            // names (TxOut: address/value/datum_hash; Address:
            // payment_credential/stake_credential; ...). Scoped to the
            // types `rename_tx_info_binders` does not already cover.
            rewritten = render_prep::stub_adt::rename_typed_record_field_binders(
                rewritten,
                &names,
                &typed_records,
            );
        }
        // Merge structurally-identical Unknown_S_* stub ADTs into one
        // canonical decl: each scrutinee binder gets its own class, so
        // V1/V2 scripts produce dozens of
        // isomorphic-but-distinctly-named stub types.
        let (rewritten, _merged) = render_prep::stub_adt::merge_isomorphic_stub_adts(
            &mut names,
            rewritten,
            &observed_arities,
            &cardano_sum_scrutinees,
        );
        // DCE: drop synthetic `pub type Unknown_S_*` decls whose TypeHintId
        // never appears in the rendered AST. The pretty-printer re-runs
        // `prepare_for_render` at render time with `DECODE_CHURCH` active,
        // replacing church shapes with native List/Pair/Bool, so mirror that
        // here to get the truly-referenced hint set. RAII-guard the toggle so
        // a `prepare_for_render` panic can't leak it onto a reused thread;
        // `expect_or_fail` is irrelevant at this AST level and passes through
        // unchanged.
        let (rendered_ast_for_dce, handler_views) = {
            // `render_ctx()` mirrors the final render's church decode, its
            // compilable-data-access mode (so this prepare runs
            // `lower_constr_field_sugar` exactly as the real render will, and
            // the referenced-hint set can't diverge from the rendered AST)
            // and both version channels.
            let render_ctx = ctx.render_ctx();
            let flat = render_prep::prepare_for_render(&rewritten, &render_ctx);
            // A scattered multi-purpose body is rendered MORE THAN ONCE:
            // once flat, and once per purpose after `specialize_to_purpose`
            // (see `build_purpose_handler_bodies`). Each of those goes
            // through its own `prepare_for_render`, and dropping arms
            // changes what the binder materialization can do — an arm the
            // flat tree leaves nullary comes out destructured. The stub
            // declarations are emitted ONCE for all of them, so measure
            // every tree that will be rendered; reconciling against the
            // flat one alone declared `Unknown_E_0_1` nullary while a
            // handler matched `Unknown_E_0_1(field_0, field_1)`.
            let purposes = scattered_purposes(&flat);
            let handler_views: Vec<PseudoExpr> = if purposes.len() < 2 {
                Vec::new()
            } else {
                purposes
                    .into_iter()
                    .map(|p| {
                        render_prep::prepare_for_render(
                            &specialize_to_purpose(flat.clone(), p),
                            &render_ctx,
                        )
                    })
                    .collect()
            };
            (flat, handler_views)
        };
        let referenced =
            render_prep::stub_adt::collect_referenced_type_hints(&rendered_ast_for_dce);
        render_prep::stub_adt::prune_unused_stub_adts(&mut names, &referenced);
        // The DCE `prepare_for_render` above ran the overflow expansion +
        // `unify_constructor_pattern_arity`, so `rendered_ast_for_dce`
        // carries each stub constructor at its final uniform arity. Bump
        // the frozen pre-expansion `names` arities to match so the
        // emitted `pub type` declarations agree with the destructuring
        // sites.
        render_prep::stub_adt::reconcile_declared_arities(&mut names, &rendered_ast_for_dce);
        // `bump_variant_arities` only ever raises, so folding the handler
        // trees in after the flat one leaves each declaration at the
        // widest arity any rendered site binds.
        for view in &handler_views {
            render_prep::stub_adt::reconcile_declared_arities(&mut names, view);
        }
        let prefix = render_prep::stub_adt::format_stub_adt_prefix(&names);
        (rewritten, std::rc::Rc::new(registry), prefix)
    }
}

pub fn decompile_program(
    program: &Program<NamedDeBruijn>,
    mut options: DecompileOptions,
) -> Result<String> {
    // Inconsistent leaf toggles surface as an error here rather
    // than as a pipeline-runtime panic later.
    options.validate()?;

    // Layer output (UPLC): echo the parsed program with unique variable
    // names and run no decompilation. `Uplc` = readable spine-flattened
    // (`[f a b c]`); `UplcCanonical` = the uplc crate's binary-nested
    // layout. See `render_uplc_layer`.
    if matches!(
        options.output_layer,
        OutputLayer::Uplc | OutputLayer::UplcCanonical
    ) {
        let canonical = options.output_layer == OutputLayer::UplcCanonical;
        return Ok(render_uplc_layer(program, canonical));
    }

    // With no explicit version, resolve both: the plan version (the
    // whole-pipeline stance — the V1/V2-ambiguous `(1,0)` header coerces
    // to V2) and the field-naming version (`None` unless V1-vs-V2 is
    // certain). `render_field_version` gates the render-time
    // `tx_info.fields[N]` → schema-named relabel.
    let (plan_version, render_field_version) =
        resolve_render_versions(program, options.script_version);
    // V1 and V2 share the (1, 0) UPLC header. With no explicit version and
    // no builtin evidence pinning V2, the V2 plan default is a GUESS — real
    // V1 scripts do land here — so surface it as an Info diagnostic:
    // `--script-version` can change context-field naming.
    let version_inferred_ambiguous = options.script_version.is_none()
        && render_field_version.is_none()
        && plan_version.is_some();
    options.script_version = plan_version;
    let show_types = options.type_passes.any_enabled();
    // Clone the validator metadata before the pipeline consumes
    // `options`. `None` still wraps with the fallback
    // (`validator decompiled { else(_) { body } }`), so every output
    // is a legal surface syntax validator-block declaration.
    let validator_meta = options.validator_meta.clone();
    let synthesize_stub_adts = options.synthesize_stub_adts;
    let recognize_prelude = options.recognize_prelude_constructors;
    let decode_church = options.decode_church_to_native;
    let expect_or_fail = options.expect_or_fail;
    let compilable_data_access = options.compilable_data_access;
    let strip_all_traces = options.strip_all_traces;
    let strip_plutustx_traces = options.strip_plutustx_traces;
    let output_layer = options.output_layer;
    // capture the polarity-oracle runtime inputs BEFORE `options`
    // is moved into the pipeline — consumed only by the polarity report.
    let oracle_data_args = options.oracle_data_args.clone();
    let oracle_tx = options.oracle_tx.clone();
    // capture validator-shape inputs BEFORE
    // `options` is moved into the pipeline.
    let validator_shape_options = options.validator_shape.clone();
    let script_version_for_plan = options.script_version;
    // Plain decompile only needs `expr` + `blueprint_registry` + `final_types`
    // from the pipeline; skipping per-pass snapshot collection is a ~10x win on
    // large scripts. Callers that need `source_map.final_pseudo_to_mid` (debug
    // bundle, stepping bridge) go through the `_opts` variant with true.
    let pipeline_output = run_pipeline_with_artifacts_opts(program, options, |_, _| {}, false)?;

    // Layer output (raw-pseudo / post-pipeline): render the pseudo AST
    // as-is, before the render-prep dressing below and without the
    // church→native / `expect ... or fail` toggles. For `RawPseudo` the
    // pipeline already stopped at the lowering seed, so
    // `pipeline_output.expr` is that seed; for `PostPipeline` it is the
    // post-passes AST — both render identically here.
    // `layer_pretty_config`'s default `RenderCtx` pins every opt-in to its
    // faithful-view default, so this output cannot depend on anything but
    // the AST. `to_pretty` still runs the unconditional
    // `prepare_for_render` disambiguation internally.
    if matches!(
        output_layer,
        OutputLayer::RawPseudo | OutputLayer::PostPipeline
    ) {
        return Ok(pipeline_output
            .expr
            .to_pretty_with_config(layer_pretty_config(show_types)));
    }

    // The program-scoped church-bool convention, detected by the pipeline
    // on the lowering seed and carried out on `PipelineOutput` — it cannot
    // be re-derived here, simplify having folded the producer signals.
    let church_polarity = pipeline_output.church_polarity_signals.verdict();

    // Layer output (polarity report): the pipeline above already ran that
    // detection and returned its signal breakdown. Emit the diagnostic
    // instead of the rendered program.
    if matches!(output_layer, OutputLayer::PolarityReport) {
        return Ok(crate::decompile::church_polarity::render_polarity_report(
            program,
            &pipeline_output.church_polarity_signals,
            &oracle_data_args,
            oracle_tx.as_ref(),
        ));
    }

    // Stub-ADT synthesis for unresolved `Constr<N>` constructors, so
    // the output uses valid constructor syntax
    // (`Unknown_S_<ord>_<tag>`) rather than the syntax-error
    // placeholder: the collector registers the synthetic types in the
    // BlueprintHintRegistry, the rewriter attaches a `type_hint` to each
    // unresolved Constr node, and the render is prefixed with the
    // synthetic `pub type ...` declarations. All of it is gated on
    // `options.synthesize_stub_adts`; with it off the raw `Constr<tag>`
    // shapes survive — round-trip-friendly, but not valid surface syntax.
    //
    // First, the relabel pass reverts a stub-sum producer's mislabeled
    // `Nil` / `None` / `Unknown_E_*` return leaves to raw `Constr<tag>`,
    // so the collector groups them under its EXCLUSIVE consumer's
    // scrutinee class (see `stub_adt`'s `producer_leaf_fns`
    // attribution). Fail-closed and witness-gated inside the pass.
    let (expr_for_render, registry_for_render, stub_prefix) = dress_stub_adts(
        pipeline_output.expr,
        pipeline_output.blueprint_registry,
        &StubAdtRenderContext {
            synthesize_stub_adts,
            decode_church,
            compilable_data_access,
            strip_all_traces,
            strip_plutustx_traces,
            // Same stance as the pipeline's Cardano naming — see
            // `resolve_render_versions`.
            render_field_version: plan_version,
            plan_version,
            version_guessed: version_inferred_ambiguous,
        },
    );

    // Layer output (render-prep profile): prepare the dressed tree ONCE
    // and report what each step cost, instead of the code. Measured on
    // the same tree and the same context the real render uses, so the
    // shares are the ones that matter — and stated per-prepare, because a
    // full render prepares the tree several times over.
    if matches!(output_layer, OutputLayer::PrepProfile) {
        let render_ctx = RenderCtx::new(plan_version, plan_version)
            .with_version_guessed(version_inferred_ambiguous)
            .with_decode_church(decode_church)
            .with_compilable_data_access(compilable_data_access)
            .with_expect_or_fail(expect_or_fail)
            .with_strip_all_traces(strip_all_traces)
            .with_strip_plutustx_traces(strip_plutustx_traces)
            .with_church_polarity(church_polarity);
        let prepared = render_prep::prepare_for_render_with_notes(&expr_for_render, &render_ctx);
        return Ok(prepared.profile.render_table(0.005));
    }

    // When prelude-constructor recognition is disabled,
    // downgrade `Known(True/False/Some/None/Void)` to
    // `Unknown { tag, arity }` so the renderer emits raw
    // `Constr<N>` form.
    let expr_for_render = if recognize_prelude {
        expr_for_render
    } else {
        render_prep::prelude_downgrade::downgrade_prelude_constructors(expr_for_render)
    };
    // Every opt-in for exactly this render, carried by value: nothing to
    // activate and nothing to restore, so no render can observe another's
    // settings even on a reused blocking-pool thread.
    let (rendered, purpose_bodies, auto_single_purpose, observed_purposes) = {
        // Both version channels carry the plan version: the pipeline's
        // Cardano naming already runs on it, so a stricter render channel
        // only half-named the same tree. `version_inferred_ambiguous`
        // above still reports when that version is a guess.
        let render_ctx = RenderCtx::new(plan_version, plan_version)
            .with_version_guessed(version_inferred_ambiguous)
            .with_decode_church(decode_church)
            .with_compilable_data_access(compilable_data_access)
            .with_expect_or_fail(expect_or_fail)
            .with_strip_all_traces(strip_all_traces)
            .with_strip_plutustx_traces(strip_plutustx_traces)
            .with_church_polarity(church_polarity);
        let (rendered, _spans) = render_decompiled_expr_with_registry_and_final_types(
            &expr_for_render,
            show_types,
            &registry_for_render,
            &pipeline_output.final_types,
            &render_ctx,
        );
        // Shared prepared tree for the pre-wrap AST analyses below (both
        // need the render-prep names; prepare is idempotent so this is
        // the same tree the render produced internally).
        let prepared_for_analysis = render_prep::prepare_for_render(&expr_for_render, &render_ctx);
        // Pre-render per-purpose handler bodies from per-purpose ASTs
        // (dispatch arm selected + handler-local DCE) under the SAME
        // render toggles. Empty when the body has no >=2-arm purpose
        // dispatch — the wrap then uses the legacy text path.
        let purpose_bodies = build_purpose_handler_bodies(
            &prepared_for_analysis,
            show_types,
            &registry_for_render,
            &pipeline_output.final_types,
            &render_ctx,
        );
        // V3 single-purpose auto-detection from the prepared entry
        // spine. DEFINITIVELY V3 only — an explicit flag or the (1,1,_)
        // UPLC header, which V1/V2 cannot carry (tag 5 = Propose is
        // V3-only).
        let auto_single_purpose = if purpose_bodies.is_empty()
            && script_version_for_plan == Some(ScriptVersion::PlutusV3)
        {
            detect_single_purpose_v3(&prepared_for_analysis)
        } else {
            None
        };
        // Weaker, wrap-neutral companion to `auto_single_purpose`: what
        // the body actually discriminates on. Read for the diagnostic
        // only, and only for V3, where `ScriptInfo` carries the purpose.
        let observed_purposes = if script_version_for_plan == Some(ScriptVersion::PlutusV3) {
            observe_script_info_purposes(&prepared_for_analysis)
        } else {
            Vec::new()
        };
        (
            rendered,
            purpose_bodies,
            auto_single_purpose,
            observed_purposes,
        )
    };
    // Route through `validator_shape::build_plan` + `wrap_rendered`.
    // The plan resolver picks BlueprintBlock / PurposeBlock / Flat
    // based on blueprint metadata, explicit `--purpose`, and detected
    // dispatch.
    let mut dispatch = validator_shape::detect_dispatch(&expr_for_render);
    // A body whose purpose arms are SCATTERED has no single `when` for
    // `detect_dispatch` to read, so it reports `None` — but the split
    // above already produced a handler body per purpose, specialized
    // from the whole body. Real bodies are the proof the shape detector
    // could not supply: promote, so the wrap emits them as handlers
    // instead of dropping them on the floor beside a flat wrap.
    if matches!(dispatch, validator_shape::PurposeDispatch::None) && purpose_bodies.len() >= 2 {
        dispatch = validator_shape::PurposeDispatch::MultiPurpose {
            purposes: purpose_bodies.iter().map(|(p, _)| *p).collect(),
        };
    }
    let outer = validator_shape::inspect_outer(program);
    let plan_input = validator_shape::PlanInput {
        meta: validator_meta.as_ref(),
        options: &validator_shape_options,
        script_version: script_version_for_plan,
        outer: &outer,
        dispatch: &dispatch,
        detected_single_purpose: auto_single_purpose,
        observed_script_info_purposes: observed_purposes,
        version_inferred_ambiguous,
    };
    let plan = validator_shape::build_plan(plan_input);
    let (diagnostics, wrapped) = validator_shape::wrap_rendered_separated_with_bodies(
        &rendered,
        &plan,
        if purpose_bodies.is_empty() {
            None
        } else {
            Some(&purpose_bodies)
        },
    );
    // Annotate hoisted module-level `const X = ...` decls with
    // `// ↓ extracted from param_K` comments, so each constant
    // traces back to its outer-Apply origin.
    let compile_count_for_annotate =
        outer
            .applied_params
            .len()
            .saturating_sub(validator_shape::param_surface_runtime_count(
                validator_shape_options.applied_kind,
                &outer,
                validator_shape::runtime_arity_for(
                    script_version_for_plan,
                    validator_shape_options.purpose,
                ),
            ));
    let (wrapped, mut annotated_param_indices) =
        validator_shape::annotate_hoisted_consts_with_param_origin(
            &wrapped,
            &outer.applied_params,
            compile_count_for_annotate,
            &outer.compiler_binding_indices,
        );
    // Hoist inlined `let NAME = <RHS>` lines whose RHS
    // contains a known compile-param hex up to module-level
    // `const NAME = RHS` declarations above the validator,
    // deduplicating repeats across arms. Returns the hoisted
    // param indices, which the prefix block then drops.
    let (wrapped, hoisted_param_indices) = validator_shape::hoist_compile_param_lets(
        &wrapped,
        &outer.applied_params,
        compile_count_for_annotate,
        &outer.compiler_binding_indices,
    );
    // Merge the two sets: annotate (pre-existing module-level
    // const) and hoist (newly hoisted from an arm body) both
    // annotate the const decl, so the prefix block drops those
    // params either way.
    annotated_param_indices.extend(hoisted_param_indices.iter().copied());
    let hoisted_param_indices = annotated_param_indices;
    // Surface applied compile-time params as a `const param_K = ...`
    // prefix above the wrap; the body itself stays β-reduced.
    // `applied_kind` picks compile-params vs runtime-args labeling
    // (debug-snapshot interpretation). Passing the calling-convention
    // runtime arity lets `format_applied_params_prefix` compute the
    // compile/runtime split from version+purpose instead of trusting
    // `pre_applied_runtime_args` alone. `PlainFn` wraps get no prefix:
    // plain Plutus scripts have no compile/runtime distinction.
    let is_plain = matches!(plan.wrap_form, validator_shape::WrapForm::PlainFn);
    let param_prefix = if is_plain {
        String::new()
    } else {
        let runtime_arity_for_prefix = validator_shape::runtime_arity_for(
            script_version_for_plan,
            validator_shape_options.purpose,
        );
        // Exclude hoisted compile params from the prefix
        // block — the const decl + annotation documents them.
        validator_shape::format_applied_params_prefix_with_skip(
            &outer,
            validator_shape_options.applied_kind,
            runtime_arity_for_prefix,
            &hoisted_param_indices,
        )
        .unwrap_or_default()
    };
    // Composition order: polarity note → diagnostics → param prefix →
    // stub-ADT decls → validator wrap. The note and diagnostics MUST come
    // first so they are not buried below a potentially-large stub-ADT block.
    let polarity_note = crate::decompile::church_polarity::inverse_cip_header_note(church_polarity);
    Ok(format!(
        "{polarity_note}{diagnostics}{param_prefix}{stub_prefix}{wrapped}"
    ))
}

/// Render the decoded program (the [`OutputLayer::Uplc`] /
/// [`OutputLayer::UplcCanonical`] echo) as UPLC text with UNIQUE variable names.
///
/// The decoded `Program<NamedDeBruijn>` carries the placeholder `text` "i_0" on
/// EVERY binder — the de Bruijn index is the real identity — so the uplc crate's
/// pretty-printer, which prints `name.text()`, names every `lam`/`var` `i_0`.
/// Round-tripping `NamedDeBruijn → DeBruijn → Name` assigns a distinct
/// `i_<unique>` per binder instead.
///
/// `canonical = false` ([`OutputLayer::Uplc`]): the readable spine-flattened
/// layout (`[f a b c]` — see [`uplc_render`]). `canonical = true`
/// ([`OutputLayer::UplcCanonical`]): the `uplc` crate's own canonical
/// binary-nested layout (`[[[f a] b] c]`). Both carry the unique names.
///
/// Falls back to the raw `NamedDeBruijn` render when the scope round-trip fails
/// on a malformed / open-term program.
pub(crate) fn render_uplc_layer(program: &Program<NamedDeBruijn>, canonical: bool) -> String {
    use uplc::ast::{DeBruijn, Name};
    let debruijn: Program<DeBruijn> = program.clone().into();
    match Program::<Name>::try_from(debruijn) {
        Ok(named) => {
            // Both layouts go through our own printer: the `uplc` crate's
            // `Display` builds a `pretty::RcDoc`, whose `Rc` destructor
            // recurses once per level and blows the wasm stack on a deep
            // script.
            if canonical {
                uplc_render::render_program_canonical(&named)
            } else {
                uplc_render::render_program_flattened(&named)
            }
        }
        Err(_) => program.to_string(),
    }
}

/// `PrettyConfig` for an intermediate-layer render
/// ([`OutputLayer::RawPseudo`] / [`OutputLayer::PostPipeline`]): the
/// bare pretty-printer config honoring only `show_types`, so the layer
/// view matches the final layer's type-annotation behavior without any
/// of the registry / final-types / validator-wrap dressing.
pub(crate) fn layer_pretty_config(show_types: bool) -> crate::decompile::render::PrettyConfig {
    crate::decompile::render::PrettyConfig {
        show_types,
        ..Default::default()
    }
}

#[cfg(test)]
pub(crate) fn render_decompiled_expr(expr: PseudoExpr, show_types: bool) -> String {
    render_decompiled_expr_with_spans(&expr, show_types).0
}

#[cfg(test)]
pub(crate) fn render_decompiled_expr_with_spans(
    expr: &PseudoExpr,
    show_types: bool,
) -> (
    String,
    Vec<(
        crate::pseudo::ast::PseudoNodeId,
        crate::pseudo::mid::expr_id::SourceSpan,
    )>,
) {
    let config = if show_types {
        crate::decompile::render::PrettyConfig {
            show_types: true,
            ..Default::default()
        }
    } else {
        crate::decompile::render::PrettyConfig::default()
    };
    crate::decompile::render::PrettyPrinter::with_config(config).print_with_spans(expr)
}

/// Render with a pipeline-built [`BlueprintHintRegistry`] so user-ADT
/// constructor names are resolved through the registry instead of the
/// inline `display_name` field.
#[allow(dead_code)]
pub(crate) fn render_decompiled_expr_with_registry(
    expr: &PseudoExpr,
    show_types: bool,
    registry: &std::rc::Rc<BlueprintHintRegistry>,
) -> (
    String,
    Vec<(
        crate::pseudo::ast::PseudoNodeId,
        crate::pseudo::mid::expr_id::SourceSpan,
    )>,
) {
    let config = if show_types {
        crate::decompile::render::PrettyConfig {
            show_types: true,
            ..Default::default()
        }
    } else {
        crate::decompile::render::PrettyConfig::default()
    };
    expr.to_pretty_with_spans_config_and_registry(config, std::rc::Rc::clone(registry))
}

pub(crate) fn render_decompiled_expr_with_registry_and_final_types(
    expr: &PseudoExpr,
    show_types: bool,
    registry: &std::rc::Rc<BlueprintHintRegistry>,
    final_types: &std::rc::Rc<final_type_table::FinalTypeTable>,
    render_ctx: &RenderCtx,
) -> (
    String,
    Vec<(
        crate::pseudo::ast::PseudoNodeId,
        crate::pseudo::mid::expr_id::SourceSpan,
    )>,
) {
    let config = crate::decompile::render::PrettyConfig {
        show_types,
        render_ctx: *render_ctx,
        ..Default::default()
    };
    expr.to_pretty_with_spans_config_registry_and_final_types(
        config,
        std::rc::Rc::clone(registry),
        std::rc::Rc::clone(final_types),
    )
}

/// Decompile to PseudoExpr AST (for further processing).
pub(crate) fn decompile_to_ast(
    program: &Program<NamedDeBruijn>,
    mut options: DecompileOptions,
) -> Result<PseudoExpr> {
    // Apply the same builtin-aware auto-detect as `decompile_program`
    // so AST-level callers also benefit from version inference.
    if options.script_version.is_none() {
        let decision = validator_shape::infer_version(program);
        options.script_version = decision.to_script_version();
    }
    run_pipeline(program, options, |_, _| {})
}

#[cfg(test)]
pub(crate) mod tests;
