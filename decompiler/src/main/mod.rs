//! UPLC Decompiler CLI
//!
//! Decompiles UPLC bytecode to readable pseudocode. Deeply nested scripts
//! can exceed the default main-thread stack, so decompilation runs on a
//! dedicated 64 MB worker thread via `decompile_with_large_stack` /
//! `decompile_with_debug_large_stack`.

use std::io::Write;
use std::path::{Path, PathBuf};

use clap::{Parser, Subcommand, ValueEnum};
use miette::{IntoDiagnostic, Result};

use dehosk::cardano::{Blueprint, BlueprintHints};
use dehosk::{
    DecompileOptions, OutputLayer, ScriptVersion, decompile_with_debug_large_stack,
    decompile_with_large_stack,
};

#[derive(Parser)]
#[command(name = "dehosk")]
#[command(
    author,
    version,
    about = "Decompile UPLC bytecode to readable pseudocode"
)]
#[command(after_help = "EXAMPLES:
    # Decompile hex-encoded UPLC
    dehosk hex 59014c010000...

    # Decompile from a file
    dehosk file validator.uplc

    # Decompile from plutus.json
    dehosk blueprint plutus.json --validator spend

    # List validators in a blueprint
    dehosk blueprint plutus.json

    # Decompile all validators to a file
    dehosk blueprint plutus.json --all --output decompiled.dehosk
")]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Don't recognize high-level patterns (output raw translation)
    #[arg(long, global = true)]
    raw: bool,

    /// Don't infer types
    #[arg(long, global = true)]
    no_types: bool,

    /// Don't optimize output (keep all let bindings)
    #[arg(long, global = true)]
    no_optimize: bool,

    /// Safer, less opinionated decompilation (disables ambiguous rewrites)
    #[arg(long, global = true)]
    safe_mode: bool,

    /// Rewrite Church-encoded values to their native type equivalents in the
    /// rendered output (`fn(x) { x(a, b) }` → `Pair(a, b)`, `fn(t, _) { t }` →
    /// `True`, `fn(_, f) { f }` → `False`). Useful when a helper's
    /// Church-encoded shape obscures its type intent.
    #[arg(long, global = true)]
    decode_church_to_native: bool,

    /// Render single-branch `when X is { P -> body; _ -> fail @"msg" }` as
    /// `expect P = X or fail @"msg"`, preserving the fail message the default
    /// `expect P = X` sugar drops. Non-strict surface syntax (the `or fail` clause is a
    /// readability annotation, not compilable surface syntax). Default: off.
    #[arg(long, global = true)]
    expect_or_fail: bool,

    /// Drop every `trace` from the rendered output, keeping only the traced
    /// value. Semantically LOG-DROPPING: the compiled script still emits
    /// those traces, so the render stops saying everything the program does.
    /// Default: off.
    #[arg(long, global = true)]
    strip_all_traces: bool,

    /// Drop the PlutusTx per-call-site `entering X` / `exiting X` trace pairs
    /// that wrap every call. Narrower than `--strip-all-traces`: user-facing
    /// `trace @"msg"` is kept. Default: off.
    #[arg(long, global = true)]
    strip_plutustx_traces: bool,

    /// Lower the un-recovered raw-`Data` access spine to the compilable
    /// `builtin` surface (`builtin.un_constr_data(X).1st`/`.2nd` for
    /// `.tag`/`.fields`, `builtin.head_list` / `builtin.tail_list` /
    /// `builtin.null_list`, `coll[N]` → `head_list(tail_list^N(coll))`,
    /// `coll[N..]` → nested `tail_list`). Default: off — the readable pseudo
    /// (`Constr.unpack(X)`, `X.tag`, `X.fields`, `X[N]`, `X[N..]`, `.head`,
    /// `List.head`/`List.tail`/`List.is_empty`) reads better but is NOT valid
    /// surface syntax.
    #[arg(long, global = true)]
    compilable_data_access: bool,

    /// Name 3-nullary-variant `when` shapes as the prelude `Ordering`
    /// (`Less`/`Equal`/`Greater`), incl. the producer-side comparator relabel
    /// (which still requires canonical `==`/`<` branch semantics). Default:
    /// off — the shape also matches non-comparison enums, and prelude
    /// comparison names on those (or on scrambled-tag comparators) mislead.
    #[arg(long, global = true)]
    ordering_names: bool,

    /// Plutus script version (v1, v2, or v3). Enables semantic field naming.
    #[arg(long, global = true, value_enum)]
    script_version: Option<CliScriptVersion>,

    /// Don't synthesize stub `pub type Unknown_S_<n> { ... }`
    /// declarations for unresolved `Constr<tag>` constructors. With
    /// this flag the raw `Constr<tag>` placeholders survive in the
    /// output (round-trip-friendly but not valid surface
    /// syntax). Default: synthesize stubs.
    #[arg(long, global = true)]
    no_stub_adts: bool,

    /// Explicit validator purpose for single-purpose interpretation.
    /// Required when V1/V2 non-spend purpose is ambiguous from
    /// bytecode (mint vs withdraw vs certificate) or when V3 single-
    /// purpose is detected without explicit dispatch. Mutually
    /// exclusive with `--split-purposes always`.
    #[arg(long, global = true, value_enum)]
    purpose: Option<CliPurpose>,

    /// How aggressively to split a multi-purpose validator body:
    /// - auto (default): split when V3 dispatch is detected.
    /// - always: split whenever ≥2 purpose arms are detected.
    /// - never: keep body intact (flat-wrap), even if dispatch found.
    #[arg(long, global = true, value_enum, default_value = "auto")]
    split_purposes: CliSplitPurposes,

    /// Treat the script as a Cardano on-chain validator or a plain
    /// Plutus script (library function / debug snapshot):
    /// - auto (default): classify by shape (V3 dispatch / lambda arity).
    /// - validator: force validator-block wrap.
    /// - plain: emit `pub fn <name>(...) { ... }`, skip purpose
    ///   diagnostics.
    #[arg(long, global = true, value_enum, default_value = "auto")]
    script_kind: CliScriptKind,

    /// How to interpret the outer Apply chain:
    /// - compile (default): all outer Apply are compile-time
    ///   params. The common case for deployed validators.
    /// - auto: classify by structural fit, else as `compile`.
    /// - runtime: runtime args ARE pre-applied (debug snapshot);
    ///   the last `runtime_arity_for(version, purpose)` Apply
    ///   nodes are runtime args, the rest compile params.
    /// - <N>: explicit per-arg split — the LAST N outer Apply
    ///   nodes are runtime args; first `applied_count - N` are
    ///   compile-time params.
    #[arg(long, global = true, default_value = "compile")]
    applied_as: CliAppliedKind,

    /// Disable recognition of prelude constructors. When set,
    /// every recognized prelude constructor renders as raw `Constr<N>`
    /// form: `True`/`False`, `Some`/`None`, `Void`, `Ok`/`Error`, the
    /// constructor-encoded `Pair`, list constructors, ordering, etc.
    /// The only constructors that stay named are the Cardano purpose
    /// anchors (`Spend`/`Mint`/`Withdraw`/`Publish`/`Vote`/`Propose`),
    /// because purpose-dispatch detection needs them. Pairs that come
    /// in as the UPLC builtin pair type render via a separate path
    /// (`Pair(a, b)`) that this flag does not affect.
    #[arg(long, global = true)]
    no_prelude_constructors: bool,

    /// Which pipeline layer to emit instead of full decompilation:
    /// - decompiled (default): full decompilation.
    /// - uplc: echo the decoded input as UPLC, readable spine-flattened layout
    ///   (`[f a b c]`) with unique names — runs no decompilation.
    /// - uplc-canonical: the same echo in the uplc crate's binary-nested layout
    ///   (`[[[f a] b] c]`).
    /// - raw-pseudo: the pseudo-AST seed straight out of MIR lowering,
    ///   before any structural passes (the closest "MIR" view).
    /// - post-pipeline: the pseudo-AST after all structural passes,
    ///   before render-prep dressing (stub-ADTs, validator wrap).
    /// - polarity-report: a church-bool polarity diagnostic — the detected
    ///   convention (Cip/InverseCip), the structural signals behind it, and a
    ///   heuristic-caveat warning. Useful when a script's `True`/`False`/`!`
    ///   look suspect (PlutusTx-compiled scripts use the inverse convention).
    /// - prep-profile: a render-prep COST diagnostic — what each of the ~140
    ///   render-prep steps took on this program, slowest first. Reports instead
    ///   of emitting code; use it to find which pass is expensive on a script.
    ///
    /// Intermediate layers are a faithful view of the intermediate
    /// representation, NOT valid surface syntax. Orthogonal to
    /// `--raw` (which controls WHICH passes run; `--emit` controls
    /// WHERE the pipeline stops).
    #[arg(long, global = true, value_enum, default_value = "decompiled")]
    emit: CliOutputLayer,

    /// A CBOR-hex `PlutusData` runtime argument for the `--emit
    /// polarity-report` data-tag oracle. Repeat once per validator argument
    /// in calling order — datum, redeemer, script_context (drop datum for a
    /// minting policy). When given, the oracle APPLIES these and RUNS the
    /// validator to resolve the `Constr<0>` = true/false convention by
    /// execution. Ignored by every other layer.
    #[arg(long = "oracle-arg", global = true, value_name = "CBOR_HEX")]
    oracle_arg: Vec<String>,

    /// Path to a phase-2 oracle BUNDLE for `--emit polarity-report` — the
    /// practical data-tag path. JSON: `{ "tx": "<cbor-hex>", "resolved_inputs":
    /// [{"input":"<cbor-hex>","output":"<cbor-hex>"}, ...] }`, listing the
    /// transaction and every input it spends/references (incl. the
    /// reference-script UTxO). The oracle RUNS the real tx to resolve the
    /// `Constr<0>` = true/false convention. Takes precedence over `--oracle-arg`.
    #[arg(long = "oracle-tx", global = true, value_name = "BUNDLE_JSON")]
    oracle_tx: Option<PathBuf>,

    /// Show verbose output
    #[arg(short, long, global = true)]
    verbose: bool,

    /// Output file (default: stdout)
    #[arg(short, long, global = true)]
    output: Option<PathBuf>,

    /// Write debug bundle JSON with provenance/source-map.
    /// For `blueprint --all`, pass a directory path.
    #[arg(long, global = true)]
    debug_bundle: Option<PathBuf>,
}

#[derive(Subcommand)]
enum Commands {
    /// Decompile from hex-encoded UPLC
    Hex {
        /// Hex-encoded CBOR or Flat UPLC code
        code: String,
    },

    /// Decompile from a file
    File {
        /// Path to the file containing UPLC code
        path: PathBuf,

        /// Input format
        #[arg(long, value_enum, default_value = "auto")]
        format: InputFormat,
    },

    /// Decompile from a Plutus blueprint (plutus.json)
    Blueprint {
        /// Path to plutus.json
        path: PathBuf,

        /// Validator name to decompile (if not specified, lists available validators)
        #[arg(long)]
        validator: Option<String>,

        /// Decompile all validators
        #[arg(long)]
        all: bool,
    },
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum InputFormat {
    /// Auto-detect format
    Auto,
    /// Hex-encoded bytes
    Hex,
    /// Raw CBOR bytes
    Cbor,
    /// Raw Flat bytes
    Flat,
    /// Text UPLC
    Text,
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum CliScriptVersion {
    /// Plutus V1
    V1,
    /// Plutus V2
    V2,
    /// Plutus V3
    V3,
}

impl CliScriptVersion {
    fn to_script_version(self) -> ScriptVersion {
        match self {
            CliScriptVersion::V1 => ScriptVersion::PlutusV1,
            CliScriptVersion::V2 => ScriptVersion::PlutusV2,
            CliScriptVersion::V3 => ScriptVersion::PlutusV3,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Default)]
enum CliOutputLayer {
    /// Full decompilation to readable pseudocode.
    #[default]
    Decompiled,
    /// Echo the decoded input as UPLC, readable spine-flattened layout.
    Uplc,
    /// Echo the decoded input as UPLC, the uplc crate's canonical binary-nested
    /// layout.
    UplcCanonical,
    /// Pseudo-AST seed out of MIR lowering, before any structural pass.
    RawPseudo,
    /// Pseudo-AST after all structural passes, before render-prep.
    PostPipeline,
    /// Church-bool polarity diagnostic: the detected convention, the
    /// structural signals behind it, and a heuristic-caveat warning.
    PolarityReport,
    /// Render-prep cost diagnostic: what each of the ~140 render-prep
    /// steps took on this program, slowest first.
    PrepProfile,
}

impl CliOutputLayer {
    fn to_output_layer(self) -> OutputLayer {
        match self {
            CliOutputLayer::Decompiled => OutputLayer::Decompiled,
            CliOutputLayer::Uplc => OutputLayer::Uplc,
            CliOutputLayer::UplcCanonical => OutputLayer::UplcCanonical,
            CliOutputLayer::RawPseudo => OutputLayer::RawPseudo,
            CliOutputLayer::PostPipeline => OutputLayer::PostPipeline,
            CliOutputLayer::PolarityReport => OutputLayer::PolarityReport,
            CliOutputLayer::PrepProfile => OutputLayer::PrepProfile,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum CliPurpose {
    Spend,
    Mint,
    Withdraw,
    Certificate,
    Vote,
    /// V3-only governance purpose (`ScriptInfo::Proposing`).
    Propose,
}

impl CliPurpose {
    fn to_purpose(self) -> dehosk::decompile::validator_meta::ValidatorPurpose {
        use dehosk::decompile::validator_meta::ValidatorPurpose as P;
        match self {
            CliPurpose::Spend => P::Spend,
            CliPurpose::Mint => P::Mint,
            CliPurpose::Withdraw => P::Withdraw,
            CliPurpose::Certificate => P::Certificate,
            CliPurpose::Vote => P::Vote,
            CliPurpose::Propose => P::Propose,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Default)]
enum CliSplitPurposes {
    /// Split when V3 dispatch is detected.
    #[default]
    Auto,
    /// Always split when ≥2 purpose arms found.
    Always,
    /// Never split — keep body intact.
    Never,
}

impl CliSplitPurposes {
    fn to_split_purposes(self) -> dehosk::decompile::validator_shape::SplitPurposes {
        use dehosk::decompile::validator_shape::SplitPurposes as S;
        match self {
            CliSplitPurposes::Auto => S::Auto,
            CliSplitPurposes::Always => S::Always,
            CliSplitPurposes::Never => S::Never,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Default)]
enum CliScriptKind {
    /// Classify by shape — V3 dispatch / lambda arity matching a
    /// validator calling convention → validator; otherwise plain.
    #[default]
    Auto,
    /// Force validator-block wrap (with purpose diagnostics).
    Validator,
    /// Force `pub fn <name>(...) { ... }` plain-function wrap.
    Plain,
}

impl CliScriptKind {
    fn to_script_kind(self) -> Option<dehosk::decompile::validator_shape::ScriptKind> {
        use dehosk::decompile::validator_shape::ScriptKind as K;
        match self {
            CliScriptKind::Auto => None,
            CliScriptKind::Validator => Some(K::Validator),
            CliScriptKind::Plain => Some(K::Plain),
        }
    }
}

/// Accepts `auto`, `compile`, `runtime`, or a non-negative integer N
/// (last N Apply nodes are runtime).
#[derive(Copy, Clone, PartialEq, Eq, Default)]
enum CliAppliedKind {
    /// Structural auto-classification: when
    /// `applied + lambda == runtime_arity` for the inferred
    /// version/purpose, all outer Apply nodes are pre-applied
    /// runtime args. Otherwise falls back to `compile`.
    #[default]
    Auto,
    Compile,
    Runtime,
    /// Explicit per-arg split: last `N` outer Apply nodes are
    /// runtime args.
    RuntimeCount(usize),
}

impl std::str::FromStr for CliAppliedKind {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "auto" => Ok(CliAppliedKind::Auto),
            "compile" => Ok(CliAppliedKind::Compile),
            "runtime" => Ok(CliAppliedKind::Runtime),
            other => other.parse::<usize>().map(CliAppliedKind::RuntimeCount).map_err(
                |_| {
                    format!(
                        "expected `auto`, `compile`, `runtime`, or a non-negative integer; got `{other}`"
                    )
                },
            ),
        }
    }
}

impl CliAppliedKind {
    fn to_applied_kind(self) -> dehosk::decompile::validator_shape::AppliedKind {
        use dehosk::decompile::validator_shape::AppliedKind as A;
        match self {
            CliAppliedKind::Auto => A::Auto,
            CliAppliedKind::Compile => A::Compile,
            CliAppliedKind::Runtime => A::Runtime,
            CliAppliedKind::RuntimeCount(n) => A::RuntimeCount(n),
        }
    }
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    // Clap can't gate on a value, so enforce the `--purpose` ×
    // `--split-purposes always` exclusion by hand.
    if cli.purpose.is_some() && matches!(cli.split_purposes, CliSplitPurposes::Always) {
        return Err(miette::miette!(
            "`--purpose` and `--split-purposes always` are mutually exclusive: \
             `--purpose` forces a single-purpose interpretation while \
             `--split-purposes always` forces a multi-purpose split. \
             Pick one — drop `--purpose` to keep `always`, or drop \
             `--split-purposes` (defaults to `auto`) to keep `--purpose`."
        ));
    }

    let mut options = if cli.raw {
        // Raw mode already preserves placeholder `Constr<tag>` shapes,
        // so `--no-stub-adts` adds nothing here; nothing re-enables
        // stub synthesis on top of `--raw` — drop `--raw` for full
        // output.
        //
        // `--emit` is orthogonal (passes vs stop point), so overlay
        // the chosen layer onto the raw preset.
        DecompileOptions {
            output_layer: cli.emit.to_output_layer(),
            ..DecompileOptions::raw()
        }
    } else {
        DecompileOptions {
            output_layer: cli.emit.to_output_layer(),
            type_passes: if cli.no_types {
                dehosk::decompile::TypePasses::all_off()
            } else {
                dehosk::decompile::TypePasses::all_on()
            },
            simplify_passes: if cli.no_optimize {
                dehosk::decompile::SimplifyPasses::all_off()
            } else {
                dehosk::decompile::SimplifyPasses::all_on()
            },
            safe_mode: cli.safe_mode,
            script_version: cli.script_version.map(|v| v.to_script_version()),
            synthesize_stub_adts: !cli.no_stub_adts,
            recognize_prelude_constructors: !cli.no_prelude_constructors,
            decode_church_to_native: cli.decode_church_to_native,
            strip_all_traces: cli.strip_all_traces,
            strip_plutustx_traces: cli.strip_plutustx_traces,
            expect_or_fail: cli.expect_or_fail,
            compilable_data_access: cli.compilable_data_access,
            ordering_names: cli.ordering_names,
            validator_shape: dehosk::decompile::validator_shape::ValidatorShapeOptions {
                purpose: cli.purpose.map(|p| p.to_purpose()),
                split_purposes: cli.split_purposes.to_split_purposes(),
                script_kind: cli.script_kind.to_script_kind(),
                applied_kind: cli.applied_as.to_applied_kind(),
            },
            ..DecompileOptions::default()
        }
    };

    // Decode any `--oracle-arg <cbor-hex>` runtime args for the polarity
    // report's data-tag oracle. Fail early on bad hex / CBOR rather than
    // skipping silently.
    if !cli.oracle_arg.is_empty() {
        let mut decoded = Vec::with_capacity(cli.oracle_arg.len());
        for (i, arg) in cli.oracle_arg.iter().enumerate() {
            let bytes = hex::decode(arg.trim())
                .map_err(|e| miette::miette!("--oracle-arg #{}: invalid hex: {e}", i + 1))?;
            let data = dehosk::decode_plutus_data(&bytes).map_err(|e| {
                miette::miette!("--oracle-arg #{}: invalid CBOR PlutusData: {e}", i + 1)
            })?;
            decoded.push(data);
        }
        options.oracle_data_args = decoded;
    }

    // Load the phase-2 oracle bundle for `--emit polarity-report`.
    if let Some(path) = &cli.oracle_tx {
        let text = std::fs::read_to_string(path)
            .map_err(|e| miette::miette!("--oracle-tx: cannot read {}: {e}", path.display()))?;
        let json: serde_json::Value = serde_json::from_str(&text)
            .map_err(|e| miette::miette!("--oracle-tx: invalid JSON: {e}"))?;
        let dehex = |v: &serde_json::Value, what: &str| -> miette::Result<Vec<u8>> {
            let s = v
                .as_str()
                .ok_or_else(|| miette::miette!("--oracle-tx: {what} must be a hex string"))?;
            hex::decode(s.trim()).map_err(|e| miette::miette!("--oracle-tx: {what}: bad hex: {e}"))
        };
        let tx_cbor = dehex(&json["tx"], "tx")?;
        let mut resolved_inputs = Vec::new();
        for (i, entry) in json["resolved_inputs"]
            .as_array()
            .ok_or_else(|| miette::miette!("--oracle-tx: `resolved_inputs` must be an array"))?
            .iter()
            .enumerate()
        {
            let input = dehex(&entry["input"], &format!("resolved_inputs[{i}].input"))?;
            let output = dehex(&entry["output"], &format!("resolved_inputs[{i}].output"))?;
            resolved_inputs.push((input, output));
        }
        options.oracle_tx = Some(dehosk::decompile::OracleTxBundle {
            tx_cbor,
            resolved_inputs,
        });
    }

    let output: Box<dyn Write> = match &cli.output {
        Some(path) => {
            let file = std::fs::File::create(path).into_diagnostic()?;
            Box::new(file)
        }
        None => Box::new(std::io::stdout()),
    };

    match cli.command {
        Commands::Hex { code } => {
            decompile_hex(
                &code,
                options,
                cli.verbose,
                output,
                cli.debug_bundle.as_ref(),
            )?;
        }

        Commands::File { path, format } => {
            decompile_file(
                &path,
                format,
                options,
                cli.verbose,
                output,
                cli.debug_bundle.as_ref(),
            )?;
        }

        Commands::Blueprint {
            path,
            validator,
            all,
        } => {
            decompile_blueprint(
                &path,
                validator,
                all,
                options,
                cli.verbose,
                output,
                cli.debug_bundle.as_ref(),
            )?;
        }
    }

    if let Some(path) = cli.output.as_ref().filter(|_| cli.verbose) {
        eprintln!("Output written to: {}", path.display());
    }

    Ok(())
}

fn decompile_hex(
    code: &str,
    options: DecompileOptions,
    verbose: bool,
    mut output: Box<dyn Write>,
    debug_bundle: Option<&PathBuf>,
) -> Result<()> {
    if verbose {
        eprintln!("Decompiling hex code ({} chars)...", code.len());
    }

    let result =
        decompile_with_optional_debug(code, options, debug_bundle.map(|p| p.as_path()), verbose)?;
    writeln!(output, "{}", result).into_diagnostic()?;

    Ok(())
}

fn decompile_file(
    path: &PathBuf,
    format: InputFormat,
    options: DecompileOptions,
    verbose: bool,
    mut output: Box<dyn Write>,
    debug_bundle: Option<&PathBuf>,
) -> Result<()> {
    if verbose {
        eprintln!("Reading file: {}", path.display());
    }

    let content = std::fs::read(path).into_diagnostic()?;

    let hex_content = match format {
        InputFormat::Auto => {
            // Try text hex first (allowing arbitrary whitespace in dumps).
            let text = String::from_utf8_lossy(&content);
            normalize_hex_text(&text).unwrap_or_else(|| hex::encode(&content))
        }
        InputFormat::Hex => {
            let text = String::from_utf8_lossy(&content);
            normalize_hex_text(&text)
                .ok_or_else(|| miette::miette!("File '{}' is not valid hex text", path.display()))?
        }
        InputFormat::Cbor | InputFormat::Flat => hex::encode(&content),
        InputFormat::Text => {
            return Err(miette::miette!(
                "Text UPLC parsing not yet implemented; \
                 use --format cbor or --format flat instead"
            ));
        }
    };

    if verbose {
        eprintln!("Decompiling {} bytes...", hex_content.len() / 2);
    }

    let result = decompile_with_optional_debug(
        &hex_content,
        options,
        debug_bundle.map(|p| p.as_path()),
        verbose,
    )?;
    writeln!(output, "{}", result).into_diagnostic()?;

    Ok(())
}

fn normalize_hex_text(text: &str) -> Option<String> {
    let mut normalized = String::with_capacity(text.len());

    for ch in text.chars() {
        if ch.is_ascii_whitespace() {
            continue;
        }

        if ch.is_ascii_hexdigit() {
            normalized.push(ch);
            continue;
        }

        return None;
    }

    if normalized.is_empty() || !normalized.len().is_multiple_of(2) {
        return None;
    }

    Some(normalized)
}

fn decompile_blueprint(
    path: &PathBuf,
    validator: Option<String>,
    all: bool,
    options: DecompileOptions,
    verbose: bool,
    mut output: Box<dyn Write>,
    debug_bundle: Option<&PathBuf>,
) -> Result<()> {
    validate_blueprint_selection(validator.as_deref(), all)?;

    if verbose {
        eprintln!("Loading blueprint: {}", path.display());
    }

    let blueprint = Blueprint::from_file(path).into_diagnostic()?;

    if verbose {
        eprintln!(
            "Blueprint: {} v{}",
            blueprint.preamble.title, blueprint.preamble.version
        );
        eprintln!("Found {} validator(s)", blueprint.validators.len());

        let types = blueprint.extract_types();
        if !types.is_empty() {
            eprintln!("Found {} type definition(s)", types.len());
        }
    }

    if validator.is_none() && !all {
        writeln!(output, "Available validators:").into_diagnostic()?;
        for v in &blueprint.validators {
            writeln!(
                output,
                "  - {} (hash: {}...)",
                v.title,
                &v.hash[..16.min(v.hash.len())]
            )
            .into_diagnostic()?;

            if let Some(datum) = &v.datum
                && let Some(name) = &datum.title
            {
                writeln!(output, "      datum: {}", name).into_diagnostic()?;
            }
            // `else` blueprint entries can
            // legitimately omit `redeemer`.
            if let Some(redeemer) = &v.redeemer
                && let Some(name) = &redeemer.title
            {
                writeln!(output, "      redeemer: {}", name).into_diagnostic()?;
            }
        }
        writeln!(output).into_diagnostic()?;
        writeln!(
            output,
            "Use --validator <name> to decompile a specific validator"
        )
        .into_diagnostic()?;
        writeln!(output, "Use --all to decompile all validators").into_diagnostic()?;
        return Ok(());
    }

    let validators_to_decompile: Vec<_> = if all {
        blueprint.validators.iter().collect()
    } else {
        let name = validator.as_ref().unwrap();
        match blueprint.find_validator(name) {
            Some(v) => vec![v],
            None => {
                return Err(miette::miette!(
                    "Validator '{}' not found. Available: {}",
                    name,
                    blueprint.validator_titles().join(", ")
                ));
            }
        }
    };

    let _types = blueprint.extract_types();

    if all && let Some(debug_path) = debug_bundle {
        std::fs::create_dir_all(debug_path).into_diagnostic()?;
    }

    for v in validators_to_decompile {
        writeln!(output, "// Validator: {}", v.title).into_diagnostic()?;
        writeln!(output, "// Hash: {}", v.hash).into_diagnostic()?;

        if !v.description.is_empty() {
            writeln!(output, "// Description: {}", v.description).into_diagnostic()?;
        }

        let hints = BlueprintHints::from_blueprint(&blueprint, &v.title);
        if let Some(ref hints) = hints {
            writeln!(output, "// Parameters: {}", hints.param_names.join(", "))
                .into_diagnostic()?;
        } else {
            let param_names = v.parameter_names();
            if !param_names.is_empty() {
                let names: Vec<_> = param_names.iter().map(|n| n.unwrap_or("?")).collect();
                writeln!(output, "// Parameters: {}", names.join(", ")).into_diagnostic()?;
            }
        }

        writeln!(output).into_diagnostic()?;

        let mut validator_options = options.clone();
        validator_options.blueprint_hints = hints;

        // Build `ValidatorMeta` from the hash group containing this
        // validator, so the renderer emits `validator NAME { spend(...) {...}
        // mint(...) {...} else(_) { fail } }` instead of a bare
        // `fn decompiled(...)`. Entries sharing a compiled image collapse into
        // one block — one image, one body.
        let mut hash_group: Vec<(&str, Vec<String>)> = Vec::new();
        for sibling in &blueprint.validators {
            if sibling.hash == v.hash {
                let raw_names = sibling.parameter_names();
                let params: Vec<String> = raw_names
                    .iter()
                    .enumerate()
                    .map(|(i, n)| n.map(|s| s.to_string()).unwrap_or_else(|| format!("p{i}")))
                    .collect();
                hash_group.push((sibling.title.as_str(), params));
            }
        }
        validator_options.validator_meta =
            dehosk::decompile::ValidatorMeta::from_blueprint_group(hash_group);

        let debug_path_for_validator = debug_bundle.map(|debug_path| {
            if all {
                debug_path.join(format!("{}.debug.json", v.title))
            } else {
                debug_path.clone()
            }
        });

        let result = decompile_with_optional_debug(
            &v.compiled_code,
            validator_options,
            debug_path_for_validator.as_deref(),
            verbose,
        )?;
        writeln!(output, "{}", result).into_diagnostic()?;
        writeln!(output).into_diagnostic()?;
    }

    Ok(())
}

fn validate_blueprint_selection(validator: Option<&str>, all: bool) -> Result<()> {
    if all && validator.is_some() {
        return Err(miette::miette!(
            "Options --all and --validator are mutually exclusive"
        ));
    }

    Ok(())
}

fn decompile_with_optional_debug(
    hex_code: &str,
    options: DecompileOptions,
    debug_bundle_path: Option<&Path>,
    verbose: bool,
) -> Result<String> {
    if let Some(path) = debug_bundle_path {
        let (code, bundle) =
            decompile_with_debug_large_stack(hex_code, options).into_diagnostic()?;
        let json = serde_json::to_string_pretty(&bundle).into_diagnostic()?;
        std::fs::write(path, json).into_diagnostic()?;
        if verbose {
            eprintln!("Debug bundle written to: {}", path.display());
        }
        Ok(code)
    } else {
        decompile_with_large_stack(hex_code, options).into_diagnostic()
    }
}

#[cfg(test)]
mod tests;
