use axum::extract::Request;
use axum::http::{StatusCode, header};
use axum::response::{IntoResponse, Json, Response};
use rust_embed::Embed;
use serde::{Deserialize, Serialize};
use std::time::Instant;

use dehosk::decompile::{
    DisplayPolishPasses, OutputLayer, ReadabilityPasses, SimplifyPasses, StructuralRecoveryPasses,
    TypePasses,
};
use dehosk::error::DecompileError;
use dehosk::{DecompileOptions, ScriptVersion, decompile};

use crate::options_dto::OptionCatalogueDto;

#[derive(Embed)]
#[folder = "frontend/dist/"]
struct FrontendAssets;

#[derive(Deserialize)]
pub struct DecompileRequest {
    hex_code: String,
    #[serde(default)]
    options: DecompileOptionsDto,
}

#[derive(Deserialize)]
pub struct DecompileOptionsDto {
    #[serde(default)]
    safe_mode: bool,
    #[serde(default)]
    script_version: Option<ScriptVersionDto>,
    /// Synthesize stub-ADT declarations for a valid surface.
    /// The crate default is `true`; the web starts `false` so raw
    /// `Constr<tag>` placeholders stay visible.
    #[serde(default)]
    synthesize_stub_adts: bool,
    /// Render prelude constructors (`True`/`False`,
    /// `Some`/`None`, `Void`) by name; `false` leaves the raw
    /// `Constr<N>` form.
    #[serde(default = "default_true")]
    recognize_prelude_constructors: bool,
    /// Rewrite Church-encoded values to native types in the rendered
    /// output (`fn(x) { x(a, b) }` → `Pair(a, b)  // church-pair`,
    /// `fn(t, _) { t }` → `True  // church-true`); `false` keeps the raw
    /// Lambda form.
    #[serde(default)]
    decode_church_to_native: bool,
    /// Render single-branch `when X is { P -> body; _ -> fail @"msg" }` as
    /// `expect P = X or fail @"msg"`, keeping the fail message the plain
    /// `expect P = X` sugar drops. Not compilable surface syntax — an annotation.
    #[serde(default)]
    expect_or_fail: bool,
    /// Drop every `trace` from the render, keeping only the traced value.
    /// Semantically log-dropping — the script still emits them.
    #[serde(default)]
    strip_all_traces: bool,
    /// Drop the PlutusTx per-call-site `entering X`/`exiting X` trace pairs.
    /// Narrower than `strip_all_traces`; user `trace @"msg"` is kept.
    #[serde(default)]
    strip_plutustx_traces: bool,
    /// Lower the un-recovered raw-`Data` access spine to the compilable
    /// `builtin` surface: `Constr.unpack`/`X.tag`/`X.fields` →
    /// `builtin.un_constr_data(X)`/`.1st`/`.2nd`; `.head`/`List.head`/
    /// `List.tail`/`List.is_empty` → `builtin.head_list`/`tail_list`/
    /// `null_list`; `X[N]` → `head_list(tail_list^N)`, `X[N..]` → nested
    /// `tail_list`. `false` keeps the readable pseudo, not valid surface syntax.
    #[serde(default)]
    compilable_data_access: bool,
    /// Opt-in `Ordering` (`Less`/`Equal`/`Greater`) naming; default off.
    #[serde(default)]
    ordering_names: bool,
    /// Which pipeline layer to emit. The layers before full decompilation
    /// (`Uplc` / `RawPseudo` / `PostPipeline`) render the AST
    /// faithfully, which is NOT valid surface syntax.
    #[serde(default)]
    output_layer: OutputLayerDto,
    /// Validator-shape options — explicit
    /// `purpose` for V1/V2 non-spend / V3 single-purpose
    /// disambiguation, `split_purposes` policy for V3 multi-purpose,
    /// and `script_kind` to force validator-vs-plain classification.
    #[serde(default)]
    validator_shape: ValidatorShapeOptionsDto,
    #[serde(default = "SimplifyPassesDto::default")]
    simplify_passes: SimplifyPassesDto,
    #[serde(default = "StructuralRecoveryPassesDto::default")]
    structural_recovery_passes: StructuralRecoveryPassesDto,
    #[serde(default = "ReadabilityPassesDto::default")]
    readability_passes: ReadabilityPassesDto,
    #[serde(default = "DisplayPolishPassesDto::default")]
    display_polish_passes: DisplayPolishPassesDto,
    #[serde(default = "TypePassesDto::default")]
    type_passes: TypePassesDto,
}

/// Deliberately NOT `#[derive(Default)]`.
///
/// The derive builds the struct from `bool::default()` and friends,
/// ignoring the per-field `#[serde(default = "…")]` attributes, so it
/// disagrees with an empty request body:
/// `recognize_prelude_constructors` is `false` from the derive and
/// `true` from `{}`. The published `defaults` come from this impl, so
/// the panel would load a control OFF that it shows ON.
///
/// Deserializing an empty object instead makes a request with no
/// `options` key, a request with `options: {}`, and the published
/// `defaults` the same request BY CONSTRUCTION.
impl Default for DecompileOptionsDto {
    fn default() -> Self {
        serde_json::from_value(serde_json::json!({}))
            .expect("every field of DecompileOptionsDto declares a serde default")
    }
}

fn default_true() -> bool {
    true
}

#[derive(Deserialize)]
struct SimplifyPassesDto {
    #[serde(default = "default_true")]
    simplify_fp_initial: bool,
    #[serde(default = "default_true")]
    simplify_fp_post_readability: bool,
    #[serde(default = "default_true")]
    inline_single_use: bool,
    #[serde(default = "default_true")]
    inline_fp: bool,
    #[serde(default = "default_true")]
    inline_post_readability: bool,
    #[serde(default = "default_true")]
    dead_let_elim: bool,
    #[serde(default = "default_true")]
    collapse_tail_chains: bool,
}

impl Default for SimplifyPassesDto {
    fn default() -> Self {
        Self {
            simplify_fp_initial: true,
            simplify_fp_post_readability: true,
            inline_single_use: true,
            inline_fp: true,
            inline_post_readability: true,
            dead_let_elim: true,
            collapse_tail_chains: true,
        }
    }
}

#[derive(Deserialize)]
struct StructuralRecoveryPassesDto {
    #[serde(default = "default_true")]
    recover_let_bound_tag_dispatch: bool,
    #[serde(default = "default_true")]
    simplify_double_rec_fn: bool,
    #[serde(default = "default_true")]
    recover_pair_fixpoint: bool,
    #[serde(default = "default_true")]
    simplify_z_combinator: bool,
    #[serde(default = "default_true")]
    extract_complex_when_subjects: bool,
    #[serde(default = "default_true")]
    resolve_immediate_applications: bool,
    #[serde(default = "default_true")]
    resolve_data_case: bool,
}

impl Default for StructuralRecoveryPassesDto {
    fn default() -> Self {
        Self {
            recover_let_bound_tag_dispatch: true,
            simplify_double_rec_fn: true,
            recover_pair_fixpoint: true,
            simplify_z_combinator: true,
            extract_complex_when_subjects: true,
            resolve_immediate_applications: true,
            resolve_data_case: true,
        }
    }
}

#[derive(Deserialize)]
struct ReadabilityPassesDto {
    #[serde(default = "default_true")]
    improve_variable_names: bool,
    #[serde(default = "default_true")]
    flatten_let_chains: bool,
    #[serde(default = "default_true")]
    rename_variables: bool,
    #[serde(default = "default_true")]
    hoist_local_helpers: bool,
    #[serde(default = "default_true")]
    extract_heavy_constants: bool,
}

impl Default for ReadabilityPassesDto {
    fn default() -> Self {
        Self {
            improve_variable_names: true,
            flatten_let_chains: true,
            rename_variables: true,
            hoist_local_helpers: true,
            extract_heavy_constants: true,
        }
    }
}

#[derive(Deserialize)]
struct DisplayPolishPassesDto {
    #[serde(default = "default_true")]
    strip_cosmetic_delays: bool,
    #[serde(default = "default_true")]
    cancel_force_delay_vars: bool,
    #[serde(default = "default_true")]
    normalize_list_cons_literals: bool,
    #[serde(default = "default_true")]
    normalize_display_rewrites: bool,
    #[serde(default = "default_true")]
    eliminate_cps_selectors: bool,
    #[serde(default = "default_true")]
    simplify_boolean_and_identity: bool,
    #[serde(default = "default_true")]
    collapse_eta_pair_selectors: bool,
    #[serde(default = "default_true")]
    resolve_scott_constructor_lambdas_late: bool,
    #[serde(default = "default_true")]
    resolve_data_case_late: bool,
}

impl Default for DisplayPolishPassesDto {
    fn default() -> Self {
        Self {
            strip_cosmetic_delays: true,
            cancel_force_delay_vars: true,
            normalize_list_cons_literals: true,
            normalize_display_rewrites: true,
            eliminate_cps_selectors: true,
            simplify_boolean_and_identity: true,
            collapse_eta_pair_selectors: true,
            resolve_scott_constructor_lambdas_late: true,
            resolve_data_case_late: true,
        }
    }
}

#[derive(Deserialize)]
struct TypePassesDto {
    #[serde(default = "default_true")]
    solve_type_constraints: bool,
    #[serde(default = "default_true")]
    propagate_types: bool,
    #[serde(default = "default_true")]
    resolve_cardano_field_names: bool,
}

impl Default for TypePassesDto {
    fn default() -> Self {
        Self {
            solve_type_constraints: true,
            propagate_types: true,
            resolve_cardano_field_names: true,
        }
    }
}

#[derive(Deserialize)]
pub enum ScriptVersionDto {
    PlutusV1,
    PlutusV2,
    PlutusV3,
}

/// Which pipeline layer to render. Mirrors
/// [`dehosk::decompile::OutputLayer`], variant for variant. No
/// `rename_all`, so the frontend sends the Rust variant name as-is.
#[derive(Deserialize, Default)]
pub enum OutputLayerDto {
    #[default]
    Decompiled,
    Uplc,
    UplcCanonical,
    RawPseudo,
    PostPipeline,
    /// The catalogue offers every layer the crate has, and
    /// `every_catalogue_choice_round_trips_through_the_request_body`
    /// refuses an offer the request body cannot carry.
    PolarityReport,
    PrepProfile,
}

impl From<OutputLayerDto> for OutputLayer {
    fn from(dto: OutputLayerDto) -> Self {
        match dto {
            OutputLayerDto::Decompiled => OutputLayer::Decompiled,
            OutputLayerDto::Uplc => OutputLayer::Uplc,
            OutputLayerDto::UplcCanonical => OutputLayer::UplcCanonical,
            OutputLayerDto::RawPseudo => OutputLayer::RawPseudo,
            OutputLayerDto::PostPipeline => OutputLayer::PostPipeline,
            OutputLayerDto::PolarityReport => OutputLayer::PolarityReport,
            OutputLayerDto::PrepProfile => OutputLayer::PrepProfile,
        }
    }
}

/// Mirrors `validator_shape::ValidatorShapeOptions` on the wire, so
/// the frontend can drive purpose / split / kind classification.
#[derive(Deserialize, Default)]
pub struct ValidatorShapeOptionsDto {
    #[serde(default)]
    purpose: Option<ValidatorPurposeDto>,
    #[serde(default)]
    split_purposes: SplitPurposesDto,
    #[serde(default)]
    script_kind: Option<ScriptKindDto>,
    #[serde(default)]
    applied_kind: AppliedKindDto,
}

#[derive(Deserialize)]
pub enum ValidatorPurposeDto {
    Spend,
    Mint,
    Withdraw,
    Certificate,
    Vote,
    /// V3-only governance purpose.
    Propose,
}

#[derive(Deserialize, Default)]
pub enum SplitPurposesDto {
    /// Split when V3 dispatch is detected.
    #[default]
    Auto,
    /// Always split when ≥2 purpose arms are found.
    Always,
    /// Never split — keep body intact.
    Never,
}

#[derive(Deserialize)]
pub enum ScriptKindDto {
    /// Force validator-block wrap.
    Validator,
    /// Force `pub fn <name>(...) { ... }` plain-function wrap.
    Plain,
}

#[derive(Deserialize)]
#[serde(untagged)]
pub enum AppliedKindDto {
    Keyword(AppliedKindKeyword),
    /// Explicit count of the LAST N
    /// outer Apply nodes that are runtime args.
    RuntimeCount {
        runtime_count: usize,
    },
}

impl Default for AppliedKindDto {
    fn default() -> Self {
        AppliedKindDto::Keyword(AppliedKindKeyword::Compile)
    }
}

#[derive(Deserialize, Default)]
pub enum AppliedKindKeyword {
    /// Default: all outer Apply are compile-time params.
    #[default]
    Compile,
    /// Runtime args are pre-applied; use runtime_arity from
    /// version+purpose.
    Runtime,
    /// Classify by structural fit. The crate's own default, but this
    /// DTO defaults to `Compile` — which is why `defaults` is built
    /// from this DTO and not from `DecompileOptions::default()`.
    Auto,
}

#[derive(Serialize)]
struct DecompileResponse {
    code: String,
    elapsed_ms: f64,
}

#[derive(Serialize)]
struct ErrorResponse {
    error: String,
    error_code: String,
}

impl From<SimplifyPassesDto> for SimplifyPasses {
    fn from(d: SimplifyPassesDto) -> Self {
        Self {
            simplify_fp_initial: d.simplify_fp_initial,
            simplify_fp_post_readability: d.simplify_fp_post_readability,
            inline_single_use: d.inline_single_use,
            inline_fp: d.inline_fp,
            inline_post_readability: d.inline_post_readability,
            dead_let_elim: d.dead_let_elim,
            collapse_tail_chains: d.collapse_tail_chains,
        }
    }
}

impl From<StructuralRecoveryPassesDto> for StructuralRecoveryPasses {
    fn from(d: StructuralRecoveryPassesDto) -> Self {
        Self {
            recover_let_bound_tag_dispatch: d.recover_let_bound_tag_dispatch,
            simplify_double_rec_fn: d.simplify_double_rec_fn,
            recover_pair_fixpoint: d.recover_pair_fixpoint,
            simplify_z_combinator: d.simplify_z_combinator,
            extract_complex_when_subjects: d.extract_complex_when_subjects,
            resolve_immediate_applications: d.resolve_immediate_applications,
            resolve_data_case: d.resolve_data_case,
        }
    }
}

impl From<ReadabilityPassesDto> for ReadabilityPasses {
    fn from(d: ReadabilityPassesDto) -> Self {
        Self {
            improve_variable_names: d.improve_variable_names,
            flatten_let_chains: d.flatten_let_chains,
            rename_variables: d.rename_variables,
            hoist_local_helpers: d.hoist_local_helpers,
            extract_heavy_constants: d.extract_heavy_constants,
        }
    }
}

impl From<DisplayPolishPassesDto> for DisplayPolishPasses {
    fn from(d: DisplayPolishPassesDto) -> Self {
        Self {
            strip_cosmetic_delays: d.strip_cosmetic_delays,
            cancel_force_delay_vars: d.cancel_force_delay_vars,
            normalize_list_cons_literals: d.normalize_list_cons_literals,
            normalize_display_rewrites: d.normalize_display_rewrites,
            eliminate_cps_selectors: d.eliminate_cps_selectors,
            simplify_boolean_and_identity: d.simplify_boolean_and_identity,
            collapse_eta_pair_selectors: d.collapse_eta_pair_selectors,
            resolve_scott_constructor_lambdas_late: d.resolve_scott_constructor_lambdas_late,
            resolve_data_case_late: d.resolve_data_case_late,
        }
    }
}

impl From<TypePassesDto> for TypePasses {
    fn from(d: TypePassesDto) -> Self {
        Self {
            solve_type_constraints: d.solve_type_constraints,
            propagate_types: d.propagate_types,
            resolve_cardano_field_names: d.resolve_cardano_field_names,
        }
    }
}

impl From<ValidatorShapeOptionsDto> for dehosk::decompile::validator_shape::ValidatorShapeOptions {
    fn from(dto: ValidatorShapeOptionsDto) -> Self {
        use dehosk::decompile::validator_meta::ValidatorPurpose as P;
        use dehosk::decompile::validator_shape::{
            AppliedKind as A, ScriptKind as K, SplitPurposes as S,
        };
        Self {
            purpose: dto.purpose.map(|p| match p {
                ValidatorPurposeDto::Spend => P::Spend,
                ValidatorPurposeDto::Mint => P::Mint,
                ValidatorPurposeDto::Withdraw => P::Withdraw,
                ValidatorPurposeDto::Certificate => P::Certificate,
                ValidatorPurposeDto::Vote => P::Vote,
                ValidatorPurposeDto::Propose => P::Propose,
            }),
            split_purposes: match dto.split_purposes {
                SplitPurposesDto::Auto => S::Auto,
                SplitPurposesDto::Always => S::Always,
                SplitPurposesDto::Never => S::Never,
            },
            script_kind: dto.script_kind.map(|k| match k {
                ScriptKindDto::Validator => K::Validator,
                ScriptKindDto::Plain => K::Plain,
            }),
            applied_kind: match dto.applied_kind {
                AppliedKindDto::Keyword(AppliedKindKeyword::Auto) => A::Auto,
                AppliedKindDto::Keyword(AppliedKindKeyword::Compile) => A::Compile,
                AppliedKindDto::Keyword(AppliedKindKeyword::Runtime) => A::Runtime,
                AppliedKindDto::RuntimeCount { runtime_count } => A::RuntimeCount(runtime_count),
            },
        }
    }
}

impl From<DecompileOptionsDto> for DecompileOptions {
    fn from(dto: DecompileOptionsDto) -> Self {
        Self {
            safe_mode: dto.safe_mode,
            script_version: dto.script_version.map(|v| match v {
                ScriptVersionDto::PlutusV1 => ScriptVersion::PlutusV1,
                ScriptVersionDto::PlutusV2 => ScriptVersion::PlutusV2,
                ScriptVersionDto::PlutusV3 => ScriptVersion::PlutusV3,
            }),
            blueprint_hints: None,
            validator_meta: None,
            use_varkind_recovery: true,
            synthesize_stub_adts: dto.synthesize_stub_adts,
            recognize_prelude_constructors: dto.recognize_prelude_constructors,
            decode_church_to_native: dto.decode_church_to_native,
            strip_all_traces: dto.strip_all_traces,
            strip_plutustx_traces: dto.strip_plutustx_traces,
            expect_or_fail: dto.expect_or_fail,
            compilable_data_access: dto.compilable_data_access,
            ordering_names: dto.ordering_names,
            output_layer: dto.output_layer.into(),
            validator_shape: dto.validator_shape.into(),
            simplify_passes: dto.simplify_passes.into(),
            structural_recovery_passes: dto.structural_recovery_passes.into(),
            readability_passes: dto.readability_passes.into(),
            display_polish_passes: dto.display_polish_passes.into(),
            type_passes: dto.type_passes.into(),
            // The web UI does not expose the polarity-report data-tag oracle.
            oracle_data_args: Vec::new(),
            oracle_tx: None,
            // Diagnostics-only, and this is the SERVED path: it must stay off
            // here. The instruments that read routes build their own options.
            record_lineage_routes: false,
        }
    }
}

/// Map a [`DecompileError`] onto the client-facing `(status, error_code)`
/// pair, by VARIANT.
///
/// The variants already carry `#[diagnostic(code(decompiler::…))]`, and
/// this mirrors those codes rather than re-deriving them by matching
/// substrings of the rendered message — which misfiled every error whose
/// text happened to contain "decode"/"unsupported" (an `UnknownBuiltin`
/// named `decodeUtf8` was reported to the caller as a decode error) and
/// answered `400` even for faults that are ours.
///
/// The 4xx/5xx split is the same question: did the CALLER get something
/// wrong? Bad bytes, a bad blueprint and bad options are 4xx; an internal
/// invariant break or an unhandled UPLC construct is 5xx — those are the
/// ones that must show up in server-error monitoring.
fn classify(err: &DecompileError) -> (StatusCode, &'static str) {
    match err {
        DecompileError::HexError(_) => (StatusCode::BAD_REQUEST, "hex"),
        DecompileError::DecodeError(_) => (StatusCode::BAD_REQUEST, "decode"),
        DecompileError::BlueprintError(_) => (StatusCode::BAD_REQUEST, "blueprint"),
        DecompileError::ValidatorNotFound(_) => (StatusCode::BAD_REQUEST, "validator_not_found"),
        DecompileError::JsonError(_) => (StatusCode::BAD_REQUEST, "json"),
        DecompileError::InvalidOptions(_) => (StatusCode::BAD_REQUEST, "invalid_options"),
        // Not the caller's fault: a construct we cannot yet decompile, an
        // unknown builtin leaking out of a pass, an internal invariant, or
        // local IO. All 5xx so they land in error monitoring.
        DecompileError::Unsupported(_) => (StatusCode::NOT_IMPLEMENTED, "unsupported"),
        DecompileError::UnknownBuiltin { .. } => {
            (StatusCode::INTERNAL_SERVER_ERROR, "unknown_builtin")
        }
        DecompileError::IoError(_) => (StatusCode::INTERNAL_SERVER_ERROR, "io"),
        DecompileError::Internal(_) => (StatusCode::INTERNAL_SERVER_ERROR, "internal"),
    }
}

fn error_response(status: StatusCode, message: String, code: &str) -> Response {
    (
        status,
        Json(ErrorResponse {
            error: message,
            error_code: code.to_string(),
        }),
    )
        .into_response()
}

pub async fn decompile_handler(Json(req): Json<DecompileRequest>) -> Response {
    let hex_code = req
        .hex_code
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect::<String>();

    if hex_code.is_empty() {
        return error_response(
            StatusCode::BAD_REQUEST,
            "No hex code provided".into(),
            "hex",
        );
    }

    if hex_code.len() > 2 * 1024 * 1024 {
        return error_response(
            StatusCode::BAD_REQUEST,
            "Input too large (max 2MB)".into(),
            "hex",
        );
    }

    if !hex_code.chars().all(|c| c.is_ascii_hexdigit()) {
        return error_response(
            StatusCode::BAD_REQUEST,
            "Input contains non-hex characters".into(),
            "hex",
        );
    }

    let options: DecompileOptions = req.options.into();

    let result = tokio::task::spawn_blocking(move || {
        let start = Instant::now();
        let code = decompile(&hex_code, options);
        let elapsed = start.elapsed();
        (code, elapsed)
    })
    .await;

    match result {
        Ok((Ok(code), elapsed)) => Json(DecompileResponse {
            code,
            elapsed_ms: elapsed.as_secs_f64() * 1000.0,
        })
        .into_response(),
        Ok((Err(e), _)) => {
            let (status, code) = classify(&e);
            error_response(status, format!("{e}"), code)
        }
        Err(e) => error_response(
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("Task panicked: {}", e),
            "internal",
        ),
    }
}

/// The option panel, as data: every option the crate exposes, with its
/// prose, its group, and the exact request body that reproduces the
/// server's default behaviour.
///
/// Nothing here is a second copy of the option list —
/// [`OptionCatalogueDto::from_catalogue`] walks the crate's static
/// catalogue, and `defaults` is READ out of the same default request
/// the decompile handler applies.
pub async fn options_handler() -> Json<OptionCatalogueDto> {
    Json(OptionCatalogueDto::from_catalogue(default_options_json()))
}

/// The `options` object a client can POST to get the server's default
/// behaviour, built by reading each catalogue path out of the DEFAULT
/// REQUEST — not out of `DecompileOptions::default()`.
///
/// The difference is load-bearing: the web starts with
/// `synthesize_stub_adts: false` (crate default `true`) and
/// `applied_kind: Compile` (crate default `Auto`), so crate defaults
/// here would change what the panel shows on first load.
fn default_options_json() -> serde_json::Value {
    use dehosk::decompile::options::{ChoicePayload, OptionKind, OptionValue, ui_options};

    let defaults: DecompileOptions = DecompileOptionsDto::default().into();
    let mut root = serde_json::Map::new();

    for entry in ui_options() {
        let value = defaults
            .get(entry.path)
            .expect("every catalogue-exposed option is readable");
        let json = match value {
            OptionValue::Bool(b) => serde_json::Value::Bool(b),
            OptionValue::Choice(None) => serde_json::Value::Null,
            OptionValue::Choice(Some(token)) => serde_json::Value::String(token.to_string()),
            OptionValue::Count(n) => {
                // The count travels inside the object form, under the
                // key the descriptor declares.
                let key = entry
                    .ui()
                    .and_then(|(_, _, kind, _)| match kind {
                        OptionKind::Choice { choices, .. } => choices
                            .iter()
                            .find_map(|c| c.payload.map(|ChoicePayload::Count { key, .. }| key)),
                        OptionKind::Toggle => None,
                    })
                    .expect("a count-valued option declares a count payload");
                serde_json::json!({ key: n })
            }
        };
        insert_at(&mut root, entry.path, json);
    }

    serde_json::Value::Object(root)
}

/// Write `value` at `path` inside `root`, creating intermediate objects.
fn insert_at(
    root: &mut serde_json::Map<String, serde_json::Value>,
    path: &[&str],
    value: serde_json::Value,
) {
    let Some((last, parents)) = path.split_last() else {
        return;
    };
    let mut cursor = root;
    for segment in parents {
        cursor = cursor
            .entry((*segment).to_string())
            .or_insert_with(|| serde_json::Value::Object(serde_json::Map::new()))
            .as_object_mut()
            .expect("catalogue paths never cross a non-object");
    }
    cursor.insert((*last).to_string(), value);
}

pub async fn health_handler() -> Json<serde_json::Value> {
    Json(serde_json::json!({ "status": "ok" }))
}

pub async fn fallback_handler(req: Request) -> Response {
    let path = req.uri().path().trim_start_matches('/');
    let resp = serve_static(path);
    if resp.status() == StatusCode::NOT_FOUND {
        // SPA fallback: serve index.html for non-file routes
        serve_static("index.html")
    } else {
        resp
    }
}

fn serve_static(path: &str) -> Response {
    match FrontendAssets::get(path) {
        Some(file) => {
            let mime = mime_guess::from_path(path).first_or_octet_stream();
            (
                StatusCode::OK,
                [(header::CONTENT_TYPE, mime.as_ref().to_string())],
                file.data.to_vec(),
            )
                .into_response()
        }
        None => (StatusCode::NOT_FOUND, "Not found").into_response(),
    }
}

/// THE REQUEST BODY, and nothing else.
///
/// The crate's catalogue says what the panel may offer; this module
/// says what the wire will carry. These tests pin that the two agree.
///
/// Deliberately the WRONG LAYER for anything about defaults or prose:
/// changing a crate default, a label or a hint must leave every test
/// here green, and changing a serde tag here must break them.
#[cfg(test)]
mod tests {
    use super::*;
    use dehosk::decompile::options::{ChoicePayload, OptionKind, OptionValue, ui_options};

    /// Deserialize an `options` object the way the real handler does.
    fn apply(options: serde_json::Value) -> DecompileOptions {
        let dto: DecompileOptionsDto =
            serde_json::from_value(options).expect("the request body deserializes");
        dto.into()
    }

    /// Build `{"<path>": value}` with the nesting the path describes.
    fn body_at(path: &[&str], value: serde_json::Value) -> serde_json::Value {
        let mut node = value;
        for segment in path.iter().rev() {
            node = serde_json::json!({ *segment: node });
        }
        node
    }

    /// Every state the catalogue offers must survive the round trip
    /// through the real request DTO and land on the real options
    /// struct: an option or choice the crate exposes but the
    /// request body cannot carry fails here.
    #[test]
    fn every_catalogue_choice_round_trips_through_the_request_body() {
        for entry in ui_options() {
            let (label, _, kind, _) = entry.ui().expect("ui_options yields only Ui entries");
            let path = entry.path;
            let mut checked = 0usize;

            let check = |wire: serde_json::Value, want: OptionValue| {
                let landed = apply(body_at(path, wire.clone())).get(path);
                assert_eq!(
                    landed,
                    Some(want),
                    "`{}` ({label}) sent as {wire} did not land as {want:?}",
                    path.join("."),
                );
            };

            match kind {
                OptionKind::Toggle => {
                    for want in [true, false] {
                        check(serde_json::Value::Bool(want), OptionValue::Bool(want));
                        checked += 1;
                    }
                }
                OptionKind::Choice { choices, unset } => {
                    if unset.is_some() {
                        check(serde_json::Value::Null, OptionValue::Choice(None));
                        checked += 1;
                    }
                    for choice in choices {
                        match choice.payload {
                            // The count-carrying choice travels as its
                            // object form, under the declared key.
                            Some(ChoicePayload::Count { key, min, default }) => {
                                for n in [min, default] {
                                    check(serde_json::json!({ key: n }), OptionValue::Count(n));
                                    checked += 1;
                                }
                            }
                            None => {
                                check(
                                    serde_json::Value::String(choice.value.to_string()),
                                    OptionValue::Choice(Some(choice.value)),
                                );
                                checked += 1;
                            }
                        }
                    }
                }
            }
            assert!(checked > 0, "`{}` exercised nothing", path.join("."));
        }
    }

    /// `defaults` is the exact body that reproduces what the server
    /// does with no `options` at all. If it were assembled from crate
    /// defaults instead, first load would render a different panel.
    #[test]
    fn defaults_reproduce_the_servers_own_default_request() {
        let from_catalogue = apply(default_options_json());
        let from_nothing: DecompileOptions = DecompileOptionsDto::default().into();

        for entry in ui_options() {
            assert_eq!(
                from_catalogue.get(entry.path),
                from_nothing.get(entry.path),
                "`{}` differs between the published defaults and an empty request",
                entry.path.join("."),
            );
        }
        // The two web-specific overrides, named, so that dropping one
        // is a test failure and not a quiet change of first-load
        // behaviour.
        assert_eq!(
            from_catalogue.get(&["synthesize_stub_adts"]),
            Some(OptionValue::Bool(false)),
            "the web deliberately starts with stub-ADT synthesis OFF (the crate default is ON)",
        );
        assert_eq!(
            from_catalogue.get(&["validator_shape", "applied_kind"]),
            Some(OptionValue::Choice(Some("Compile"))),
            "the web deliberately starts with Compile (the crate default is Auto)",
        );
    }

    /// The response a client actually receives: every group present,
    /// every option inside exactly one of them, and the count that a
    /// panel is expected to render.
    #[test]
    fn the_catalogue_response_carries_every_option_once() {
        let catalogue = OptionCatalogueDto::from_catalogue(default_options_json());
        let json = serde_json::to_value(&catalogue).expect("the catalogue serializes");

        assert_eq!(json["version"], 1);
        assert_eq!(
            json["groups"].as_array().expect("groups is a list").len(),
            8
        );

        let mut paths = std::collections::BTreeSet::new();
        for group in json["groups"].as_array().expect("groups is a list") {
            assert!(
                !group["options"]
                    .as_array()
                    .expect("options is a list")
                    .is_empty(),
                "group `{}` shipped empty",
                group["title"],
            );
            for option in group["options"].as_array().expect("options is a list") {
                let path: Vec<String> = option["path"]
                    .as_array()
                    .expect("path is a list of segments")
                    .iter()
                    .map(|s| s.as_str().expect("a path segment is a string").to_string())
                    .collect();
                assert!(
                    paths.insert(path.join(".")),
                    "`{}` appears in two groups",
                    path.join("."),
                );
                assert!(
                    !option["summary"]
                        .as_str()
                        .expect("summary is a string")
                        .is_empty(),
                    "`{}` shipped without prose",
                    path.join("."),
                );
            }
        }
        assert_eq!(
            paths.len(),
            46,
            "the panel renders one control per entry; if this changed, the frontend gets the \
             new one for free, but check the request DTO carries it",
        );

        // Every default is addressable by a path the catalogue
        // published, so a client can seed its state from
        // `defaults` alone.
        for path in &paths {
            let mut node = &json["defaults"];
            for segment in path.split('.') {
                node = &node[segment];
            }
            assert!(
                !node.is_null() || path.contains("purpose") || path.contains("script_"),
                "`{path}` has no entry in `defaults`",
            );
        }
    }

    /// A client may omit `options` entirely or send `options: {}`. Both
    /// are "use the defaults", so both must produce the same options —
    /// and the published `defaults` must describe that same request.
    ///
    /// A `#[derive(Default)]` on the DTO would break that by ignoring
    /// the per-field `#[serde(default = "…")]` attributes. Written
    /// against the catalogue, so it covers every option, not one field.
    #[test]
    fn an_absent_options_object_and_an_empty_one_are_the_same_request() {
        let absent: DecompileOptions = DecompileOptionsDto::default().into();
        let empty: DecompileOptions = apply(serde_json::json!({}));
        let published: DecompileOptions = apply(default_options_json());

        for entry in ui_options() {
            let path = entry.path.join(".");
            assert_eq!(
                absent.get(entry.path),
                empty.get(entry.path),
                "`{path}` differs between an omitted `options` key and `options: {{}}` — \
                 `DecompileOptionsDto`'s `Default` has drifted from its serde defaults",
            );
            assert_eq!(
                published.get(entry.path),
                empty.get(entry.path),
                "`{path}` differs between the published `defaults` and `options: {{}}`",
            );
        }

        // The field named explicitly, so a regression is reported as
        // itself rather than as "something differs".
        assert_eq!(
            published.get(&["recognize_prelude_constructors"]),
            Some(OptionValue::Bool(true)),
            "the panel has always shown Recognize Prelude Constructors ON",
        );
    }

    /// `ordering_names` sits in both the crate and the request DTO, so
    /// rendering the panel from the crate publishes it like any other
    /// control — and setting it must take effect.
    #[test]
    fn ordering_names_is_published_and_settable() {
        let catalogue = OptionCatalogueDto::from_catalogue(default_options_json());
        let json = serde_json::to_value(&catalogue).expect("the catalogue serializes");
        let published = json["groups"]
            .as_array()
            .expect("groups is a list")
            .iter()
            .flat_map(|g| g["options"].as_array().expect("options is a list"))
            .any(|o| o["field"] == "ordering_names");
        assert!(published, "ordering_names is still not on the wire");

        let opts = apply(serde_json::json!({ "ordering_names": true }));
        assert_eq!(
            opts.get(&["ordering_names"]),
            Some(OptionValue::Bool(true)),
            "ordering_names is published but does not take effect",
        );
    }

    /// Read a frontend source file that must stay catalogue-driven.
    fn frontend_source(relative: &str) -> String {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("frontend/src")
            .join(relative);
        std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
    }

    /// Whether `needle` occurs in `haystack` on a word boundary, so
    /// that a short tag like `Auto` does not match inside `AutoFoo`.
    fn contains_word(haystack: &str, needle: &str) -> bool {
        let boundary = |c: Option<char>| !matches!(c, Some(c) if c.is_alphanumeric() || c == '_');
        haystack.match_indices(needle).any(|(i, _)| {
            boundary(haystack[..i].chars().next_back())
                && boundary(haystack[i + needle.len()..].chars().next())
        })
    }

    /// The options panel must not restate ANY part of the option list.
    ///
    /// The panel renders its controls by mapping over the catalogue, so
    /// the two agree by construction. What breaks that is hardcoded
    /// option knowledge: a field name that special-cases a control, or
    /// a serde tag written into one `<option>`.
    ///
    /// It checks identity, not prose: every option's path segment
    /// (nested container names and a choice payload's own key included)
    /// and every choice's serde tag. Labels and help text are not
    /// checked — they flow through the panel as data.
    ///
    /// The repository has no frontend test runner, so the check reads
    /// the source text instead of rendering React and counting controls
    /// in a DOM.
    #[test]
    fn the_options_panel_hardcodes_no_option_identity() {
        let mut identifiers: Vec<String> = Vec::new();
        let mut tags: Vec<String> = Vec::new();

        for entry in ui_options() {
            for segment in entry.path {
                identifiers.push((*segment).to_string());
            }
            let (_, _, kind, _) = entry.ui().expect("ui_options yields only Ui entries");
            if let OptionKind::Choice { choices, .. } = kind {
                for choice in choices {
                    tags.push(choice.value.to_string());
                    if let Some(ChoicePayload::Count { key, .. }) = choice.payload {
                        identifiers.push(key.to_string());
                    }
                }
            }
        }

        // Path segments are checked only when they are unambiguous
        // (snake_case). A bare word like `purpose` is ordinary English
        // and appears legitimately in unrelated frontend code.
        identifiers.retain(|i| i.contains('_'));
        identifiers.sort();
        identifiers.dedup();
        tags.sort();
        tags.dedup();

        assert!(
            identifiers.len() >= 40 && tags.len() >= 20,
            "the catalogue looks empty ({} identifiers, {} tags) — this test would pass vacuously",
            identifiers.len(),
            tags.len(),
        );

        for file in ["components/OptionsPanel.tsx", "lib/api.ts"] {
            let source = frontend_source(file);

            let leaked: Vec<&String> = identifiers
                .iter()
                .filter(|name| contains_word(&source, name))
                .collect();
            assert!(
                leaked.is_empty(),
                "{file} names option fields {leaked:?} — it must reach into the options \
                 object only through a descriptor's `path`, never by writing a field name",
            );

            let quoted: Vec<&String> = tags
                .iter()
                .filter(|tag| {
                    source.contains(&format!("\"{tag}\"")) || source.contains(&format!("'{tag}'"))
                })
                .collect();
            assert!(
                quoted.is_empty(),
                "{file} hardcodes the choice tags {quoted:?} — a choice must POST the \
                 catalogue's own `value`, never a tag written in TypeScript",
            );
        }
    }

    /// The client-facing classification must come from the error VARIANT.
    ///
    /// Filing by message substring would treat any error whose text contains
    /// "decode" / "unsupported" / "hex" as a caller mistake — including
    /// internal faults — and answer 400 for all of them.
    #[test]
    fn errors_are_classified_by_variant_not_by_message_text() {
        use dehosk::error::DecompileError;

        let cases: &[(DecompileError, StatusCode, &str)] = &[
            // The caller's bytes are wrong: 4xx.
            (
                DecompileError::DecodeError("bad Flat".into()),
                StatusCode::BAD_REQUEST,
                "decode",
            ),
            (
                DecompileError::InvalidOptions("pass A needs pass B".into()),
                StatusCode::BAD_REQUEST,
                "invalid_options",
            ),
            // Ours: an unknown builtin leaked out of a pass. Its NAME
            // contains "decode", which is exactly what used to file it as
            // a caller-side decode error.
            (
                DecompileError::UnknownBuiltin {
                    name: "decodeUtf8".into(),
                    stage: "pipeline_seed".into(),
                },
                StatusCode::INTERNAL_SERVER_ERROR,
                "unknown_builtin",
            ),
            // Ours: an internal invariant. Its message contains
            // "unsupported", which used to file it as `unsupported`.
            (
                DecompileError::Internal("unsupported shape escaped stub_adt".into()),
                StatusCode::INTERNAL_SERVER_ERROR,
                "internal",
            ),
            // A construct we cannot decompile yet — not a bad request.
            (
                DecompileError::Unsupported("BLS12_381 pairing".into()),
                StatusCode::NOT_IMPLEMENTED,
                "unsupported",
            ),
        ];

        for (err, want_status, want_code) in cases {
            let (status, code) = classify(err);
            assert_eq!(
                (status, code),
                (*want_status, *want_code),
                "{err} must classify as ({want_status}, {want_code})"
            );
        }
    }

    /// Only faults that are OURS may be 5xx, and every fault that is ours
    /// must be — that is what makes server-error monitoring meaningful.
    #[test]
    fn every_error_variant_has_a_side() {
        use dehosk::error::DecompileError;

        let ours = [
            DecompileError::Unsupported(String::new()),
            DecompileError::UnknownBuiltin {
                name: String::new(),
                stage: String::new(),
            },
            DecompileError::Internal(String::new()),
        ];
        for err in &ours {
            assert!(
                classify(err).0.is_server_error(),
                "{err:?} is our fault and must be 5xx"
            );
        }

        let theirs = [
            DecompileError::DecodeError(String::new()),
            DecompileError::BlueprintError(String::new()),
            DecompileError::ValidatorNotFound(String::new()),
            DecompileError::InvalidOptions(String::new()),
        ];
        for err in &theirs {
            assert!(
                classify(err).0.is_client_error(),
                "{err:?} is the caller's mistake and must be 4xx"
            );
        }
    }
}
