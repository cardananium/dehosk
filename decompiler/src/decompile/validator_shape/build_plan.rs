//! Resolve `ValidatorPlan` from analyzed inputs.
//!
//! Priority order (highest wins):
//! 1. Blueprint metadata present → `WrapForm::BlueprintBlock`.
//! 2. Explicit `--purpose X` → single-entry `WrapForm::PurposeBlock`.
//! 3. V3 multi-purpose dispatch detected + `split_purposes != Never`
//!    → `WrapForm::PurposeBlock` with one entry per detected purpose.
//!    3b. V3 single purpose auto-detected from the entry spine →
//!    single-entry `WrapForm::PurposeBlock`.
//! 4. Otherwise → `WrapForm::Flat` with optional inferred-purposes
//!    diagnostic.
//!
//! Ambiguous cases (V1/V2 non-spend without `--purpose`, V3 single
//! without `--purpose`) emit a `Warning` diagnostic.

use super::{
    AppliedKind, DiagnosticKind, DiagnosticSeverity, PlanInput, PurposeDispatch, ScriptKind,
    SplitPurposes, ValidatorDiagnostic, ValidatorPlan, WrapForm,
};
use crate::decompile::ScriptVersion;
use crate::decompile::validator_meta::{ValidatorEntry, ValidatorPurpose};

/// Classify the script as a Cardano validator or a plain Plutus
/// script. Used when the caller left `options.script_kind` unset.
///
/// Heuristic:
/// V3 multi-purpose dispatch detected → `Validator` (strong signal).
/// Lambda arity (after applied-param peel) 1, 2, or 3 → `Validator`
///   (V3 / V1-V2 non-spend / V1-V2 spend calling conventions).
/// Lambda arity 0 or ≥4 → `Plain` (fits no validator calling
///   convention; likely a library function or constant).
///
/// Ambiguous cases bias toward `Validator`, since downstream
/// tooling assumes validators; `--script-kind plain` forces the
/// other way.
pub(crate) fn classify_script_kind(input: &PlanInput<'_>) -> ScriptKind {
    if matches!(input.dispatch, PurposeDispatch::MultiPurpose { .. }) {
        return ScriptKind::Validator;
    }
    // Over-application (`pre_applied_runtime_args > 0`) means the
    // raw Apply chain took more args than the inner Lambda chain
    // exposed — typically a validator with its runtime args
    // pre-applied. Classify `Validator` rather than let the
    // negative `effective_lambdas` saturate to 0 and mis-classify
    // as `Plain`.
    if input.outer.pre_applied_runtime_args > 0 {
        return ScriptKind::Validator;
    }
    match input.outer.truly_unapplied() {
        1..=3 => ScriptKind::Validator,
        _ => ScriptKind::Plain,
    }
}

/// Runtime arity for a (version, purpose) pair. V3: 1. V1/V2
/// spend: 3. V1/V2 non-spend: 2.
///
/// `(V1|V2, None)` defaults to 2, not 1: V1/V2 validators always
/// take at least redeemer + script_context. The 1-arity fallback
/// fires only for unknown versions.
pub(crate) fn runtime_arity_for(
    version: Option<ScriptVersion>,
    purpose: Option<ValidatorPurpose>,
) -> usize {
    match (version, purpose) {
        (Some(ScriptVersion::PlutusV3), _) => 1,
        (
            Some(ScriptVersion::PlutusV1) | Some(ScriptVersion::PlutusV2),
            Some(ValidatorPurpose::Spend),
        ) => 3,
        (Some(ScriptVersion::PlutusV1) | Some(ScriptVersion::PlutusV2), Some(_)) => 2,
        // Unknown purpose: non-spend baseline.
        // `--purpose spend` selects the 3-arg reading.
        (Some(ScriptVersion::PlutusV1) | Some(ScriptVersion::PlutusV2), None) => 2,
        // Unknown version: default to 1 (V3-style) — least invasive.
        _ => 1,
    }
}

pub(crate) fn build_plan_impl(input: PlanInput<'_>) -> ValidatorPlan {
    let mut diagnostics: Vec<ValidatorDiagnostic> = Vec::new();
    let script_version = input.script_version;
    let purpose_was_explicit = input.options.purpose.is_some();

    let runtime_arity = runtime_arity_for(input.script_version, input.options.purpose);
    let runtime_count = super::param_surface::resolve_runtime_count(
        input.options.applied_kind,
        input.outer,
        runtime_arity,
    );
    let applied_total = input.outer.applied_params.len();
    if runtime_count > 0 {
        let source_tag = match input.options.applied_kind {
            AppliedKind::Auto => "auto-classified (applied + lambda == runtime arity)",
            _ => "--applied-as",
        };
        let msg = if runtime_count == applied_total {
            format!(
                "All {applied_total} outer Apply node(s) labeled as pre-applied runtime args ({source_tag})."
            )
        } else {
            format!(
                "Split: last {runtime_count} of {applied_total} outer Apply node(s) labeled as runtime args; rest as compile-time params ({source_tag})."
            )
        };
        diagnostics.push(ValidatorDiagnostic {
            severity: DiagnosticSeverity::Info,
            kind: DiagnosticKind::OuterApplyLabeled,
            message: msg,
        });
    }

    if input.version_inferred_ambiguous {
        diagnostics.push(ValidatorDiagnostic {
            severity: DiagnosticSeverity::Info,
            kind: DiagnosticKind::V1V2VersionAssumed,
            message:
                "Plutus version assumed V2: the (1, 0) UPLC header is shared by V1 and V2 and no V2-only builtins were found. Pass --script-version v1|v2 to pin it (affects context field naming)."
                    .to_string(),
        });
    }

    // `--script-kind plain` (or an unoverridden Plain
    // classification) skips all validator-specific work and emits a
    // plain-fn wrap.
    //
    // Exception: an explicit `--purpose <X>` outranks it — mixed
    // curried/uncurried entry lambdas and pre-applied runtime args
    // fool the structural classifier into Plain.
    let user_forced_purpose = input.options.purpose.is_some();
    // An auto-detected single purpose bypasses Plain the same way: a
    // dominating `script_info` assertion on the prepared entry spine
    // is stronger evidence than the arity heuristic, which deep
    // helper-hoisting nesting fools by inflating the lambda chain.
    let auto_detected_purpose = input.detected_single_purpose.is_some();
    let kind = input
        .options
        .script_kind
        .unwrap_or_else(|| classify_script_kind(&input));
    if matches!(kind, ScriptKind::Plain) && !user_forced_purpose && !auto_detected_purpose {
        return ValidatorPlan {
            name: input
                .meta
                .map(|m| m.name.clone())
                .unwrap_or_else(|| "decompiled".to_string()),
            wrap_form: WrapForm::PlainFn,
            script_version,
            purpose_was_explicit,
            diagnostics,
        };
    }

    // 1. Blueprint metadata wins.
    if let Some(meta) = input.meta {
        return ValidatorPlan {
            name: meta.name.clone(),
            wrap_form: WrapForm::BlueprintBlock(meta.clone()),
            script_version,
            purpose_was_explicit,
            diagnostics,
        };
    }

    let name = "decompiled".to_string();

    // 2. Explicit --purpose forces a single-purpose interpretation.
    if let Some(purpose) = input.options.purpose {
        return ValidatorPlan {
            name,
            wrap_form: WrapForm::PurposeBlock {
                entries: vec![ValidatorEntry {
                    purpose,
                    params: Vec::new(),
                }],
            },
            script_version,
            purpose_was_explicit,
            diagnostics,
        };
    }

    // 3. V3 multi-purpose dispatch detected. Only V3 auto-splits:
    // there is no V1/V2 multivalidator detection.
    if let PurposeDispatch::MultiPurpose { purposes } = input.dispatch {
        let version_supports_split =
            matches!(input.script_version, Some(ScriptVersion::PlutusV3) | None);
        let allowed = match input.options.split_purposes {
            SplitPurposes::Never => false,
            SplitPurposes::Always | SplitPurposes::Auto => version_supports_split,
        };
        if allowed && purposes.len() >= 2 {
            let entries: Vec<ValidatorEntry> = purposes
                .iter()
                .map(|p| ValidatorEntry {
                    purpose: *p,
                    params: Vec::new(),
                })
                .collect();
            return ValidatorPlan {
                name,
                wrap_form: WrapForm::PurposeBlock { entries },
                script_version,
                purpose_was_explicit,
                diagnostics,
            };
        }
        // When the version gate refuses `--split-purposes always`,
        // warn rather than silently drop to flat-wrap.
        if matches!(input.options.split_purposes, SplitPurposes::Always)
            && !version_supports_split
            && purposes.len() >= 2
        {
            diagnostics.push(ValidatorDiagnostic {
                severity: DiagnosticSeverity::Warning,
                kind: DiagnosticKind::SplitAlwaysIgnoredForV1V2,
                message:
                    "--split-purposes=always was requested but the inferred V1/V2 version doesn't support multi-purpose splits in this decompiler yet. Falling back to flat-wrap."
                        .to_string(),
            });
        }
    }

    // 3b. V3 single purpose auto-detected from the prepared entry
    // spine — a dominating `script_info` assertion with one live
    // purpose arm (`detect_single_purpose_v3`). Same plan shape as an
    // explicit `--purpose`, plus an Info line. Ordered after the
    // multi-purpose split, which is the stronger evidence.
    if let Some(purpose) = input.detected_single_purpose {
        diagnostics.push(ValidatorDiagnostic {
            severity: DiagnosticSeverity::Info,
            kind: DiagnosticKind::AutoDetectedSinglePurpose,
            message: format!(
                "V3 single-purpose: `{}` auto-detected from the script_info assertion on the entry spine.",
                purpose.keyword()
            ),
        });
        return ValidatorPlan {
            name,
            wrap_form: WrapForm::PurposeBlock {
                entries: vec![ValidatorEntry {
                    purpose,
                    params: Vec::new(),
                }],
            },
            script_version,
            purpose_was_explicit,
            diagnostics,
        };
    }

    // 4. Flat fallback. Compute inferred purposes (for the comment
    // header) from the dispatch detection regardless of split policy.
    let inferred_purposes = match input.dispatch {
        PurposeDispatch::MultiPurpose { purposes } => purposes.clone(),
        PurposeDispatch::None => Vec::new(),
    };

    // Emit ambiguity diagnostics only when the shape is genuinely
    // ambiguous and a flag can resolve it. The `outer` info skips
    // the V1/V2 false positive: a 3-arg lambda is unambiguously
    // spend.
    if input.options.purpose.is_none() && inferred_purposes.is_empty() {
        match input.script_version {
            Some(ScriptVersion::PlutusV1) | Some(ScriptVersion::PlutusV2) => {
                // Compile-param count is invisible from bytecode,
                // so only an unapplied script with exactly 3 lambdas
                // (datum, redeemer, ctx) is provably V1/V2 spend.
                // Any other shape — compile-applied, 2-lambda
                // non-spend, 4+-lambda parameterised — leaves the
                // purpose ambiguous and warns.
                let bare_spend = input.outer.applied_params.is_empty()
                    && input.outer.lambda_chain_length == 3
                    && input.outer.pre_applied_runtime_args == 0;
                if !bare_spend {
                    diagnostics.push(ValidatorDiagnostic {
                        severity: DiagnosticSeverity::Warning,
                        kind: DiagnosticKind::V1V2NonSpendPurposeAmbiguous,
                        message:
                            "V1/V2 non-spend purpose is ambiguous from bytecode; pass --purpose to specify (mint|withdraw|certificate)"
                                .to_string(),
                    });
                }
            }
            Some(ScriptVersion::PlutusV3) => {
                // V3 without a recognised dispatch. Before claiming the
                // purpose is unrecoverable, say what the body actually
                // tests: a PlutusTx-compiled validator discriminates by
                // ScriptInfo field count first and tag second, which the
                // dispatch detector does not read, but the tags name the
                // purposes outright.
                let observed = &input.observed_script_info_purposes;
                let message = match observed.len() {
                    0 => "V3 single-purpose: purpose name not recoverable from bytecode. Pass --purpose to specify."
                        .to_string(),
                    1 => format!(
                        "V3 purpose `{}` is the only ScriptInfo tag the body matches, but no dispatch shape was recognised — the wrap stays flat. Pass --purpose to render it as a handler.",
                        observed[0].keyword()
                    ),
                    _ => format!(
                        "V3 multi-purpose: the body matches ScriptInfo tags for {} — no dispatch shape was recognised, so the wrap stays flat. Pass --purpose to render one of them as a handler.",
                        observed
                            .iter()
                            .map(|p| format!("`{}`", p.keyword()))
                            .collect::<Vec<_>>()
                            .join(" and ")
                    ),
                };
                diagnostics.push(ValidatorDiagnostic {
                    severity: DiagnosticSeverity::Warning,
                    kind: DiagnosticKind::V3SinglePurposeAmbiguous,
                    message,
                });
            }
            None => {
                // The flag is `--script-version`, not `--plutus-version`;
                // the wrong name sends users into a clap parse error.
                diagnostics.push(ValidatorDiagnostic {
                    severity: DiagnosticSeverity::Warning,
                    kind: DiagnosticKind::UnknownPlutusVersion,
                    message:
                        "Plutus version could not be inferred. Pass --script-version to specify."
                            .to_string(),
                });
            }
        }
    }

    ValidatorPlan {
        name,
        wrap_form: WrapForm::Flat { inferred_purposes },
        script_version,
        purpose_was_explicit,
        diagnostics,
    }
}
