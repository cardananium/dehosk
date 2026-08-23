//! Render the validator-wrap text from a `ValidatorPlan`.
//!
//! `WrapForm` selects the wrap path:
//! `BlueprintBlock`, `PurposeBlock` →
//!   `validator_meta::wrap_render_with_validator_block_with_bodies`
//!   (`PurposeBlock` synthesizes the `ValidatorMeta` from its entries).
//! `Flat` → `wrap_render_with_flat_validator_using_purposes`.
//! `PlainFn` → rewrite the `fn decompiled(..)` header.
//!
//! Diagnostics are prepended as `// Warning:` / `// Info:` comments
//! at the top of the output.

use crate::decompile::validator_meta::{
    ValidatorMeta, split_validator_entry_block, wrap_render_with_flat_validator_using_purposes,
};

use super::{DiagnosticKind, DiagnosticSeverity, ValidatorDiagnostic, ValidatorPlan, WrapForm};

/// Test-only: production wraps through
/// `wrap_rendered_separated_with_bodies`.
/// Render the validator wrap from a plan, returning the diagnostic
/// header and the wrap body as separate strings so the caller can
/// place diagnostics ABOVE the (potentially large) stub-ADT prefix.
/// Use [`wrap_rendered`] for the concatenated form.
#[cfg(test)]
pub(crate) fn wrap_rendered_separated(rendered: &str, plan: &ValidatorPlan) -> (String, String) {
    wrap_rendered_separated_with_bodies(rendered, plan, None)
}

/// `wrap_rendered_separated` with optional pre-rendered per-purpose handler
/// bodies (the AST-level split path).
pub(crate) fn wrap_rendered_separated_with_bodies(
    rendered: &str,
    plan: &ValidatorPlan,
    purpose_bodies: Option<&[(crate::decompile::ValidatorPurpose, String)]>,
) -> (String, String) {
    let (diag, body) = wrap_rendered_inner(rendered, plan, purpose_bodies);
    (diag, body)
}

/// Render the validator wrap from a plan as a single
/// `{diagnostics}{body}` string.
///
/// Unused today: every wrap goes through
/// `wrap_rendered_separated_with_bodies`, which additionally takes the
/// per-purpose handler bodies. Kept as the single-purpose reference
/// shape the `_separated*` pair specialises.
#[allow(dead_code)]
pub(crate) fn wrap_rendered(rendered: &str, plan: &ValidatorPlan) -> String {
    let (diag, body) = wrap_rendered_inner(rendered, plan, None);
    format!("{diag}{body}")
}

fn wrap_rendered_inner(
    rendered: &str,
    plan: &ValidatorPlan,
    purpose_bodies: Option<&[(crate::decompile::ValidatorPurpose, String)]>,
) -> (String, String) {
    // Most diagnostics are actionable only when the renderer
    // emitted an `fn decompiled(...)` shape to wrap; the identity
    // term `fn(x) { x }` skips the wrap and gets no warnings.
    let wrap_will_apply = split_validator_entry_block(rendered).is_some();

    // Upgrade `PlainFn` using the rendered arg count, for V1/V2 with
    // no pinned purpose:
    // 3 args → `PurposeBlock(Spend)` — the only V1/V2 3-arg convention.
    // 2 args → `Flat { inferred_purposes: [] }` — non-spend is ambiguous
    //         between mint/withdraw/certificate, and `validator decompiled(
    //         redeemer, script_context)` is more honest than
    //         `pub fn`: the script IS a validator, only the purpose
    //         is unrecoverable.
    let rendered_args = split_validator_entry_block(rendered)
        .map(|e| count_top_level_args(e.args))
        .unwrap_or(0);
    let is_v1_v2_no_explicit_purpose = matches!(plan.wrap_form, WrapForm::PlainFn)
        && !plan.purpose_was_explicit
        && matches!(
            plan.script_version,
            Some(crate::decompile::ScriptVersion::PlutusV1)
                | Some(crate::decompile::ScriptVersion::PlutusV2)
        );
    let effective_wrap_form = if is_v1_v2_no_explicit_purpose && rendered_args == 3 {
        WrapForm::PurposeBlock {
            entries: vec![crate::decompile::validator_shape::ValidatorEntry {
                purpose: crate::decompile::ValidatorPurpose::Spend,
                params: Vec::new(),
            }],
        }
    } else if is_v1_v2_no_explicit_purpose && rendered_args == 2 {
        WrapForm::Flat {
            inferred_purposes: Vec::new(),
        }
    } else {
        plan.wrap_form.clone()
    };

    let body = match &effective_wrap_form {
        WrapForm::BlueprintBlock(meta) => {
            crate::decompile::validator_meta::wrap_render_with_validator_block_with_bodies(
                rendered,
                meta,
                purpose_bodies,
            )
        }
        WrapForm::PurposeBlock { entries } => {
            // Synthesize a `ValidatorMeta` from the entries and
            // reuse the block wrap; `render_validator_block`'s
            // `has_else` check adds the `else(_) { fail }` tail.
            let synthesized = ValidatorMeta {
                name: plan.name.clone(),
                entries: entries.clone(),
            };
            crate::decompile::validator_meta::wrap_render_with_validator_block_with_bodies(
                rendered,
                &synthesized,
                purpose_bodies,
            )
        }
        WrapForm::Flat { inferred_purposes } => {
            // Pass AST-derived purposes rather than letting the
            // wrap re-derive them from the rendered string via
            // `infer_purposes_from_body`.
            wrap_render_with_flat_validator_using_purposes(rendered, &plan.name, inferred_purposes)
        }
        WrapForm::PlainFn => render_plain_fn(rendered, &plan.name),
    };

    // Structural diagnostics (unknown Plutus version) surface even
    // when the wrap didn't apply; purpose-ambiguity warnings need
    // a real validator block — see `is_diagnostic_universal`.
    if plan.diagnostics.is_empty() {
        return (String::new(), body);
    }
    // Refine V1/V2 purpose ambiguity from the rendered arg count:
    // the `fn decompiled(a, b, c)` shape is the strongest
    // runtime-arity signal, since it survives the simplifier and
    // includes any synthesized wrapper lambdas.
    let rendered_arg_count = split_validator_entry_block(rendered)
        .map(|e| count_top_level_args(e.args))
        .unwrap_or(0);
    let mut diag = String::new();
    for d in &plan.diagnostics {
        if !(wrap_will_apply || is_diagnostic_universal(d)) {
            continue;
        }
        // Suppress the non-spend ambiguity warning when the renderer
        // emitted a 3-arg validator (spend is the only V1/V2 calling
        // convention with 3 runtime args).
        if matches!(d.kind, DiagnosticKind::V1V2NonSpendPurposeAmbiguous) && rendered_arg_count == 3
        {
            continue;
        }
        diag.push_str(&format_diagnostic_comment(d));
        diag.push('\n');
    }
    (diag, body)
}

/// Count top-level args in `fn decompiled(<args>)`, ignoring
/// bracket-nested commas — the renderer emits no nested-comma type
/// annotations (`Pair<Int, Int>`) today, but this stays correct.
fn count_top_level_args(args: &str) -> usize {
    let trimmed = args.trim();
    if trimmed.is_empty() {
        return 0;
    }
    let mut depth_paren: i32 = 0;
    let mut depth_angle: i32 = 0;
    let mut depth_bracket: i32 = 0;
    let mut count: usize = 1;
    for c in trimmed.chars() {
        match c {
            '(' => depth_paren += 1,
            ')' => depth_paren = depth_paren.saturating_sub(1),
            '<' => depth_angle += 1,
            '>' => depth_angle = depth_angle.saturating_sub(1),
            '[' => depth_bracket += 1,
            ']' => depth_bracket = depth_bracket.saturating_sub(1),
            ',' if depth_paren == 0 && depth_angle == 0 && depth_bracket == 0 => {
                count += 1;
            }
            _ => {}
        }
    }
    count
}

/// Whether a diagnostic is actionable even without a validator
/// wrap. `UnknownPlutusVersion` and `OuterApplyLabeled` describe
/// the program itself; purpose/shape diagnostics need a real
/// validator block.
///
/// Gating on `DiagnosticKind` rather than message text keeps
/// rewording from silently flipping the classification.
fn is_diagnostic_universal(d: &ValidatorDiagnostic) -> bool {
    matches!(
        d.kind,
        DiagnosticKind::UnknownPlutusVersion | DiagnosticKind::OuterApplyLabeled
    )
}

/// Rewrite the renderer's `fn decompiled(...)` header to
/// `pub fn <name>(...)`, so plain scripts (library functions or
/// debug snapshots) render as a function, not a validator wrap.
fn render_plain_fn(rendered: &str, name: &str) -> String {
    let needle = "fn decompiled(";
    if let Some(start) = rendered.find(needle) {
        let mut out = String::with_capacity(rendered.len() + 8);
        out.push_str(&rendered[..start]);
        out.push_str("pub fn ");
        out.push_str(name);
        out.push('(');
        out.push_str(&rendered[start + needle.len()..]);
        out
    } else {
        // No `fn decompiled(` shape — return the renderer's output
        // unchanged (covers identity-term cases and bare lambdas).
        rendered.to_string()
    }
}

/// Render a diagnostic as a `// <severity>: <message>` comment line.
fn format_diagnostic_comment(d: &ValidatorDiagnostic) -> String {
    let tag = match d.severity {
        DiagnosticSeverity::Info => "Info",
        DiagnosticSeverity::Warning => "Warning",
    };
    format!("// {tag}: {}", d.message)
}
