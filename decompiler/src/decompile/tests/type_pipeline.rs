//! Typed-output pipeline contract regression tests.
//!
//! The typed-output contract:
//!   1. typed public render surfaces at least one type annotation when
//!      `infer_types: true` is requested;
//!   2. typed debug render surfaces the same annotations from the same
//!      source;
//!   3. post-MIR ID rewrites mean a frozen MIR `TypeEnvironment` can
//!      never resolve every pseudo-AST `VarId` the typed-output path
//!      walks, so a pseudo-AST keyed `FinalTypeTable` is required;
//!   4. `PipelineOutput.final_types` is the consumer-facing handle,
//!      frozen before hand-off whether or not the solver runs.

#![cfg(test)]

use crate::debug::decompile_program_debug_with_options;
use crate::decompile::blueprint_registry::BlueprintHintRegistry;
use crate::decompile::pipeline::run_pipeline_with_artifacts;
use crate::decompile::tests::MIR_V3_SMOKE_HEX;
use crate::decompile::{
    decode_hex_to_program, decompile_program, render_decompiled_expr_with_registry_and_final_types,
};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, PseudoType};
use crate::{DecompileOptions, ScriptVersion};
use uplc::ast::{NamedDeBruijn, Program};

#[test]
fn tp1_decompile_program_renders_type_annotation_when_infer_types_enabled() {
    let program: Program<NamedDeBruijn> =
        decode_hex_to_program(MIR_V3_SMOKE_HEX).expect("expected valid V3 smoke program");
    let mut opts = DecompileOptions::default();
    opts.script_version = Some(ScriptVersion::PlutusV3);
    opts.type_passes = crate::decompile::TypePasses::all_on();

    let rendered = decompile_program(&program, opts).expect("typed decompile should succeed");

    let candidate_markers = [
        ": Int",
        ": ByteArray",
        ": Bool",
        ": Data",
        ": ScriptContext",
        ": ScriptInfo",
        ": TxInfo",
    ];
    let saw_marker = candidate_markers.iter().any(|m| rendered.contains(m));

    assert!(
        saw_marker,
        "TP5 contract: typed public render must surface at least one let-binding type \
         annotation when `infer_types: true`. None of {candidate_markers:?} were found in \
         the rendered output:\n{rendered}"
    );
}

#[test]
fn tp1_debug_render_renders_type_annotation_when_infer_types_enabled() {
    let program: Program<NamedDeBruijn> =
        decode_hex_to_program(MIR_V3_SMOKE_HEX).expect("expected valid V3 smoke program");
    let mut opts = DecompileOptions::default();
    opts.script_version = Some(ScriptVersion::PlutusV3);
    opts.type_passes = crate::decompile::TypePasses::all_on();

    let bundle = decompile_program_debug_with_options(&program, opts)
        .expect("typed debug decompile should succeed");

    let candidate_markers = [
        ": Int",
        ": ByteArray",
        ": Bool",
        ": Data",
        ": ScriptContext",
        ": ScriptInfo",
        ": TxInfo",
    ];
    let saw_marker = candidate_markers.iter().any(|m| bundle.code.contains(m));

    assert!(
        saw_marker,
        "TP5 contract: debug bundle render must consume the same final solved type source \
         as the public render and surface at least one let-binding type annotation. None of \
         {candidate_markers:?} were found in the rendered code:\n{}",
        bundle.code
    );
}

#[test]
fn tp1_post_mir_rewritten_var_needs_final_ast_keyed_type_table() {
    use crate::decompile::final_type_table::FinalTypeTable;
    use crate::decompile::mid::type_env::TypeEnvironment;
    use crate::pseudo::var_id::VarId;
    use std::rc::Rc;

    let mut env = TypeEnvironment::new();
    let unrelated_mir_id = VarId::fresh_binding();
    env.bind_var(unrelated_mir_id, Rc::new(PseudoType::Int));
    env.freeze();

    let post_mir_id = VarId::fresh_binding();
    let expr = PseudoExpr::let_bind_with_id(
        "post_mir_rewritten",
        post_mir_id,
        PseudoExpr::Int(1.into()),
        PseudoExpr::var_with_id("post_mir_rewritten", post_mir_id),
    );

    // There is no env-only render path: a MIR `TypeEnvironment` alone
    // cannot resolve a post-MIR rewritten id. The `FinalTypeTable`
    // check below is the contract.
    let _ = &env; // constructed above, never consulted by render

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(post_mir_id, Rc::new(PseudoType::Int));
    final_types.freeze();
    let registry = Rc::new(BlueprintHintRegistry::default());
    let (rendered, _spans) = render_decompiled_expr_with_registry_and_final_types(
        &expr,
        true,
        &registry,
        &Rc::new(final_types),
        &crate::decompile::RenderCtx::default(),
    );

    assert!(
        rendered.contains("let post_mir_rewritten: Int"),
        "TP2-TP5 contract: a pseudo-AST keyed type table must surface the type of a \
         post-MIR rewritten Var even when the frozen MIR env cannot resolve its id. \
         Got rendered output:\n{rendered}"
    );
}

#[test]
fn tp4_final_types_handle_populated_when_infer_types_enabled() {
    let program: Program<NamedDeBruijn> =
        decode_hex_to_program(MIR_V3_SMOKE_HEX).expect("valid V3 smoke program");
    let mut opts = DecompileOptions::default();
    opts.script_version = Some(ScriptVersion::PlutusV3);
    opts.type_passes = crate::decompile::TypePasses::all_on();

    let pipeline_output = run_pipeline_with_artifacts(&program, opts, |_, _| {})
        .expect("pipeline should succeed with infer_types=true");

    assert!(
        pipeline_output.final_types.is_frozen(),
        "TP4 contract: `PipelineOutput.final_types` must be frozen before \
         being handed to consumers so late mutation cannot silently change \
         typed-output source of truth."
    );
    assert!(
        pipeline_output.final_types.var_type_count() > 0,
        "TP4 contract: with `infer_types=true`, the latest solver must emit \
         at least one declaration type into the output type table (got empty). \
         If this trips, either the solver stopped populating the table \
         (regress on TP3) or threading is wired to a stage that never runs."
    );
}

#[test]
fn tp4_final_types_handle_empty_when_infer_types_disabled() {
    let program: Program<NamedDeBruijn> =
        decode_hex_to_program(MIR_V3_SMOKE_HEX).expect("valid V3 smoke program");
    let mut opts = DecompileOptions::default();
    opts.script_version = Some(ScriptVersion::PlutusV3);
    opts.type_passes = crate::decompile::TypePasses::all_off();

    let pipeline_output = run_pipeline_with_artifacts(&program, opts, |_, _| {})
        .expect("pipeline should succeed with infer_types=false");

    assert!(
        pipeline_output.final_types.is_frozen(),
        "TP4 contract: final_types must always be frozen, even when no \
         solve ran."
    );
    assert_eq!(
        pipeline_output.final_types.var_type_count(),
        0,
        "TP4 contract: with `infer_types=false` no solver runs; final_types \
         must be empty."
    );
}

/// `let X: Data = ...` and `let X: Unknown` (both render as `: Data`)
/// are the language default and add no information, so the renderer
/// suppresses them. Refined types (`ByteArray`, `Int`, named types,
/// `List<...>`, ...) must still render their annotation.
#[test]
fn p6_3_resolve_type_suppresses_bare_data_annotation() {
    use crate::decompile::final_type_table::FinalTypeTable;
    use crate::pseudo::var_id::VarId;
    use std::rc::Rc;

    let data_id = VarId::fresh_binding();
    let unknown_id = VarId::fresh_binding();
    let int_id = VarId::fresh_binding();
    let bytearray_id = VarId::fresh_binding();

    // Four nested lets — bare Data, Unknown (also displays as "Data"), Int,
    // ByteArray — in a unit body. The Int and ByteArray annotations are kept,
    // Data and Unknown suppressed.
    let expr = PseudoExpr::let_bind_with_id(
        "o",
        data_id,
        PseudoExpr::var_with_id("payload", VarId::fresh_binding()),
        PseudoExpr::let_bind_with_id(
            "u",
            unknown_id,
            PseudoExpr::var_with_id("payload", VarId::fresh_binding()),
            PseudoExpr::let_bind_with_id(
                "n",
                int_id,
                PseudoExpr::Int(1.into()),
                PseudoExpr::let_bind_with_id(
                    "bytes_2",
                    bytearray_id,
                    PseudoExpr::var_with_id("blob", VarId::fresh_binding()),
                    PseudoExpr::Unit,
                ),
            ),
        ),
    );

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(data_id, Rc::new(PseudoType::Data));
    final_types.bind_var(unknown_id, Rc::new(PseudoType::Unknown));
    final_types.bind_var(int_id, Rc::new(PseudoType::Int));
    final_types.bind_var(bytearray_id, Rc::new(PseudoType::ByteArray));
    final_types.freeze();

    let registry = Rc::new(BlueprintHintRegistry::default());
    let (rendered, _spans) = render_decompiled_expr_with_registry_and_final_types(
        &expr,
        true,
        &registry,
        &Rc::new(final_types),
        &crate::decompile::RenderCtx::default(),
    );

    assert!(
        !rendered.contains(": Data"),
        "P6.3 contract: bare-`Data` annotations are the implicit default and \
         must be suppressed (e.g. `let o = payload`, never `let o: Data = \
         payload`). Got:\n{rendered}"
    );
    assert!(
        rendered.contains(": Int"),
        "P6.3 contract: refined `Int` annotations must survive suppression. \
         Got:\n{rendered}"
    );
    assert!(
        rendered.contains(": ByteArray"),
        "P6.3 contract: refined `ByteArray` annotations must survive \
         suppression. Got:\n{rendered}"
    );
    assert!(
        rendered.contains("let o ="),
        "P6.3 contract: bare-Data binder must render without annotation. \
         Got:\n{rendered}"
    );
    assert!(
        rendered.contains("let u ="),
        "P6.3 contract: Unknown-typed binder (also displays as Data) must \
         render without annotation. Got:\n{rendered}"
    );
}

/// Only the *top-level* `Data` / `Unknown` variant is suppressed.
/// Refined containers — `List<Data>`, `Option<Data>`, `Pair<Data, Data>`
/// — say the binder is a sequence/option/pair of Plutus values, not a
/// single one, so they keep their annotation.
#[test]
fn p6_3_resolve_type_keeps_refined_containers_holding_data() {
    use crate::decompile::final_type_table::FinalTypeTable;
    use crate::pseudo::var_id::VarId;
    use std::rc::Rc;

    let list_data_id = VarId::fresh_binding();
    let option_data_id = VarId::fresh_binding();
    let pair_data_id = VarId::fresh_binding();

    let expr = PseudoExpr::let_bind_with_id(
        "items",
        list_data_id,
        PseudoExpr::var_with_id("payload", VarId::fresh_binding()),
        PseudoExpr::let_bind_with_id(
            "maybe_item",
            option_data_id,
            PseudoExpr::var_with_id("payload", VarId::fresh_binding()),
            PseudoExpr::let_bind_with_id(
                "kv",
                pair_data_id,
                PseudoExpr::var_with_id("payload", VarId::fresh_binding()),
                PseudoExpr::Unit,
            ),
        ),
    );

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(
        list_data_id,
        Rc::new(PseudoType::List(Rc::new(PseudoType::Data))),
    );
    final_types.bind_var(
        option_data_id,
        Rc::new(PseudoType::Option(Rc::new(PseudoType::Data))),
    );
    final_types.bind_var(
        pair_data_id,
        Rc::new(PseudoType::Pair(
            Rc::new(PseudoType::Data),
            Rc::new(PseudoType::Data),
        )),
    );
    final_types.freeze();

    let registry = Rc::new(BlueprintHintRegistry::default());
    let (rendered, _spans) = render_decompiled_expr_with_registry_and_final_types(
        &expr,
        true,
        &registry,
        &Rc::new(final_types),
        &crate::decompile::RenderCtx::default(),
    );

    assert!(
        rendered.contains(": List<Data>"),
        "P6.3 boundary: refined containers holding Data (List<Data>) must \
         keep their annotation — only top-level bare Data is suppressed. \
         Got:\n{rendered}"
    );
    assert!(
        rendered.contains(": Option<Data>"),
        "P6.3 boundary: Option<Data> annotation must survive — the \
         option-ness is information past the implicit default. Got:\n{rendered}"
    );
    assert!(
        rendered.contains(": Pair<Data, Data>"),
        "P6.3 boundary: Pair<Data, Data> annotation must survive. \
         Got:\n{rendered}"
    );
}

/// The `fn name(...) -> T` annotation path also routes through
/// `resolve_type`: a bare `Data` return suppresses the `-> Data`,
/// mirroring `let X: Data`. Refined and container return types still
/// render the arrow.
#[test]
fn p6_3_resolve_type_suppresses_bare_data_return_in_let_lambda() {
    use crate::decompile::final_type_table::FinalTypeTable;
    use crate::pseudo::var_id::VarId;
    use std::rc::Rc;

    // Two nested fn binders: one returning Data (suppressed), one returning
    // ByteArray (kept).
    let fn_data_id = VarId::fresh_binding();
    let fn_bytes_id = VarId::fresh_binding();
    let param_id = VarId::fresh_binding();

    let fn_data_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", param_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", param_id)),
    };
    let fn_bytes_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::var_with_id("blob", VarId::fresh_binding())),
    };
    let expr = PseudoExpr::let_bind_with_id(
        "to_data",
        fn_data_id,
        fn_data_lambda,
        PseudoExpr::let_bind_with_id("to_bytes", fn_bytes_id, fn_bytes_lambda, PseudoExpr::Unit),
    );

    let mut final_types = FinalTypeTable::new();
    final_types.bind_var(fn_data_id, Rc::new(PseudoType::Data));
    final_types.bind_var(fn_bytes_id, Rc::new(PseudoType::ByteArray));
    final_types.freeze();

    let registry = Rc::new(BlueprintHintRegistry::default());
    let (rendered, _spans) = render_decompiled_expr_with_registry_and_final_types(
        &expr,
        true,
        &registry,
        &Rc::new(final_types),
        &crate::decompile::RenderCtx::default(),
    );

    assert!(
        !rendered.contains("-> Data"),
        "P6.3 contract (lambda boundary): bare `-> Data` return annotations \
         are the implicit default and must be suppressed mirroring the let \
         case. Got:\n{rendered}"
    );
    assert!(
        rendered.contains("-> ByteArray") || rendered.contains(": ByteArray"),
        "P6.3 contract (lambda boundary): refined return types must \
         survive. Got:\n{rendered}"
    );
}

/// Cumulative regression guard: a vanilla public-render of
/// `MIR_V3_SMOKE_HEX` must contain none of these shapes — `expect!` in
/// either spelling, `Data.un_*` / `Data.serialize` / `Data.ByteArray(`,
/// `fn validator_(` (the legal form is `validator NAME {...}`), column-0
/// `let X =` (module scope is `const`), `[N..][K]` slice-then-index, and
/// bare `: Data` / `-> Data` annotations. Each is also pinned by its own
/// test; this one is the cumulative backstop.
#[test]
fn audit_2026_05_14_cumulative_ugliness_guard() {
    let program: Program<NamedDeBruijn> =
        decode_hex_to_program(MIR_V3_SMOKE_HEX).expect("expected valid V3 smoke program");
    let mut opts = DecompileOptions::default();
    opts.script_version = Some(ScriptVersion::PlutusV3);
    opts.type_passes = crate::decompile::TypePasses::all_on();

    let rendered = decompile_program(&program, opts).expect("typed decompile should succeed");

    // Each entry: (substring to forbid, fix tag, brief why)
    let forbidden: &[(&str, &str, &str)] = &[
        ("expect!\n", "P1.1", "standalone `expect!` (keyword form)"),
        ("expect! ", "P1.1", "standalone `expect! <expr>` form"),
        // `expect!(` call form. It survives elsewhere for shapes with
        // top-level commas; this fixture must contain none.
        ("expect!(", "P1.1-x", "`expect!(...)` synthetic call form"),
        // `Data.*` capitalized pseudonym module — not valid surface syntax.
        ("Data.un_", "P1.2", "`Data.un_*` (use `builtin.un_*_data`)"),
        (
            "Data.serialize",
            "P1.2",
            "`Data.serialize` (use `builtin.serialise_data`)",
        ),
        (
            "Data.ByteArray(",
            "P1.2",
            "`Data.ByteArray(...)` (use `builtin.b_data`)",
        ),
        // trailing-underscore `validator_` from keyword sanitization.
        (
            "fn validator_(",
            "P2.3",
            "`fn validator_(` (keyword collision)",
        ),
        // `[N..][K]` slice-then-index residual (open-end + index).
        ("][1..][1]", "P5.3", "`[N..][K]` slice-then-index"),
        ("][2..][1]", "P5.3", "`[N..][K]` slice-then-index"),
        // `Constr<N>` is the bare unresolved constructor placeholder and
        // invalid surface syntax; stub-ADT synthesis resolves such shapes to
        // `Unknown_S_<ord>_A<arity>_<tag>` or `Unknown_E_<arity>_<tag>`
        // names registered through the BlueprintHintRegistry chain.
        (
            "Constr<",
            "A1",
            "`Constr<N>` unresolved placeholder (stub-ADT synthesized)",
        ),
    ];

    let mut violations: Vec<String> = Vec::new();
    for (substr, fix, why) in forbidden {
        if rendered.contains(*substr) {
            violations.push(format!("  [{fix}] {why}: `{substr}` found"));
        }
    }

    // Only the top-level shape is forbidden: `: Data` followed by ` =`, a
    // newline, or end of string. Refined containers like `: List<Data>`
    // must survive — the `<` after `Data` keeps them out of the needles.
    for needle in [": Data =", ": Data\n", "-> Data\n", "-> Data ", "-> Data {"] {
        if rendered.contains(needle) {
            violations.push(format!(
                "  [P6.3] bare-`Data` annotation must be suppressed: `{needle}` found"
            ));
        }
    }

    // A module-scope `let X = ...` lives at column 0; inside a
    // `validator` or `fn` body it is indented and allowed.
    let module_let_lines: Vec<&str> = rendered
        .lines()
        .filter(|line| line.starts_with("let "))
        .collect();
    if !module_let_lines.is_empty() {
        violations.push(format!(
            "  [P5.4] module-scope `let X = ...` (must be `const`): {} line(s) — first: {:?}",
            module_let_lines.len(),
            module_let_lines[0]
        ));
    }

    assert!(
        violations.is_empty(),
        "Audit-cumulative regression guard: forbidden ugliness re-appeared \
         in the public-render of MIR_V3_SMOKE_HEX. Each violation maps back \
         to a landed audit fix; if you're intentionally changing a contract, \
         update this list AND the fix-specific test.\n\nViolations:\n{}\n\nFull rendered output:\n{rendered}",
        violations.join("\n")
    );
}
