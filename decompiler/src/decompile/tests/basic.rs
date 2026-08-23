//! Small unit tests for basic-API surfaces —
//! `decode_hex_to_program`, `validate_known_builtins`,
//! `DecompileOptions`.

#![cfg(test)]

use crate::decompile::pipeline::validate_known_builtins;
use crate::decompile::tests::MIR_V2_SMOKE_HEX;
use crate::decompile::{
    DecompileOptions, DisplayPolishPasses, OutputLayer, ReadabilityPasses, SimplifyPasses,
    StructuralRecoveryPasses, TypePasses, decode_hex_to_program, decompile, decompile_program,
    select_exact_program,
};
use crate::error::DecompileError;
use crate::pseudo::ast::PseudoExpr;
use uplc::ast::{FakeNamedDeBruijn, Program};

// validate_known_builtins

#[test]
fn test_validate_known_builtins_accepts_internal_surface_names() {
    for name in [
        "Constr.unpack",
        "List.cons",
        "List.empty",
        "Data.to_bytes",
        "Data.constr_index",
        "verify_ecdsa_secp256k1",
    ] {
        let expr = PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known(name),
            args: vec![].into(),
        };
        validate_known_builtins(&expr, "unit_test")
            .unwrap_or_else(|err| panic!("expected builtin `{name}` to validate: {err:?}"));
    }
}

#[test]
fn test_validate_known_builtins_rejects_unknown_builtin() {
    match crate::BuiltinId::parse_known("definitely_unknown_builtin", "unit_test") {
        Err(DecompileError::UnknownBuiltin { name, stage }) => {
            assert_eq!(name, "definitely_unknown_builtin");
            assert_eq!(stage, "unit_test");
        }
        other => panic!("expected unknown builtin error, got: {other:?}"),
    };
}

// DecompileOptions

#[test]
fn test_decompile_options_default() {
    let opts = DecompileOptions::default();
    assert!(opts.type_passes.any_enabled());
    assert!(!opts.safe_mode);
}

#[test]
fn test_decompile_options_raw() {
    let opts = DecompileOptions::raw();
    assert!(!opts.type_passes.any_enabled());
    assert!(opts.safe_mode);
}

// decode_hex_to_program

#[test]
fn test_decode_hex_to_program_cbor_exact() {
    // UPLC (lambda x. x) in canonical CBOR-wrapped Flat form.
    let hex = "46010000200101";
    let result = decode_hex_to_program(hex);
    assert!(result.is_ok());
}

#[test]
fn test_decode_hex_to_program_flat_exact() {
    // UPLC (lambda x. x) in raw Flat form.
    let hex = "010000200101";
    let result = decode_hex_to_program(hex);
    assert!(result.is_ok());
}

#[test]
fn uplc_layer_renders_unique_variable_names() {
    // The `--emit uplc` layer must give each binder a DISTINCT name. The raw
    // decoded `Program<NamedDeBruijn>` carries the placeholder text `i_0` on
    // EVERY binder; `render_uplc_unique_names` round-trips through DeBruijn->Name
    // so nested lambdas read as `i_0`, `i_1`, … instead of all `i_0`.
    let program = decode_hex_to_program(MIR_V2_SMOKE_HEX).expect("decode smoke hex");
    let opts = DecompileOptions {
        output_layer: OutputLayer::Uplc,
        ..DecompileOptions::default()
    };
    let out = decompile_program(&program, opts).expect("uplc layer render");
    assert!(
        out.contains("(program"),
        "should be canonical UPLC, got:\n{out}"
    );
    // ≥2 distinct binder names ⇒ not the all-`i_0` placeholder render.
    assert!(
        out.contains("i_0") && out.contains("i_1"),
        "UPLC layer must use distinct binder names (i_0, i_1, …), got:\n{out}"
    );
}

/// The V2 smoke constant must stay the compiled form of the source
/// checked in beside it. Re-encode `smoke/vault_v2.uplc` and compare, so
/// the constant cannot quietly become bytes from somewhere else.
#[test]
fn mir_v2_smoke_hex_matches_its_checked_in_source() {
    use uplc::ast::{DeBruijn, Name, Program};

    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("smoke/vault_v2.uplc");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("smoke source {} is unreadable: {err}", path.display()));
    let program: Program<Name> = uplc::parser::program(&source).expect("smoke source parses");
    let program: Program<DeBruijn> = program.try_into().expect("smoke source de-Bruijnizes");
    let bytes = program.to_cbor().expect("smoke source encodes");

    assert_eq!(
        hex::encode(bytes),
        MIR_V2_SMOKE_HEX,
        "MIR_V2_SMOKE_HEX no longer matches {}",
        path.display()
    );
}

#[test]
fn test_decode_hex_to_program_rejects_trailing_bytes() {
    let hex = "4601000020010100";
    let result = decode_hex_to_program(hex);
    assert!(matches!(
        result,
        Err(DecompileError::DecodeError(msg))
            if msg.contains("CBOR bytes header declares")
                && msg.contains("extra 1")
    ));
}

#[test]
fn test_decode_hex_to_program_reports_truncated_cbor_bytes() {
    let hex = "460100002001";
    let result = decode_hex_to_program(hex);
    assert!(matches!(
        result,
        Err(DecompileError::DecodeError(msg))
            if msg.contains("CBOR bytes header declares")
                && msg.contains("missing 1")
    ));
}

#[test]
fn test_select_exact_program_rejects_ambiguous_programs() {
    let base = Program::<FakeNamedDeBruijn>::from_flat(&hex::decode("010000200101").unwrap())
        .expect("expected valid flat program");
    let mut different = base.clone();
    different.version = (2, 0, 0);

    let result = select_exact_program(Some(base), Some(different));
    assert!(matches!(
        result,
        Err(DecompileError::DecodeError(msg))
            if msg.contains("Ambiguous UPLC encoding")
    ));
}

// Public-API smoke tests: every `DecompileOptions` pass-group toggle must
// change the output, so a toggle that decays into dead code fails here.

/// Decompile `MIR_V2_SMOKE_HEX` with the given options.
fn decompile_smoke(options: DecompileOptions) -> String {
    decompile(MIR_V2_SMOKE_HEX, options).expect("smoke fixture must decompile")
}

#[test]
fn pass_group_simplify_passes_off_changes_output() {
    let baseline = decompile_smoke(DecompileOptions::default());
    let no_simplify = decompile_smoke(DecompileOptions {
        simplify_passes: SimplifyPasses::all_off(),
        ..DecompileOptions::default()
    });
    assert_ne!(
        baseline, no_simplify,
        "SimplifyPasses::all_off() must change output vs default"
    );
}

#[test]
fn pass_group_readability_off_changes_output() {
    let baseline = decompile_smoke(DecompileOptions::default());
    let no_readability = decompile_smoke(DecompileOptions {
        readability_passes: ReadabilityPasses::all_off(),
        ..DecompileOptions::default()
    });
    assert_ne!(
        baseline, no_readability,
        "ReadabilityPasses::all_off() must change output vs default"
    );
}

#[test]
fn pass_group_display_polish_off_changes_output() {
    let baseline = decompile_smoke(DecompileOptions::default());
    let no_display = decompile_smoke(DecompileOptions {
        display_polish_passes: DisplayPolishPasses::all_off(),
        ..DecompileOptions::default()
    });
    assert_ne!(
        baseline, no_display,
        "DisplayPolishPasses::all_off() must change output vs default"
    );
}

#[test]
fn pass_group_type_passes_off_changes_output() {
    let baseline = decompile_smoke(DecompileOptions::default());
    let no_types = decompile_smoke(DecompileOptions {
        type_passes: TypePasses::all_off(),
        ..DecompileOptions::default()
    });
    assert_ne!(
        baseline, no_types,
        "TypePasses::all_off() must change output vs default"
    );
}

#[test]
fn top_level_synthesize_stub_adts_off_changes_output() {
    let with_stubs = decompile_smoke(DecompileOptions::default());
    let no_stubs = decompile_smoke(DecompileOptions {
        synthesize_stub_adts: false,
        ..DecompileOptions::default()
    });
    assert_ne!(
        with_stubs, no_stubs,
        "synthesize_stub_adts=false must change output vs default (true)"
    );
}

#[test]
fn top_level_recognize_prelude_constructors_off_changes_output() {
    let with_prelude = decompile_smoke(DecompileOptions::default());
    let no_prelude = decompile_smoke(DecompileOptions {
        recognize_prelude_constructors: false,
        ..DecompileOptions::default()
    });
    assert_ne!(
        with_prelude, no_prelude,
        "recognize_prelude_constructors=false must change output vs default (true)"
    );
}

#[test]
fn top_level_raw_mode_changes_output() {
    let baseline = decompile_smoke(DecompileOptions::default());
    let raw = decompile_smoke(DecompileOptions::raw());
    assert_ne!(
        baseline, raw,
        "DecompileOptions::raw() must change output vs default"
    );
}
// exploratory probe (ignored — leaf-toggle coverage table)
pub(crate) fn opts_with_simplify_leaf(name: &str) -> Option<DecompileOptions> {
    let mut p = SimplifyPasses::all_on();
    match name {
        "simplify_fp_initial" => p.simplify_fp_initial = false,
        "simplify_fp_post_readability" => p.simplify_fp_post_readability = false,
        "inline_single_use" => p.inline_single_use = false,
        "inline_fp" => p.inline_fp = false,
        "inline_post_readability" => p.inline_post_readability = false,
        "dead_let_elim" => p.dead_let_elim = false,
        "collapse_tail_chains" => p.collapse_tail_chains = false,
        _ => return None,
    }
    Some(DecompileOptions {
        simplify_passes: p,
        ..Default::default()
    })
}

pub(crate) fn opts_with_structural_leaf(name: &str) -> Option<DecompileOptions> {
    let mut p = StructuralRecoveryPasses::all_on();
    match name {
        "recover_let_bound_tag_dispatch" => p.recover_let_bound_tag_dispatch = false,
        "simplify_double_rec_fn" => p.simplify_double_rec_fn = false,
        "simplify_z_combinator" => p.simplify_z_combinator = false,
        "extract_complex_when_subjects" => p.extract_complex_when_subjects = false,
        "resolve_immediate_applications" => p.resolve_immediate_applications = false,
        "resolve_data_case" => p.resolve_data_case = false,
        _ => return None,
    }
    Some(DecompileOptions {
        structural_recovery_passes: p,
        ..Default::default()
    })
}

pub(crate) fn opts_with_readability_leaf(name: &str) -> Option<DecompileOptions> {
    let mut p = ReadabilityPasses::all_on();
    match name {
        "improve_variable_names" => p.improve_variable_names = false,
        "flatten_let_chains" => p.flatten_let_chains = false,
        "rename_variables" => p.rename_variables = false,
        "hoist_local_helpers" => p.hoist_local_helpers = false,
        "extract_heavy_constants" => p.extract_heavy_constants = false,
        _ => return None,
    }
    Some(DecompileOptions {
        readability_passes: p,
        ..Default::default()
    })
}

pub(crate) fn opts_with_display_leaf(name: &str) -> Option<DecompileOptions> {
    let mut p = DisplayPolishPasses::all_on();
    match name {
        "strip_cosmetic_delays" => p.strip_cosmetic_delays = false,
        "cancel_force_delay_vars" => p.cancel_force_delay_vars = false,
        "normalize_list_cons_literals" => p.normalize_list_cons_literals = false,
        "normalize_display_rewrites" => p.normalize_display_rewrites = false,
        "eliminate_cps_selectors" => p.eliminate_cps_selectors = false,
        "simplify_boolean_and_identity" => p.simplify_boolean_and_identity = false,
        "collapse_eta_pair_selectors" => p.collapse_eta_pair_selectors = false,
        "resolve_scott_constructor_lambdas_late" => {
            p.resolve_scott_constructor_lambdas_late = false
        }
        "resolve_data_case_late" => p.resolve_data_case_late = false,
        _ => return None,
    }
    Some(DecompileOptions {
        display_polish_passes: p,
        ..Default::default()
    })
}

pub(crate) fn opts_with_type_leaf(name: &str) -> Option<DecompileOptions> {
    let mut p = TypePasses::all_on();
    match name {
        "solve_type_constraints" => p.solve_type_constraints = false,
        "propagate_types" => p.propagate_types = false,
        "resolve_cardano_field_names" => p.resolve_cardano_field_names = false,
        _ => return None,
    }
    Some(DecompileOptions {
        type_passes: p,
        ..Default::default()
    })
}

#[allow(dead_code)] // overlay leaf-toggle coverage probe
pub(crate) fn build_opts(group: &str, leaf: &str) -> DecompileOptions {
    match group {
        "Simplify" => opts_with_simplify_leaf(leaf).unwrap(),
        "Structural" => opts_with_structural_leaf(leaf).unwrap(),
        "Readability" => opts_with_readability_leaf(leaf).unwrap(),
        "Display" => opts_with_display_leaf(leaf).unwrap(),
        "Type" => opts_with_type_leaf(leaf).unwrap(),
        _ => unreachable!(),
    }
}

// The 3 known pass-dependency violations, pinned as API contract:
// `decompile_program` calls `DecompileOptions::validate()` up front so library
// callers see `DecompileError::InvalidOptions`, not a pipeline-runtime panic.

#[test]
fn invalid_options_simplify_fp_initial_off_with_inline_single_use_on() {
    let mut s = SimplifyPasses::all_on();
    s.simplify_fp_initial = false;
    // inline_single_use stays true (the violating combination).
    let opts = DecompileOptions {
        simplify_passes: s,
        ..Default::default()
    };
    let err = decompile(MIR_V2_SMOKE_HEX, opts).expect_err("must reject");
    assert!(
        matches!(&err, DecompileError::InvalidOptions(msg) if msg.contains("inline_single_use")),
        "expected InvalidOptions mentioning inline_single_use, got: {err:?}"
    );
}

#[test]
fn invalid_options_solve_off_with_propagate_on() {
    let mut t = TypePasses::all_on();
    t.solve_type_constraints = false;
    let opts = DecompileOptions {
        type_passes: t,
        ..Default::default()
    };
    let err = decompile(MIR_V2_SMOKE_HEX, opts).expect_err("must reject");
    assert!(
        matches!(&err, DecompileError::InvalidOptions(msg) if msg.contains("propagate_types")),
        "expected InvalidOptions mentioning propagate_types, got: {err:?}"
    );
}

#[test]
fn invalid_options_propagate_off_with_resolve_cardano_on() {
    let mut t = TypePasses::all_on();
    t.propagate_types = false;
    let opts = DecompileOptions {
        type_passes: t,
        ..Default::default()
    };
    let err = decompile(MIR_V2_SMOKE_HEX, opts).expect_err("must reject");
    assert!(
        matches!(&err, DecompileError::InvalidOptions(msg) if msg.contains("resolve_cardano_field_names")),
        "expected InvalidOptions mentioning resolve_cardano_field_names, got: {err:?}"
    );
}

#[test]
fn invalid_options_group_all_off_is_always_valid() {
    // Group `all_off()` resets every leaf at once, so no dependency
    // can be violated; the group toggle is the user-facing API.
    for opts in [
        DecompileOptions {
            simplify_passes: SimplifyPasses::all_off(),
            ..Default::default()
        },
        DecompileOptions {
            type_passes: TypePasses::all_off(),
            ..Default::default()
        },
        DecompileOptions {
            structural_recovery_passes: StructuralRecoveryPasses::all_off(),
            ..Default::default()
        },
        DecompileOptions {
            readability_passes: ReadabilityPasses::all_off(),
            ..Default::default()
        },
        DecompileOptions {
            display_polish_passes: DisplayPolishPasses::all_off(),
            ..Default::default()
        },
        DecompileOptions::raw(),
    ] {
        opts.validate().expect("group all_off / raw must validate");
    }
}

/// The two trace-strip options must reach the render context.
///
/// They were `DEHOSK_STRIP_TRACES` / `DEHOSK_STRIP_PLUTUSTX_TRACES`, read
/// straight out of the environment inside the passes. Now they travel
/// options → [`StubAdtRenderContext`] → `RenderCtx` → pass, and each hop
/// is a place a copy-paste could drop or transpose one. This pins the
/// hop that a mistake would otherwise pass every other test:
/// [`StubAdtRenderContext::render_ctx`], which the analysis and DCE preps
/// share with the final render (`tests::mir_pipeline` pins that they
/// agree).
///
/// The published tree has no trace-bearing fixture — the one that renders
/// a `trace` lives in the overlay — so the pass half is pinned on a
/// synthetic tree in `render_prep::strip_all_traces`'s own tests instead
/// of end-to-end here.
#[test]
fn trace_strip_options_reach_the_render_context() {
    use crate::decompile::StubAdtRenderContext;

    let ctx_of = |strip_all: bool, strip_plutustx: bool| {
        StubAdtRenderContext {
            synthesize_stub_adts: true,
            decode_church: false,
            compilable_data_access: false,
            strip_all_traces: strip_all,
            strip_plutustx_traces: strip_plutustx,
            render_field_version: None,
            plan_version: None,
            version_guessed: false,
        }
        .render_ctx()
    };

    let off = ctx_of(false, false);
    assert!(!off.strip_all_traces(), "default keeps every trace");
    assert!(
        !off.strip_plutustx_traces(),
        "default keeps the PlutusTx pairs"
    );

    // Set one at a time: a transposed assignment would carry the OTHER
    // flag's value and still pass a both-on check.
    let all_only = ctx_of(true, false);
    assert!(all_only.strip_all_traces());
    assert!(
        !all_only.strip_plutustx_traces(),
        "flags must not be transposed"
    );

    let plutustx_only = ctx_of(false, true);
    assert!(
        !plutustx_only.strip_all_traces(),
        "flags must not be transposed"
    );
    assert!(plutustx_only.strip_plutustx_traces());
}

/// `--emit prep-profile` reports the render-prep chain instead of the code.
///
/// The chain is the largest single cost in a decompile and had no
/// per-step reporting at all, unlike the core pipeline one layer up.
#[test]
fn prep_profile_layer_reports_every_step() {
    let mut opts = DecompileOptions::default();
    opts.output_layer = OutputLayer::PrepProfile;
    let report = crate::decompile(MIR_V2_SMOKE_HEX, opts).expect("prep-profile layer");

    assert!(
        report.starts_with("render-prep profile —"),
        "the layer emits the profile, not the program:\n{report}"
    );
    // A pass the chain definitely runs, so an empty or truncated table fails.
    assert!(
        report.contains("render_improve_variable_names"),
        "the table must name the steps it timed:\n{report}"
    );
    assert!(
        !report.contains("validator "),
        "the layer must NOT fall through to the rendered program:\n{report}"
    );
}
