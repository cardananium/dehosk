use super::*;
use crate::pseudo::ast::PBox;
use std::collections::BTreeSet;
use uplc::ast::{NamedDeBruijn, Program};

/// The two smoke fixtures the non-corpus tests run on.
///
/// Both are compiled from sources written for this repository and kept
/// beside them in `decompiler/smoke/`: `vault.ak` for the V3 program and
/// `vault_v2.uplc` for the V2 one. Neither is a deployed contract — do
/// not replace them with bytes lifted off the chain — that is what the
/// local overlay corpus is for.
pub(crate) const MIR_V3_SMOKE_HEX: &str = "5902e401010029800aba2aba1aba0aab9faab9eaab9dab9a48888889660033001300337540112259800800c52000899b8048008cc008008c0240050064dc3a4001370e90014dc424000911114c004c030016601600b300400491192cc004c018006264646644b300130130038034590101bae3010001375a6020004602000260166ea800e2b3001300500189919912cc004c048006264660020026eb0c048008896600200300789919801801980a8011bae3013001404516403c6eb4c03c004c040004c02cdd5001c56600266e1d20040018acc004c02cdd5001c00a2c80622c804900920123009375400491111919912cc004c02400a26466446600e0082b3001300d3011375400319800980a98091baa0019180b180b980b800c8c058c05c00660226ea801122223322598009809801c4c8c966002602600315980099b8933706002900a001c6600266e3c010dd7180e980f001528528a0308a50406114a080c0dd6980e000980c1baa00a8acc004c04800e2646644b3001301430110018acc004c05000a330013371f30014800290044c8cc0040040088966002003148900899b8a375c604000266004004604200280f1718005a50a51406514a080ca29410191bad301c00137586038603a00260306ea802a26026646600200266036600a60326ea801ccc06cc018c064dd50039980d9ba80024bd70112cc0040062900044cdc01bad301d00133002002301e001406c80b101619b8a375c6032602c6ea80112201055641554c5400337026eb4c008c058dd50021bad3003301637540088a504040602600260266028002601e6ea800e2b3001300a002899198028010992cc004c030006264b3001300b375a602a0031980099b8f375c602a602c00291100a50a51404114a08080c044dd5001c56600260160031325980098059bad3015001899b8848008c020dd6180a980b000c52820203011375400714a0807900f18079baa002375c6024601e6ea800e2c806900d18061baa0013010005300f3010004229344d9590011";
pub(crate) const MIR_V2_SMOKE_HEX: &str = "5901a901000022232323232323232323232325333573466e1c00920001323232325333573466e21200000415333573466e2400802054ccd5cd1805a40002a666ae68cdc78008018b0a4c2a666ae68cdc78008008b0a4c2c2c66e28021221055641554c540033706004900a1bae357426ae88008dd69aba100115333573466e1c00920021323232325333573466e1ccdc0180780198078010008a999ab9a33710900018070018a4c2c2c601600e66ae80dd400319aba03750900125eb80dd61aba100135573c6ea80304c8c8c94ccd5cd19b880073370000e0062a666ae68cdc7999b8c48000dc68040008040a4c2c2c60160026eb0d5d09aba2002375a6ae84004d55cf0011aab9d00137540146eb4d5d09aba2002375c6ae84004d55cf1baa00823370e0029000119b8200148010c8c8c0088cc0080080048c0088cc008008004894ccd55cf8008a441001337146eb8d5d080098011aba200132323002233002002001230022330020020012253335573e00229000099b8048008c008d5d10009919180111980100100091801119801001000912999aab9f0011480004cdc01bad3574200260046ae880041";
pub(crate) const MIR_SHARED_PIPELINE_PASSES: &[&str] = &[
    "lower_mir",
    "rename_variables",
    "simplify_1",
    "inline_single_use",
    "simplify_2",
    "inline_fp",
    "simplify_fp",
    "uniquify_final",
    "eliminate_dead_lets",
    "inline_post_readability",
    "simplify_post_readability",
];
pub(crate) const MIR_SHARED_STRUCTURAL_NORMALIZATION_PASSES: &[&str] = &[
    "collapse_tail_chains",
    "strip_cosmetic_delays",
    "cancel_force_delay_vars",
    "normalize_list_cons_literals",
    "resolve_scott_constructor_lambdas",
    "lift_unpack_tag_when_subjects",
    "simplify_z_combinator",
    "simplify_double_rec_fn",
    "destructure_when_fields",
    "extract_complex_when_subjects",
    "collapse_eta_pair_selector_when_subjects",
    "collapse_eta_pair_selector_when_subjects_post_readability",
    "flatten_let_chains",
    "flatten_let_chains_post_inline",
    "flatten_let_chains_post_readability",
    "hoist_local_helpers",
    "extract_heavy_constants",
    "normalize_display_rewrites",
    "hoist_local_helpers_post_normalize",
];
pub(crate) const MIR_SHARED_SEMANTIC_RECOVERY_PASSES: &[&str] = &[
    "convert_expect_tag",
    "resolve_field_accesses",
    "eliminate_cps_selectors",
    "disambiguate_constructors",
    "simplify_boolean_and_identity",
    "simplify_boolean_and_identity_late",
    "simplify_boolean_and_identity_post_readability",
    "eliminate_cps_selectors_post_readability",
    "resolve_cardano_field_names",
    "resolve_cardano_field_names_late",
];
pub(crate) const MIR_SHARED_TYPE_AND_NAMING_PASSES: &[&str] = &[
    "rename_validator_params",
    "deduplicate_var_ids_for_type_refinement",
    "solve_type_constraints",
    "solve_type_constraints_late",
    "solve_type_constraints_post_late_structural",
    "solve_type_constraints_final",
    // Collapses Bool↔Constr<0|1> roundtrip Whens into Ifs using
    // the freshly-solved type table.
    "bool_constr_collapse_final",
    "propagate_types",
    "propagate_types_late",
    "propagate_types_post_late_structural",
    "propagate_types_final",
    "resolve_cardano_field_names_post_late_structural",
    "resolve_cardano_field_names_final",
    "improve_variable_names",
    "improve_variable_names_post_late",
    // upstream ref-retargeting before
    // display_rewrite (src/decompile/ref_retarget.rs).
    "retarget_refs_by_scope",
    // per-pass instrumentation for
    // run_structural_final_cleanup_stage sub-passes.
    "structural_final_cleanup",
    "deduplicate_var_ids_final",
    "inline_dangling_field_aliases",
    "default_nameless_post_pipeline",
];

pub(crate) fn decompile_program_with_mir(
    hex: &str,
    script_version: Option<ScriptVersion>,
) -> String {
    let program: Program<NamedDeBruijn> =
        decode_hex_to_program(hex).expect("expected valid test program");
    let mut opts = DecompileOptions::default();
    opts.script_version = script_version;
    decompile_program(&program, opts).expect("MIR decompile should succeed")
}

/// Render with the compilable-data-access surface enabled (`coll[N]` →
/// `head_list`/`tail_list`, `.tag`/`.fields` → `un_constr_data`, …).
pub(crate) fn decompile_program_compilable(
    hex: &str,
    script_version: Option<ScriptVersion>,
) -> String {
    let program: Program<NamedDeBruijn> =
        decode_hex_to_program(hex).expect("expected valid test program");
    let mut opts = DecompileOptions::default();
    opts.script_version = script_version;
    opts.decode_church_to_native = true;
    opts.compilable_data_access = true;
    decompile_program(&program, opts).expect("MIR decompile should succeed")
}

/// Count `<collection>[N]` / `<collection>[N..]` index/slice brackets left
/// in the rendered output — an index directly after an identifier or a
/// closing paren, not a list literal `[N]` (preceded by `=`/`(`/`,`/space).
/// In compilable-data-access mode every such access must lower to
/// `head_list`/`tail_list`, so this is that lowering's coverage signal.
pub(crate) fn count_unlowered_index_brackets(s: &str) -> usize {
    let bytes = s.as_bytes();
    let mut count = 0;
    for (i, &c) in bytes.iter().enumerate() {
        if c != b'[' || i == 0 {
            continue;
        }
        let prev = bytes[i - 1];
        let after_collection = prev.is_ascii_alphanumeric() || prev == b'_' || prev == b')';
        if !after_collection {
            continue;
        }
        let rest = &s[i + 1..];
        let digits = rest
            .find(|ch: char| !ch.is_ascii_digit())
            .unwrap_or(rest.len());
        if digits == 0 {
            continue;
        }
        let tail = &rest[digits..];
        if tail.starts_with(']') || tail.starts_with("..]") {
            count += 1;
        }
    }
    count
}

pub(crate) fn load_repo_hex_fixture(path: &str) -> Option<String> {
    let relative = format!("repo_hex/{path}");
    let hex = crate::fixtures::read_fixture(&relative);
    if hex.is_none() {
        println!("Skipping corpus file {relative}: not installed in this checkout");
    }
    hex
}

/// Read a corpus file the caller has established is present (an overlay
/// test, compiled only with the corpus installed): absence is a broken
/// install, not a bare checkout, so this panics rather than skips.
pub(crate) fn load_decompiler_hex_fixture(path: &str) -> String {
    crate::fixtures::read_fixture(path).unwrap_or_else(|| {
        panic!(
            "corpus file {path} is missing; expected it under {} \
             (or set DEHOSK_FIXTURES)",
            crate::fixtures::default_fixture_root().display()
        )
    })
}

pub(crate) fn collect_mir_passes(
    hex: &str,
    script_version: Option<ScriptVersion>,
) -> Vec<&'static str> {
    collect_pipeline_passes(hex, script_version)
}

pub(crate) fn mir_shared_classified_passes() -> BTreeSet<&'static str> {
    let mut passes: BTreeSet<&'static str> = MIR_SHARED_PIPELINE_PASSES.iter().copied().collect();
    passes.extend(MIR_SHARED_STRUCTURAL_NORMALIZATION_PASSES.iter().copied());
    passes.extend(MIR_SHARED_SEMANTIC_RECOVERY_PASSES.iter().copied());
    passes.extend(MIR_SHARED_TYPE_AND_NAMING_PASSES.iter().copied());
    passes
}

pub(crate) fn collect_pipeline_passes(
    hex: &str,
    script_version: Option<ScriptVersion>,
) -> Vec<&'static str> {
    let program: Program<NamedDeBruijn> =
        decode_hex_to_program(hex).expect("expected valid test program");
    let mut opts = DecompileOptions::default();
    opts.script_version = script_version;

    let mut passes = Vec::new();
    let _expr =
        run_pipeline(&program, opts, |name, _| passes.push(name)).expect("pipeline should succeed");

    passes
}

pub(crate) fn collect_pipeline_telemetry(
    hex: &str,
    script_version: Option<ScriptVersion>,
    safe_mode: bool,
) -> PipelineTelemetry {
    let program: Program<NamedDeBruijn> =
        decode_hex_to_program(hex).expect("expected valid test program");
    let mut opts = DecompileOptions::default();
    opts.script_version = script_version;
    opts.safe_mode = safe_mode;

    run_pipeline_with_artifacts(&program, opts, |_, _| {})
        .expect("pipeline should succeed")
        .telemetry
}

pub(crate) fn pipeline_parity_test_lock() -> &'static std::sync::Mutex<()> {
    static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
    LOCK.get_or_init(|| std::sync::Mutex::new(()))
}

pub(crate) fn extract_root_lambda_params(
    expr: &PseudoExpr,
) -> Vec<(String, crate::pseudo::var_id::VarId)> {
    if let PseudoExpr::Lambda { params, .. } = expr {
        return params
            .iter()
            .map(|b| (b.as_str().to_string(), b.var_id()))
            .collect();
    }
    Vec::new()
}

#[test]
fn resolve_scott_constructor_lambdas_ignores_outer_same_name_binding() {
    let outer_some_id = crate::pseudo::var_id::VarId::fresh_binding();
    let param_some_id = crate::pseudo::var_id::VarId::fresh_binding();
    let none_id = crate::pseudo::var_id::VarId::fresh_binding();

    let expr = PseudoExpr::Let {
        name: "some".to_string(),
        id: Some(outer_some_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new(
                "x",
                crate::pseudo::var_id::VarId::fresh_binding(),
            )],
            body: PBox::new(PseudoExpr::Unit),
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("some", param_some_id),
                Binder::new("none", none_id),
            ],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: "some".to_string(),
                    id: Some(outer_some_id),
                }),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };

    let resolved = resolve_scott_constructor_lambdas(expr);

    match resolved {
        PseudoExpr::Let { body, .. } => {
            assert!(
                matches!(body.as_ref(), PseudoExpr::Lambda { .. }),
                "expected outer same-name binding not to trigger Scott constructor rewrite, got: {body:?}"
            );
        }
        other => panic!("expected outer let to stay intact, got: {other:?}"),
    }
}

#[test]
fn resolve_scott_constructor_lambdas_rewrites_explicit_selector_application() {
    let field_id = crate::pseudo::var_id::VarId::fresh_binding();
    let param_some_id = crate::pseudo::var_id::VarId::fresh_binding();
    let none_id = crate::pseudo::var_id::VarId::fresh_binding();

    let expr = PseudoExpr::Let {
        name: "field".to_string(),
        id: Some(field_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("some", param_some_id),
                Binder::new("none", none_id),
            ],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("some", param_some_id)),
                args: vec![PseudoExpr::var_with_id("field", field_id)].into(),
            }),
        }),
    };

    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr));
    let resolved = resolve_scott_constructor_lambdas(expr);
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&resolved));

    let PseudoExpr::Let { body, .. } = resolved else {
        panic!("expected outer let to stay intact");
    };
    let PseudoExpr::Constr {
        tag, fields, shape, ..
    } = body.as_ref()
    else {
        panic!("expected Scott lambda to resolve to constructor, got: {body:?}");
    };
    assert_eq!(*tag, 0);
    assert_eq!(fields.len(), 1);
    assert!(matches!(
        shape,
        ConstructorShape::Unknown {
            tag: 0,
            arity: 1,
            ..
        }
    ));
}

#[test]
fn resolve_scott_constructor_lambdas_skips_selector_param_as_field() {
    let outer_some_id = crate::pseudo::var_id::VarId::fresh_binding();
    let param_some_id = crate::pseudo::var_id::VarId::fresh_binding();
    let none_id = crate::pseudo::var_id::VarId::fresh_binding();

    let expr = PseudoExpr::Let {
        name: "some".to_string(),
        id: Some(outer_some_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("some", param_some_id),
                Binder::new("none", none_id),
            ],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("some", param_some_id)),
                args: vec![PseudoExpr::var_with_id("some", param_some_id)].into(),
            }),
        }),
    };

    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr));
    let resolved = resolve_scott_constructor_lambdas(expr);
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&resolved));

    let PseudoExpr::Let { body, .. } = resolved else {
        panic!("expected outer let to stay intact");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Lambda { .. }),
        "expected selector-param field use to block Scott constructor rewrite, got: {body:?}"
    );
}

pub(crate) mod architecture_regression;
pub(crate) mod basic;
mod disambiguate;
mod mir_pipeline;
pub(crate) mod nameless_corpus;
pub(crate) mod nameless_guards;
mod resolution;
mod simplify_helpers;
mod single_purpose_detect;
pub(crate) mod snapshots;
mod type_pipeline;

/// Where the corpus-driven insta snapshots live.
///
/// They are the decompiled output of scripts that are not distributed
/// with the source, so they belong to the overlay next to the
/// corpus rather than in the published tree. `DEHOSK_OVERLAY_SNAPSHOTS`
/// relocates them, mirroring `DEHOSK_FIXTURES` for the inputs.
pub(crate) fn overlay_snapshot_path() -> std::path::PathBuf {
    if let Ok(dir) = std::env::var("DEHOSK_OVERLAY_SNAPSHOTS") {
        if !dir.is_empty() {
            return std::path::PathBuf::from(dir);
        }
    }
    if let Some(root) = crate::fixtures::overlay_root() {
        return root.join("snapshots");
    }
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("decompile")
        .join("tests")
        .join("snapshots")
}

#[cfg(test)]
include!(concat!(env!("OUT_DIR"), "/temporal.rs"));
