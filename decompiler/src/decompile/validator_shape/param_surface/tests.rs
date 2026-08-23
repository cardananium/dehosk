use super::*;
use crate::decompile::validator_shape::AppliedParam;

fn outer_with(params: Vec<AppliedParam>) -> OuterStructure {
    OuterStructure {
        applied_params: params,
        compiler_binding_indices: Vec::new(),
        lambda_chain_length: 1,
        runtime_arity: 1,
        pre_applied_runtime_args: 0,
    }
}

#[test]
fn empty_applied_params_returns_none() {
    let outer = outer_with(vec![]);
    assert!(format_applied_params_prefix(&outer, AppliedKind::Compile, 1).is_none());
}

/// V1 spend with applied=2 + lambda=1 (typical pre-applied
/// V1 spend shape) and `runtime_arity=3` (V1 spend): `Auto`
/// classifies all applied as runtime, since the exact-match
/// `applied + lambda == runtime_arity` condition holds.
#[test]
fn auto_classifies_v1_spend_pre_applied_runtime() {
    let outer = OuterStructure {
        applied_params: vec![
            AppliedParam::NonConstant {
                summary: String::new(),
            },
            AppliedParam::NonConstant {
                summary: String::new(),
            },
        ],
        compiler_binding_indices: Vec::new(),
        lambda_chain_length: 1,
        runtime_arity: 3,
        pre_applied_runtime_args: 1,
    };
    assert_eq!(
        resolve_runtime_count(AppliedKind::Auto, &outer, 3),
        2,
        "applied=2 + lambda=1 = 3 == runtime_arity → auto picks all-runtime"
    );
}

/// Non-match: `applied + lambda != runtime_arity`. Auto must
/// stay compile-time so the user can override with `--applied-as`.
#[test]
fn auto_does_not_classify_when_sum_disagrees_with_runtime_arity() {
    let outer = OuterStructure {
        applied_params: vec![
            AppliedParam::NonConstant {
                summary: String::new(),
            },
            AppliedParam::NonConstant {
                summary: String::new(),
            },
        ],
        compiler_binding_indices: Vec::new(),
        lambda_chain_length: 1,
        runtime_arity: 2,
        pre_applied_runtime_args: 1,
    };
    assert_eq!(
        resolve_runtime_count(AppliedKind::Auto, &outer, 2),
        0,
        "applied + lambda = 3 ≠ runtime_arity=2 → auto stays compile"
    );
}

/// Explicit `Compile` always wins over the auto heuristic.
#[test]
fn explicit_compile_disables_auto_classification() {
    let outer = OuterStructure {
        applied_params: vec![
            AppliedParam::NonConstant {
                summary: String::new(),
            },
            AppliedParam::NonConstant {
                summary: String::new(),
            },
        ],
        compiler_binding_indices: Vec::new(),
        lambda_chain_length: 1,
        runtime_arity: 3,
        pre_applied_runtime_args: 1,
    };
    assert_eq!(
        resolve_runtime_count(AppliedKind::Compile, &outer, 3),
        0,
        "explicit Compile suppresses auto-classification even on match"
    );
}

/// NonConstant compile params are
/// surfaced, including when no Constant is
/// present: the policy is "always surface", not
/// suppress-without-a-Constant.
/// Note: with `Auto` + `pre_applied_runtime_args = 0` the result
/// is all-compile.
#[test]
fn all_nonconstant_renders_as_compile_section() {
    let outer = outer_with(vec![
        AppliedParam::NonConstant {
            summary: String::new(),
        },
        AppliedParam::NonConstant {
            summary: String::new(),
        },
    ]);
    let out = format_applied_params_prefix(&outer, AppliedKind::Compile, 1)
        .expect("NonConstant compile params must be surfaced");
    assert!(
        out.contains("// Applied compile-time params"),
        "expected compile-params header: {out}"
    );
    assert!(
        out.contains("// param_0: <non-constant:"),
        "expected param_0 NonConstant line: {out}"
    );
    assert!(
        out.contains("// param_1: <non-constant:"),
        "expected param_1 NonConstant line: {out}"
    );
}

#[test]
fn single_int_param_renders_as_const_decl() {
    let outer = outer_with(vec![AppliedParam::Constant(Constant::Integer(42.into()))]);
    let out =
        format_applied_params_prefix(&outer, AppliedKind::Compile, 1).expect("expected prefix");
    assert!(
        out.contains("// const param_0: Int = 42"),
        "expected `// const param_0: Int = 42` line: {out}"
    );
    assert!(
        out.starts_with("// Applied compile-time params"),
        "expected header comment: {out}"
    );
}

#[test]
fn bytestring_param_renders_as_hex_lit() {
    let outer = outer_with(vec![AppliedParam::Constant(Constant::ByteString(vec![
        0xde, 0xad, 0xbe, 0xef,
    ]))]);
    let out =
        format_applied_params_prefix(&outer, AppliedKind::Compile, 1).expect("expected prefix");
    assert!(
        out.contains("// const param_0: ByteArray = #\"deadbeef\""),
        "expected hex-literal const: {out}"
    );
}

#[test]
fn mixed_constant_and_nonconstant_keeps_indices() {
    let outer = outer_with(vec![
        AppliedParam::Constant(Constant::Bool(true)),
        AppliedParam::NonConstant {
            summary: String::new(),
        },
        AppliedParam::Constant(Constant::Integer(7.into())),
    ]);
    let out =
        format_applied_params_prefix(&outer, AppliedKind::Compile, 1).expect("expected prefix");
    assert!(
        out.contains("// const param_0: Bool = True"),
        "expected param_0 Bool=True: {out}"
    );
    assert!(
        out.contains("// param_1: <non-constant:"),
        "expected param_1 non-constant comment: {out}"
    );
    assert!(
        out.contains("// const param_2: Int = 7"),
        "expected param_2 Int=7: {out}"
    );
}

/// `AppliedKind::Runtime` uses `runtime_arity`
/// (calling-convention count), not "all applied". With
/// `runtime_arity = 2` and 2 applied, both are runtime.
#[test]
fn runtime_kind_uses_runtime_arity_to_split() {
    let outer = outer_with(vec![
        AppliedParam::Constant(Constant::Integer(42.into())),
        AppliedParam::NonConstant {
            summary: String::new(),
        },
    ]);
    // runtime_arity = 2 (V1/V2 non-spend) ⇒ both are runtime.
    let out =
        format_applied_params_prefix(&outer, AppliedKind::Runtime, 2).expect("expected prefix");
    assert!(
        out.starts_with("// Pre-applied runtime args"),
        "expected runtime-args header: {out}"
    );
    assert!(out.contains("// runtime_arg_0: Int = 42"));
    assert!(out.contains("// runtime_arg_1: <non-constant:"));
    assert!(!out.contains("Applied compile-time params"));
}

/// `AppliedKind::Runtime` with
/// `runtime_arity = 1` (V3) and 2 applied ⇒ 1 compile + 1
/// runtime (the trailing one), which is the calling
/// convention — not "all runtime".
#[test]
fn runtime_kind_splits_when_runtime_arity_smaller_than_applied() {
    let outer = outer_with(vec![
        AppliedParam::Constant(Constant::Integer(42.into())),
        AppliedParam::Constant(Constant::Integer(7.into())),
    ]);
    // runtime_arity = 1 (V3 / unknown) ⇒ last 1 = runtime,
    // first 1 = compile.
    let out =
        format_applied_params_prefix(&outer, AppliedKind::Runtime, 1).expect("expected prefix");
    assert!(
        out.contains("// const param_0: Int = 42"),
        "first applied should be compile: {out}"
    );
    assert!(
        out.contains("// runtime_arg_0: Int = 7"),
        "last applied should be runtime: {out}"
    );
}

/// Default `Compile` mode treats ALL
/// applied params as compile, regardless of over-apply.
#[test]
fn compile_mode_treats_all_applied_as_compile_even_with_over_apply() {
    let mut outer = outer_with(vec![AppliedParam::Constant(Constant::Integer(7.into()))]);
    outer.pre_applied_runtime_args = 1;
    let out =
        format_applied_params_prefix(&outer, AppliedKind::Compile, 1).expect("expected prefix");
    assert!(
        out.contains("// const param_0: Int = 7"),
        "Compile mode should label as compile-param even with over-apply: {out}"
    );
    assert!(
        !out.contains("runtime_arg_"),
        "Compile mode must not produce runtime_arg labels: {out}"
    );
}

/// `Runtime` mode uses `runtime_arity_for(version,
/// purpose)` to determine the count. For V1/V2 with applied
/// = 3 + runtime_arity = 2: 1 compile + 2 runtime.
#[test]
fn runtime_mode_uses_runtime_arity_for_split() {
    let outer = outer_with(vec![
        AppliedParam::NonConstant {
            summary: String::new(),
        },
        AppliedParam::Constant(Constant::Integer(1.into())),
        AppliedParam::Constant(Constant::Integer(2.into())),
    ]);
    // runtime_arity = 2 (V1/V2 non-spend default).
    let out =
        format_applied_params_prefix(&outer, AppliedKind::Runtime, 2).expect("expected prefix");
    // Compile section has 1 entry (first NonConstant).
    assert!(
        out.contains("// param_0: <non-constant:"),
        "first applied should be compile: {out}"
    );
    // Runtime section has 2 entries (last 2 Constants, re-
    // indexed from 0).
    assert!(
        out.contains("// runtime_arg_0: Int = 1"),
        "first runtime arg (= second applied): {out}"
    );
    assert!(
        out.contains("// runtime_arg_1: Int = 2"),
        "second runtime arg (= third applied): {out}"
    );
}

/// User-specified per-arg split. Three
/// applied params with `RuntimeCount(1)` → first 2 are compile,
/// last is runtime. The output has BOTH header sections.
#[test]
fn runtime_count_splits_compile_and_runtime() {
    let outer = outer_with(vec![
        AppliedParam::Constant(Constant::Integer(42.into())),
        AppliedParam::Constant(Constant::ByteString(vec![0xde, 0xad])),
        AppliedParam::Constant(Constant::Integer(7.into())),
    ]);
    let out = format_applied_params_prefix(&outer, AppliedKind::RuntimeCount(1), 1)
        .expect("expected prefix");
    // Compile section.
    assert!(
        out.contains("// Applied compile-time params"),
        "expected compile-params header: {out}"
    );
    assert!(
        out.contains("// const param_0: Int = 42"),
        "expected compile param_0: {out}"
    );
    assert!(
        out.contains("// const param_1: ByteArray = #\"dead\""),
        "expected compile param_1: {out}"
    );
    // Runtime section (numbered from 0 within the runtime
    // block).
    assert!(
        out.contains("// Pre-applied runtime args"),
        "expected runtime-args header: {out}"
    );
    assert!(
        out.contains("// runtime_arg_0: Int = 7"),
        "expected runtime_arg_0 (last applied param): {out}"
    );
}

/// `RuntimeCount(0)` is equivalent to `Compile` —
/// no runtime section emitted.
#[test]
fn runtime_count_zero_acts_like_compile() {
    let outer = outer_with(vec![AppliedParam::Constant(Constant::Integer(42.into()))]);
    let out = format_applied_params_prefix(&outer, AppliedKind::RuntimeCount(0), 1)
        .expect("expected prefix");
    assert!(out.contains("// const param_0: Int = 42"));
    assert!(
        !out.contains("Pre-applied runtime args"),
        "RuntimeCount(0) must not emit runtime section: {out}"
    );
}

/// `RuntimeCount(N >= applied)` saturates to "all
/// runtime".
#[test]
fn runtime_count_excess_saturates_to_all_runtime() {
    let outer = outer_with(vec![
        AppliedParam::Constant(Constant::Integer(42.into())),
        AppliedParam::Constant(Constant::Integer(7.into())),
    ]);
    let out = format_applied_params_prefix(&outer, AppliedKind::RuntimeCount(99), 1)
        .expect("expected prefix");
    assert!(
        !out.contains("Applied compile-time params"),
        "all-runtime split must not emit compile section: {out}"
    );
    assert!(
        out.contains("// runtime_arg_0: Int = 42"),
        "expected runtime_arg_0: {out}"
    );
    assert!(
        out.contains("// runtime_arg_1: Int = 7"),
        "expected runtime_arg_1: {out}"
    );
}

/// Annotation walks hoisted const
/// declarations and prepends `// ↓ extracted from <label>`
/// when the RHS contains a hex bytestring matching an applied
/// param.
#[test]
fn annotate_matches_bytestring_param_to_extracted_const() {
    let outer = outer_with(vec![AppliedParam::Constant(Constant::ByteString(vec![
        0xde, 0xad, 0xbe, 0xef,
    ]))]);
    let rendered = "pub type X { X_0 }\n\nconst h: ByteArray = #\"deadbeef\"\n\nvalidator decompiled(_) { Void }\n";
    let (out, matched) = annotate_hoisted_consts_with_param_origin(
        rendered,
        &outer.applied_params,
        /* compile_count = */ 1,
        /* bindings = */ &[],
    );
    assert!(
        out.contains("// ↓ extracted from param_0\nconst h: ByteArray ="),
        "expected annotation above const: {out}"
    );
    assert!(
        matched.contains(&0),
        "expected param_0 in matched set: {matched:?}"
    );
}

/// a runtime-classified applied param gets labeled
/// as `runtime_arg_K` (relative to the runtime range, not the
/// absolute applied index).
#[test]
fn annotate_uses_runtime_arg_label_for_runtime_classified_params() {
    let outer = outer_with(vec![
        AppliedParam::NonConstant {
            summary: String::new(),
        },
        AppliedParam::Constant(Constant::ByteString(vec![0xca, 0xfe, 0xba, 0xbe])),
    ]);
    let rendered = "const c: ByteArray = #\"cafebabe\"\n\nvalidator decompiled(_) { Void }\n";
    // compile_count = 1 → first applied (NonConstant) is
    // compile, second (ByteString) is runtime_arg_0.
    let (out, matched) = annotate_hoisted_consts_with_param_origin(
        rendered,
        &outer.applied_params,
        1,
        /* bindings = */ &[],
    );
    assert!(
        out.contains("// ↓ extracted from runtime_arg_0"),
        "expected runtime_arg_0 label: {out}"
    );
    assert!(
        matched.contains(&1),
        "expected param_1 in matched set: {matched:?}"
    );
}

/// A `Data` BigInt compile param is DECODED to its structural
/// literal (here `42`) plus a canonical CBOR round-trip line —
/// no longer dropped as an opaque stub. The comment must still
/// avoid the `const X: Data = ...` decl shape the P6.3 audit
/// forbids.
#[test]
fn data_int_param_renders_decoded_value_and_cbor() {
    use pallas_primitives::Int as PallasInt;
    use uplc::{BigInt, PlutusData};
    let outer = outer_with(vec![AppliedParam::Constant(Constant::Data(
        PlutusData::BigInt(BigInt::Int(PallasInt::from(42))),
    ))]);
    let out =
        format_applied_params_prefix(&outer, AppliedKind::Compile, 1).expect("expected prefix");
    assert!(
        out.contains("// param_0 (Plutus Data, decoded): 42"),
        "expected decoded Data value: {out}"
    );
    assert!(
        out.contains("// param_0 (Plutus Data, CBOR): "),
        "expected CBOR round-trip line: {out}"
    );
    assert!(
        !out.contains("<opaque"),
        "Data must be decoded, not opaque: {out}"
    );
    assert!(
        !out.contains(": Data ="),
        "Data param must not emit `: Data =` (P6.3): {out}"
    );
}

/// A realistic DEX pool-config `Data` Constr (asset class + name
/// + fee) decodes to a structural `Constr(..)` tree: printable
///   asset names render `@"USDA"`, policy IDs `#"hex"`, ints inline.
///   The emitted CBOR round-trips back to the same `Data`. Output
///   stays free of the body's `Data.Constr(` artifact and any
///   `: Data` annotation.
#[test]
fn data_constr_param_renders_structural_config() {
    use uplc::{PlutusData, plutus_data};
    // Constr(0, [ Constr(0, [#"deadbeef", "USDA"]), 30 ])
    //   d879 9f  (d879 9f 44 deadbeef 44 55534441 ff)  181e  ff
    let cbor = "d8799fd8799f44deadbeef4455534441ff181eff";
    let d: PlutusData = plutus_data(&hex::decode(cbor).unwrap()).unwrap();
    let d_expected = d.clone();
    let outer = outer_with(vec![AppliedParam::Constant(Constant::Data(d))]);
    let out =
        format_applied_params_prefix(&outer, AppliedKind::Compile, 1).expect("expected prefix");
    assert!(
        out.contains(
            "// param_0 (Plutus Data, decoded): \
             Constr(0, [Constr(0, [#\"deadbeef\", @\"USDA\"]), 30])"
        ),
        "expected structural config literal: {out}"
    );
    // The emitted CBOR must round-trip to the exact same Data.
    let emitted_hex = out
        .lines()
        .find_map(|l| l.split_once("(Plutus Data, CBOR): ").map(|(_, h)| h))
        .expect("CBOR line");
    let reparsed = plutus_data(&hex::decode(emitted_hex).unwrap()).unwrap();
    assert_eq!(
        reparsed, d_expected,
        "emitted CBOR must round-trip to the same Data"
    );
    // Bare `Constr(` only (MIR-pipeline guards `Data.Constr(`),
    // and no `: Data` annotation anywhere (P6.3).
    assert!(
        !out.contains("Data.Constr("),
        "must use bare Constr(, not Data.Constr(: {out}"
    );
    assert!(!out.contains(": Data"), "must not contain `: Data`: {out}");
}

/// A `Data` BoundedBytes param (e.g. a script-hash knob) renders
/// the FULL bytestring value, not a truncated `search body` hint.
#[test]
fn data_bytestring_param_renders_full_value() {
    use uplc::{PlutusData, plutus_data};
    // 10-byte bytestring `907c341fbc305a17dead` (0x4a = bytes, len 10).
    let d: PlutusData = plutus_data(&hex::decode("4a907c341fbc305a17dead").unwrap()).unwrap();
    let outer = outer_with(vec![AppliedParam::Constant(Constant::Data(d))]);
    let out =
        format_applied_params_prefix(&outer, AppliedKind::Compile, 1).expect("expected prefix");
    assert!(
        out.contains("// param_0 (Plutus Data, decoded): #\"907c341fbc305a17dead\""),
        "expected full bytestring value: {out}"
    );
    assert!(
        !out.contains("search body for"),
        "must not emit a truncated hint: {out}"
    );
}
