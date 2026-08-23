//! Unit tests for `validator_shape`.
//!
//! Inputs are synthetic — raw UPLC programs built by hand and
//! hand-built `PseudoExpr` ASTs; the decompile pipeline is not
//! involved.

use crate::pseudo::ast::PBox;
use std::rc::Rc;

use num_bigint::BigInt;
use uplc::ast::{Constant, NamedDeBruijn, Program, Term};
use uplc::builtins::DefaultFunction;

use super::{
    AppliedParam, PurposeDispatch, VersionDecision, detect_dispatch, infer_version, inspect_outer,
};
use crate::decompile::validator_meta::ValidatorPurpose;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

// Helpers for building synthetic UPLC terms.

fn nd(name: &str) -> Rc<NamedDeBruijn> {
    Rc::new(NamedDeBruijn {
        text: name.to_string(),
        index: 0.into(),
    })
}

fn lambda(name: &str, body: Term<NamedDeBruijn>) -> Term<NamedDeBruijn> {
    Term::Lambda {
        parameter_name: nd(name),
        body: Rc::new(body),
        uniq_id: 0,
    }
}

fn apply(function: Term<NamedDeBruijn>, argument: Term<NamedDeBruijn>) -> Term<NamedDeBruijn> {
    Term::Apply {
        function: Rc::new(function),
        argument: Rc::new(argument),
        uniq_id: 0,
    }
}

fn constant_int(n: i64) -> Term<NamedDeBruijn> {
    Term::Constant {
        value: Rc::new(Constant::Integer(BigInt::from(n))),
        uniq_id: 0,
    }
}

fn constant_bytes(bytes: Vec<u8>) -> Term<NamedDeBruijn> {
    Term::Constant {
        value: Rc::new(Constant::ByteString(bytes)),
        uniq_id: 0,
    }
}

fn builtin(fun: DefaultFunction) -> Term<NamedDeBruijn> {
    Term::Builtin { fun, uniq_id: 0 }
}

fn program(version: (usize, usize, usize), term: Term<NamedDeBruijn>) -> Program<NamedDeBruijn> {
    Program { version, term }
}

// `inspect_outer` tests

#[test]
fn inspect_outer_bare_v3_one_lambda() {
    // `fn(ctx) { 0 }` — no applied params, 1 unapplied lambda.
    let term = lambda("ctx", constant_int(0));
    let prog = program((1, 1, 0), term);
    let outer = inspect_outer(&prog);
    assert_eq!(outer.applied_params, Vec::<AppliedParam>::new());
    assert_eq!(outer.lambda_chain_length, 1);
    assert_eq!(outer.pre_applied_runtime_args, 0);
}

#[test]
fn inspect_outer_v3_with_one_unapplied_compile_param() {
    // `fn(creator) { fn(ctx) { 0 } }` — 0 applied, 2 unapplied.
    let body = lambda("ctx", constant_int(0));
    let term = lambda("creator", body);
    let prog = program((1, 1, 0), term);
    let outer = inspect_outer(&prog);
    assert!(outer.applied_params.is_empty());
    assert_eq!(outer.lambda_chain_length, 2);
}

#[test]
fn inspect_outer_v3_with_applied_compile_param() {
    // `{ fn(creator) { fn(ctx) { 0 } } }(#"abc")` — 1 applied param,
    // 2 lambdas total.
    let inner = lambda("ctx", constant_int(0));
    let outer_lambda = lambda("creator", inner);
    let term = apply(outer_lambda, constant_bytes(vec![0xab]));
    let prog = program((1, 1, 0), term);
    let outer = inspect_outer(&prog);
    assert_eq!(outer.applied_params.len(), 1);
    assert!(matches!(
        &outer.applied_params[0],
        AppliedParam::Constant(Constant::ByteString(b)) if b == &[0xab]
    ));
    // `lambda_chain_length` is the whole chain, not
    // reduced by the applied count.
    assert_eq!(outer.lambda_chain_length, 2);
}

#[test]
fn inspect_outer_v3_with_two_applied_compile_params() {
    // `{ fn(a) { fn(b) { fn(ctx) { 0 } } } }(#"x", #"y")` — 2
    // applied, 3 lambdas total.
    let inner = lambda("ctx", constant_int(0));
    let mid = lambda("b", inner);
    let outer_lambda = lambda("a", mid);
    let term = apply(
        apply(outer_lambda, constant_bytes(vec![0x01])),
        constant_bytes(vec![0x02]),
    );
    let prog = program((1, 1, 0), term);
    let outer = inspect_outer(&prog);
    assert_eq!(outer.applied_params.len(), 2);
    // applied_params are OUTER-to-INNER: a=0x01, then b=0x02.
    assert!(matches!(
        &outer.applied_params[0],
        AppliedParam::Constant(Constant::ByteString(b)) if b == &[0x01]
    ));
    assert!(matches!(
        &outer.applied_params[1],
        AppliedParam::Constant(Constant::ByteString(b)) if b == &[0x02]
    ));
    assert_eq!(outer.lambda_chain_length, 3);
}

#[test]
fn inspect_outer_non_constant_apply_argument_marked_non_constant() {
    let inner = lambda("ctx", constant_int(0));
    let outer_lambda = lambda("p", inner);
    let term = apply(
        outer_lambda,
        Term::Var {
            name: nd("foreign"),
            uniq_id: 0,
        },
    );
    let prog = program((1, 1, 0), term);
    let outer = inspect_outer(&prog);
    assert_eq!(outer.applied_params.len(), 1);
    match &outer.applied_params[0] {
        AppliedParam::NonConstant { summary } => {
            assert_eq!(summary, "var foreign");
        }
        other => panic!("expected NonConstant, got {other:?}"),
    }
}

/// the compiler pre-applies head/tail-list builtins as innermost
/// compile-time args to avoid repeated `force`; the summary
/// must name them rather than show `<non-constant>`.
#[test]
fn inspect_outer_force_builtin_summary() {
    let inner = lambda("ctx", constant_int(0));
    let outer_lambda = lambda("p", inner);
    let force_tail = Term::Force {
        body: Rc::new(builtin(DefaultFunction::TailList)),
        uniq_id: 0,
    };
    let term = apply(outer_lambda, force_tail);
    let prog = program((1, 0, 0), term);
    let outer = inspect_outer(&prog);
    assert_eq!(outer.applied_params.len(), 1);
    match &outer.applied_params[0] {
        AppliedParam::NonConstant { summary } => {
            assert_eq!(summary, "force builtin.tailList");
        }
        other => panic!("expected NonConstant force builtin, got {other:?}"),
    }
}

#[test]
fn inspect_outer_v1v2_spend_three_lambdas() {
    // `fn(datum) { fn(redeemer) { fn(ctx) { 0 } } }` — 3
    // unapplied, V1/V2 spend shape.
    let body = lambda("ctx", constant_int(0));
    let mid = lambda("redeemer", body);
    let term = lambda("datum", mid);
    let prog = program((1, 0, 0), term);
    let outer = inspect_outer(&prog);
    assert!(outer.applied_params.is_empty());
    assert_eq!(outer.lambda_chain_length, 3);
}

// `infer_version` tests

#[test]
fn infer_version_v3_from_uplc_header() {
    let term = lambda("ctx", constant_int(0));
    let prog = program((1, 1, 0), term);
    assert_eq!(infer_version(&prog), VersionDecision::DefinitelyV3);
}

#[test]
fn infer_version_v1v2_ambiguous_no_signal() {
    let term = lambda("ctx", constant_int(0));
    let prog = program((1, 0, 0), term);
    assert_eq!(infer_version(&prog), VersionDecision::AmbiguousV1OrV2);
}

#[test]
fn infer_version_v2_from_serialise_data_builtin() {
    // Body uses `SerialiseData` — V2-only.
    let body = builtin(DefaultFunction::SerialiseData);
    let term = lambda("ctx", body);
    let prog = program((1, 0, 0), term);
    assert_eq!(infer_version(&prog), VersionDecision::DefinitelyV2);
}

#[test]
fn infer_version_v2_from_secp256k1_builtin() {
    let body = builtin(DefaultFunction::VerifyEcdsaSecp256k1Signature);
    let term = lambda("ctx", body);
    let prog = program((1, 0, 0), term);
    assert_eq!(infer_version(&prog), VersionDecision::DefinitelyV2);
}

#[test]
fn infer_version_inconsistent_v3_builtin_in_v1v2_header() {
    // V3-only builtin (BLS) but UPLC header says V1/V2.
    let body = builtin(DefaultFunction::Bls12_381_G1_Add);
    let term = lambda("ctx", body);
    let prog = program((1, 0, 0), term);
    assert_eq!(
        infer_version(&prog),
        VersionDecision::InconsistentV3BuiltinInV1V2
    );
}

#[test]
fn infer_version_unknown_uplc_version() {
    let term = lambda("ctx", constant_int(0));
    let prog = program((2, 0, 0), term);
    assert!(matches!(
        infer_version(&prog),
        VersionDecision::UnknownUplcVersion { .. }
    ));
}

#[test]
fn infer_version_v3_keccak_builtin_in_v3_header() {
    // V3 header + V3-only builtin — definitively V3.
    let body = builtin(DefaultFunction::Keccak_256);
    let term = lambda("ctx", body);
    let prog = program((1, 1, 0), term);
    assert_eq!(infer_version(&prog), VersionDecision::DefinitelyV3);
}

// `detect_dispatch` tests

fn purpose_pattern(known: KnownConstructor, tag: usize) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag,
        fields: vec![],
        shape: ConstructorShape::Known(known),
    }
}

fn purpose_when_with(arms: Vec<(WhenPattern, PseudoExpr)>) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("script_info")),
        subject_name: None,
        clauses: arms
            .into_iter()
            .map(|(pattern, body)| WhenClause {
                pattern,
                guard: None,
                body,
            })
            .collect(),
    }
}

#[test]
fn detect_dispatch_v3_multi_purpose_with_spend_and_mint() {
    let when = purpose_when_with(vec![
        (
            purpose_pattern(KnownConstructor::Spend, 1),
            PseudoExpr::Unit,
        ),
        (purpose_pattern(KnownConstructor::Mint, 0), PseudoExpr::Unit),
    ]);
    let result = detect_dispatch(&when);
    match result {
        PurposeDispatch::MultiPurpose { purposes } => {
            assert!(purposes.contains(&ValidatorPurpose::Spend));
            assert!(purposes.contains(&ValidatorPurpose::Mint));
            assert_eq!(purposes.len(), 2);
        }
        other => panic!("expected MultiPurpose, got {other:?}"),
    }
}

#[test]
fn detect_dispatch_v3_multi_purpose_includes_propose() {
    // A `Proposing` (tag 5) arm resolves to the `propose` purpose. An
    // arm whose constructor maps to no purpose sets
    // `saw_non_purpose_arm` and collapses the whole dispatch to `None`.
    let when = purpose_when_with(vec![
        (
            purpose_pattern(KnownConstructor::Spend, 1),
            PseudoExpr::Unit,
        ),
        (
            purpose_pattern(KnownConstructor::Propose, 5),
            PseudoExpr::Unit,
        ),
    ]);
    let result = detect_dispatch(&when);
    match result {
        PurposeDispatch::MultiPurpose { purposes } => {
            assert!(purposes.contains(&ValidatorPurpose::Spend));
            assert!(purposes.contains(&ValidatorPurpose::Propose));
            assert_eq!(purposes.len(), 2);
        }
        other => panic!("expected MultiPurpose incl. Propose, got {other:?}"),
    }
}

#[test]
fn detect_dispatch_with_wildcard_arm_ignored() {
    let when = purpose_when_with(vec![
        (
            purpose_pattern(KnownConstructor::Spend, 1),
            PseudoExpr::Unit,
        ),
        (purpose_pattern(KnownConstructor::Mint, 0), PseudoExpr::Unit),
        (WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
    ]);
    let result = detect_dispatch(&when);
    assert!(matches!(result, PurposeDispatch::MultiPurpose { .. }));
}

#[test]
fn detect_dispatch_single_purpose_arm_refused() {
    // Only ONE purpose arm — not enough for dispatch detection.
    let when = purpose_when_with(vec![
        (
            purpose_pattern(KnownConstructor::Spend, 1),
            PseudoExpr::Unit,
        ),
        (WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
    ]);
    let result = detect_dispatch(&when);
    assert_eq!(result, PurposeDispatch::None);
}

#[test]
fn detect_dispatch_mixed_with_non_purpose_arm_refused() {
    // Arm with `Some` (not a script purpose) — bail.
    let when = purpose_when_with(vec![
        (
            purpose_pattern(KnownConstructor::Spend, 1),
            PseudoExpr::Unit,
        ),
        (purpose_pattern(KnownConstructor::Some, 0), PseudoExpr::Unit),
    ]);
    let result = detect_dispatch(&when);
    assert_eq!(result, PurposeDispatch::None);
}

#[test]
fn detect_dispatch_unknown_shape_refused() {
    // Unknown constructor — refuse to assume it's a purpose.
    let when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(0, 0),
                },
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 1,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(1, 0),
                },
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let result = detect_dispatch(&when);
    assert_eq!(result, PurposeDispatch::None);
}

#[test]
fn detect_dispatch_finds_when_below_let_chain() {
    // `let x = a; let y = b; when x is { Spend -> ...; Mint -> ... }`
    let inner_when = purpose_when_with(vec![
        (
            purpose_pattern(KnownConstructor::Spend, 1),
            PseudoExpr::Unit,
        ),
        (purpose_pattern(KnownConstructor::Mint, 0), PseudoExpr::Unit),
    ]);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: None,
        value: PBox::new(PseudoExpr::Int(1.into())),
        body: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: None,
            value: PBox::new(PseudoExpr::Int(2.into())),
            body: PBox::new(inner_when),
        }),
    };
    let result = detect_dispatch(&expr);
    assert!(matches!(result, PurposeDispatch::MultiPurpose { .. }));
}

#[test]
fn detect_dispatch_non_when_body_returns_none() {
    let expr = PseudoExpr::Int(0.into());
    assert_eq!(detect_dispatch(&expr), PurposeDispatch::None);
}

/// V3 ScriptInfo `Spending(TxOutRef, Option<Datum>)` arrives as
/// `Unknown { tag: 1, arity: 2 }` (`KnownConstructor::Spend` is the
/// V1/V2 arity-1 form); a Known purpose arm anchors it.
#[test]
fn detect_dispatch_v3_mixed_known_and_unknown_tags() {
    let when = purpose_when_with(vec![
        // Known V1/V2-style Mint anchor (Constr<0>(_)).
        (purpose_pattern(KnownConstructor::Mint, 0), PseudoExpr::Unit),
        // V3 ScriptInfo::Spending — Unknown { tag: 1, arity: 2 }.
        (
            WhenPattern::Constructor {
                type_hint: None,
                tag: 1,
                fields: vec![],
                shape: ConstructorShape::unknown_data(1, 2),
            },
            PseudoExpr::Unit,
        ),
    ]);
    let result = detect_dispatch(&when);
    match result {
        PurposeDispatch::MultiPurpose { purposes } => {
            assert!(purposes.contains(&ValidatorPurpose::Mint));
            assert!(purposes.contains(&ValidatorPurpose::Spend));
        }
        other => panic!("expected MultiPurpose for mixed Known+Unknown, got {other:?}"),
    }
}

/// Two Unknown-tag arms with no Known purpose anchor are not a
/// purpose dispatch: `when option is { Some -> ..; None -> .. }`
/// also has shape `Unknown { tag: 0 }` / `Unknown { tag: 1 }`.
#[test]
fn detect_dispatch_refuses_two_unknown_arms_without_known_anchor() {
    let when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(0, 0),
                },
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 1,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(1, 0),
                },
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let result = detect_dispatch(&when);
    assert_eq!(
        result,
        PurposeDispatch::None,
        "Unknown-only arms without a Known purpose anchor must NOT be a purpose dispatch"
    );
}

// Script-kind classification + plain-fn wrap.

use super::build_plan::classify_script_kind;
use super::{
    AppliedKind, OuterStructure, PlanInput, ScriptKind, SplitPurposes, ValidatorShapeOptions,
    WrapForm, build_plan,
};

fn outer_with_lambdas(n: usize, applied: usize) -> OuterStructure {
    let applied_params = (0..applied)
        .map(|_| AppliedParam::NonConstant {
            summary: String::new(),
        })
        .collect();
    OuterStructure {
        applied_params,
        compiler_binding_indices: Vec::new(),
        lambda_chain_length: n,
        runtime_arity: 1,
        pre_applied_runtime_args: 0,
    }
}

fn plan_input_with<'a>(
    outer: &'a OuterStructure,
    dispatch: &'a PurposeDispatch,
    script_kind: Option<ScriptKind>,
) -> PlanInput<'a> {
    let opts: &'static ValidatorShapeOptions = Box::leak(Box::new(ValidatorShapeOptions {
        purpose: None,
        split_purposes: SplitPurposes::Auto,
        script_kind,
        applied_kind: AppliedKind::Compile,
    }));
    PlanInput {
        meta: None,
        options: opts,
        script_version: None,
        outer,
        dispatch,
        detected_single_purpose: None,
        observed_script_info_purposes: Vec::new(),
        version_inferred_ambiguous: false,
    }
}

#[test]
fn classify_v3_dispatch_is_validator() {
    let outer = outer_with_lambdas(1, 0);
    let dispatch = PurposeDispatch::MultiPurpose {
        purposes: vec![ValidatorPurpose::Spend, ValidatorPurpose::Mint],
    };
    let input = plan_input_with(&outer, &dispatch, None);
    assert_eq!(classify_script_kind(&input), ScriptKind::Validator);
}

#[test]
fn classify_one_lambda_is_validator() {
    let outer = outer_with_lambdas(1, 0);
    let dispatch = PurposeDispatch::None;
    let input = plan_input_with(&outer, &dispatch, None);
    assert_eq!(classify_script_kind(&input), ScriptKind::Validator);
}

#[test]
fn classify_three_lambdas_is_validator() {
    let outer = outer_with_lambdas(3, 0);
    let dispatch = PurposeDispatch::None;
    let input = plan_input_with(&outer, &dispatch, None);
    assert_eq!(classify_script_kind(&input), ScriptKind::Validator);
}

#[test]
fn classify_zero_lambdas_is_plain() {
    let outer = outer_with_lambdas(0, 0);
    let dispatch = PurposeDispatch::None;
    let input = plan_input_with(&outer, &dispatch, None);
    assert_eq!(classify_script_kind(&input), ScriptKind::Plain);
}

#[test]
fn classify_four_plus_lambdas_is_plain() {
    let outer = outer_with_lambdas(5, 0);
    let dispatch = PurposeDispatch::None;
    let input = plan_input_with(&outer, &dispatch, None);
    assert_eq!(classify_script_kind(&input), ScriptKind::Plain);
}

#[test]
fn classify_four_lambdas_one_applied_remains_three_is_validator() {
    // 4 lambdas total, 1 applied → 3 effective unapplied → looks like
    // a V1/V2 spend (datum,redeemer,ctx) with one compile param.
    let outer = outer_with_lambdas(4, 1);
    let dispatch = PurposeDispatch::None;
    let input = plan_input_with(&outer, &dispatch, None);
    assert_eq!(classify_script_kind(&input), ScriptKind::Validator);
}

/// When the raw Apply chain over-applies (more Apply nodes
/// than Lambdas in the curried inner term), `effective_lambdas
/// = raw - applied` saturates to 0, so lambda count alone would
/// classify a V1/V2 validator debug snapshot as `Plain`.
/// Over-application is itself a strong `Validator` signal.
#[test]
fn classify_over_applied_is_validator() {
    let mut outer = outer_with_lambdas(1, 3);
    outer.pre_applied_runtime_args = 2;
    let dispatch = PurposeDispatch::None;
    let input = plan_input_with(&outer, &dispatch, None);
    assert_eq!(classify_script_kind(&input), ScriptKind::Validator);
}

#[test]
fn explicit_script_kind_plain_skips_validator_diagnostics() {
    // 1-lambda input that would otherwise hit the V3-single-purpose
    // ambiguity warning; `script_kind = Plain` suppresses it.
    let outer = outer_with_lambdas(1, 0);
    let dispatch = PurposeDispatch::None;
    let input = plan_input_with(&outer, &dispatch, Some(ScriptKind::Plain));
    let plan = build_plan(input);
    assert!(matches!(plan.wrap_form, WrapForm::PlainFn));
    assert!(
        plan.diagnostics.is_empty(),
        "plain script_kind should suppress all validator diagnostics: {:?}",
        plan.diagnostics
    );
}

#[test]
fn explicit_script_kind_validator_keeps_diagnostics_for_v3_single() {
    let outer = outer_with_lambdas(1, 0);
    let dispatch = PurposeDispatch::None;
    let opts: &'static ValidatorShapeOptions = Box::leak(Box::new(ValidatorShapeOptions {
        purpose: None,
        split_purposes: SplitPurposes::Auto,
        script_kind: Some(ScriptKind::Validator),
        applied_kind: AppliedKind::Compile,
    }));
    let input = PlanInput {
        meta: None,
        options: opts,
        script_version: Some(crate::decompile::ScriptVersion::PlutusV3),
        outer: &outer,
        dispatch: &dispatch,
        detected_single_purpose: None,
        observed_script_info_purposes: Vec::new(),
        version_inferred_ambiguous: false,
    };
    let plan = build_plan(input);
    assert!(matches!(plan.wrap_form, WrapForm::Flat { .. }));
    assert!(
        plan.diagnostics
            .iter()
            .any(|d| matches!(d.kind, super::DiagnosticKind::V3SinglePurposeAmbiguous)),
        "V3 single-purpose warning should fire when script_kind = Validator: {:?}",
        plan.diagnostics
    );
}

// PlutusTx's hoisted-builtin `let` chain on the outer Apply spine.

/// The compiler's own top-level binding sits on the SAME Apply spine as
/// the real params: `[(lam b [(lam h <5-lam>) hd]) tl D1 D2]`. Only
/// `D1`/`D2` reach the surface chain; `tl` binds `b`, eight binders above.
#[test]
fn spine_classifies_the_compilers_own_let_binding() {
    let surface = lambda(
        "p1",
        lambda(
            "p2",
            lambda("datum", lambda("redeemer", lambda("ctx", constant_int(0)))),
        ),
    );
    // `(lam h <surface>) (force headList)` — the inner administrative redex.
    let inner_let = apply(
        lambda("h", surface),
        Term::Force {
            body: Rc::new(builtin(DefaultFunction::HeadList)),
            uniq_id: 0,
        },
    );
    // `(lam b <inner_let>) (force tailList) D1 D2` — the outer one shares
    // the spine with the two params.
    let term = apply(
        apply(
            apply(
                lambda("b", inner_let),
                Term::Force {
                    body: Rc::new(builtin(DefaultFunction::TailList)),
                    uniq_id: 0,
                },
            ),
            constant_bytes(vec![0xd1]),
        ),
        constant_bytes(vec![0xd2]),
    );
    let outer = inspect_outer(&program((1, 0, 0), term));
    assert_eq!(
        outer.applied_params.len(),
        3,
        "the raw spine still carries all three args"
    );
    assert_eq!(
        outer.compiler_binding_indices,
        vec![0],
        "only slot 0 (force tailList) binds the compiler's let chain"
    );
}

/// The plain `Apply^M (Lambda^N body)` shape every non-PlutusTx compiler
/// emits has no head-position Apply, so nothing is reclassified.
#[test]
fn spine_reports_no_compiler_bindings_for_the_plain_shape() {
    let inner = lambda("p", lambda("ctx", constant_int(0)));
    let term = apply(inner, constant_bytes(vec![0xab, 0xcd, 0xef, 0x01]));
    let outer = inspect_outer(&program((1, 1, 0), term));
    assert_eq!(outer.applied_params.len(), 1);
    assert!(
        outer.compiler_binding_indices.is_empty(),
        "plain shape must reclassify nothing: {:?}",
        outer.compiler_binding_indices
    );
}

/// A `Constant` spine argument is never demoted, whatever the reduction
/// walk concludes: off-chain parameterisation applies `con data` and a
/// compiler's let-chain prologue does not.
#[test]
fn spine_never_demotes_a_constant_argument() {
    // `(lam b [(lam h <1-lam>) hd]) D1` — the walk strands slot 0, but it
    // holds a constant, so it stays a param.
    let inner_let = apply(
        lambda("h", lambda("ctx", constant_int(0))),
        builtin(DefaultFunction::HeadList),
    );
    let term = apply(lambda("b", inner_let), constant_int(7));
    let outer = inspect_outer(&program((1, 1, 0), term));
    assert!(
        outer.compiler_binding_indices.is_empty(),
        "a constant argument must stay a param: {:?}",
        outer.compiler_binding_indices
    );
}

/// `param_N` numbers the params, so a compiled-in binding on the spine
/// does not push every real param one along.
#[test]
fn param_label_index_skips_compiler_bindings() {
    use super::param_surface::param_label_index;
    assert_eq!(param_label_index(&[0], 0), None, "slot 0 is a binding");
    assert_eq!(
        param_label_index(&[0], 1),
        Some(0),
        "first real param is param_0"
    );
    assert_eq!(param_label_index(&[0], 2), Some(1));
    assert_eq!(param_label_index(&[], 2), Some(2), "no bindings: identity");
    assert_eq!(param_label_index(&[1], 2), Some(1));
}

/// A builtin on the spine is not a parameter, whatever the head does
/// with it. No route that applies a parameter to a deployed script can
/// produce one — they all carry CBOR and emit `con data`.
#[test]
fn spine_demotes_a_builtin_argument() {
    let head = lambda(
        "f",
        apply(
            Term::Var {
                name: nd("f"),
                uniq_id: 0,
            },
            constant_int(1),
        ),
    );
    let term = apply(head, builtin(DefaultFunction::HeadList));
    let outer = inspect_outer(&program((1, 1, 0), term));
    assert_eq!(outer.applied_params.len(), 1, "the spine still carries it");
    assert_eq!(
        outer.compiler_binding_indices,
        vec![0],
        "a builtin cannot be an applied parameter"
    );
}

/// A 1.1.0 `constr` term likewise: `Data` has no SOP constructor, so
/// nothing off-chain can hand one to a script.
#[test]
fn spine_demotes_a_constr_argument() {
    let term = apply(
        lambda("p", lambda("ctx", constant_int(0))),
        Term::Constr {
            tag: 0,
            fields: Vec::new(),
            uniq_id: 0,
        },
    );
    let outer = inspect_outer(&program((1, 1, 0), term));
    assert_eq!(outer.compiler_binding_indices, vec![0]);
}
