use super::*;

fn nd(text: &str, index: usize) -> NamedDeBruijn {
    NamedDeBruijn {
        text: text.to_string(),
        index: uplc::ast::DeBruijn::new(index),
    }
}

fn lam(param: &str, body: Term<NamedDeBruijn>) -> Term<NamedDeBruijn> {
    Term::Lambda {
        parameter_name: Rc::new(nd(param, 0)),
        body: Rc::new(body),
        uniq_id: SYNTH_UNIQ,
    }
}

fn var(text: &str, index: usize) -> Term<NamedDeBruijn> {
    Term::Var {
        name: Rc::new(nd(text, index)),
        uniq_id: SYNTH_UNIQ,
    }
}

/// `λt.λf.t` — selects the first arg → PROVEN true.
fn church_true() -> Term<NamedDeBruijn> {
    lam("t", lam("f", var("t", 2)))
}

/// `λt.λf.f` — selects the second arg → PROVEN false.
fn church_false() -> Term<NamedDeBruijn> {
    lam("t", lam("f", var("f", 1)))
}

const V: Version = (1, 1, 0);

#[test]
fn proves_church_true_by_evaluation() {
    assert_eq!(prove_church_lambda_bool(church_true(), V), Some(true));
}

#[test]
fn proves_church_false_by_evaluation() {
    assert_eq!(prove_church_lambda_bool(church_false(), V), Some(false));
}

#[test]
fn non_church_bool_is_inconclusive() {
    // A bare integer is not a 2-arg selector: [[7 1] 0] errors → None.
    assert_eq!(prove_church_lambda_bool(int_sentinel(7), V), None);
}

#[test]
fn scan_counts_both_polarities() {
    // A program body `[church_true church_false]` embeds both combinators.
    let program = Program {
        version: V,
        term: apply(church_true(), church_false()),
    };
    let oracle = scan_church_lambda_bools(&program);
    assert_eq!(oracle.proven_true, 1);
    assert_eq!(oracle.proven_false, 1);
    assert_eq!(oracle.inconclusive, 0);
    assert_eq!(oracle.total(), 2);
}

fn err_term() -> Term<NamedDeBruijn> {
    Term::Error {
        uniq_id: SYNTH_UNIQ,
    }
}

/// Applying a data arg to identity `λx.x` runs to a value → SUCCESS.
#[test]
fn run_with_data_args_reports_success_for_identity() {
    let identity = lam("x", var("x", 1));
    let program = Program {
        version: V,
        term: identity,
    };
    let arg = uplc::plutus_data(&[0x00]).expect("decode int 0"); // CBOR 0 = int 0
    let outcome = run_with_data_args(&program, std::slice::from_ref(&arg));
    assert_eq!(outcome.applied, 1);
    assert!(outcome.success, "identity applied to data should succeed");
    assert!(outcome.error.is_none());
}

/// A validator that always `error`s → FAILURE with the machine error.
#[test]
fn run_with_data_args_reports_failure_for_error_body() {
    let always_fail = lam("x", err_term());
    let program = Program {
        version: V,
        term: always_fail,
    };
    let arg = uplc::plutus_data(&[0x00]).expect("decode int 0");
    let outcome = run_with_data_args(&program, std::slice::from_ref(&arg));
    assert!(!outcome.success, "an `error` body must report failure");
    assert!(outcome.error.is_some());
}

/// No args applied still evaluates the bare program (here, a value).
#[test]
fn run_with_data_args_zero_args() {
    let program = Program {
        version: V,
        term: int_sentinel(42),
    };
    let outcome = run_with_data_args(&program, &[]);
    assert_eq!(outcome.applied, 0);
    assert!(outcome.success);
}

#[test]
fn selector_shape_detection() {
    assert_eq!(closed_church_bool_selector(&church_true()), Some(2));
    assert_eq!(closed_church_bool_selector(&church_false()), Some(1));
    assert_eq!(closed_church_bool_selector(&int_sentinel(0)), None);
    // `λx.x` is a one-arg lambda, not a church bool.
    assert_eq!(closed_church_bool_selector(&lam("x", var("x", 1))), None);
}
