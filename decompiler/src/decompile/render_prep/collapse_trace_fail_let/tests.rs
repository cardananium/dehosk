use super::*;
use crate::pseudo::ast::PVec;
use crate::pseudo::var_id::VarId;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `let x = trace @"PT1": <value>; fail`
fn traced_let(value: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("PT1".to_string())),
            value: PBox::new(value),
        }),
        body: PBox::new(PseudoExpr::error()),
    }
}

#[test]
fn collapses_a_traced_pure_value() {
    let out = collapse_trace_fail_let(traced_let(PseudoExpr::Unit));
    assert!(
        matches!(&out, PseudoExpr::Error { message: Some(m) } if m == "PT1"),
        "expected `fail @\"PT1\"`, got {out:?}"
    );
}

#[test]
fn collapses_a_traced_builtin_call() {
    // A builtin callee is total for this purpose — the same line both
    // sibling sweeps draw — so the value can go.
    let call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::DataUnInt,
            args: PVec::new(),
        }),
        args: vec![var("d", 2)].into(),
    };
    let out = collapse_trace_fail_let(traced_let(call));
    assert!(
        matches!(&out, PseudoExpr::Error { message: Some(m) } if m == "PT1"),
        "expected `fail @\"PT1\"`, got {out:?}"
    );
}

#[test]
fn keeps_a_traced_call_to_unknown_code() {
    // `f(a)` with a `Var` callee is code this pass cannot see, and UPLC
    // binds strictly, so it really runs — and may trace on its way to
    // the abort. Collapsing would report one message where two were
    // emitted. A `Var` is a pure value to REFERENCE, not to CALL.
    let call = PseudoExpr::Apply {
        function: PBox::new(var("f", 3)),
        args: vec![var("a", 4)].into(),
    };
    let before = traced_let(call);
    assert_eq!(collapse_trace_fail_let(before.clone()), before);
}

#[test]
fn keeps_a_traced_force_of_a_binder() {
    // Forcing a binder runs whatever was suspended in it.
    let before = traced_let(PseudoExpr::Force(PBox::new(var("thunk", 5))));
    assert_eq!(collapse_trace_fail_let(before.clone()), before);
}

#[test]
fn collapses_a_traced_force_of_a_delayed_pure_value() {
    let out = collapse_trace_fail_let(traced_let(PseudoExpr::Force(PBox::new(PseudoExpr::Delay(
        PBox::new(PseudoExpr::Unit),
    )))));
    assert!(
        matches!(&out, PseudoExpr::Error { message: Some(m) } if m == "PT1"),
        "expected `fail @\"PT1\"`, got {out:?}"
    );
}
