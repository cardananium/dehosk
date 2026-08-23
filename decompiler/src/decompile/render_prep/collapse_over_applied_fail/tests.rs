use super::*;

fn fail(msg: &str) -> PseudoExpr {
    PseudoExpr::Error {
        message: Some(msg.to_string()),
    }
}

fn varref(name: &str, id: VarId) -> PseudoExpr {
    PseudoExpr::var_with_id(name, id)
}

/// `const a = fail; a(x, y)` → `const a = fail; a`.
#[test]
fn collapses_over_applied_fail_const() {
    let a = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "a".into(),
        id: Some(a),
        value: PBox::new(fail("PT1")),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("a", a)),
            args: vec![PseudoExpr::Bool(true), PseudoExpr::int(3)].into(),
        }),
    };
    let out = collapse_over_applied_fail(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let")
    };
    assert!(
        matches!(*body, PseudoExpr::Var { .. }),
        "call collapsed to the fail var"
    );
}

/// A literal `fail(args)` collapses to `fail`.
#[test]
fn collapses_literal_fail_application() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(fail("boom")),
        args: vec![PseudoExpr::Unit].into(),
    };
    let out = collapse_over_applied_fail(expr);
    assert!(matches!(out, PseudoExpr::Error { .. }));
}

/// An argument carrying a strict failpoint is NOT dropped (retention-biased).
#[test]
fn keeps_args_with_strict_failpoint() {
    let a = VarId::fresh_binding();
    // arg = a non-builtin call `g(x)` — a strict failpoint.
    let risky_arg = PseudoExpr::Apply {
        function: PBox::new(varref("g", VarId::fresh_binding())),
        args: vec![PseudoExpr::Unit].into(),
    };
    let expr = PseudoExpr::Let {
        name: "a".into(),
        id: Some(a),
        value: PBox::new(fail("PT1")),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("a", a)),
            args: vec![risky_arg].into(),
        }),
    };
    let out = collapse_over_applied_fail(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let")
    };
    assert!(
        matches!(*body, PseudoExpr::Apply { .. }),
        "risky arg preserved"
    );
}

/// A non-fail callee is untouched.
#[test]
fn leaves_normal_application() {
    let f = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(varref("f", f)),
        args: vec![PseudoExpr::int(1)].into(),
    };
    let out = collapse_over_applied_fail(expr);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}
