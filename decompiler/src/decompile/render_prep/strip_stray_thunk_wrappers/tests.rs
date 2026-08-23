use super::*;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};

fn make_when(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body,
        }],
    }
}

#[test]
fn unwraps_apply_when_with_no_args() {
    let when_expr = make_when(PseudoExpr::var("result"));
    let apply_wrap = PseudoExpr::Apply {
        function: PBox::new(when_expr.clone()),
        args: vec![].into(),
    };
    let result = strip_stray_thunk_wrappers(apply_wrap);
    assert_eq!(result, when_expr);
}

#[test]
fn unwraps_apply_if_with_no_args() {
    let if_expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("c")),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let apply_wrap = PseudoExpr::Apply {
        function: PBox::new(if_expr.clone()),
        args: vec![].into(),
    };
    let result = strip_stray_thunk_wrappers(apply_wrap);
    assert_eq!(result, if_expr);
}

#[test]
fn unwraps_apply_let_with_no_args() {
    let let_expr = PseudoExpr::let_bind("x", PseudoExpr::int(1), PseudoExpr::var("x"));
    let apply_wrap = PseudoExpr::Apply {
        function: PBox::new(let_expr.clone()),
        args: vec![].into(),
    };
    let result = strip_stray_thunk_wrappers(apply_wrap);
    assert_eq!(result, let_expr);
}

#[test]
fn unwraps_apply_trace_with_no_args() {
    let trace_expr = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::string("hit")),
        value: PBox::new(PseudoExpr::var("v")),
    };
    let apply_wrap = PseudoExpr::Apply {
        function: PBox::new(trace_expr.clone()),
        args: vec![].into(),
    };
    let result = strip_stray_thunk_wrappers(apply_wrap);
    assert_eq!(result, trace_expr);
}

#[test]
fn keeps_apply_var_with_no_args() {
    // Calling a 0-arity function is legitimate surface.
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("compute")),
        args: vec![].into(),
    };
    let result = strip_stray_thunk_wrappers(expr.clone());
    assert_eq!(result, expr, "0-arity call on Var must be preserved");
}

#[test]
fn keeps_apply_lambda_with_no_args() {
    // `(fn() { body })()` could be present as a deliberate zero-arity
    // application; conservatively preserve.
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![],
            body: PBox::new(PseudoExpr::var("body")),
        }),
        args: vec![].into(),
    };
    let result = strip_stray_thunk_wrappers(expr.clone());
    assert_eq!(result, expr);
}

#[test]
fn keeps_apply_builtin_with_no_args() {
    // Some builtins are 0-arity (e.g. `List.empty()`).
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::builtin("List.empty", vec![])),
        args: vec![].into(),
    };
    let result = strip_stray_thunk_wrappers(expr.clone());
    assert_eq!(result, expr);
}

#[test]
fn keeps_apply_with_args() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(make_when(PseudoExpr::var("result"))),
        args: vec![PseudoExpr::var("arg")].into(),
    };
    let result = strip_stray_thunk_wrappers(expr.clone());
    assert_eq!(result, expr, "Apply with >0 args must not be unwrapped");
}

#[test]
fn recurses_into_nested_apply_zero_arg() {
    // `((<when>())) → <when>` — strip both apply layers.
    let when_expr = make_when(PseudoExpr::var("inner"));
    let nested = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(when_expr.clone()),
            args: vec![].into(),
        }),
        args: vec![].into(),
    };
    let result = strip_stray_thunk_wrappers(nested);
    assert_eq!(result, when_expr);
}

#[test]
fn unwraps_force_around_when() {
    // The renderer prints `Force(non-Var)` as `x()`, so `Force(When { .. })`
    // → `when { .. }()`. Unwrap to just the when.
    let when_expr = make_when(PseudoExpr::var("result"));
    let force_wrap = PseudoExpr::Force(PBox::new(when_expr.clone()));
    let result = strip_stray_thunk_wrappers(force_wrap);
    assert_eq!(result, when_expr);
}

#[test]
fn unwraps_force_around_if() {
    let if_expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("c")),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let force_wrap = PseudoExpr::Force(PBox::new(if_expr.clone()));
    let result = strip_stray_thunk_wrappers(force_wrap);
    assert_eq!(result, if_expr);
}

#[test]
fn keeps_force_around_var() {
    // `Force(Var(_))` renders as `x()` which is a real 0-arity call; preserve.
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::var("compute")));
    let result = strip_stray_thunk_wrappers(expr.clone());
    assert_eq!(result, expr);
}

#[test]
fn unwraps_force_around_trace() {
    let trace_expr = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::string("log")),
        value: PBox::new(PseudoExpr::var("v")),
    };
    let force_wrap = PseudoExpr::Force(PBox::new(trace_expr.clone()));
    let result = strip_stray_thunk_wrappers(force_wrap);
    assert_eq!(result, trace_expr);
}

#[test]
fn unwraps_force_around_let() {
    let let_expr = PseudoExpr::let_bind("x", PseudoExpr::int(1), PseudoExpr::var("x"));
    let force_wrap = PseudoExpr::Force(PBox::new(let_expr.clone()));
    let result = strip_stray_thunk_wrappers(force_wrap);
    assert_eq!(result, let_expr);
}

#[test]
fn recurses_into_let_body() {
    let body = PseudoExpr::Apply {
        function: PBox::new(make_when(PseudoExpr::var("res"))),
        args: vec![].into(),
    };
    let expr = PseudoExpr::let_bind("x", PseudoExpr::int(1), body);
    let result = strip_stray_thunk_wrappers(expr);
    match result {
        PseudoExpr::Let { body, .. } => {
            assert!(matches!(*body, PseudoExpr::When { .. }));
        }
        _ => panic!(),
    }
}
