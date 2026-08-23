use super::*;
use crate::pseudo::ast::Binder;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn fail_expr(msg: &str) -> PseudoExpr {
    PseudoExpr::Error {
        message: Some(msg.to_string()),
    }
}

/// `fn assert_valid(_) { fail @"msg" }` + all-call uses → all inlined,
/// helper dropped.
#[test]
fn inlines_always_fail_and_drops_let() {
    let helper_id = VarId::new(500);
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("_", 100)],
        body: PBox::new(fail_expr("msg")),
    };
    let body = PseudoExpr::Apply {
        function: PBox::new(varref("assert_valid", 500)),
        args: vec![PseudoExpr::Unit].into(),
    };
    let expr = PseudoExpr::Let {
        name: "assert_valid".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(body),
    };
    let out = inline_always_fail_helpers(expr);
    // Result should be just the fail expression — let dropped.
    match out {
        PseudoExpr::Error { message } => {
            assert_eq!(message.as_deref(), Some("msg"));
        }
        _ => panic!("expected Error, got {:?}", out),
    }
}

/// Bare ref keeps helper alive; call sites still inlined.
#[test]
fn bare_ref_keeps_let_but_inlines_calls() {
    let helper_id = VarId::new(500);
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("_", 100)],
        body: PBox::new(fail_expr("msg")),
    };
    let body = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Apply {
                function: PBox::new(varref("assert_valid_2", 500)),
                args: vec![PseudoExpr::Unit].into(),
            },
            varref("assert_valid_2", 500), // bare ref
        ]
        .into(),
    );
    let expr = PseudoExpr::Let {
        name: "assert_valid_2".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(body),
    };
    let out = inline_always_fail_helpers(expr);
    // Let survives.
    match out {
        PseudoExpr::Let { body, .. } => {
            if let PseudoExpr::Tuple(items) = body.as_ref() {
                // First item: was `Apply(...)` → now Error
                assert!(matches!(items[0], PseudoExpr::Error { .. }));
                // Second item: bare ref — stays
                assert!(matches!(items[1], PseudoExpr::Var { .. }));
            } else {
                panic!("expected Tuple body");
            }
        }
        _ => panic!("expected Let to survive, got {:?}", out),
    }
}

/// A body that is an `Apply`, not a bare `Error` → not recognised.
#[test]
fn does_not_inline_when_body_is_not_bare_error() {
    let helper_id = VarId::new(500);
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("_", 100)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("some_helper", 999)),
            args: vec![PseudoExpr::Unit].into(),
        }),
    };
    let body = PseudoExpr::Apply {
        function: PBox::new(varref("h", 500)),
        args: vec![PseudoExpr::Unit].into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(body),
    };
    let out = inline_always_fail_helpers(expr.clone());
    assert_eq!(out, expr);
}

/// `fn f_2(x_9) { trace x_9: fail }` called `f_2(@"PT2")` → the
/// string-literal arg folds into `fail @"PT2"`, helper dropped.
#[test]
fn inlines_trace_param_fail_and_folds_string_literal() {
    let helper_id = VarId::new(500);
    let param = binder("x_9", 100);
    let helper_value = PseudoExpr::Lambda {
        params: vec![param.clone()],
        body: PBox::new(PseudoExpr::Trace {
            message: PBox::new(varref("x_9", 100)),
            value: PBox::new(PseudoExpr::Error { message: None }),
        }),
    };
    let body = PseudoExpr::Apply {
        function: PBox::new(varref("f_2", 500)),
        args: vec![PseudoExpr::string("PT2")].into(),
    };
    let expr = PseudoExpr::Let {
        name: "f_2".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(body),
    };
    let out = inline_always_fail_helpers(expr);
    // Let dropped, call site folded to `fail @"PT2"`.
    match out {
        PseudoExpr::Error { message } => assert_eq!(message.as_deref(), Some("PT2")),
        _ => panic!("expected fail @\"PT2\", got {:?}", out),
    }
}

/// A non-literal arg preserves the faithful `trace arg: fail`.
#[test]
fn inlines_trace_param_fail_keeps_trace_for_non_literal_arg() {
    let helper_id = VarId::new(500);
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("x", 100)],
        body: PBox::new(PseudoExpr::Trace {
            message: PBox::new(varref("x", 100)),
            value: PBox::new(PseudoExpr::Error { message: None }),
        }),
    };
    let body = PseudoExpr::Apply {
        function: PBox::new(varref("f_2", 500)),
        args: vec![varref("some_expr", 42)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "f_2".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(body),
    };
    let out = inline_always_fail_helpers(expr);
    match out {
        PseudoExpr::Trace { message, value } => {
            assert!(matches!(message.as_ref(), PseudoExpr::Var { .. }));
            assert!(matches!(
                value.as_ref(),
                PseudoExpr::Error { message: None }
            ));
        }
        _ => panic!("expected `trace some_expr: fail`, got {:?}", out),
    }
}

/// A `Trace` message that is not a parameter must not classify as a
/// trace-param helper.
#[test]
fn does_not_treat_non_param_trace_message_as_param() {
    let helper_id = VarId::new(500);
    // body: `trace @"const": fail` — message is a literal, not a param.
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("x", 100)],
        body: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::string("const")),
            value: PBox::new(PseudoExpr::Error { message: None }),
        }),
    };
    let body = PseudoExpr::Apply {
        function: PBox::new(varref("f", 500)),
        args: vec![PseudoExpr::string("ignored")].into(),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(body),
    };
    // Not classified as a trace-param helper (message isn't a param),
    // so the Let survives unchanged.
    let out = inline_always_fail_helpers(expr.clone());
    assert_eq!(out, expr);
}
