use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::var_id::VarId;

#[test]
fn disabled_returns_input_unchanged() {
    let expr = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("hello".to_string())),
        value: PBox::new(PseudoExpr::int(42)),
    };
    let result = strip_all_traces_with_enabled(expr, false);
    assert!(matches!(result, PseudoExpr::Trace { .. }));
}

#[test]
fn enabled_strips_2arg_pseudo_trace() {
    let expr = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("log".to_string())),
        value: PBox::new(PseudoExpr::int(42)),
    };
    let result = strip_all_traces_with_enabled(expr, true);
    assert!(
        matches!(result, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(42)),
        "trace stripped to value, got {result:?}"
    );
}

#[test]
fn enabled_strips_2arg_builtin_trace() {
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![PseudoExpr::String("log".to_string()), PseudoExpr::int(7)].into(),
    };
    let result = strip_all_traces_with_enabled(expr, true);
    assert!(
        matches!(result, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(7)),
        "2-arg trace builtin stripped to value, got {result:?}"
    );
}

#[test]
fn enabled_strips_3arg_builtin_trace_with_apply_remainder() {
    // trace(msg, fn, arg) — curried apply chain. Strip msg,
    // result is Apply(fn, [arg]).
    let lam = PseudoExpr::Lambda {
        params: vec![Binder::new("_", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::int(11)),
    };
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![PseudoExpr::String("log".to_string()), lam, PseudoExpr::Unit].into(),
    };
    let result = strip_all_traces_with_enabled(expr, true);
    match result {
        PseudoExpr::Apply { function, args } => {
            assert!(matches!(*function, PseudoExpr::Lambda { .. }));
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected Apply, got: {other:?}"),
    }
}

#[test]
fn enabled_leaves_non_trace_builtin_alone() {
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::IfThenElse,
        args: vec![
            PseudoExpr::Bool(true),
            PseudoExpr::int(1),
            PseudoExpr::int(0),
        ]
        .into(),
    };
    let result = strip_all_traces_with_enabled(expr, true);
    assert!(matches!(
        result,
        PseudoExpr::BuiltinCall {
            name: BuiltinId::IfThenElse,
            ..
        }
    ));
}

#[test]
fn enabled_strips_recursively_nested_traces() {
    // trace("outer", trace("inner", 99))
    let inner = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("inner".to_string())),
        value: PBox::new(PseudoExpr::int(99)),
    };
    let outer = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("outer".to_string())),
        value: PBox::new(inner),
    };
    let result = strip_all_traces_with_enabled(outer, true);
    assert!(
        matches!(result, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(99)),
        "nested traces fully stripped, got {result:?}"
    );
}

/// The ctx→pass hop: the entry point must consult
/// [`RenderCtx::strip_all_traces`] and nothing else.
///
/// The pass used to read `DEHOSK_STRIP_TRACES` itself, which is why
/// this is worth pinning — its own opinion about whether it is on is
/// exactly what got removed.
#[test]
fn entry_point_is_gated_on_the_render_context() {
    let traced = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("checking".to_string())),
        value: PBox::new(PseudoExpr::int(1)),
    };

    let kept = strip_all_traces(traced.clone(), &RenderCtx::default());
    assert_eq!(kept, traced, "the default context keeps every trace");

    let ctx = RenderCtx::default().with_strip_all_traces(true);
    let stripped = strip_all_traces(traced.clone(), &ctx);
    assert_eq!(
        stripped,
        PseudoExpr::int(1),
        "with the option on, the trace is dropped and the value survives"
    );

    // The sibling flag drives the OTHER pass; it must not switch this one on.
    let sibling = RenderCtx::default().with_strip_plutustx_traces(true);
    assert_eq!(
        strip_all_traces(traced.clone(), &sibling),
        traced,
        "the PlutusTx-pair flag must not activate the blanket strip"
    );
}
