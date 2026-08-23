use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::var_id::VarId;

fn trace_pair(msg: &str, inner_body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String(msg.to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::fresh_binding())],
                body: PBox::new(inner_body),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    }
}

#[test]
fn strips_canonical_plutustx_entering_pair() {
    let body = PseudoExpr::int(42);
    let expr = trace_pair("entering fooBar", body.clone());
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(
        matches!(stripped, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(42)),
        "expected strip to body, got: {stripped:?}"
    );
}

#[test]
fn strips_nested_entering_pair_recursively() {
    // trace("entering outer", fn(_) { trace("entering inner", fn(_) { 42 }, _) }, _)
    // After strip: 42.
    let inner = trace_pair("entering inner", PseudoExpr::int(42));
    let outer = trace_pair("entering outer", inner);
    let stripped = strip_plutustx_trace_pairs(outer);
    assert!(
        matches!(stripped, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(42)),
        "expected nested strip to inner-most body, got: {stripped:?}"
    );
}

#[test]
fn leaves_non_trace_builtin_alone() {
    // Builtin other than Trace — must not strip even with similar args shape.
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::IfThenElse,
        args: vec![
            PseudoExpr::String("entering fooBar".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::fresh_binding())],
                body: PBox::new(PseudoExpr::int(1)),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(matches!(
        stripped,
        PseudoExpr::BuiltinCall {
            name: BuiltinId::IfThenElse,
            ..
        }
    ));
}

#[test]
fn leaves_trace_with_wrong_message_prefix_alone() {
    // Trace whose message doesn't start with "entering " — likely a user-facing
    // user-facing trace. Must not strip.
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("user trace message".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::fresh_binding())],
                body: PBox::new(PseudoExpr::int(1)),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(matches!(
        stripped,
        PseudoExpr::BuiltinCall {
            name: BuiltinId::Trace,
            ..
        }
    ));
}

#[test]
fn leaves_trace_with_non_underscore_lambda_param_alone() {
    // Trace with a Lambda whose param is NOT named "_" — implies the
    // body uses the value. Not the safe PlutusTx pattern.
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("entering fooBar".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("x", VarId::fresh_binding())],
                body: PBox::new(PseudoExpr::int(1)),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(matches!(
        stripped,
        PseudoExpr::BuiltinCall {
            name: BuiltinId::Trace,
            ..
        }
    ));
}

#[test]
fn leaves_2_arg_user_trace_alone() {
    // 2-arg trace(msg, value) — the surface's user-facing trace.
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("entering fooBar".to_string()),
            PseudoExpr::int(1),
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(
        matches!(stripped, PseudoExpr::BuiltinCall { name: BuiltinId::Trace, args } if args.len() == 2)
    );
}

#[test]
fn strips_pair_with_double_underscore_param() {
    // PlutusTx emits `fn(__N)` for instrumentation thunks; this
    // pass runs before `rename_unused_lambda_params` renames
    // them to `_`, so the gate accepts any underscore-prefixed
    // param name.
    let body = PseudoExpr::int(99);
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("entering plutusTxHelper".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("__2", VarId::fresh_binding())],
                body: PBox::new(body),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(
        matches!(stripped, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(99)),
        "expected strip with __2 param, got: {stripped:?}"
    );
}

#[test]
fn leaves_lambda_with_non_underscore_prefix_alone() {
    // A param like `foo` is not the unused-arg convention; the
    // body might use it. Don't strip.
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("entering fooBar".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("foo", VarId::fresh_binding())],
                body: PBox::new(PseudoExpr::int(1)),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(matches!(
        stripped,
        PseudoExpr::BuiltinCall {
            name: BuiltinId::Trace,
            ..
        }
    ));
}

#[test]
fn leaves_standalone_exit_trace_pseudo_variant_alone() {
    // A standalone `Trace { message: "exiting X" }`
    // without a matching outer `entering X` wrapper must NOT be
    // stripped — it could be an user-facing trace whose
    // message happens to start with "exiting ".
    let body = PseudoExpr::int(7);
    let expr = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("exiting bar".to_string())),
        value: PBox::new(body),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(
        matches!(stripped, PseudoExpr::Trace { .. }),
        "standalone exit-trace must be left intact (no pairing context), got: {stripped:?}"
    );
}

#[test]
fn leaves_user_trace_pseudo_variant_alone() {
    // 2-arg `Trace { message: "user log", value: ... }` — surface
    // user-facing trace, not PlutusTx instrumentation. Don't strip.
    let expr = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("user log".to_string())),
        value: PBox::new(PseudoExpr::int(42)),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(matches!(stripped, PseudoExpr::Trace { .. }));
}

#[test]
fn strips_full_plutustx_pair_with_exit_inside() {
    // Combined shape: outer 3-arg BuiltinCall(Trace, entering, fn(_){...})
    // wraps an inner 2-arg PseudoExpr::Trace { exiting X, body }.
    // Stripping both layers gives the bare body.
    let body = PseudoExpr::int(100);
    let exit = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("exiting foo".to_string())),
        value: PBox::new(body),
    };
    let outer = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("entering foo".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::fresh_binding())],
                body: PBox::new(exit),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(outer);
    assert!(
        matches!(stripped, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(100)),
        "expected full pair strip to body, got: {stripped:?}"
    );
}

#[test]
fn leaves_lambda_with_param_referenced_in_body() {
    // Even with a `_`-prefixed param name, a body that
    // free-references the param must NOT strip: dropping the
    // wrapper would leave that reference free.
    let param_id = VarId::fresh_binding();
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("entering fooBar".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_x", param_id)],
                body: PBox::new(PseudoExpr::var_with_id("_x", param_id)),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(
        matches!(
            stripped,
            PseudoExpr::BuiltinCall {
                name: BuiltinId::Trace,
                ..
            }
        ),
        "must not strip when body references the param, got: {stripped:?}"
    );
}

#[test]
fn leaves_pair_with_non_unit_third_arg() {
    // args[2] must be exactly Unit; dropping anything else (an
    // Apply, a trace with side effects) changes semantics.
    // Must NOT strip.
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("entering fooBar".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::fresh_binding())],
                body: PBox::new(PseudoExpr::int(1)),
            },
            // Not Unit — a side-effecting Trace.
            PseudoExpr::Trace {
                message: PBox::new(PseudoExpr::String("important log".to_string())),
                value: PBox::new(PseudoExpr::int(0)),
            },
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    assert!(
        matches!(
            stripped,
            PseudoExpr::BuiltinCall {
                name: BuiltinId::Trace,
                ..
            }
        ),
        "must not strip when args[2] is non-Unit, got: {stripped:?}"
    );
}

#[test]
fn strips_paired_exit_trace_with_matching_identifier() {
    // Matching identifiers strip both layers — the outer
    // `entering foo` wrap and the inner `exiting foo` trace —
    // leaving the bare body.
    let body = PseudoExpr::int(123);
    let inner_exit = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("exiting foo".to_string())),
        value: PBox::new(body),
    };
    let outer = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("entering foo".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::fresh_binding())],
                body: PBox::new(inner_exit),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(outer);
    assert!(
        matches!(stripped, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(123)),
        "matched pair must strip both layers to body, got: {stripped:?}"
    );
}

#[test]
fn keeps_inner_exit_trace_when_identifier_mismatches() {
    // A mismatched inner exit-trace identifier strips only the
    // OUTER wrap; the inner trace is preserved — it may be an
    // user trace whose message coincidentally starts with
    // "exiting ".
    let body = PseudoExpr::int(456);
    let inner = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("exiting BAR".to_string())),
        value: PBox::new(body),
    };
    let outer = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("entering foo".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::fresh_binding())],
                body: PBox::new(inner),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(outer);
    // Outer is stripped; inner Trace (with mismatched ident) stays.
    assert!(
        matches!(&stripped, PseudoExpr::Trace { message, .. }
            if matches!(message.as_ref(), PseudoExpr::String(s) if s == "exiting BAR")),
        "outer strip should keep mismatched inner exit-trace, got: {stripped:?}"
    );
}

#[test]
fn strips_extended_form_preserves_trailing_args_as_apply() {
    // 5-arg form: `trace(msg, lam, Void, x, y)` is the
    // flattened Apply chain `((trace(msg)(lam)(Void))(x))(y)`,
    // so the strip leaves `Apply(stripped_lam_body, [x, y])`.
    let exit_body = PseudoExpr::int(99);
    let inner_exit = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("exiting baz".to_string())),
        value: PBox::new(exit_body),
    };
    let extra_x = PseudoExpr::var_with_id("x", VarId::fresh_binding());
    let extra_y = PseudoExpr::var_with_id("y", VarId::fresh_binding());
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::Trace,
        args: vec![
            PseudoExpr::String("entering baz".to_string()),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::fresh_binding())],
                body: PBox::new(inner_exit),
            },
            PseudoExpr::Unit,
            extra_x,
            extra_y,
        ]
        .into(),
    };
    let stripped = strip_plutustx_trace_pairs(expr);
    // Expected: Apply(Int(99), [x, y])
    match stripped {
        PseudoExpr::Apply { function, args } => {
            assert!(
                matches!(*function, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(99))
            );
            assert_eq!(args.len(), 2);
            assert!(matches!(args[0], PseudoExpr::Var { ref name, .. } if name == "x"));
            assert!(matches!(args[1], PseudoExpr::Var { ref name, .. } if name == "y"));
        }
        other => panic!("expected Apply(stripped, [x, y]), got: {other:?}"),
    }
}

#[test]
fn idempotent_after_strip() {
    let body = PseudoExpr::int(42);
    let expr = trace_pair("entering fooBar", body);
    let once = strip_plutustx_trace_pairs(expr);
    let twice = strip_plutustx_trace_pairs(once.clone());
    assert!(matches!(once, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(42)));
    assert!(matches!(twice, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(42)));
}
