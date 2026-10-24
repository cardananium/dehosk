use super::*;
use num_bigint::BigInt;

fn id() -> VarId {
    VarId::fresh_binding()
}

#[test]
fn drops_unused_pure_let() {
    // let _ = 42 in 7 → 7
    let unused = id();
    let expr = NamelessExpr::Let {
        binder: unused,
        value: NBox::new(NamelessExpr::Int(BigInt::from(42))),
        body: NBox::new(NamelessExpr::Int(BigInt::from(7))),
    };
    let result = eliminate_dead_lets_nameless(expr);
    assert!(matches!(result, NamelessExpr::Int(ref n) if *n == 7.into()));
}

#[test]
fn keeps_used_let() {
    let used = id();
    let expr = NamelessExpr::Let {
        binder: used,
        value: NBox::new(NamelessExpr::Int(BigInt::from(42))),
        body: NBox::new(NamelessExpr::Var(used)),
    };
    let result = eliminate_dead_lets_nameless(expr);
    assert!(matches!(result, NamelessExpr::Let { .. }));
}

#[test]
fn keeps_let_with_apply_value_even_unused() {
    // let _ = f(x) in 7 → let _ = f(x) in 7 (Apply may have effects)
    let unused = id();
    let f = id();
    let x = id();
    let expr = NamelessExpr::Let {
        binder: unused,
        value: NBox::new(NamelessExpr::Apply {
            function: NBox::new(NamelessExpr::Var(f)),
            args: vec![NamelessExpr::Var(x)].into(),
        }),
        body: NBox::new(NamelessExpr::Int(BigInt::from(7))),
    };
    let result = eliminate_dead_lets_nameless(expr);
    assert!(matches!(result, NamelessExpr::Let { .. }));
}

#[test]
fn keeps_let_with_explicit_error_value() {
    let unused = id();
    let expr = NamelessExpr::Let {
        binder: unused,
        value: NBox::new(NamelessExpr::Error {
            message: Some("boom".to_string()),
        }),
        body: NBox::new(NamelessExpr::Int(BigInt::from(7))),
    };
    let result = eliminate_dead_lets_nameless(expr);
    assert!(matches!(result, NamelessExpr::Let { .. }));
}

#[test]
fn keeps_let_with_explicit_error_inside_when_value() {
    use crate::pseudo::constructor::ConstructorShape;
    use crate::pseudo::nameless::NamelessPattern;

    let unused = id();
    let subject = id();
    let expr = NamelessExpr::Let {
        binder: unused,
        value: NBox::new(NamelessExpr::When {
            subject: NBox::new(NamelessExpr::Var(subject)),
            subject_name: None,
            clauses: vec![NamelessClause {
                pattern: NamelessPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(0, 0),
                },
                guard: None,
                body: NamelessExpr::Error {
                    message: Some("boom".to_string()),
                },
            }]
            .into(),
        }),
        body: NBox::new(NamelessExpr::Int(BigInt::from(7))),
    };
    let result = eliminate_dead_lets_nameless(expr);
    assert!(matches!(result, NamelessExpr::Let { .. }));
}

#[test]
fn drops_chain_of_unused_pure_lets() {
    // let a = 1; let b = 2; let c = 3; 99 → 99
    let a = id();
    let b = id();
    let c = id();
    let expr = NamelessExpr::Let {
        binder: a,
        value: NBox::new(NamelessExpr::Int(BigInt::from(1))),
        body: NBox::new(NamelessExpr::Let {
            binder: b,
            value: NBox::new(NamelessExpr::Int(BigInt::from(2))),
            body: NBox::new(NamelessExpr::Let {
                binder: c,
                value: NBox::new(NamelessExpr::Int(BigInt::from(3))),
                body: NBox::new(NamelessExpr::Int(BigInt::from(99))),
            }),
        }),
    };
    let result = eliminate_dead_lets_nameless(expr);
    assert!(matches!(result, NamelessExpr::Int(ref n) if *n == 99.into()));
}

#[test]
fn keeps_outer_let_when_body_uses_inner() {
    // let outer = 1; let inner = outer; inner
    // outer used (1), inner used (1) → both kept
    let outer = id();
    let inner = id();
    let expr = NamelessExpr::Let {
        binder: outer,
        value: NBox::new(NamelessExpr::Int(BigInt::from(1))),
        body: NBox::new(NamelessExpr::Let {
            binder: inner,
            value: NBox::new(NamelessExpr::Var(outer)),
            body: NBox::new(NamelessExpr::Var(inner)),
        }),
    };
    let result = eliminate_dead_lets_nameless(expr);
    // Outer let is kept (body's inner uses it)
    match result {
        NamelessExpr::Let { binder, body, .. } => {
            assert_eq!(binder, outer);
            assert!(matches!(body.as_ref(), NamelessExpr::Let { .. }));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn nameless_dce_does_not_need_textual_fallback() {
    // In nameless IR the binder VarId is the SOLE identity:
    // no "same NAME, different ID" class exists, so DCE is a
    // single VarId-count check.
    let unused = id();
    let body = NamelessExpr::Int(BigInt::from(0));
    let expr = NamelessExpr::Let {
        binder: unused,
        value: NBox::new(NamelessExpr::Int(BigInt::from(1))),
        body: NBox::new(body),
    };
    let result = eliminate_dead_lets_nameless(expr);
    assert!(matches!(result, NamelessExpr::Int(_)));
}

// ===== strict-failpoint retention (nested positions) =====
// Each value below puts the failpoint BELOW the top level (inside a Pair) so
// it bypasses the top-level `matches!(Apply|Force|Trace|Error)` floor and
// exercises `nameless_contains_strict_failpoint`.

fn pair_with(value_a: NamelessExpr) -> NamelessExpr {
    NamelessExpr::Pair(
        NBox::new(value_a),
        NBox::new(NamelessExpr::Int(BigInt::from(0))),
    )
}

fn dead_let(value: NamelessExpr) -> NamelessExpr {
    NamelessExpr::Let {
        binder: id(),
        value: NBox::new(value),
        body: NBox::new(NamelessExpr::Int(BigInt::from(7))),
    }
}

#[test]
fn keeps_let_with_nested_nonbuiltin_apply() {
    // let _ = Pair(f(x), 0) in 7 — a non-builtin call nested in a Pair field
    // can fail; the let must NOT be dropped.
    let f = id();
    let x = id();
    let value = pair_with(NamelessExpr::Apply {
        function: NBox::new(NamelessExpr::Var(f)),
        args: vec![NamelessExpr::Var(x)].into(),
    });
    assert!(matches!(
        eliminate_dead_lets_nameless(dead_let(value)),
        NamelessExpr::Let { .. }
    ));
}

#[test]
fn drops_let_with_nested_pure_builtin() {
    // let _ = Pair(headList([]), 0) in 7 — a builtin-headed call with pure
    // operands is treated as total; the let is dropped (negative control).
    let value = pair_with(NamelessExpr::BuiltinCall {
        name: crate::BuiltinId::ListHead,
        args: vec![NamelessExpr::List {
            elements: vec![].into(),
            tail: None,
        }]
        .into(),
    });
    assert!(matches!(
        eliminate_dead_lets_nameless(dead_let(value)),
        NamelessExpr::Int(_)
    ));
}

#[test]
fn keeps_let_with_nested_force_var() {
    // let _ = Pair(force(opaque_thunk), 0) in 7 — forcing an opaque thunk
    // executes unknown suspended code that can fail; retain.
    let thunk = id();
    let value = pair_with(NamelessExpr::Force(NBox::new(NamelessExpr::Var(thunk))));
    assert!(matches!(
        eliminate_dead_lets_nameless(dead_let(value)),
        NamelessExpr::Let { .. }
    ));
}

#[test]
fn keeps_let_with_nested_force_delay_error() {
    // let _ = Pair(force(delay(error)), 0) in 7 — forcing opens the delay and
    // runs the error; retain.
    let value = pair_with(NamelessExpr::Force(NBox::new(NamelessExpr::Delay(
        NBox::new(NamelessExpr::Error { message: None }),
    ))));
    assert!(matches!(
        eliminate_dead_lets_nameless(dead_let(value)),
        NamelessExpr::Let { .. }
    ));
}

#[test]
fn drops_let_with_nested_force_builtin() {
    // let _ = Pair(force(headList), 0) in 7 — forcing a builtin is the arity
    // mechanism (total); with no failing operand the let is dropped (control).
    let value = pair_with(NamelessExpr::Force(NBox::new(NamelessExpr::BuiltinCall {
        name: crate::BuiltinId::ListHead,
        args: vec![].into(),
    })));
    assert!(matches!(
        eliminate_dead_lets_nameless(dead_let(value)),
        NamelessExpr::Int(_)
    ));
}
