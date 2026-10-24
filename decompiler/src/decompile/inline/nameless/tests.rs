use super::*;
use num_bigint::BigInt;

fn id() -> VarId {
    VarId::fresh_compat_placeholder()
}

#[test]
fn inlines_single_use_int_let() {
    // let x = 42 in x + 1 → 42 + 1
    let x = id();
    let expr = NamelessExpr::Let {
        binder: x,
        value: NBox::new(NamelessExpr::Int(BigInt::from(42))),
        body: NBox::new(NamelessExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: NBox::new(NamelessExpr::Var(x)),
            right: NBox::new(NamelessExpr::Int(BigInt::from(1))),
        }),
    };
    let result = inline_single_use_nameless(expr);
    match result {
        NamelessExpr::BinOp { left, right, .. } => {
            assert!(matches!(*left, NamelessExpr::Int(_)));
            assert!(matches!(*right, NamelessExpr::Int(_)));
        }
        _ => panic!("expected BinOp after inlining"),
    }
}

#[test]
fn keeps_multi_use_let() {
    // let x = 42 in x + x → let x = 42 in x + x
    let x = id();
    let expr = NamelessExpr::Let {
        binder: x,
        value: NBox::new(NamelessExpr::Int(BigInt::from(42))),
        body: NBox::new(NamelessExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: NBox::new(NamelessExpr::Var(x)),
            right: NBox::new(NamelessExpr::Var(x)),
        }),
    };
    let result = inline_single_use_nameless(expr);
    assert!(matches!(result, NamelessExpr::Let { .. }));
}

#[test]
fn keeps_complex_value_let() {
    // let x = f(1) in x → let x = f(1) in x (Apply isn't simple)
    let x = id();
    let f_id = id();
    let expr = NamelessExpr::Let {
        binder: x,
        value: NBox::new(NamelessExpr::Apply {
            function: NBox::new(NamelessExpr::Var(f_id)),
            args: vec![NamelessExpr::Int(BigInt::from(1))].into(),
        }),
        body: NBox::new(NamelessExpr::Var(x)),
    };
    let result = inline_single_use_nameless(expr);
    assert!(matches!(result, NamelessExpr::Let { .. }));
}

#[test]
fn preserved_binding_is_not_inlined() {
    let x = id();
    let mut preserved = HashSet::new();
    preserved.insert(x);
    let expr = NamelessExpr::Let {
        binder: x,
        value: NBox::new(NamelessExpr::Int(BigInt::from(42))),
        body: NBox::new(NamelessExpr::Var(x)),
    };
    let result = inline_single_use_nameless_preserving(expr, &preserved);
    assert!(matches!(result, NamelessExpr::Let { .. }));
}

#[test]
fn inlines_nullary_builtin() {
    // let x = List.empty() in x → List.empty()
    let x = id();
    let expr = NamelessExpr::Let {
        binder: x,
        value: NBox::new(NamelessExpr::BuiltinCall {
            name: crate::builtins::BuiltinId::expect_known("List.empty"),
            args: vec![].into(),
        }),
        body: NBox::new(NamelessExpr::Var(x)),
    };
    let result = inline_single_use_nameless(expr);
    match result {
        NamelessExpr::BuiltinCall { args, .. } => assert!(args.is_empty()),
        other => panic!("expected BuiltinCall, got {other:?}"),
    }
}

#[test]
fn inlines_multi_use_nullary_builtin() {
    // let x = List.empty() in (x, x) → (List.empty(), List.empty())
    let x = id();
    let expr = NamelessExpr::Let {
        binder: x,
        value: NBox::new(NamelessExpr::BuiltinCall {
            name: crate::builtins::BuiltinId::expect_known("List.empty"),
            args: vec![].into(),
        }),
        body: NBox::new(NamelessExpr::Tuple(
            vec![NamelessExpr::Var(x), NamelessExpr::Var(x)].into(),
        )),
    };

    let result = inline_single_use_nameless(expr);

    let items = match result {
        NamelessExpr::Tuple(items) => items,
        other => panic!("expected Tuple after inlining, got {other:?}"),
    };
    assert_eq!(items.len(), 2);
    assert!(items.iter().all(|item| {
        matches!(
            item,
            NamelessExpr::BuiltinCall { args, .. } if args.is_empty()
        )
    }));
}

#[test]
fn cascades_chain_of_simple_aliases() {
    // let a = 1; let b = a; b → 1
    let a = id();
    let b = id();
    let expr = NamelessExpr::Let {
        binder: a,
        value: NBox::new(NamelessExpr::Int(BigInt::from(1))),
        body: NBox::new(NamelessExpr::Let {
            binder: b,
            value: NBox::new(NamelessExpr::Var(a)),
            body: NBox::new(NamelessExpr::Var(b)),
        }),
    };
    let result = inline_single_use_nameless(expr);
    assert!(matches!(result, NamelessExpr::Int(_)));
}

#[test]
fn lambda_param_with_unique_var_id_no_shadow_conflict() {
    // A lambda param has a unique VarId and cannot collide
    // with an outer let's — no shadow tracking needed.
    let outer = id();
    let inner = id(); // distinct VarId
    let expr = NamelessExpr::Let {
        binder: outer,
        value: NBox::new(NamelessExpr::Int(BigInt::from(42))),
        body: NBox::new(NamelessExpr::Tuple(
            vec![
                NamelessExpr::Var(outer),
                NamelessExpr::Lambda {
                    params: vec![inner],
                    body: NBox::new(NamelessExpr::Var(inner)),
                },
            ]
            .into(),
        )),
    };
    let result = inline_single_use_nameless(expr);
    // outer used 1 time → inlined. lambda body Var(inner) should
    // remain Var(inner) — it's bound by the param, not the let.
    let items = match result {
        NamelessExpr::Tuple(items) => items,
        other => panic!("expected Tuple, got {other:?}"),
    };
    assert_eq!(items.len(), 2);
    assert!(matches!(items[0], NamelessExpr::Int(_)));
    match &items[1] {
        NamelessExpr::Lambda { body, .. } => {
            assert!(matches!(body.as_ref(), NamelessExpr::Var(actual) if *actual == inner));
        }
        other => panic!("expected Lambda, got {other:?}"),
    }
}
