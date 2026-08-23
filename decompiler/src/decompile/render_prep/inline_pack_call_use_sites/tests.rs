use super::*;
use crate::pseudo::ast::Binder;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `const x = Pair(1, 2); x(fn(a, b) { a + b })` →
/// `let a = x.fst; let b = x.snd; a + b`.
#[test]
fn rewrites_pair_call() {
    let pack_id = VarId::new(100);
    let body = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(pack_id),
        value: PBox::new(PseudoExpr::Pair(
            PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
            PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(2))),
        )),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x", 100)),
            args: vec![PseudoExpr::Lambda {
                params: vec![binder("a", 1), binder("b", 2)],
                body: PBox::new(PseudoExpr::BinOp {
                    op: crate::pseudo::ast::BinaryOp::Add,
                    left: PBox::new(var("a", 1)),
                    right: PBox::new(var("b", 2)),
                }),
            }]
            .into(),
        }),
    };
    let out = inline_pack_call_use_sites(body);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected outer let");
    };
    // body should be `Let a = x.fst in Let b = x.snd in a + b`
    let PseudoExpr::Let {
        name: outer_name,
        value: outer_val,
        body: inner,
        ..
    } = body.into_inner()
    else {
        panic!("expected let a");
    };
    assert_eq!(outer_name, "a");
    match outer_val.as_ref() {
        PseudoExpr::FieldAccess { selector, .. } => {
            assert!(matches!(selector, FieldSelector::PairFst));
        }
        other => panic!("expected FieldAccess PairFst, got {:?}", other),
    }
    let PseudoExpr::Let {
        name: inner_name,
        value: inner_val,
        ..
    } = inner.into_inner()
    else {
        panic!("expected let b");
    };
    assert_eq!(inner_name, "b");
    match inner_val.as_ref() {
        PseudoExpr::FieldAccess { selector, .. } => {
            assert!(matches!(selector, FieldSelector::PairSnd));
        }
        other => panic!("expected FieldAccess PairSnd, got {:?}", other),
    }
}

/// `const x = (1, 2, 3); x(fn(a, b, c) { a })` →
/// `let a = x.0; let b = x.1; let c = x.2; a`.
#[test]
fn rewrites_tuple_3_call() {
    let pack_id = VarId::new(200);
    let body = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(pack_id),
        value: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Int(num_bigint::BigInt::from(1)),
                PseudoExpr::Int(num_bigint::BigInt::from(2)),
                PseudoExpr::Int(num_bigint::BigInt::from(3)),
            ]
            .into(),
        )),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x", 200)),
            args: vec![PseudoExpr::Lambda {
                params: vec![binder("a", 1), binder("b", 2), binder("c", 3)],
                body: PBox::new(var("a", 1)),
            }]
            .into(),
        }),
    };
    let out = inline_pack_call_use_sites(body);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("outer let");
    };
    // Outermost introduced let is `a = x.0` — bare index;
    // `normalize_tuple_field_ordinals` later rewrites it to `.1st`.
    let PseudoExpr::Let { name, value, .. } = body.into_inner() else {
        panic!("inlined let a");
    };
    assert_eq!(name, "a");
    match value.as_ref() {
        PseudoExpr::FieldAccess {
            selector: FieldSelector::NamedField(n),
            ..
        } => {
            assert_eq!(n, "0");
        }
        other => panic!("expected FieldAccess NamedField(0), got {:?}", other),
    }
}

/// Curried `pack(cont, extra)` preserves the extra-arg outer Apply.
#[test]
fn preserves_extra_args() {
    let pack_id = VarId::new(300);
    let body = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(pack_id),
        value: PBox::new(PseudoExpr::Pair(
            PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
            PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(2))),
        )),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x", 300)),
            args: vec![
                PseudoExpr::Lambda {
                    params: vec![binder("a", 1), binder("b", 2)],
                    body: PBox::new(var("a", 1)),
                },
                var("extra", 99),
            ]
            .into(),
        }),
    };
    let out = inline_pack_call_use_sites(body);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("outer let");
    };
    // Outer should now be Apply(<inlined>, [extra]).
    match body.into_inner() {
        PseudoExpr::Apply { args, .. } => {
            assert_eq!(args.len(), 1);
            assert!(matches!(args[0], PseudoExpr::Var { .. }));
        }
        other => panic!("expected outer Apply, got {:?}", other),
    }
}

/// Arity mismatch (Lambda has 3 params, Pair is arity-2) — no rewrite.
#[test]
fn rejects_arity_mismatch() {
    let pack_id = VarId::new(400);
    let original = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(pack_id),
        value: PBox::new(PseudoExpr::Pair(
            PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
            PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(2))),
        )),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x", 400)),
            args: vec![PseudoExpr::Lambda {
                params: vec![binder("a", 1), binder("b", 2), binder("c", 3)],
                body: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(0))),
            }]
            .into(),
        }),
    };
    let out = inline_pack_call_use_sites(original.clone());
    assert_eq!(out, original);
}

/// Continuation is a Var ref (not Lambda literal) — no rewrite.
#[test]
fn skips_var_continuation() {
    let pack_id = VarId::new(500);
    let original = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(pack_id),
        value: PBox::new(PseudoExpr::Pair(
            PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
            PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(2))),
        )),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x", 500)),
            args: vec![var("some_helper", 600)].into(),
        }),
    };
    let out = inline_pack_call_use_sites(original.clone());
    assert_eq!(out, original);
}

/// `let e = Unknown_E_0_0; let p = Pair(F, g); p(e, x, y)` →
/// `p.fst(x, y)` (church-true sentinel selects fst).
#[test]
fn rewrites_church_pair_with_true_sentinel() {
    let pair_id = VarId::new(800);
    let sentinel_id = VarId::new(900);
    let inner_fn = PseudoExpr::Lambda {
        params: vec![binder("x", 1), binder("y", 2)],
        body: PBox::new(var("y", 2)),
    };
    let body = PseudoExpr::Let {
        name: "e".to_string(),
        id: Some(sentinel_id),
        value: PBox::new(PseudoExpr::Constr {
            tag: 0,
            fields: vec![].into(),
            shape: crate::pseudo::constructor::ConstructorShape::unknown_data(0, 0),
            type_hint: None,
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "p".to_string(),
            id: Some(pair_id),
            value: PBox::new(PseudoExpr::Pair(
                PBox::new(inner_fn),
                PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(99))),
            )),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("p", 800)),
                args: vec![var("e", 900), var("x_arg", 10), var("y_arg", 11)].into(),
            }),
        }),
    };
    let out = inline_pack_call_use_sites(body);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("e let");
    };
    let PseudoExpr::Let { body, .. } = body.into_inner() else {
        panic!("p let");
    };
    // Expected: Apply { fn: FieldAccess(p, PairFst), args: [x_arg, y_arg] }
    match body.into_inner() {
        PseudoExpr::Apply { function, args } => {
            match function.into_inner() {
                PseudoExpr::FieldAccess { selector, .. } => {
                    assert!(matches!(selector, FieldSelector::PairFst));
                }
                other => panic!("expected FieldAccess PairFst, got {:?}", other),
            }
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected Apply, got {:?}", other),
    }
}

/// Tag-1 sentinel (`b`) selects `.snd`.
#[test]
fn rewrites_church_pair_with_false_sentinel() {
    let pair_id = VarId::new(801);
    let sentinel_id = VarId::new(901);
    let body = PseudoExpr::Let {
        name: "b".to_string(),
        id: Some(sentinel_id),
        value: PBox::new(PseudoExpr::Constr {
            tag: 1,
            fields: vec![].into(),
            shape: crate::pseudo::constructor::ConstructorShape::unknown_data(1, 0),
            type_hint: None,
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "p".to_string(),
            id: Some(pair_id),
            value: PBox::new(PseudoExpr::Pair(
                PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
                PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(2))),
            )),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("p", 801)),
                args: vec![var("b", 901)].into(),
            }),
        }),
    };
    let out = inline_pack_call_use_sites(body);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("b let");
    };
    let PseudoExpr::Let { body, .. } = body.into_inner() else {
        panic!("p let");
    };
    // With no extras, result is bare `p.snd`.
    match body.into_inner() {
        PseudoExpr::FieldAccess { selector, .. } => {
            assert!(matches!(selector, FieldSelector::PairSnd));
        }
        other => panic!("expected FieldAccess PairSnd, got {:?}", other),
    }
}

/// Higher-tag sentinel (tag ≥ 2) is NOT church-bool — no rewrite.
#[test]
fn skips_higher_tag_sentinel() {
    let pair_id = VarId::new(802);
    let sentinel_id = VarId::new(902);
    let original = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(sentinel_id),
        value: PBox::new(PseudoExpr::Constr {
            tag: 2,
            fields: vec![].into(),
            shape: crate::pseudo::constructor::ConstructorShape::unknown_data(2, 0),
            type_hint: None,
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "p".to_string(),
            id: Some(pair_id),
            value: PBox::new(PseudoExpr::Pair(
                PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
                PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(2))),
            )),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("p", 802)),
                args: vec![var("g", 902)].into(),
            }),
        }),
    };
    let out = inline_pack_call_use_sites(original.clone());
    assert_eq!(out, original);
}

/// `pack_var` bound to a function (Lambda) — no rewrite. Only
/// literal Tuple/Pair values qualify.
#[test]
fn skips_non_tuple_value() {
    let f_id = VarId::new(700);
    let original = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("k", 1)],
            body: PBox::new(var("k", 1)),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("f", 700)),
            args: vec![PseudoExpr::Lambda {
                params: vec![binder("a", 2), binder("b", 3)],
                body: PBox::new(var("a", 2)),
            }]
            .into(),
        }),
    };
    let out = inline_pack_call_use_sites(original.clone());
    assert_eq!(out, original);
}
