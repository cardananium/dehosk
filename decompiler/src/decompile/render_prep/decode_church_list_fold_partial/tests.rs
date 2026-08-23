use super::*;
use crate::pseudo::constructor::ConstructorShape;
use num_bigint::BigInt;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn nil_const(let_id: u32, in_body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "e".to_string(),
        id: Some(VarId::new(let_id)),
        value: PBox::new(PseudoExpr::Constr {
            tag: 0,
            fields: vec![].into(),
            shape: ConstructorShape::unknown_data(0, 0),
            type_hint: None,
        }),
        body: PBox::new(in_body),
    }
}

/// `let e = Constr0; [H, ..e](k)` (k is a Var) →
/// `let e = Constr0; fn(n) { k(H, n) }` (no alias let since k is Var).
#[test]
fn rewrites_single_element_with_var_k() {
    let e_id = 10;
    let inner = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::List {
            elements: vec![PseudoExpr::Int(BigInt::from(42))].into(),
            tail: Some(PBox::new(var("e", e_id))),
        }),
        args: vec![var("k", 99)].into(),
    };
    let input = nil_const(e_id, inner);
    let out = decode_church_list_fold_partial(input);
    // outer let e = Constr0 is preserved
    let PseudoExpr::Let { name, body, .. } = out else {
        panic!("e let");
    };
    assert_eq!(name, "e");
    // body should be Lambda(n) { k(42, n) } — no alias let since k is Var
    match body.into_inner() {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].name, "n");
            match body.into_inner() {
                PseudoExpr::Apply { function, args } => {
                    // function should be Var(k)
                    assert!(matches!(*function, PseudoExpr::Var { ref name, .. } if name == "k"));
                    // args = [42, Var(n)]
                    assert_eq!(args.len(), 2);
                    assert!(matches!(args[0], PseudoExpr::Int(_)));
                    assert!(matches!(args[1], PseudoExpr::Var { ref name, .. } if name == "n"));
                }
                other => panic!("expected Apply inside Lambda, got {:?}", other),
            }
        }
        other => panic!("expected Lambda, got {:?}", other),
    }
}

/// Non-Var `k` → wrap in `let k_alias = k` so the runtime
/// evaluates `k` once and reuses across cons steps.
#[test]
fn binds_complex_k_via_let_alias() {
    let e_id = 11;
    let inner = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::List {
            elements: vec![
                PseudoExpr::Int(BigInt::from(1)),
                PseudoExpr::Int(BigInt::from(2)),
            ]
            .into(),
            tail: Some(PBox::new(var("e", e_id))),
        }),
        args: vec![PseudoExpr::Apply {
            function: PBox::new(var("compute_k", 50)),
            args: vec![var("ctx", 51)].into(),
        }]
        .into(),
    };
    let input = nil_const(e_id, inner);
    let out = decode_church_list_fold_partial(input);
    // outer let e = Constr0, then Lambda(n) { let k_alias = ...; k_alias(1, k_alias(2, n)) }
    let PseudoExpr::Let { body, .. } = out else {
        panic!("e let");
    };
    let PseudoExpr::Lambda { body: lam_body, .. } = body.into_inner() else {
        panic!("Lambda");
    };
    match lam_body.into_inner() {
        PseudoExpr::Let {
            name: alias_name,
            body: chain,
            ..
        } => {
            assert_eq!(alias_name, "k_alias");
            // chain should be Apply(k_alias, [1, Apply(k_alias, [2, Var(n)])])
            if let PseudoExpr::Apply { function, args } = chain.into_inner() {
                assert!(matches!(*function, PseudoExpr::Var { ref name, .. } if name == "k_alias"));
                assert!(matches!(args[0], PseudoExpr::Int(_)));
                // args[1] is the inner k_alias(2, n) apply
                if let PseudoExpr::Apply {
                    function: f2,
                    args: a2,
                } = &args[1]
                {
                    assert!(
                        matches!(f2.as_ref(), PseudoExpr::Var { name, .. } if name == "k_alias")
                    );
                    assert!(matches!(a2[0], PseudoExpr::Int(_)));
                    assert!(matches!(a2[1], PseudoExpr::Var { ref name, .. } if name == "n"));
                } else {
                    panic!("expected nested Apply");
                }
            } else {
                panic!("expected outer Apply in chain");
            }
        }
        other => panic!("expected Let(k_alias = ...), got {:?}", other),
    }
}

/// Tail is a Var but NOT a nil sentinel — no rewrite.
#[test]
fn rejects_non_nil_tail() {
    // No let-binding for the tail-var ⇒ not in nil_vids.
    let other_tail_id = 30;
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::List {
            elements: vec![PseudoExpr::Int(BigInt::from(1))].into(),
            tail: Some(PBox::new(var("other", other_tail_id))),
        }),
        args: vec![var("k", 99)].into(),
    };
    // Need at least one nil sentinel SOMEWHERE so the pass doesn't early-return
    let e_id = 10;
    let wrapped = nil_const(e_id, input);
    let out = decode_church_list_fold_partial(wrapped.clone());
    // Should be structurally identical to input (no rewrite fired).
    assert_eq!(out, wrapped);
}

/// 2 args to the list — NOT a partial fold; no rewrite.
#[test]
fn rejects_full_fold_two_args() {
    let e_id = 12;
    let inner = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::List {
            elements: vec![PseudoExpr::Int(BigInt::from(1))].into(),
            tail: Some(PBox::new(var("e", e_id))),
        }),
        args: vec![var("k", 99), var("z", 100)].into(),
    };
    let input = nil_const(e_id, inner);
    let out = decode_church_list_fold_partial(input.clone());
    assert_eq!(out, input);
}

/// Let-chain on function position is preserved around the
/// rewritten Lambda.
#[test]
fn preserves_function_side_let_chain() {
    let e_id = 13;
    // Apply { fn: Let { let_inner_x = 5; List[42, ..e] }, args: [k] }
    let inner_apply = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Let {
            name: "let_inner_x".to_string(),
            id: Some(VarId::new(40)),
            value: PBox::new(PseudoExpr::Int(BigInt::from(5))),
            body: PBox::new(PseudoExpr::List {
                elements: vec![PseudoExpr::Int(BigInt::from(42))].into(),
                tail: Some(PBox::new(var("e", e_id))),
            }),
        }),
        args: vec![var("k", 99)].into(),
    };
    let input = nil_const(e_id, inner_apply);
    let out = decode_church_list_fold_partial(input);
    // expect: let e = Constr0; let let_inner_x = 5; Lambda(n) { k(42, n) }
    let PseudoExpr::Let {
        body, name: e_name, ..
    } = out
    else {
        panic!("e let");
    };
    assert_eq!(e_name, "e");
    let PseudoExpr::Let {
        body,
        name: inner_name,
        ..
    } = body.into_inner()
    else {
        panic!("inner let preserved")
    };
    assert_eq!(inner_name, "let_inner_x");
    assert!(matches!(*body, PseudoExpr::Lambda { .. }));
}

/// Already-rewritten output (no `Apply { fn: List, args: [_] }`)
/// is idempotent under a second pass.
#[test]
fn idempotent_on_already_rewritten() {
    let e_id = 14;
    let inner = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::List {
            elements: vec![PseudoExpr::Int(BigInt::from(7))].into(),
            tail: Some(PBox::new(var("e", e_id))),
        }),
        args: vec![var("k", 99)].into(),
    };
    let input = nil_const(e_id, inner);
    let once = decode_church_list_fold_partial(input);
    let twice = decode_church_list_fold_partial(once.clone());
    assert_eq!(once, twice);
}
