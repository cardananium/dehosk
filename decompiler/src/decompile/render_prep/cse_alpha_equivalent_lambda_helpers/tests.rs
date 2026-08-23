use super::*;
use crate::pseudo::ast::Binder;
use num_bigint::BigInt;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// Two alpha-equivalent lets in the same chain get CSE'd.
/// `let f = fn(x) { x + 1 }; let g = fn(y) { y + 1 }; body`
/// → `let f = fn(x) { x + 1 }; body[g→f]`.
#[test]
fn cse_two_alpha_equivalent_helpers() {
    let f_id = 100;
    let g_id = 101;
    let body = PseudoExpr::Apply {
        function: PBox::new(var("g", g_id)),
        args: vec![PseudoExpr::Int(BigInt::from(42))].into(),
    };
    let make_lambda = |p_id| PseudoExpr::Lambda {
        params: vec![binder("x", p_id)],
        body: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(var("x", p_id)),
            right: PBox::new(PseudoExpr::Int(BigInt::from(1))),
        }),
    };
    let input = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(f_id)),
        value: PBox::new(make_lambda(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "g".to_string(),
            id: Some(VarId::new(g_id)),
            value: PBox::new(make_lambda(2)),
            body: PBox::new(body),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input);
    let PseudoExpr::Let {
        name: outer_name,
        id: outer_id,
        body: outer_body,
        ..
    } = out
    else {
        panic!("expected outer Let");
    };
    assert_eq!(outer_name, "f");
    assert_eq!(outer_id, Some(VarId::new(f_id)));
    // Outer body is the original body (Let g was dropped).
    match outer_body.into_inner() {
        PseudoExpr::Apply { function, .. } => {
            let PseudoExpr::Var { name, id } = function.into_inner() else {
                panic!("expected Var function")
            };
            assert_eq!(name, "f");
            assert_eq!(id, Some(VarId::new(f_id)));
        }
        other => panic!("expected Apply body, got {:?}", other),
    }
}

/// A When-pattern binder that shares a VarId with a DROPPED helper must
/// NOT be collaterally redirected — inside the clause the id denotes the
/// pattern binder, not the helper.
#[test]
fn redirect_does_not_capture_shadowing_pattern_binder() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    let h1_id = 100;
    let h2_id = 500; // dropped dup; deliberately collides with the binder
    let ident = |p_id| PseudoExpr::Lambda {
        params: vec![binder("x", p_id)],
        body: PBox::new(var("x", p_id)),
    };
    let when = PseudoExpr::When {
        subject: PBox::new(var("subj", 9)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![binder("field", h2_id)],
                shape: ConstructorShape::unknown_data(0, 1),
            },
            guard: None,
            body: var("field", h2_id),
        }],
    };
    let input = PseudoExpr::Let {
        name: "h1".to_string(),
        id: Some(VarId::new(h1_id)),
        value: PBox::new(ident(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "h2".to_string(),
            id: Some(VarId::new(h2_id)),
            value: PBox::new(ident(2)),
            body: PBox::new(when),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input);
    // h2 dropped → `Let h1 { body: When }`. The clause body Var must
    // still be the pattern binder (id 500), NOT redirected to h1 (100).
    let PseudoExpr::Let { body, .. } = out else {
        panic!("outer let h1")
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected when body")
    };
    match &clauses[0].body {
        PseudoExpr::Var { id, .. } => assert_eq!(
            *id,
            Some(VarId::new(h2_id)),
            "pattern binder must not be redirected to the dropped helper"
        ),
        other => panic!("expected Var clause body, got {other:?}"),
    }
}

/// Helpers with different bodies don't merge.
#[test]
fn keeps_different_helpers() {
    let f_id = 200;
    let g_id = 201;
    let input = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(f_id)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("x", 1)],
            body: PBox::new(var("x", 1)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "g".to_string(),
            id: Some(VarId::new(g_id)),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![binder("y", 2)],
                body: PBox::new(PseudoExpr::Int(BigInt::from(42))),
            }),
            body: PBox::new(var("g", g_id)),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input.clone());
    assert_eq!(out, input);
}

/// Helpers that capture DIFFERENT outer vars don't merge.
#[test]
fn does_not_merge_different_captures() {
    let f_id = 300;
    let g_id = 301;
    let outer1_id = 1000;
    let outer2_id = 1001;
    let input = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(f_id)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("x", 1)],
            body: PBox::new(PseudoExpr::BinOp {
                op: crate::pseudo::ast::BinaryOp::Add,
                left: PBox::new(var("x", 1)),
                right: PBox::new(var("outer1", outer1_id)),
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "g".to_string(),
            id: Some(VarId::new(g_id)),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![binder("y", 2)],
                body: PBox::new(PseudoExpr::BinOp {
                    op: crate::pseudo::ast::BinaryOp::Add,
                    left: PBox::new(var("y", 2)),
                    right: PBox::new(var("outer2", outer2_id)),
                }),
            }),
            body: PBox::new(var("g", g_id)),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input.clone());
    assert_eq!(out, input);
}

/// Two alpha-equivalent let-bound RecFn helpers in the same
/// chain get CSE'd. Self-reference compares by position (the
/// self-name binder is the first local placeholder), so two
/// RecFns whose recursive calls carry different VarIds still
/// merge:
/// `let s = rec fn self(p) { self(p) }; let j = rec fn self(q) { self(q) }`.
#[test]
fn cse_two_alpha_equivalent_recfns() {
    let s_id = 400;
    let j_id = 401;
    let make_recfn = |self_id, param_id| PseudoExpr::RecFn {
        name: binder("self", self_id),
        params: vec![binder("p", param_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("self", self_id)),
            args: vec![var("p", param_id)].into(),
        }),
    };
    let body = PseudoExpr::Apply {
        function: PBox::new(var("j", j_id)),
        args: vec![PseudoExpr::Int(BigInt::from(0))].into(),
    };
    let input = PseudoExpr::Let {
        name: "s".to_string(),
        id: Some(VarId::new(s_id)),
        value: PBox::new(make_recfn(10, 11)),
        body: PBox::new(PseudoExpr::Let {
            name: "j".to_string(),
            id: Some(VarId::new(j_id)),
            value: PBox::new(make_recfn(20, 21)),
            body: PBox::new(body),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input);
    let PseudoExpr::Let {
        name: outer_name,
        id: outer_id,
        body: outer_body,
        ..
    } = out
    else {
        panic!("expected outer Let s");
    };
    assert_eq!(outer_name, "s");
    assert_eq!(outer_id, Some(VarId::new(s_id)));
    match outer_body.into_inner() {
        PseudoExpr::Apply { function, .. } => {
            let PseudoExpr::Var { name, id } = function.into_inner() else {
                panic!("expected Var function")
            };
            assert_eq!(name, "s");
            assert_eq!(id, Some(VarId::new(s_id)));
        }
        other => panic!("expected Apply body, got {:?}", other),
    }
}

/// Two RecFn helpers that capture DIFFERENT outer vars don't
/// merge: the free `Var` keeps its raw VarId in the canonical
/// signature.
#[test]
fn recfns_with_different_captures_do_not_merge() {
    let s_id = 500;
    let j_id = 501;
    let outer1_id = 1000;
    let outer2_id = 1001;
    let make_recfn = |self_id, param_id, outer_id| PseudoExpr::RecFn {
        name: binder("self", self_id),
        params: vec![binder("p", param_id)],
        body: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(var("p", param_id)),
            right: PBox::new(var("outer", outer_id)),
        }),
    };
    let input = PseudoExpr::Let {
        name: "s".to_string(),
        id: Some(VarId::new(s_id)),
        value: PBox::new(make_recfn(10, 11, outer1_id)),
        body: PBox::new(PseudoExpr::Let {
            name: "j".to_string(),
            id: Some(VarId::new(j_id)),
            value: PBox::new(make_recfn(20, 21, outer2_id)),
            body: PBox::new(var("j", j_id)),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input.clone());
    assert_eq!(out, input);
}

/// A RecFn never collides with a Lambda whose body happens to
/// canonicalise the same way — the `RecFn(`/`Lambda(` prefix
/// keeps the two universes disjoint.
#[test]
fn recfn_signature_does_not_collide_with_lambda() {
    let lam_id = 600;
    let rec_id = 601;
    let body = PseudoExpr::Apply {
        function: PBox::new(var("r", rec_id)),
        args: vec![PseudoExpr::Int(BigInt::from(0))].into(),
    };
    let lam = PseudoExpr::Lambda {
        params: vec![binder("p", 1)],
        body: PBox::new(var("p", 1)),
    };
    let rec = PseudoExpr::RecFn {
        name: binder("self", 10),
        params: vec![binder("p", 11)],
        body: PBox::new(var("p", 11)),
    };
    let input = PseudoExpr::Let {
        name: "l".to_string(),
        id: Some(VarId::new(lam_id)),
        value: PBox::new(lam),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(VarId::new(rec_id)),
            value: PBox::new(rec),
            body: PBox::new(body),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input.clone());
    assert_eq!(out, input);
}

/// The self-name binder takes the first placeholder and the
/// params follow, so `self(param)` and `param(self)`
/// canonicalise to different signatures.
#[test]
fn recfn_self_position_distinguishes_signature() {
    let f_id = 700;
    let g_id = 701;
    // f: rec fn self(p) { self(p) }  -- self at call position
    let f_val = PseudoExpr::RecFn {
        name: binder("self", 10),
        params: vec![binder("p", 11)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("self", 10)),
            args: vec![var("p", 11)].into(),
        }),
    };
    // g: rec fn self(p) { p(self) }  -- self as argument
    let g_val = PseudoExpr::RecFn {
        name: binder("self", 20),
        params: vec![binder("p", 21)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("p", 21)),
            args: vec![var("self", 20)].into(),
        }),
    };
    let input = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(f_id)),
        value: PBox::new(f_val),
        body: PBox::new(PseudoExpr::Let {
            name: "g".to_string(),
            id: Some(VarId::new(g_id)),
            value: PBox::new(g_val),
            body: PBox::new(var("g", g_id)),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input.clone());
    assert_eq!(out, input);
}

/// Helper builder: a church-pack-N constructor
/// `fn(a1, …, aN) { fn(x) { x(a1, …, aN) } }`.
fn pack_helper(arity: usize, base_id: u32) -> PseudoExpr {
    let outer_params: Vec<Binder> = (0..arity)
        .map(|i| binder(&format!("a{}", i + 1), base_id + i as u32 + 1))
        .collect();
    let x_id = base_id + arity as u32 + 1;
    let call_args: Vec<PseudoExpr> = (0..arity)
        .map(|i| var(&format!("a{}", i + 1), base_id + i as u32 + 1))
        .collect();
    PseudoExpr::Lambda {
        params: outer_params,
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("x", x_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("x", x_id)),
                args: call_args.into(),
            }),
        }),
    }
}

/// Two alpha-equivalent `pair_pack(Lambda, Var)` applications
/// merge once `pair_pack` is recognised as a church-pack helper.
#[test]
fn cse_two_alpha_equivalent_pair_pack_calls() {
    let pair_pack_id = 800;
    let e_id = 801;
    let x583_id = 810;
    let x583_2_id = 811;
    let body = PseudoExpr::Tuple((vec![var("x583", x583_id), var("x583_2", x583_2_id)]).into());
    let make_call = |lam_param_id, lam_param_id2| PseudoExpr::Apply {
        function: PBox::new(var("pair_pack", pair_pack_id)),
        args: vec![
            PseudoExpr::Lambda {
                params: vec![binder("p", lam_param_id), binder("q", lam_param_id2)],
                body: PBox::new(var("p", lam_param_id)),
            },
            var("e", e_id),
        ]
        .into(),
    };
    let input = PseudoExpr::Let {
        name: "pair_pack".to_string(),
        id: Some(VarId::new(pair_pack_id)),
        value: PBox::new(pack_helper(2, 1000)),
        body: PBox::new(PseudoExpr::Let {
            name: "x583".to_string(),
            id: Some(VarId::new(x583_id)),
            value: PBox::new(make_call(20, 21)),
            body: PBox::new(PseudoExpr::Let {
                name: "x583_2".to_string(),
                id: Some(VarId::new(x583_2_id)),
                value: PBox::new(make_call(30, 31)),
                body: PBox::new(body),
            }),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input);
    // Walk down to the body Tuple — should contain refs both
    // pointing at x583_id (canonical).
    let mut cur = &out;
    while let PseudoExpr::Let { body, .. } = cur {
        cur = body;
    }
    match cur {
        PseudoExpr::Tuple(items) => {
            assert_eq!(items.len(), 2);
            for item in items {
                let PseudoExpr::Var { id, .. } = item else {
                    panic!("expected Var")
                };
                assert_eq!(*id, Some(VarId::new(x583_id)));
            }
        }
        other => panic!("expected Tuple body, got {:?}", other),
    }
}

/// `pair_pack(L, e)` is NOT CSE'd when no validated pack-helper
/// definition is in scope: the head Var has no recognised
/// constructor shape, so the applications stay separate.
#[test]
fn pack_calls_without_helper_definition_do_not_merge() {
    let opaque_fn_id = 900;
    let e_id = 901;
    let l1_id = 910;
    let l2_id = 911;
    let make_call = |p_id| PseudoExpr::Apply {
        function: PBox::new(var("opaque_fn", opaque_fn_id)),
        args: vec![
            PseudoExpr::Lambda {
                params: vec![binder("p", p_id)],
                body: PBox::new(var("p", p_id)),
            },
            var("e", e_id),
        ]
        .into(),
    };
    let input = PseudoExpr::Let {
        name: "l1".to_string(),
        id: Some(VarId::new(l1_id)),
        value: PBox::new(make_call(40)),
        body: PBox::new(PseudoExpr::Let {
            name: "l2".to_string(),
            id: Some(VarId::new(l2_id)),
            value: PBox::new(make_call(41)),
            body: PBox::new(var("l2", l2_id)),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input.clone());
    assert_eq!(out, input);
}

/// `pair_pack(impure_apply(x), e)` must NOT merge with a
/// structurally identical twin: dropping the duplicate loses
/// one evaluation of `impure_apply(x)`, which is not provably
/// pure.
#[test]
fn pack_call_with_impure_arg_does_not_merge() {
    let pair_pack_id = 1000;
    let f_id = 1001;
    let x_id = 1002;
    let e_id = 1003;
    let l1_id = 1010;
    let l2_id = 1011;
    // pair_pack(f(x), e) — the f(x) Apply is impure (not a known
    // pack helper, not in is_pure_value's accept list).
    let make_call = || PseudoExpr::Apply {
        function: PBox::new(var("pair_pack", pair_pack_id)),
        args: vec![
            PseudoExpr::Apply {
                function: PBox::new(var("f", f_id)),
                args: vec![var("x", x_id)].into(),
            },
            var("e", e_id),
        ]
        .into(),
    };
    let input = PseudoExpr::Let {
        name: "pair_pack".to_string(),
        id: Some(VarId::new(pair_pack_id)),
        value: PBox::new(pack_helper(2, 2000)),
        body: PBox::new(PseudoExpr::Let {
            name: "l1".to_string(),
            id: Some(VarId::new(l1_id)),
            value: PBox::new(make_call()),
            body: PBox::new(PseudoExpr::Let {
                name: "l2".to_string(),
                id: Some(VarId::new(l2_id)),
                value: PBox::new(make_call()),
                body: PBox::new(var("l2", l2_id)),
            }),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input.clone());
    assert_eq!(out, input);
}

/// `pack_3(a, b, c)` calls with alpha-equivalent arg lists
/// merge — the pack-helper path is not hardcoded to arity 2.
#[test]
fn cse_two_alpha_equivalent_pack_3_calls() {
    let pack3_id = 1100;
    let a_id = 1101;
    let b_id = 1102;
    let c_id = 1103;
    let l1_id = 1110;
    let l2_id = 1111;
    let make_call = || PseudoExpr::Apply {
        function: PBox::new(var("pack_3", pack3_id)),
        args: vec![var("a", a_id), var("b", b_id), var("c", c_id)].into(),
    };
    let input = PseudoExpr::Let {
        name: "pack_3".to_string(),
        id: Some(VarId::new(pack3_id)),
        value: PBox::new(pack_helper(3, 3000)),
        body: PBox::new(PseudoExpr::Let {
            name: "l1".to_string(),
            id: Some(VarId::new(l1_id)),
            value: PBox::new(make_call()),
            body: PBox::new(PseudoExpr::Let {
                name: "l2".to_string(),
                id: Some(VarId::new(l2_id)),
                value: PBox::new(make_call()),
                body: PBox::new(var("l2", l2_id)),
            }),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input);
    // Inner-most non-Let is the body var, which should be
    // redirected to l1_id.
    let mut cur = &out;
    while let PseudoExpr::Let { body, .. } = cur {
        cur = body;
    }
    let PseudoExpr::Var { id, .. } = cur else {
        panic!("expected body Var")
    };
    assert_eq!(*id, Some(VarId::new(l1_id)));
}

/// An over-applied pack-helper call is a continuation call, not
/// a constructor literal: `pair_pack(a, b, k)` returns
/// `k(a, b)`, whose evaluation is observable, so two such
/// applications must NOT merge even when alpha-equivalent.
#[test]
fn over_applied_pack_call_does_not_merge() {
    let pair_pack_id = 1200;
    let a_id = 1201;
    let b_id = 1202;
    let k_id = 1203;
    let l1_id = 1210;
    let l2_id = 1211;
    // pair_pack(a, b, k) — Apply with arity 3 against a
    // 2-arity helper. `is_pure_value` accepts the Var args, so
    // only the arity guard rejects this.
    let make_call = || PseudoExpr::Apply {
        function: PBox::new(var("pair_pack", pair_pack_id)),
        args: vec![var("a", a_id), var("b", b_id), var("k", k_id)].into(),
    };
    let input = PseudoExpr::Let {
        name: "pair_pack".to_string(),
        id: Some(VarId::new(pair_pack_id)),
        value: PBox::new(pack_helper(2, 4000)),
        body: PBox::new(PseudoExpr::Let {
            name: "l1".to_string(),
            id: Some(VarId::new(l1_id)),
            value: PBox::new(make_call()),
            body: PBox::new(PseudoExpr::Let {
                name: "l2".to_string(),
                id: Some(VarId::new(l2_id)),
                value: PBox::new(make_call()),
                body: PBox::new(var("l2", l2_id)),
            }),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input.clone());
    assert_eq!(out, input);
}

/// `matches_pack_helper` rejects:
/// (a) arity-1 outer Lambda (would be redundant alias);
/// (b) inner Apply arg-list permuted relative to outer params;
/// (c) extra args / fewer args.
#[test]
fn matches_pack_helper_rejects_invalid_shapes() {
    // (a) arity-1 outer.
    let bad_arity_1 = PseudoExpr::Lambda {
        params: vec![binder("a", 1)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("x", 2)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("x", 2)),
                args: vec![var("a", 1)].into(),
            }),
        }),
    };
    assert!(!matches_pack_helper(&bad_arity_1));

    // (b) permuted Apply args (a, b) vs outer (a, b) → ok
    // baseline; then (b, a) permutation rejected.
    let good = pack_helper(2, 100);
    assert!(matches_pack_helper(&good));
    let bad_permuted = PseudoExpr::Lambda {
        params: vec![binder("a1", 101), binder("a2", 102)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("x", 103)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("x", 103)),
                args: vec![var("a2", 102), var("a1", 101)].into(),
            }),
        }),
    };
    assert!(!matches_pack_helper(&bad_permuted));

    // (c) too few inner args.
    let bad_short = PseudoExpr::Lambda {
        params: vec![binder("a1", 201), binder("a2", 202)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("x", 203)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("x", 203)),
                args: vec![var("a1", 201)].into(),
            }),
        }),
    };
    assert!(!matches_pack_helper(&bad_short));
}

/// Three alpha-equivalent helpers: only one survives, all uses
/// rewire to it.
#[test]
fn cse_three_alpha_equivalent_helpers() {
    let make_lambda = |p_id| PseudoExpr::Lambda {
        params: vec![binder("p", p_id)],
        body: PBox::new(var("p", p_id)),
    };
    let body = PseudoExpr::Tuple((vec![var("f1", 100), var("f2", 101), var("f3", 102)]).into());
    let input = PseudoExpr::Let {
        name: "f1".to_string(),
        id: Some(VarId::new(100)),
        value: PBox::new(make_lambda(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "f2".to_string(),
            id: Some(VarId::new(101)),
            value: PBox::new(make_lambda(2)),
            body: PBox::new(PseudoExpr::Let {
                name: "f3".to_string(),
                id: Some(VarId::new(102)),
                value: PBox::new(make_lambda(3)),
                body: PBox::new(body),
            }),
        }),
    };
    let out = cse_alpha_equivalent_lambda_helpers(input);
    // Only Let f1 survives at top.
    let PseudoExpr::Let {
        name,
        body: outer_body,
        ..
    } = out
    else {
        panic!("Let")
    };
    assert_eq!(name, "f1");
    // outer_body should be the Tuple, with all 3 uses pointing to f1.
    match outer_body.into_inner() {
        PseudoExpr::Tuple(items) => {
            assert_eq!(items.len(), 3);
            for item in &items {
                let PseudoExpr::Var { name, id } = item else {
                    panic!("Var");
                };
                assert_eq!(name, "f1");
                assert_eq!(*id, Some(VarId::new(100)));
            }
        }
        other => panic!("expected Tuple body, got {:?}", other),
    }
}
