use super::*;
use crate::pseudo::ast::Binder;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `fn(a,b){ fn(x){ x(a,b) } }` with stable ids a=2 b=3 x=4.
fn pair_pack_helper() -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![
            Binder::new("a".to_string(), VarId::new(2)),
            Binder::new("b".to_string(), VarId::new(3)),
        ],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x".to_string(), VarId::new(4))],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("x", 4)),
                args: vec![var("a", 2), var("b", 3)].into(),
            }),
        }),
    }
}

/// Wrap a body in `let pair_pack = <helper> in body` (binder id 1).
fn with_helper(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "pair_pack".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(pair_pack_helper()),
        body: PBox::new(body),
    }
}

fn construct(a: PseudoExpr, b: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(var("pair_pack", 1)),
        args: vec![a, b].into(),
    }
}

/// `pair_pack(p, q)` with data args → native `Pair(p, q)` (and since it's
/// the only site, the helper is dropped, leaving a bare `Pair`).
#[test]
fn converts_data_pair_to_native() {
    let input = with_helper(construct(var("p", 10), var("q", 11)));
    let out = decode_safe_pair_pack(input);
    match out {
        PseudoExpr::Pair(a, b) => {
            assert!(matches!(*a, PseudoExpr::Var { id: Some(v), .. } if v == VarId::new(10)));
            assert!(matches!(*b, PseudoExpr::Var { id: Some(v), .. } if v == VarId::new(11)));
        }
        other => panic!("expected Pair, got {:?}", other),
    }
}

/// `pair_pack(fn(z){z}, q)` — lambda component → stays Church (readability).
#[test]
fn keeps_lambda_component_pair() {
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("z".to_string(), VarId::new(20))],
        body: PBox::new(var("z", 20)),
    };
    let input = with_helper(construct(lambda, var("q", 11)));
    let out = decode_safe_pair_pack(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("Let");
    };
    // Still an Apply of pair_pack, not a Pair.
    assert!(matches!(*body, PseudoExpr::Apply { .. }));
}

/// `pair_pack(p, q)(selector)` — construction applied as a function →
/// inner construction stays Church (would be `Pair(...)(...)` = type error).
#[test]
fn keeps_applied_construction() {
    let applied = PseudoExpr::Apply {
        function: PBox::new(construct(var("p", 10), var("q", 11))),
        args: vec![var("selector", 30)].into(),
    };
    let input = with_helper(applied);
    let out = decode_safe_pair_pack(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("Let");
    };
    let PseudoExpr::Apply { function, .. } = body.into_inner() else {
        panic!("expected Apply");
    };
    // inner (the function) must remain the Church construction, not a Pair.
    assert!(
        matches!(*function, PseudoExpr::Apply { .. }),
        "applied construction must stay Church"
    );
}

/// `let X = pair_pack(p, q); X(sel)` — X applied as a function → kept Church.
#[test]
fn keeps_bound_applied_pair() {
    let inner = PseudoExpr::Let {
        name: "x_260".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(construct(var("p", 10), var("q", 11))),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x_260", 50)),
            args: vec![var("sel", 30)].into(),
        }),
    };
    let input = with_helper(inner);
    let out = decode_safe_pair_pack(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("outer Let");
    };
    let PseudoExpr::Let { value, .. } = body.into_inner() else {
        panic!("inner Let");
    };
    assert!(
        matches!(*value, PseudoExpr::Apply { .. }),
        "bound-and-applied pair must stay Church"
    );
}

/// Every site converted → the unused `pair_pack` helper is dropped.
#[test]
fn drops_helper_when_all_sites_converted() {
    let input = with_helper(construct(var("p", 10), var("q", 11)));
    let out = decode_safe_pair_pack(input);
    // The `let pair_pack = …` wrapper is gone; result is just `Pair(p, q)`.
    match out {
        PseudoExpr::Pair(a, b) => {
            assert!(matches!(*a, PseudoExpr::Var { id: Some(v), .. } if v == VarId::new(10)));
            assert!(matches!(*b, PseudoExpr::Var { id: Some(v), .. } if v == VarId::new(11)));
        }
        other => panic!("expected bare Pair (helper dropped), got {:?}", other),
    }
}

/// When a Church site survives (lambda component), the helper is KEPT.
#[test]
fn keeps_helper_when_a_site_survives() {
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("z".to_string(), VarId::new(20))],
        body: PBox::new(var("z", 20)),
    };
    let input = with_helper(construct(lambda, var("q", 11)));
    let out = decode_safe_pair_pack(input);
    // Helper Let must remain (still referenced by the Church site).
    assert!(matches!(out, PseudoExpr::Let { id: Some(v), .. } if v == VarId::new(1)));
}

/// Escape via nesting: `let j8 = when c is { _ -> pair_pack(p, q) }; j8(arg)`.
/// j8 is applied as a function, so the pair inside its value (a Scott
/// accumulator) must stay Church — converting it would make the `when`
/// arm a `Pair` while j8 is typed as a function (a type mismatch).
#[test]
fn keeps_pair_nested_in_applied_binding_value() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let when_val = PseudoExpr::When {
        subject: PBox::new(var("c", 60)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: construct(var("p", 10), var("q", 11)),
        }],
    };
    let inner = PseudoExpr::Let {
        name: "j8".to_string(),
        id: Some(VarId::new(70)),
        value: PBox::new(when_val),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("j8", 70)),
            args: vec![var("arg", 80)].into(),
        }),
    };
    let input = with_helper(inner);
    let out = decode_safe_pair_pack(input);
    // Find the j8 binding's value; its when-arm must remain a pair_pack Apply.
    let found_church = {
        let mut church = false;
        fn walk(e: &PseudoExpr, church: &mut bool) {
            if let PseudoExpr::Apply { function, args } = e
                && args.len() == 2
                && matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "pair_pack")
            {
                *church = true;
            }
            for c in super::children(e) {
                walk(c, church);
            }
        }
        walk(&out, &mut church);
        church
    };
    assert!(
        found_church,
        "pair nested in an applied binding's value must stay Church"
    );
}

/// `fn pack_3(a,b,c){ fn(x){ x(a,b,c) } }` (3-arity) with stable ids.
fn pack3_helper() -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![
            Binder::new("a".to_string(), VarId::new(2)),
            Binder::new("b".to_string(), VarId::new(3)),
            Binder::new("c".to_string(), VarId::new(5)),
        ],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x".to_string(), VarId::new(4))],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("x", 4)),
                args: vec![var("a", 2), var("b", 3), var("c", 5)].into(),
            }),
        }),
    }
}

/// A 3-arity Church pack `pack_3(p, q, r)` (data args) → native tuple
/// `(p, q, r)` (and the helper is dropped, all sites converted).
#[test]
fn converts_data_tuple_to_native() {
    let input = PseudoExpr::Let {
        name: "pack_3".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(pack3_helper()),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("pack_3", 1)),
            args: vec![var("p", 10), var("q", 11), var("r", 12)].into(),
        }),
    };
    let out = decode_safe_pair_pack(input);
    match out {
        PseudoExpr::Tuple(items) => {
            assert_eq!(items.len(), 3);
            assert!(
                matches!(&items[0], PseudoExpr::Var { id: Some(v), .. } if *v == VarId::new(10))
            );
            assert!(
                matches!(&items[2], PseudoExpr::Var { id: Some(v), .. } if *v == VarId::new(12))
            );
        }
        other => panic!("expected 3-tuple, got {:?}", other),
    }
}

/// A partial application `pack_3(p, q)` (fewer than arity args) is NOT a
/// construction — left untouched.
#[test]
fn ignores_partial_pack_application() {
    let input = PseudoExpr::Let {
        name: "pack_3".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(pack3_helper()),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("pack_3", 1)),
            args: vec![var("p", 10), var("q", 11)].into(), // only 2 of 3
        }),
    };
    let out = decode_safe_pair_pack(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("Let");
    };
    assert!(matches!(*body, PseudoExpr::Apply { .. }));
}

/// A pair built inside an APPLIED helper function's body is the helper's
/// own data and must still convert — the escape gate resets at the lambda
/// boundary.
#[test]
fn converts_pair_inside_applied_helper() {
    // let pair_pack = <helper> in
    //   let f = fn(x) { pair_pack(p, q) } in f(arg)   -- f is applied
    let f_body = PseudoExpr::Lambda {
        params: vec![Binder::new("x10".to_string(), VarId::new(60))],
        body: PBox::new(construct(var("p", 10), var("q", 11))),
    };
    let inner = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(70)),
        value: PBox::new(f_body),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("f", 70)),
            args: vec![var("arg", 80)].into(),
        }),
    };
    let input = with_helper(inner);
    let out = decode_safe_pair_pack(input);
    // The pair inside f's body must be a native Pair, not pair_pack.
    let mut found_pair = false;
    fn walk(e: &PseudoExpr, found: &mut bool) {
        if matches!(e, PseudoExpr::Pair(..)) {
            *found = true;
        }
        for c in super::children(e) {
            walk(c, found);
        }
    }
    walk(&out, &mut found_pair);
    assert!(
        found_pair,
        "pair inside an applied helper's body must convert: {out:?}"
    );
}

/// Same as `converts_pair_inside_applied_helper` but the helper is a
/// `RecFn` — the gate must reset at the RecFn boundary too.
#[test]
fn converts_pair_inside_applied_recfn() {
    let rec_body = PseudoExpr::RecFn {
        name: Binder::new("g".to_string(), VarId::new(71)),
        params: vec![Binder::new("x10".to_string(), VarId::new(60))],
        body: PBox::new(construct(var("p", 10), var("q", 11))),
    };
    let inner = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(VarId::new(71)),
        value: PBox::new(rec_body),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("g", 71)),
            args: vec![var("arg", 80)].into(),
        }),
    };
    let input = with_helper(inner);
    let out = decode_safe_pair_pack(input);
    let mut found_pair = false;
    fn walk(e: &PseudoExpr, found: &mut bool) {
        if matches!(e, PseudoExpr::Pair(..)) {
            *found = true;
        }
        for c in super::children(e) {
            walk(c, found);
        }
    }
    walk(&out, &mut found_pair);
    assert!(
        found_pair,
        "pair inside an applied RecFn body must convert: {out:?}"
    );
}

/// No pair_pack helper present → unchanged.
#[test]
fn no_helper_no_change() {
    let input = PseudoExpr::Apply {
        function: PBox::new(var("not_pair_pack", 99)),
        args: vec![var("p", 10), var("q", 11)].into(),
    };
    let out = decode_safe_pair_pack(input.clone());
    assert_eq!(out, input);
}

/// Nested safe pairs `pair_pack(p, pair_pack(q, r))` → `Pair(p, Pair(q, r))`.
#[test]
fn converts_nested_data_pairs() {
    let input = with_helper(construct(
        var("p", 10),
        construct(var("q", 11), var("r", 12)),
    ));
    let out = decode_safe_pair_pack(input);
    // Helper dropped (all sites converted) → bare nested Pair.
    let PseudoExpr::Pair(a, b) = out else {
        panic!("expected outer Pair");
    };
    assert!(matches!(*a, PseudoExpr::Var { id: Some(v), .. } if v == VarId::new(10)));
    assert!(
        matches!(*b, PseudoExpr::Pair(..)),
        "inner must also be Pair"
    );
}
