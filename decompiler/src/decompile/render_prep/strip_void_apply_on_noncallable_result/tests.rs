use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};

const FN_ID: u32 = 100;

fn list_returning_recfn_let(body_after: PseudoExpr) -> PseudoExpr {
    // let f = rec fn f(xs) { [] }  in  <body_after>
    PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(FN_ID)),
        value: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("f", VarId::new(FN_ID)),
            params: vec![Binder::new("xs", VarId::new(101))],
            body: PBox::new(PseudoExpr::List {
                elements: vec![].into(),
                tail: None,
            }),
        }),
        body: PBox::new(body_after),
    }
}

/// `f(arg)()` — the stray `()` on a List-returning fn.
fn void_apply_call() -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("f", VarId::new(FN_ID))),
            args: vec![PseudoExpr::int(0)].into(),
        }),
        args: vec![].into(),
    }
}

#[test]
fn drops_stray_void_apply_on_list_returning_fn() {
    let expr = list_returning_recfn_let(void_apply_call());
    let out = strip_void_apply_on_noncallable_result(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("let");
    };
    // `f(0)()` → `f(0)` (inner call, no trailing empty apply).
    assert!(
        matches!(&*body, PseudoExpr::Apply { function, args }
            if args.len() == 1
                && matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "f")),
        "expected f(0), got {body:?}"
    );
}

#[test]
fn keeps_void_apply_on_lambda_returning_fn() {
    // let g = fn(x) { fn(y) { y } } in g(0)() — g returns a Lambda
    // (callable!), so the `()` is a real 0-arity application; preserve.
    let g = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(VarId::new(FN_ID)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", VarId::new(201))],
            body: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("y", VarId::new(202))],
                body: PBox::new(PseudoExpr::var_with_id("y", VarId::new(202))),
            }),
        }),
        body: PBox::new(void_apply_call()),
    };
    let out = strip_void_apply_on_noncallable_result(g.clone());
    assert_eq!(out, g, "a Lambda-returning fn's () must be preserved");
}

#[test]
fn keeps_void_apply_on_partial_application() {
    // let f = fn(a, b) { Pair(a, b) } in f(0)() — arity 2, but only 1 arg is
    // supplied, so `f(0)` is a CALLABLE curried remainder and the `()` is a
    // real application, NOT stray.
    let f = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(FN_ID)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("a", VarId::new(401)),
                Binder::new("b", VarId::new(402)),
            ],
            body: PBox::new(PseudoExpr::Pair(
                PBox::new(PseudoExpr::var_with_id("a", VarId::new(401))),
                PBox::new(PseudoExpr::var_with_id("b", VarId::new(402))),
            )),
        }),
        // f(0)() — only 1 of 2 args supplied.
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("f", VarId::new(FN_ID))),
                args: vec![PseudoExpr::int(0)].into(),
            }),
            args: vec![].into(),
        }),
    };
    let out = strip_void_apply_on_noncallable_result(f.clone());
    assert_eq!(
        out, f,
        "partial application f(0)() must NOT be stripped (f arity 2)"
    );
}

#[test]
fn keeps_void_apply_on_unknown_fn() {
    // The called fn isn't a collected non-callable binder → preserve.
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("h", VarId::new(999))),
            args: vec![PseudoExpr::int(0)].into(),
        }),
        args: vec![].into(),
    };
    let out = strip_void_apply_on_noncallable_result(expr.clone());
    assert_eq!(out, expr);
}

#[test]
fn pair_returning_fn_through_expect_chain() {
    // let f = fn(x) { when x is { Some(v) -> Pair(v, v); _ -> fail } } in f(0)()
    // — the body returns a Pair via a When (expect-sugar) with a fail arm.
    let fbody = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", VarId::new(301))),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(
                    crate::pseudo::constructor::ConstructorShape::unknown_data(0, 1),
                    vec![Binder::new("v", VarId::new(302))],
                ),
                PseudoExpr::Pair(
                    PBox::new(PseudoExpr::var_with_id("v", VarId::new(302))),
                    PBox::new(PseudoExpr::var_with_id("v", VarId::new(302))),
                ),
            ),
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::error()),
        ],
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(FN_ID)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", VarId::new(301))],
            body: PBox::new(fbody),
        }),
        body: PBox::new(void_apply_call()),
    };
    let out = strip_void_apply_on_noncallable_result(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("let");
    };
    assert!(
        matches!(&*body, PseudoExpr::Apply { args, .. } if args.len() == 1),
        "Pair-via-expect-chain return should still strip the (), got {body:?}"
    );
}

/// A helper whose tails are an operator result and a `Bool` literal
/// returns a scalar, so the trailing `()` is Force residue too. This
/// is what left `-> Bool` predicates rendering as `helper(a, b)()`.
#[test]
fn drops_stray_void_apply_on_scalar_returning_fn() {
    let f = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(FN_ID)),
        value: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("f", VarId::new(FN_ID)),
            params: vec![Binder::new("xs", VarId::new(101))],
            body: PBox::new(PseudoExpr::BinOp {
                op: crate::pseudo::ast::BinaryOp::Eq,
                left: PBox::new(PseudoExpr::int(0)),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
        body: PBox::new(void_apply_call()),
    };
    let out = strip_void_apply_on_noncallable_result(f);
    let PseudoExpr::Let { body, .. } = &out else {
        panic!("expected the Let: {out:?}");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Apply { args, .. } if args.len() == 1),
        "the stray `()` must be gone: {out:?}"
    );
}

/// Mutual recursion: `a` returns `b(..)` and `b` returns `a(..)`, so a
/// least fixpoint proves neither — yet neither can return a function,
/// since every other tail is a scalar.
#[test]
fn proves_mutually_recursive_helpers_non_callable() {
    const A: u32 = 200;
    const B: u32 = 201;
    let call = |id: u32| PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("g", VarId::new(id))),
        args: vec![PseudoExpr::int(0)].into(),
    };
    let two_arm = |other: u32| PseudoExpr::When {
        subject: PBox::new(PseudoExpr::int(0)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: call(other),
            },
        ],
    };
    let fn_let = |id: u32, other: u32, inner: PseudoExpr| PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(VarId::new(id)),
        value: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("g", VarId::new(id)),
            params: vec![Binder::new("x", VarId::new(id + 50))],
            body: PBox::new(two_arm(other)),
        }),
        body: PBox::new(inner),
    };
    // `a(0)()` — the stray `()` on the mutually recursive pair.
    let use_site = PseudoExpr::Apply {
        function: PBox::new(call(A)),
        args: vec![].into(),
    };
    let expr = fn_let(A, B, fn_let(B, A, use_site));
    let out = strip_void_apply_on_noncallable_result(expr);
    let rendered = format!("{out:?}");
    assert!(
        !rendered.contains("args: [] }"),
        "the stray `()` must be gone through the mutual recursion: {rendered}"
    );
}
