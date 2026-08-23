use super::*;

/// `let map = fn(v) { v }; let r = map; r(42)` — the alias call is
/// inlined and the alias let dropped; the identity fn stays (dead-let
/// elimination removes it once its ref count hits 0).
#[test]
fn inlines_and_drops_identity_alias() {
    let map_id = VarId::fresh_binding();
    let v_id = VarId::fresh_binding();
    let r_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "map".to_string(),
        id: Some(map_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", v_id)],
            body: PBox::new(PseudoExpr::var_with_id("v", v_id)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(r_id),
            value: PBox::new(PseudoExpr::var_with_id("map", map_id)),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("r", r_id)),
                args: vec![PseudoExpr::int(42)].into(),
            }),
        }),
    };
    let result = inline_identity_helpers(expr);
    // alias gone, call inlined; outer identity let kept (0 refs now).
    let PseudoExpr::Let { name, body, .. } = &result else {
        panic!("expected outer map let, got {result:?}");
    };
    assert_eq!(name, "map");
    assert!(matches!(body.as_ref(), PseudoExpr::Int(n) if n == &num_bigint::BigInt::from(42)));
}

/// A bare (non-call) use of the alias keeps the let.
#[test]
fn keeps_alias_with_bare_use() {
    let map_id = VarId::fresh_binding();
    let v_id = VarId::fresh_binding();
    let r_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "map".to_string(),
        id: Some(map_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", v_id)],
            body: PBox::new(PseudoExpr::var_with_id("v", v_id)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(r_id),
            value: PBox::new(PseudoExpr::var_with_id("map", map_id)),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("r", r_id),
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var_with_id("r", r_id)),
                        args: vec![PseudoExpr::int(1)].into(),
                    },
                ]
                .into(),
            )),
        }),
    };
    let result = inline_identity_helpers(expr.clone());
    // Alias let must survive (one bare ref); the call may inline.
    let PseudoExpr::Let { body: map_body, .. } = &result else {
        panic!("expected outer let");
    };
    assert!(matches!(map_body.as_ref(), PseudoExpr::Let { name, .. } if name == "r"));
}

/// A 2-arg call through the alias is over-application — never inlined,
/// let kept.
#[test]
fn keeps_alias_with_two_arg_call() {
    let map_id = VarId::fresh_binding();
    let v_id = VarId::fresh_binding();
    let r_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "map".to_string(),
        id: Some(map_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", v_id)],
            body: PBox::new(PseudoExpr::var_with_id("v", v_id)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(r_id),
            value: PBox::new(PseudoExpr::var_with_id("map", map_id)),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("r", r_id)),
                args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
            }),
        }),
    };
    let result = inline_identity_helpers(expr.clone());
    assert_eq!(result, expr);
}

/// An id-less alias value (`Var { id: None }`) is never registered.
#[test]
fn ignores_idless_alias() {
    let map_id = VarId::fresh_binding();
    let v_id = VarId::fresh_binding();
    let r_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "map".to_string(),
        id: Some(map_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", v_id)],
            body: PBox::new(PseudoExpr::var_with_id("v", v_id)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(r_id),
            value: PBox::new(PseudoExpr::var("map")),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("r", r_id)),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };
    let result = inline_identity_helpers(expr.clone());
    assert_eq!(result, expr);
}

/// Transitive chain: `let map = id-fn; let r1 = map; let r2 = r1;
/// r2(7)` — the call inlines through both aliases.
#[test]
fn inlines_transitive_alias_chain() {
    let map_id = VarId::fresh_binding();
    let v_id = VarId::fresh_binding();
    let r1_id = VarId::fresh_binding();
    let r2_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "map".to_string(),
        id: Some(map_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", v_id)],
            body: PBox::new(PseudoExpr::var_with_id("v", v_id)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r1".to_string(),
            id: Some(r1_id),
            value: PBox::new(PseudoExpr::var_with_id("map", map_id)),
            body: PBox::new(PseudoExpr::Let {
                name: "r2".to_string(),
                id: Some(r2_id),
                value: PBox::new(PseudoExpr::var_with_id("r1", r1_id)),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("r2", r2_id)),
                    args: vec![PseudoExpr::int(7)].into(),
                }),
            }),
        }),
    };
    let result = inline_identity_helpers(expr);
    let PseudoExpr::Let { name, body, .. } = &result else {
        panic!("expected outer map let");
    };
    assert_eq!(name, "map");
    // r2(7) -> 7 and r2's let is dropped. Bottom-up: r2's post_let runs
    // while folding r1's BODY, so by r1's post_let that body is already
    // `7` with zero r1 refs; r1's let is kept for dead-let elimination.
    let PseudoExpr::Let {
        name: r1_name,
        body: r1_body,
        ..
    } = body.as_ref()
    else {
        panic!("expected r1 let kept (0 refs), got {body:?}");
    };
    assert_eq!(r1_name, "r1");
    assert!(matches!(r1_body.as_ref(), PseudoExpr::Int(n) if n == &num_bigint::BigInt::from(7)));
}

/// An alias to a NON-identity fn is never inlined.
#[test]
fn ignores_alias_to_non_identity() {
    use crate::pseudo::ast::BinaryOp;
    let f_id = VarId::fresh_binding();
    let v_id = VarId::fresh_binding();
    let r_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", v_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("v", v_id)),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(r_id),
            value: PBox::new(PseudoExpr::var_with_id("f", f_id)),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("r", r_id)),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };
    let result = inline_identity_helpers(expr.clone());
    assert_eq!(result, expr);
}

/// Idempotence: a second application of the pass is a no-op.
#[test]
fn alias_inline_idempotent() {
    let map_id = VarId::fresh_binding();
    let v_id = VarId::fresh_binding();
    let r_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "map".to_string(),
        id: Some(map_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", v_id)],
            body: PBox::new(PseudoExpr::var_with_id("v", v_id)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(r_id),
            value: PBox::new(PseudoExpr::var_with_id("map", map_id)),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("r", r_id)),
                args: vec![PseudoExpr::int(42)].into(),
            }),
        }),
    };
    let once = inline_identity_helpers(expr);
    let twice = inline_identity_helpers(once.clone());
    assert_eq!(twice, once);
}

/// An unrelated same-name Var with a different VarId is never
/// rewritten through the alias branch.
#[test]
fn alias_branch_respects_var_ids() {
    let map_id = VarId::fresh_binding();
    let v_id = VarId::fresh_binding();
    let r_id = VarId::fresh_binding();
    let other_r = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "map".to_string(),
        id: Some(map_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", v_id)],
            body: PBox::new(PseudoExpr::var_with_id("v", v_id)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(r_id),
            value: PBox::new(PseudoExpr::var_with_id("map", map_id)),
            // The call goes through a DIFFERENT id that merely shares
            // the display name.
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("r", other_r)),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };
    let result = inline_identity_helpers(expr.clone());
    assert_eq!(result, expr);
}

#[test]
fn inlines_and_drops_identity_helper() {
    // let c = fn(x) { x } in c(42)   →   42
    let c_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(c_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("c", c_id)),
            args: vec![PseudoExpr::int(42)].into(),
        }),
    };
    let result = inline_identity_helpers(expr);
    assert!(matches!(result, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(42)));
}

#[test]
fn leaves_multi_param_identity_alone() {
    // let k = fn(x, y) { x } in k(1, 2) — leave as-is (K-combinator)
    let k_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let y_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(k_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id), Binder::new("y", y_id)],
            body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
            args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
        }),
    };
    let result = inline_identity_helpers(expr);
    assert!(matches!(result, PseudoExpr::Let { .. }));
}

#[test]
fn leaves_non_identity_helper_alone() {
    use crate::pseudo::ast::BinaryOp;
    let f_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("x", x_id)),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
            args: vec![PseudoExpr::int(42)].into(),
        }),
    };
    let result = inline_identity_helpers(expr);
    assert!(matches!(result, PseudoExpr::Let { .. }));
}

#[test]
fn inlines_multiple_calls_in_body() {
    let c_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("c", c_id)),
        args: vec![PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("c", c_id)),
            args: vec![PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("c", c_id)),
                args: vec![PseudoExpr::int(7)].into(),
            }]
            .into(),
        }]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(c_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        }),
        body: PBox::new(body),
    };
    let result = inline_identity_helpers(expr);
    assert!(matches!(result, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(7)));
}

// ---- hardening tests ----

#[test]
fn does_not_inline_id_mismatched_same_name_call() {
    // let c = fn(x) { x } in foo(c, c) — the two `c` args carry
    // different VarIds; the unrelated one must not be inlined.
    let c_id = VarId::fresh_binding();
    let other_c_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(c_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("foo")),
            args: vec![
                // c with the matching id, but a bare ref
                // (not Apply(c, [arg])) — not inlined.
                PseudoExpr::var_with_id("c", c_id),
                // c with a DIFFERENT id — must never be touched.
                PseudoExpr::var_with_id("c", other_c_id),
            ]
            .into(),
        }),
    };
    let result = inline_identity_helpers(expr);
    // bare ref exists → let must remain.
    let PseudoExpr::Let {
        id: let_id, body, ..
    } = result
    else {
        panic!("expected Let to remain due to bare refs")
    };
    assert_eq!(let_id, Some(c_id));
    let PseudoExpr::Apply { args, .. } = body.into_inner() else {
        panic!("expected Apply")
    };
    // The other-id `c` is preserved with its original id.
    assert!(matches!(&args[1], PseudoExpr::Var { id: Some(i), .. } if *i == other_c_id));
}

#[test]
fn does_not_drop_let_when_helper_is_referenced_bare() {
    // let c = fn(x) { x } in (c, c(42)) — the bare `c` keeps the
    // let alive even though `c(42)` inlines to 42.
    let c_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(c_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("c", c_id),
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("c", c_id)),
                    args: vec![PseudoExpr::int(42)].into(),
                },
            ]
            .into(),
        )),
    };
    let result = inline_identity_helpers(expr);
    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected Let to remain due to bare ref")
    };
    let PseudoExpr::Tuple(items) = body.into_inner() else {
        panic!("expected Tuple body")
    };
    // Bare c stays as `c`; the call collapsed to 42.
    assert!(matches!(&items[0], PseudoExpr::Var { name, .. } if name == "c"));
    assert!(matches!(&items[1], PseudoExpr::Int(_)));
}

#[test]
fn does_not_inline_through_shadowed_let_binder() {
    // let c = fn(x) { x } in
    //   let c = fn(y) { y + 1 } in   // shadows outer c
    //     c(42)                       // this c is the INNER, not the identity.
    // Result should keep both lets and not inline c(42).
    use crate::pseudo::ast::BinaryOp;
    let outer_c_id = VarId::fresh_binding();
    let inner_c_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let y_id = VarId::fresh_binding();
    let inner = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(inner_c_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("y", y_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("y", y_id)),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("c", inner_c_id)),
            args: vec![PseudoExpr::int(42)].into(),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(outer_c_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        }),
        body: PBox::new(inner),
    };
    let result = inline_identity_helpers(expr);
    // The outer c has 0 refs (the inner c(42) refers to the inner
    // id) and the inner c is not an identity: both lets kept
    // (dropping zero-ref lets is a separate pass), c(42) intact.
    let PseudoExpr::Let {
        value: outer_value,
        body: outer_body,
        ..
    } = result
    else {
        panic!("expected outer Let")
    };
    assert!(matches!(*outer_value, PseudoExpr::Lambda { .. }));
    let PseudoExpr::Let {
        body: inner_body, ..
    } = outer_body.into_inner()
    else {
        panic!("expected inner Let")
    };
    let PseudoExpr::Apply { function, args, .. } = inner_body.into_inner() else {
        panic!("expected Apply intact")
    };
    assert_eq!(args.len(), 1);
    assert!(matches!(*function, PseudoExpr::Var { id: Some(i), .. } if i == inner_c_id));
}

#[test]
fn does_not_inline_through_shadowed_lambda_param() {
    // let c = fn(x) { x } in fn(c) { c(42) }
    // The inner `c` is the lambda param; should not be inlined.
    let c_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let inner_c_param = VarId::fresh_binding();
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("c", inner_c_param)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("c", inner_c_param)),
            args: vec![PseudoExpr::int(42)].into(),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(c_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        }),
        body: PBox::new(lambda),
    };
    let result = inline_identity_helpers(expr);
    // Outer `c` has 0 refs (the inner c is the param); the let
    // stays (zero-ref lets are a separate pass), Apply intact.
    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected outer Let")
    };
    let PseudoExpr::Lambda { body, .. } = body.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(matches!(*body, PseudoExpr::Apply { .. }));
}

#[test]
fn does_not_inline_partial_overapplication() {
    // let c = fn(x) { x } in c(1, 2) — partial-overapply.
    // Don't inline, don't drop.
    let c_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "c".to_string(),
        id: Some(c_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("c", c_id)),
            args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
        }),
    };
    let result = inline_identity_helpers(expr);
    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected Let to remain")
    };
    let PseudoExpr::Apply { args, .. } = body.into_inner() else {
        panic!("expected Apply preserved")
    };
    assert_eq!(args.len(), 2);
}
