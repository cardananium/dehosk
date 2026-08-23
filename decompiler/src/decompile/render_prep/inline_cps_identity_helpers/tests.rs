use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

#[test]
fn inlines_fully_applied_cps_identity_helper() {
    // `let h = fn(x, y, k) { k(x, y) } in h(1, 2, my_k)`
    // → `my_k(1, 2)`. Helper dropped.
    let h_id = VarId::new(7000);
    let x_id = VarId::new(7001);
    let y_id = VarId::new(7002);
    let k_id = VarId::new(7003);
    let my_k_id = VarId::new(7010);

    let helper_body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
        args: vec![
            PseudoExpr::var_with_id("x", x_id),
            PseudoExpr::var_with_id("y", y_id),
        ]
        .into(),
    };
    let helper_lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("x", x_id),
            Binder::new("y", y_id),
            Binder::new("k", k_id),
        ],
        body: PBox::new(helper_body),
    };
    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("h", h_id)),
        args: vec![
            PseudoExpr::int(1),
            PseudoExpr::int(2),
            PseudoExpr::var_with_id("my_k", my_k_id),
        ]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".into(),
        id: Some(h_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(call_site),
    };

    let rewritten = inline_cps_identity_helpers(expr);

    // Helper let should be dropped → result is just `my_k(1, 2)`.
    let PseudoExpr::Apply { function, args } = rewritten else {
        panic!("expected Apply after rewrite, got {:?}", rewritten);
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        panic!("expected Var function, got {:?}", function);
    };
    assert_eq!(*fn_id, my_k_id);
    assert_eq!(args.len(), 2);
}

#[test]
fn does_not_inline_partial_application() {
    // `let h = fn(x, y, k) { k(x, y) } in h(1, 2)` (no callback yet)
    // → helper preserved (partial application is the church-pair pack
    // idiom — KP1 territory, not KP3-narrow).
    let h_id = VarId::new(7100);
    let x_id = VarId::new(7101);
    let y_id = VarId::new(7102);
    let k_id = VarId::new(7103);

    let helper_lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("x", x_id),
            Binder::new("y", y_id),
            Binder::new("k", k_id),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
            args: vec![
                PseudoExpr::var_with_id("x", x_id),
                PseudoExpr::var_with_id("y", y_id),
            ]
            .into(),
        }),
    };
    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("h", h_id)),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".into(),
        id: Some(h_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(call_site),
    };

    let rewritten = inline_cps_identity_helpers(expr.clone());
    // Helper should still be there.
    assert!(
        matches!(rewritten, PseudoExpr::Let { .. }),
        "partial application must not drop the helper, got {:?}",
        rewritten
    );
}

#[test]
fn kp3_extended_inlines_helper_with_pure_dead_arg() {
    // KP3-extended: `let h = fn(x, y, _, k) { k(x, y) }` — dead
    // `_` slot. At full-applied site `h(1, 2, 0, my_k)`, the dead
    // arg `0` is a pure literal → rewrite to `my_k(1, 2)`.
    let h_id = VarId::new(7200);
    let x_id = VarId::new(7201);
    let y_id = VarId::new(7202);
    let dead_id = VarId::new(7203);
    let k_id = VarId::new(7204);
    let my_k_id = VarId::new(7210);

    let helper_lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("x", x_id),
            Binder::new("y", y_id),
            Binder::new("_", dead_id),
            Binder::new("k", k_id),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
            args: vec![
                PseudoExpr::var_with_id("x", x_id),
                PseudoExpr::var_with_id("y", y_id),
            ]
            .into(),
        }),
    };
    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("h", h_id)),
        args: vec![
            PseudoExpr::int(1),
            PseudoExpr::int(2),
            PseudoExpr::int(0), // pure dead-slot arg
            PseudoExpr::var_with_id("my_k", my_k_id),
        ]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".into(),
        id: Some(h_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(call_site),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    // Helper dropped; result = `my_k(1, 2)`.
    let PseudoExpr::Apply { function, args } = rewritten else {
        panic!("expected Apply, got {:?}", rewritten);
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        panic!("expected callback Var, got {:?}", function);
    };
    assert_eq!(*fn_id, my_k_id);
    assert_eq!(
        args.len(),
        2,
        "only the flowing args x, y; dead arg dropped"
    );
}

#[test]
fn kp3_extended_refuses_inline_when_dead_arg_is_impure() {
    // Same helper shape but call-site dead-arg is an impure
    // Apply expression. Must refuse to preserve evaluation.
    let h_id = VarId::new(7220);
    let x_id = VarId::new(7221);
    let y_id = VarId::new(7222);
    let dead_id = VarId::new(7223);
    let k_id = VarId::new(7224);

    let helper_lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("x", x_id),
            Binder::new("y", y_id),
            Binder::new("_", dead_id),
            Binder::new("k", k_id),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
            args: vec![
                PseudoExpr::var_with_id("x", x_id),
                PseudoExpr::var_with_id("y", y_id),
            ]
            .into(),
        }),
    };
    let impure_dead = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("compute_thing")),
        args: vec![PseudoExpr::int(42)].into(),
    };
    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("h", h_id)),
        args: vec![
            PseudoExpr::int(1),
            PseudoExpr::int(2),
            impure_dead,
            PseudoExpr::var_with_id("my_k", VarId::new(7230)),
        ]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".into(),
        id: Some(h_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(call_site),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    assert!(
        matches!(rewritten, PseudoExpr::Let { .. }),
        "impure dead-arg must keep helper alive, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_match_when_body_reorders_args() {
    // `let h = fn(x, y, k) { k(y, x) }` — body reorders args, NOT
    // identity-CPS. Must not match.
    let h_id = VarId::new(7300);
    let x_id = VarId::new(7301);
    let y_id = VarId::new(7302);
    let k_id = VarId::new(7303);

    let helper_lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("x", x_id),
            Binder::new("y", y_id),
            Binder::new("k", k_id),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
            args: vec![
                PseudoExpr::var_with_id("y", y_id),
                PseudoExpr::var_with_id("x", x_id),
            ]
            .into(),
        }),
    };
    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("h", h_id)),
        args: vec![
            PseudoExpr::int(1),
            PseudoExpr::int(2),
            PseudoExpr::var_with_id("my_k", VarId::new(7310)),
        ]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".into(),
        id: Some(h_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(call_site),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    assert!(
        matches!(rewritten, PseudoExpr::Let { .. }),
        "reordered args must NOT match KP3-narrow, got {:?}",
        rewritten
    );
}

#[test]
fn inlines_multiple_full_applications_in_body() {
    // Two callsites, both fully applied.
    let h_id = VarId::new(7400);
    let x_id = VarId::new(7401);
    let k_id = VarId::new(7402);

    let helper_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id), Binder::new("k", k_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
            args: vec![PseudoExpr::var_with_id("x", x_id)].into(),
        }),
    };
    let inner_body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("outer")),
        args: vec![
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("h", h_id)),
                args: vec![PseudoExpr::int(1), PseudoExpr::var("k1")].into(),
            },
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("h", h_id)),
                args: vec![PseudoExpr::int(2), PseudoExpr::var("k2")].into(),
            },
        ]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".into(),
        id: Some(h_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(inner_body),
    };

    let rewritten = inline_cps_identity_helpers(expr);

    // Helper dropped → just the outer Apply with two inlined args.
    let PseudoExpr::Apply { args, .. } = rewritten else {
        panic!("expected outer Apply after rewrite, got {:?}", rewritten);
    };
    assert_eq!(args.len(), 2);
    // Each arg is now `k_N(N)`.
    for arg in &args {
        let PseudoExpr::Apply {
            function,
            args: inner_args,
        } = arg
        else {
            panic!("expected inlined Apply, got {:?}", arg);
        };
        assert!(matches!(function.as_ref(), PseudoExpr::Var { .. }));
        assert_eq!(inner_args.len(), 1);
    }
}

#[test]
fn inlines_curried_cps_pair_constructor_with_consumer() {
    // KP1: `let pack = fn(a, b) { fn(k) { k(a, b) } } in pack(1, 2)(my_cb)`
    // → `my_cb(1, 2)`. Helper dropped.
    let pack_id = VarId::new(7600);
    let a_id = VarId::new(7601);
    let b_id = VarId::new(7602);
    let k_id = VarId::new(7603);
    let cb_id = VarId::new(7610);

    let inner_body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
        args: vec![
            PseudoExpr::var_with_id("a", a_id),
            PseudoExpr::var_with_id("b", b_id),
        ]
        .into(),
    };
    let inner_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("k", k_id)],
        body: PBox::new(inner_body),
    };
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
        body: PBox::new(inner_lambda),
    };
    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("pack", pack_id)),
            args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
        }),
        args: vec![PseudoExpr::var_with_id("my_cb", cb_id)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "pack".into(),
        id: Some(pack_id),
        value: PBox::new(outer_lambda),
        body: PBox::new(call_site),
    };

    let rewritten = inline_cps_identity_helpers(expr);

    let PseudoExpr::Apply { function, args } = rewritten else {
        panic!("expected Apply, got {:?}", rewritten);
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        panic!("expected callback Var, got {:?}", function);
    };
    assert_eq!(*fn_id, cb_id);
    assert_eq!(args.len(), 2);
}

#[test]
fn does_not_inline_curried_pair_constructor_used_partially() {
    // `let pack = fn(a, b) { fn(k) { k(a, b) } } in pack(1, 2)`
    // (just the partial — no callback applied). Helper STAYS:
    // the church-pair value cannot be reduced away until a
    // consumer projects it.
    let pack_id = VarId::new(7700);
    let a_id = VarId::new(7701);
    let b_id = VarId::new(7702);
    let k_id = VarId::new(7703);

    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("k", k_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
                args: vec![
                    PseudoExpr::var_with_id("a", a_id),
                    PseudoExpr::var_with_id("b", b_id),
                ]
                .into(),
            }),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "pack".into(),
        id: Some(pack_id),
        value: PBox::new(outer_lambda),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("pack", pack_id)),
            args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
        }),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    assert!(
        matches!(rewritten, PseudoExpr::Let { .. }),
        "partial application of curried CPS-pair must keep helper alive, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_inline_when_callback_is_impure_apply() {
    // Strict-evaluation safety: an Apply callback may have
    // effects, and the rewrite would change when it runs —
    // refuse.
    let h_id = VarId::new(7800);
    let x_id = VarId::new(7801);
    let k_id = VarId::new(7802);

    let helper_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id), Binder::new("k", k_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
            args: vec![PseudoExpr::var_with_id("x", x_id)].into(),
        }),
    };
    let impure_callback = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("compute_callback")),
        args: vec![PseudoExpr::int(42)].into(),
    };
    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("h", h_id)),
        args: vec![PseudoExpr::int(1), impure_callback].into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".into(),
        id: Some(h_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(call_site),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    assert!(
        matches!(rewritten, PseudoExpr::Let { .. }),
        "impure callback (Apply) must NOT trigger the rewrite, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_inline_curried_when_callback_is_impure() {
    // Same guard for the curried form.
    let pack_id = VarId::new(7900);
    let a_id = VarId::new(7901);
    let b_id = VarId::new(7902);
    let k_id = VarId::new(7903);

    let outer = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("k", k_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
                args: vec![
                    PseudoExpr::var_with_id("a", a_id),
                    PseudoExpr::var_with_id("b", b_id),
                ]
                .into(),
            }),
        }),
    };
    let impure_cb = PseudoExpr::BuiltinCall {
        name: crate::builtins::BuiltinId::HashSha256,
        args: vec![PseudoExpr::var("input_bytes")].into(),
    };
    let chain = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("pack", pack_id)),
            args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
        }),
        args: vec![impure_cb].into(),
    };
    let expr = PseudoExpr::Let {
        name: "pack".into(),
        id: Some(pack_id),
        value: PBox::new(outer),
        body: PBox::new(chain),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    assert!(
        matches!(rewritten, PseudoExpr::Let { .. }),
        "impure callback in curried chain must NOT trigger the rewrite, got {:?}",
        rewritten
    );
}

#[test]
fn kp2_inlines_church_left_constructor() {
    // KP2: `let left = fn(x) { fn(l, _) { l(x) } } in left(42)(handle_l, handle_r)`
    // → `handle_l(42)`. The right-handler arg is dead and pure
    // (Lambda literal), so it's safely dropped.
    let left_id = VarId::new(8000);
    let x_id = VarId::new(8001);
    let l_id = VarId::new(8002);
    let r_id = VarId::new(8003);
    let handle_l_id = VarId::new(8010);

    let inner_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("l", l_id), Binder::new("r", r_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("l", l_id)),
            args: vec![PseudoExpr::var_with_id("x", x_id)].into(),
        }),
    };
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(inner_lambda),
    };
    let consumer = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("left", left_id)),
            args: vec![PseudoExpr::int(42)].into(),
        }),
        args: vec![
            PseudoExpr::var_with_id("handle_l", handle_l_id),
            // Right handler — dead but pure (Lambda literal).
            PseudoExpr::Lambda {
                params: vec![Binder::new("y", VarId::new(8004))],
                body: PBox::new(PseudoExpr::int(0)),
            },
        ]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "left".into(),
        id: Some(left_id),
        value: PBox::new(outer_lambda),
        body: PBox::new(consumer),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    let PseudoExpr::Apply { function, args } = rewritten else {
        panic!("expected Apply, got {:?}", rewritten);
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        panic!("expected callback Var, got {:?}", function);
    };
    assert_eq!(
        *fn_id, handle_l_id,
        "active handler is handle_l (l-position)"
    );
    assert_eq!(args.len(), 1);
}

#[test]
fn kp2_inlines_church_right_constructor() {
    // KP2: `let right = fn(x) { fn(_, r) { r(x) } } in right(7)(hl, hr)`
    // → `hr(7)`. Active is the SECOND inner param.
    let right_id = VarId::new(8100);
    let x_id = VarId::new(8101);
    let l_id = VarId::new(8102);
    let r_id = VarId::new(8103);
    let hr_id = VarId::new(8110);

    let inner_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("l", l_id), Binder::new("r", r_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("r", r_id)),
            args: vec![PseudoExpr::var_with_id("x", x_id)].into(),
        }),
    };
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(inner_lambda),
    };
    let consumer = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("right", right_id)),
            args: vec![PseudoExpr::int(7)].into(),
        }),
        args: vec![
            // Left handler — dead but pure (Var).
            PseudoExpr::var("hl"),
            PseudoExpr::var_with_id("hr", hr_id),
        ]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "right".into(),
        id: Some(right_id),
        value: PBox::new(outer_lambda),
        body: PBox::new(consumer),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    let PseudoExpr::Apply { function, args } = rewritten else {
        panic!("expected Apply, got {:?}", rewritten);
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        panic!("expected Var function, got {:?}", function);
    };
    assert_eq!(*fn_id, hr_id, "active is hr (r-position)");
    assert_eq!(args.len(), 1);
}

#[test]
fn kp2_does_not_match_when_body_uses_two_inner_params() {
    // Only one arm may be active in a Church Either/Option
    // projection, so the matcher rejects an inner body that
    // references more than one inner-projection param.
    //
    // Body: `l(x, r)` — uses BOTH `l` and `r`. Should reject.
    let helper_id = VarId::new(8300);
    let x_id = VarId::new(8301);
    let l_id = VarId::new(8302);
    let r_id = VarId::new(8303);

    let inner_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("l", l_id), Binder::new("r", r_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("l", l_id)),
            args: vec![
                PseudoExpr::var_with_id("x", x_id),
                // Reference to the OTHER inner param — not a clean
                // single-arm projection.
                PseudoExpr::var_with_id("r", r_id),
            ]
            .into(),
        }),
    };
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(inner_lambda),
    };
    let call_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("h", helper_id)),
            args: vec![PseudoExpr::int(1)].into(),
        }),
        args: vec![PseudoExpr::var("hl"), PseudoExpr::var("hr")].into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".into(),
        id: Some(helper_id),
        value: PBox::new(outer_lambda),
        body: PBox::new(call_site),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    // Body references both inner params — matcher rejects, helper stays.
    assert!(
        matches!(rewritten, PseudoExpr::Let { .. }),
        "mixed-inner-param body must NOT match KP2, got {:?}",
        rewritten
    );
}

#[test]
fn kp2_refuses_inline_when_dead_inner_arm_is_impure() {
    // `let left = fn(x) { fn(l, _) { l(x) } } in left(1)(hl, impure)`
    // — the right-arm callback is an impure Apply. Refuse.
    let left_id = VarId::new(8200);
    let x_id = VarId::new(8201);
    let l_id = VarId::new(8202);
    let r_id = VarId::new(8203);

    let inner_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("l", l_id), Binder::new("r", r_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("l", l_id)),
            args: vec![PseudoExpr::var_with_id("x", x_id)].into(),
        }),
    };
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(inner_lambda),
    };
    let impure_right = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("compute_fallback")),
        args: vec![PseudoExpr::int(0)].into(),
    };
    let consumer = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("left", left_id)),
            args: vec![PseudoExpr::int(1)].into(),
        }),
        args: vec![PseudoExpr::var("hl"), impure_right].into(),
    };
    let expr = PseudoExpr::Let {
        name: "left".into(),
        id: Some(left_id),
        value: PBox::new(outer_lambda),
        body: PBox::new(consumer),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    assert!(
        matches!(rewritten, PseudoExpr::Let { .. }),
        "impure dead inner arm must keep helper alive, got {:?}",
        rewritten
    );
}

#[test]
fn keeps_helper_when_some_uses_are_bare_references() {
    // `let h = fn(x, k) { k(x) } in pass(h, h(1, k1))` — `h` is
    // referenced bare (passed as a value) AND fully applied. The
    // bare reference must keep the helper alive.
    let h_id = VarId::new(7500);
    let x_id = VarId::new(7501);
    let k_id = VarId::new(7502);

    let helper_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id), Binder::new("k", k_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
            args: vec![PseudoExpr::var_with_id("x", x_id)].into(),
        }),
    };
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("pass")),
        args: vec![
            PseudoExpr::var_with_id("h", h_id), // bare ref
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("h", h_id)),
                args: vec![PseudoExpr::int(1), PseudoExpr::var("k1")].into(),
            },
        ]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".into(),
        id: Some(h_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(body),
    };

    let rewritten = inline_cps_identity_helpers(expr);
    assert!(
        matches!(rewritten, PseudoExpr::Let { .. }),
        "bare reference must keep helper alive, got {:?}",
        rewritten
    );
}
