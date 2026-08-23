use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

/// Build the canonical church-pair-pack helper:
/// `let h = fn(p_0, p_1, _, k) { k(p_0, p_1) } in body`.
fn church_pair_helper_let(
    helper_id: VarId,
    body: PseudoExpr,
) -> (VarId, VarId, VarId, VarId, PseudoExpr) {
    let p0 = VarId::fresh_binding();
    let p1 = VarId::fresh_binding();
    let p2 = VarId::fresh_binding();
    let k = VarId::fresh_binding();
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("h", p0),
            Binder::new("t", p1),
            Binder::new("_", p2),
            Binder::new("k", k),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k)),
            args: vec![
                PseudoExpr::var_with_id("h", p0),
                PseudoExpr::var_with_id("t", p1),
            ]
            .into(),
        }),
    };
    let let_expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(helper_id),
        value: PBox::new(lambda),
        body: PBox::new(body),
    };
    (p0, p1, p2, k, let_expr)
}

#[test]
fn curry_splits_when_all_calls_partial_at_k() {
    // Body has TWO 2-arg calls; helper has 4 params → split at k=2.
    let helper_id = VarId::new(11000);
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("seq", VarId::fresh_binding())),
        args: vec![
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
                args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
            },
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
                args: vec![PseudoExpr::int(3), PseudoExpr::int(4)].into(),
            },
        ]
        .into(),
    };
    let (_, _, _, _, expr) = church_pair_helper_let(helper_id, body);

    let result = curry_split_partial_helpers(expr);

    // The let value should now be:
    //   Lambda(p_0, p_1) { Lambda(p_2, k) { k(p_0, p_1) } }
    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected outer Let preserved");
    };
    let PseudoExpr::Lambda {
        params: outer_params,
        body: outer_body,
    } = value.into_inner()
    else {
        panic!("expected outer Lambda after split, got non-Lambda");
    };
    assert_eq!(outer_params.len(), 2, "outer Lambda should have 2 params");
    let PseudoExpr::Lambda {
        params: inner_params,
        ..
    } = outer_body.into_inner()
    else {
        panic!("expected inner Lambda nested in outer body");
    };
    assert_eq!(inner_params.len(), 2, "inner Lambda should have 2 params");
}

#[test]
fn does_not_split_when_some_calls_full_arity() {
    // Mixed arities — one 4-arg call and one 2-arg —
    // prevent the split.
    let helper_id = VarId::new(11100);
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("seq", VarId::fresh_binding())),
        args: vec![
            // partial 2-arg
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
                args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
            },
            // full 4-arg
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
                args: vec![
                    PseudoExpr::int(1),
                    PseudoExpr::int(2),
                    PseudoExpr::Unit,
                    PseudoExpr::Lambda {
                        params: vec![
                            Binder::new("a", VarId::fresh_binding()),
                            Binder::new("b", VarId::fresh_binding()),
                        ],
                        body: PBox::new(PseudoExpr::Unit),
                    },
                ]
                .into(),
            },
        ]
        .into(),
    };
    let (_, _, _, _, expr) = church_pair_helper_let(helper_id, body);

    let result = curry_split_partial_helpers(expr);

    // The let value should be UNCHANGED (still single outer 4-param Lambda).
    let PseudoExpr::Let { value, .. } = result else {
        panic!()
    };
    let PseudoExpr::Lambda { params, body, .. } = value.into_inner() else {
        panic!()
    };
    assert_eq!(params.len(), 4, "must NOT have been split");
    assert!(
        matches!(*body, PseudoExpr::Apply { .. }),
        "body must remain the original Apply, not a nested Lambda"
    );
}

#[test]
fn does_not_split_when_no_partial_call_sites() {
    // The helper has no call sites at all → no splitting needed.
    let helper_id = VarId::new(11200);
    let body = PseudoExpr::Unit; // Never references the helper.
    let (_, _, _, _, expr) = church_pair_helper_let(helper_id, body);

    let result = curry_split_partial_helpers(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!()
    };
    let PseudoExpr::Lambda { params, .. } = value.into_inner() else {
        panic!()
    };
    assert_eq!(params.len(), 4, "no-callsite helper must stay full-arity");
}

#[test]
fn does_not_split_three_param_helper_when_k_equals_two() {
    // 3-param helper with 2-arg call sites. K=2, n=3 sits on the
    // n >= 3 gate in try_match_church_pair_shape, so the split
    // does fire — outer 2 params, inner 1.
    let helper_id = VarId::new(11300);
    let p0 = VarId::fresh_binding();
    let p1 = VarId::fresh_binding();
    let k = VarId::fresh_binding();
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("h", p0),
            Binder::new("t", p1),
            Binder::new("k", k),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k)),
            args: vec![
                PseudoExpr::var_with_id("h", p0),
                PseudoExpr::var_with_id("t", p1),
            ]
            .into(),
        }),
    };
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(helper_id),
        value: PBox::new(lambda),
        body: PBox::new(body),
    };

    let result = curry_split_partial_helpers(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!()
    };
    let PseudoExpr::Lambda {
        params: outer_params,
        body: outer_body,
    } = value.into_inner()
    else {
        panic!()
    };
    assert_eq!(outer_params.len(), 2, "outer should have K=2 params");
    let PseudoExpr::Lambda {
        params: inner_params,
        ..
    } = outer_body.into_inner()
    else {
        panic!()
    };
    assert_eq!(inner_params.len(), 1, "inner should have n-K=1 param");
}

#[test]
fn force_wrapped_call_site_arity_is_counted_correctly() {
    // A `Force(Var(helper))` call head — helpers are thunked
    // in Plutus — must be peeled before the arity is counted.
    let helper_id = VarId::new(11400);
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id(
            "helper", helper_id,
        )))),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };
    let (_, _, _, _, expr) = church_pair_helper_let(helper_id, body);

    let result = curry_split_partial_helpers(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!()
    };
    let PseudoExpr::Lambda {
        params: outer_params,
        ..
    } = value.into_inner()
    else {
        panic!()
    };
    assert_eq!(
        outer_params.len(),
        2,
        "Force-wrapped 2-arg call must trigger K=2 split"
    );
}
