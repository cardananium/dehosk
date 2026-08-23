use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

fn church_cons_helper() -> (VarId, PseudoExpr) {
    let helper_id = VarId::fresh_binding();
    let a = VarId::fresh_binding();
    let b = VarId::fresh_binding();
    let dead = VarId::fresh_binding();
    let k = VarId::fresh_binding();
    let value = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a), Binder::new("b", b)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("_", dead), Binder::new("k", k)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("k", k)),
                args: vec![
                    PseudoExpr::var_with_id("a", a),
                    PseudoExpr::var_with_id("b", b),
                ]
                .into(),
            }),
        }),
    };
    (helper_id, value)
}

#[test]
fn merges_two_church_cons_helpers_into_one_canonical() {
    // Two structurally-equivalent helpers + a body that uses both.
    let (helper_13_id, value_13) = church_cons_helper();
    let (helper_22_id, value_22) = church_cons_helper();
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![
            PseudoExpr::var_with_id("helper_13", helper_13_id),
            PseudoExpr::var_with_id("helper_22", helper_22_id),
        ]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "helper_13".to_string(),
        id: Some(helper_13_id),
        value: PBox::new(value_13),
        body: PBox::new(PseudoExpr::Let {
            name: "helper_22".to_string(),
            id: Some(helper_22_id),
            value: PBox::new(value_22),
            body: PBox::new(body),
        }),
    };

    let result = cse_church_cons_helpers(expr);
    // Should be a single Let `church_cons` followed by the body
    // (with both helper_13 and helper_22 redirected).
    let PseudoExpr::Let {
        name,
        body: outer_body,
        ..
    } = result
    else {
        panic!("expected outer Let, got {:?}", result)
    };
    assert_eq!(name, "church_cons", "canonical name must be church_cons");
    // Inner body should be the original Apply (no more Lets for the
    // dead helper).
    let PseudoExpr::Apply { args, .. } = outer_body.into_inner() else {
        panic!()
    };
    // Both args should now point to the canonical helper VarId.
    let PseudoExpr::Var {
        id: Some(id_a),
        name: name_a,
    } = &args[0]
    else {
        panic!()
    };
    let PseudoExpr::Var {
        id: Some(id_b),
        name: name_b,
    } = &args[1]
    else {
        panic!()
    };
    assert_eq!(id_a, id_b, "both args must redirect to same canonical id");
    assert_eq!(name_a, "church_cons");
    assert_eq!(name_b, "church_cons");
}

#[test]
fn leaves_single_church_cons_helper_alone() {
    // Only ONE church-cons helper — no CSE needed.
    let (h_id, value) = church_cons_helper();
    let expr = PseudoExpr::Let {
        name: "helper_22".to_string(),
        id: Some(h_id),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::var_with_id("helper_22", h_id)),
    };
    let result = cse_church_cons_helpers(expr);
    let PseudoExpr::Let { name, .. } = result else {
        panic!()
    };
    assert_eq!(name, "helper_22", "single helper keeps original name");
}

#[test]
fn does_not_match_non_church_cons_shape() {
    // 2-param Lambda whose inner body uses a different arg pattern.
    let h_id = VarId::fresh_binding();
    let a = VarId::fresh_binding();
    let b = VarId::fresh_binding();
    let k = VarId::fresh_binding();
    let value = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a), Binder::new("b", b)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("k", k)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("k", k)),
                args: vec![
                    PseudoExpr::var_with_id("a", a),
                    PseudoExpr::var_with_id("b", b),
                ]
                .into(),
            }),
        }),
    };
    // 1 inner param (not 2) — doesn't match the Church-cons shape.
    let (h_id_2, _value_2) = church_cons_helper();
    let expr = PseudoExpr::Let {
        name: "h1".to_string(),
        id: Some(h_id),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::Let {
            name: "h2".to_string(),
            id: Some(h_id_2),
            value: PBox::new(church_cons_helper().1),
            body: PBox::new(PseudoExpr::var_with_id("h1", h_id)),
        }),
    };
    let result = cse_church_cons_helpers(expr);
    // h1 is NOT a church-cons. h2 alone isn't enough for CSE.
    // Result: both lets preserved, no CSE.
    let PseudoExpr::Let { name, .. } = &result else {
        panic!()
    };
    assert_eq!(name, "h1", "non-canonical h1 stays first");
}
