use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

fn n_pack_helper(n: usize) -> (VarId, PseudoExpr) {
    let helper_id = VarId::fresh_binding();
    let outer_ids: Vec<VarId> = (0..n).map(|_| VarId::fresh_binding()).collect();
    let outer_binders: Vec<Binder> = outer_ids
        .iter()
        .enumerate()
        .map(|(i, id)| Binder::new(format!("a_{}", i), *id))
        .collect();
    let x_id = VarId::fresh_binding();
    let inner_body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        args: outer_ids
            .iter()
            .enumerate()
            .map(|(i, id)| PseudoExpr::var_with_id(format!("a_{}", i), *id))
            .collect(),
    };
    let value = PseudoExpr::Lambda {
        params: outer_binders,
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(inner_body),
        }),
    };
    (helper_id, value)
}

#[test]
fn renames_arity_10_helper_to_pack_10() {
    let (helper_id, value) = n_pack_helper(10);
    let expr = PseudoExpr::Let {
        name: "helper_20".to_string(),
        id: Some(helper_id),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::var_with_id("helper_20", helper_id)),
    };
    let result = rename_church_n_pack_helpers(expr);
    let PseudoExpr::Let { name, body, .. } = result else {
        panic!()
    };
    assert_eq!(name, "pack_10");
    let PseudoExpr::Var { name, .. } = body.into_inner() else {
        panic!()
    };
    assert_eq!(name, "pack_10", "use site must also be renamed");
}

#[test]
fn leaves_arity_2_helpers_alone() {
    // Arity-2 packs are handled by pair_pack; this pass skips them.
    let (helper_id, value) = n_pack_helper(2);
    let expr = PseudoExpr::Let {
        name: "helper_X".to_string(),
        id: Some(helper_id),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::var_with_id("helper_X", helper_id)),
    };
    let result = rename_church_n_pack_helpers(expr);
    let PseudoExpr::Let { name, .. } = result else {
        panic!()
    };
    assert_eq!(name, "helper_X", "arity-2 must NOT be renamed");
}

#[test]
fn does_not_match_non_pack_shape() {
    // 3-param Lambda whose inner body references a different Var
    // (not the inner-Lambda's param).
    let helper_id = VarId::fresh_binding();
    let a = VarId::fresh_binding();
    let b = VarId::fresh_binding();
    let c = VarId::fresh_binding();
    let x = VarId::fresh_binding();
    let y_id = VarId::fresh_binding();
    let value = PseudoExpr::Lambda {
        params: vec![
            Binder::new("a", a),
            Binder::new("b", b),
            Binder::new("c", c),
        ],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x)],
            // Body applies a DIFFERENT var (not x) — not a pack shape.
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("y", y_id)),
                args: vec![
                    PseudoExpr::var_with_id("a", a),
                    PseudoExpr::var_with_id("b", b),
                    PseudoExpr::var_with_id("c", c),
                ]
                .into(),
            }),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(helper_id),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::var_with_id("h", helper_id)),
    };
    let result = rename_church_n_pack_helpers(expr);
    let PseudoExpr::Let { name, .. } = result else {
        panic!()
    };
    assert_eq!(name, "h", "non-pack shape must NOT be renamed");
}

#[test]
fn renames_multiple_packs_to_their_arity_specific_names() {
    let (h10_id, v10) = n_pack_helper(10);
    let (h3_id, v3) = n_pack_helper(3);
    let expr = PseudoExpr::Let {
        name: "h10".to_string(),
        id: Some(h10_id),
        value: PBox::new(v10),
        body: PBox::new(PseudoExpr::Let {
            name: "h3".to_string(),
            id: Some(h3_id),
            value: PBox::new(v3),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![
                    PseudoExpr::var_with_id("h10", h10_id),
                    PseudoExpr::var_with_id("h3", h3_id),
                ]
                .into(),
            }),
        }),
    };
    let result = rename_church_n_pack_helpers(expr);
    let PseudoExpr::Let {
        name: n1, body: b1, ..
    } = result
    else {
        panic!()
    };
    assert_eq!(n1, "pack_10");
    let PseudoExpr::Let {
        name: n2, body: b2, ..
    } = b1.into_inner()
    else {
        panic!()
    };
    assert_eq!(n2, "pack_3");
    let PseudoExpr::Apply { args, .. } = b2.into_inner() else {
        panic!()
    };
    let PseudoExpr::Var { name: a0_name, .. } = &args[0] else {
        panic!()
    };
    let PseudoExpr::Var { name: a1_name, .. } = &args[1] else {
        panic!()
    };
    assert_eq!(a0_name, "pack_10");
    assert_eq!(a1_name, "pack_3");
}
