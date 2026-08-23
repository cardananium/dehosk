use super::*;
use crate::pseudo::ast::PBox;

fn pack_let(body: PseudoExpr) -> PseudoExpr {
    // let w6 = (church_eq, b_46, c_46) in <body>
    PseudoExpr::Let {
        name: "w6".to_string(),
        id: Some(VarId::new(60)),
        value: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("church_eq", VarId::new(1)),
                PseudoExpr::var_with_id("b_46", VarId::new(2)),
                PseudoExpr::var_with_id("c_46", VarId::new(3)),
            ]
            .into(),
        )),
        body: PBox::new(body),
    }
}

fn w6_proj(sel: &str) -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::var_with_id("w6", VarId::new(60))),
        selector: FieldSelector::NamedField(sel.to_string()),
    }
}

#[test]
fn resolves_numeric_projection_to_element() {
    // w6.1 → b_46  (0-based numeric, pre-normalize)
    let out = resolve_pack_ordinal_projection(pack_let(w6_proj("1")));
    let PseudoExpr::Let { body, .. } = out else {
        panic!("let")
    };
    assert!(
        matches!(&*body, PseudoExpr::Var { name, .. } if name == "b_46"),
        "w6.1 should resolve to b_46, got {body:?}"
    );
}

#[test]
fn resolves_ordinal_projection_to_element() {
    // w6.2nd → b_46  (1-based ordinal, post-normalize); applied form.
    let call = PseudoExpr::Apply {
        function: PBox::new(w6_proj("2nd")),
        args: vec![PseudoExpr::int(0)].into(),
    };
    let out = resolve_pack_ordinal_projection(pack_let(call));
    let PseudoExpr::Let { body, .. } = out else {
        panic!("let")
    };
    // w6.2nd(0) → b_46(0)
    assert!(
        matches!(&*body, PseudoExpr::Apply { function, .. }
            if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "b_46")),
        "w6.2nd(0) should resolve to b_46(0), got {body:?}"
    );
}

#[test]
fn resolves_first_and_last() {
    // w6.1st → church_eq (idx 0); w6.3rd → c_46 (idx 2)
    let first = resolve_pack_ordinal_projection(pack_let(w6_proj("1st")));
    let PseudoExpr::Let { body, .. } = first else {
        panic!()
    };
    assert!(matches!(&*body, PseudoExpr::Var { name, .. } if name == "church_eq"));
    let last = resolve_pack_ordinal_projection(pack_let(w6_proj("3rd")));
    let PseudoExpr::Let { body, .. } = last else {
        panic!()
    };
    assert!(matches!(&*body, PseudoExpr::Var { name, .. } if name == "c_46"));
}

#[test]
fn leaves_projection_on_impure_tuple() {
    // let t = (foo(), b) — foo() is impure (Apply) → not collected → t.1st kept.
    let expr = PseudoExpr::Let {
        name: "t".to_string(),
        id: Some(VarId::new(70)),
        value: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("foo")),
                    args: vec![].into(),
                },
                PseudoExpr::var_with_id("b", VarId::new(4)),
            ]
            .into(),
        )),
        body: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("t", VarId::new(70))),
            selector: FieldSelector::NamedField("1st".to_string()),
        }),
    };
    let out = resolve_pack_ordinal_projection(expr.clone());
    assert_eq!(
        out, expr,
        "impure-element tuple projection must be left alone"
    );
}

#[test]
fn leaves_non_tuple_field_access() {
    // x.fields on a non-collected var → untouched.
    let expr = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::var_with_id("x", VarId::new(80))),
        selector: FieldSelector::NamedField("fields".to_string()),
    };
    let out = resolve_pack_ordinal_projection(expr.clone());
    assert_eq!(out, expr);
}

#[test]
fn malformed_ordinal_selector_is_rejected() {
    // A NamedField that is neither numeric nor a valid ordinal (digits +
    // st/nd/rd/th) must not be resolved.
    assert_eq!(parse_index("2foo"), None);
    assert_eq!(parse_index("nd"), None);
    assert_eq!(parse_index("fields"), None);
    assert_eq!(parse_index("2nd"), Some(1));
    assert_eq!(parse_index("1"), Some(1));
    assert_eq!(parse_index("8th"), Some(7));
}

#[test]
fn does_not_collect_tuple_with_lambda_element() {
    // A tuple element with internal binders (a Lambda) is NOT inlinable —
    // multi-site projection would duplicate its binder VarIds.
    let expr = PseudoExpr::Let {
        name: "t".to_string(),
        id: Some(VarId::new(90)),
        value: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("a", VarId::new(5)),
                PseudoExpr::Lambda {
                    params: vec![crate::pseudo::ast::Binder::new("z", VarId::new(6))],
                    body: PBox::new(PseudoExpr::var_with_id("z", VarId::new(6))),
                },
            ]
            .into(),
        )),
        body: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("t", VarId::new(90))),
            selector: FieldSelector::NamedField("1st".to_string()),
        }),
    };
    let out = resolve_pack_ordinal_projection(expr.clone());
    assert_eq!(
        out, expr,
        "tuple with a Lambda element must not be collected/resolved"
    );
}

#[test]
fn out_of_range_index_is_left_alone() {
    // w6 has 3 elements; w6.9th is out of range → leave it (defensive).
    let out = resolve_pack_ordinal_projection(pack_let(w6_proj("9th")));
    let PseudoExpr::Let { body, .. } = out else {
        panic!()
    };
    assert!(
        matches!(&*body, PseudoExpr::FieldAccess { .. }),
        "out-of-range kept"
    );
}
