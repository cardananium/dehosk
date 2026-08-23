use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

fn church_true_lambda() -> PseudoExpr {
    let t_id = VarId::fresh_binding();
    let d_id = VarId::fresh_binding();
    PseudoExpr::Lambda {
        params: vec![Binder::new("t", t_id), Binder::new("_", d_id)],
        body: PBox::new(PseudoExpr::var_with_id("t", t_id)),
    }
}

fn church_false_lambda() -> PseudoExpr {
    let d_id = VarId::fresh_binding();
    let f_id = VarId::fresh_binding();
    PseudoExpr::Lambda {
        params: vec![Binder::new("_", d_id), Binder::new("f", f_id)],
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    }
}

#[test]
fn hoists_when_church_true_appears_twice() {
    // Expression contains TWO Church-True lambdas — must hoist.
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![church_true_lambda(), church_true_lambda()].into(),
    };
    let result = hoist_church_bool_selectors(expr);
    // Result should start with `let church_true = ...; <body>`.
    let PseudoExpr::Let {
        name, value, body, ..
    } = result
    else {
        panic!("expected outer Let, got something else");
    };
    assert_eq!(name, "church_true");
    assert!(
        matches!(value.into_inner(), PseudoExpr::Lambda { params, .. } if params.len() == 2),
        "let value must be a 2-param Lambda"
    );
    // Body should be the Apply with Var refs in args.
    let PseudoExpr::Apply { args, .. } = body.into_inner() else {
        panic!("expected Apply body");
    };
    assert!(
        matches!(&args[0], PseudoExpr::Var { name, .. } if name == "church_true"),
        "first arg should be Var(church_true)"
    );
    assert!(
        matches!(&args[1], PseudoExpr::Var { name, .. } if name == "church_true"),
        "second arg should be Var(church_true)"
    );
}

#[test]
fn does_not_hoist_when_only_one_occurrence() {
    // Single occurrence — no const declaration needed.
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![church_true_lambda()].into(),
    };
    let result = hoist_church_bool_selectors(expr);
    // Should NOT be wrapped in a Let.
    assert!(
        matches!(result, PseudoExpr::Apply { .. }),
        "single-use must not hoist, got {:?}",
        result
    );
}

#[test]
fn hoists_both_when_true_and_false_each_appear_twice() {
    // Both selectors hoisted — both consts prepended.
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![
            church_true_lambda(),
            church_true_lambda(),
            church_false_lambda(),
            church_false_lambda(),
        ]
        .into(),
    };
    let result = hoist_church_bool_selectors(expr);
    // Result should start with two nested Lets.
    let PseudoExpr::Let {
        name: name1,
        body: body1,
        ..
    } = result
    else {
        panic!("expected outer Let")
    };
    assert_eq!(name1, "church_true");
    let PseudoExpr::Let {
        name: name2,
        body: body2,
        ..
    } = body1.into_inner()
    else {
        panic!("expected inner Let")
    };
    assert_eq!(name2, "church_false");
    // The innermost body is the rewritten Apply with Var refs.
    assert!(matches!(*body2, PseudoExpr::Apply { .. }));
}

#[test]
fn does_not_match_non_selector_lambda() {
    // 3-param Lambda with body referencing first param — NOT a 2-param
    // Church selector. Must not match.
    let p0 = VarId::fresh_binding();
    let p1 = VarId::fresh_binding();
    let p2 = VarId::fresh_binding();
    let not_selector = PseudoExpr::Lambda {
        params: vec![
            Binder::new("a", p0),
            Binder::new("b", p1),
            Binder::new("c", p2),
        ],
        body: PBox::new(PseudoExpr::var_with_id("a", p0)),
    };
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![not_selector.clone(), not_selector].into(),
    };
    let result = hoist_church_bool_selectors(expr);
    assert!(
        matches!(result, PseudoExpr::Apply { .. }),
        "3-param Lambda must not be hoisted"
    );
}
