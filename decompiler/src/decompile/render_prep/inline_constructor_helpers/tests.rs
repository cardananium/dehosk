use super::*;
use crate::pseudo::ast::Binder;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `fn pair_pack(a, b) { Pair(a, b) }` + call → inlined; let dropped.
#[test]
fn inlines_pair_helper_and_drops_let() {
    let helper_id = VarId::new(500);
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("a", 100), binder("b", 101)],
        body: PBox::new(PseudoExpr::Pair(
            PBox::new(varref("a", 100)),
            PBox::new(varref("b", 101)),
        )),
    };
    let use_site = PseudoExpr::Apply {
        function: PBox::new(varref("pair_pack", 500)),
        args: vec![varref("x", 1), varref("y", 2)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "pair_pack".into(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(use_site),
    };
    let out = inline_constructor_helpers(expr);
    // Result should be just `Pair(x, y)` — let dropped.
    match out {
        PseudoExpr::Pair(a, b) => {
            assert!(matches!(*a, PseudoExpr::Var { .. }));
            assert!(matches!(*b, PseudoExpr::Var { .. }));
        }
        _ => panic!("expected Pair, got {:?}", out),
    }
}

/// `fn pack_3(a, b, c) { (a, b, c) }` + call → Tuple inlined.
#[test]
fn inlines_tuple_helper() {
    let helper_id = VarId::new(500);
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("a", 100), binder("b", 101), binder("c", 102)],
        body: PBox::new(PseudoExpr::Tuple(
            vec![varref("a", 100), varref("b", 101), varref("c", 102)].into(),
        )),
    };
    let use_site = PseudoExpr::Apply {
        function: PBox::new(varref("pack_3", 500)),
        args: vec![varref("x", 1), varref("y", 2), varref("z", 3)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "pack_3".into(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(use_site),
    };
    let out = inline_constructor_helpers(expr);
    match out {
        PseudoExpr::Tuple(items) => assert_eq!(items.len(), 3),
        _ => panic!("expected Tuple, got {:?}", out),
    }
}

/// `fn helper_3(h, t) { [h, ..t] }` + call → List inlined.
#[test]
fn inlines_cons_helper() {
    let helper_id = VarId::new(500);
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("h", 100), binder("t", 101)],
        body: PBox::new(PseudoExpr::List {
            elements: vec![varref("h", 100)].into(),
            tail: Some(PBox::new(varref("t", 101))),
        }),
    };
    let use_site = PseudoExpr::Apply {
        function: PBox::new(varref("helper_3", 500)),
        args: vec![varref("a", 1), varref("b", 2)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "helper_3".into(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(use_site),
    };
    let out = inline_constructor_helpers(expr);
    match out {
        PseudoExpr::List { elements, tail } => {
            assert_eq!(elements.len(), 1);
            assert!(tail.is_some());
        }
        _ => panic!("expected List, got {:?}", out),
    }
}

/// Bare ref keeps the helper definition alive; call sites still
/// inlined.
#[test]
fn bare_ref_keeps_let_but_inlines_calls() {
    let helper_id = VarId::new(500);
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("a", 100), binder("b", 101)],
        body: PBox::new(PseudoExpr::Pair(
            PBox::new(varref("a", 100)),
            PBox::new(varref("b", 101)),
        )),
    };
    // Body has one call AND one bare ref.
    let body = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Apply {
                function: PBox::new(varref("pair_pack", 500)),
                args: vec![varref("x", 1), varref("y", 2)].into(),
            },
            varref("pair_pack", 500), // bare reference
        ]
        .into(),
    );
    let expr = PseudoExpr::Let {
        name: "pair_pack".into(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(body),
    };
    let out = inline_constructor_helpers(expr);
    // The let must survive due to the bare ref.
    assert!(matches!(out, PseudoExpr::Let { .. }));
}

/// Helper whose body uses closure-captured vars (NOT params) is not
/// inlinable. Each pair component must be exactly a `Var(params[i].id)`.
#[test]
fn does_not_inline_helper_with_closure_captures() {
    let helper_id = VarId::new(500);
    // `fn(a, b) { Pair(outer_c, outer_d) }` — body refs closure vars.
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("a", 100), binder("b", 101)],
        body: PBox::new(PseudoExpr::Pair(
            PBox::new(varref("outer_c", 999)),
            PBox::new(varref("outer_d", 1000)),
        )),
    };
    let use_site = PseudoExpr::Apply {
        function: PBox::new(varref("h", 500)),
        args: vec![varref("x", 1), varref("y", 2)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "h".into(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(use_site.clone()),
    };
    let out = inline_constructor_helpers(expr);
    // Let must survive — body shape isn't recognized as inlinable.
    assert!(matches!(out, PseudoExpr::Let { .. }));
}

/// Wrong-arity call (call with 1 arg when helper takes 2) → not inlined.
#[test]
fn does_not_inline_wrong_arity_call() {
    let helper_id = VarId::new(500);
    let helper_value = PseudoExpr::Lambda {
        params: vec![binder("a", 100), binder("b", 101)],
        body: PBox::new(PseudoExpr::Pair(
            PBox::new(varref("a", 100)),
            PBox::new(varref("b", 101)),
        )),
    };
    // Partial application — only 1 arg.
    let use_site = PseudoExpr::Apply {
        function: PBox::new(varref("pair_pack", 500)),
        args: vec![varref("x", 1)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "pair_pack".into(),
        id: Some(helper_id),
        value: PBox::new(helper_value),
        body: PBox::new(use_site),
    };
    let out = inline_constructor_helpers(expr);
    // Let must survive (the partial call is a bare-like ref).
    assert!(matches!(out, PseudoExpr::Let { .. }));
}
