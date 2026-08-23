use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::constructor::ConstructorShape;

/// Decode-on / decode-off render contexts; the flag is a plain value
/// now, so nothing needs saving and restoring.
fn decode_on() -> RenderCtx {
    RenderCtx::default().with_decode_church(true)
}
fn decode_off() -> RenderCtx {
    RenderCtx::default()
}

fn scott_cons(head: PseudoExpr, tail: PseudoExpr) -> PseudoExpr {
    PseudoExpr::constr(ConstructorShape::scott_positional(1, 2), vec![head, tail])
}

fn self_call(self_id: VarId, arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", self_id)),
        args: vec![arg].into(),
    }
}

/// `rec fn f(xs) { Constr2(head, f(tail)) }` → `[head, ..f(tail)]`.
#[test]
fn converts_scott_cons_with_self_call_to_native_cell() {
    let self_id = VarId::fresh_binding();
    let body = scott_cons(
        PseudoExpr::var_with_id("head", VarId::fresh_binding()),
        self_call(
            self_id,
            PseudoExpr::var_with_id("tail", VarId::fresh_binding()),
        ),
    );
    let rec = PseudoExpr::RecFn {
        name: Binder::new("f", self_id),
        params: vec![Binder::new("xs", VarId::fresh_binding())],
        body: PBox::new(body),
    };
    let out = recover_scott_list_builder(rec, &decode_on());
    let PseudoExpr::RecFn { body, .. } = out else {
        panic!("expected RecFn")
    };
    match body.into_inner() {
        PseudoExpr::List { elements, tail } => {
            assert_eq!(elements.len(), 1);
            assert!(tail.is_some(), "tail should be the recursive self-call");
        }
        other => panic!("expected native list cell, got {other:?}"),
    }
}

/// A 2-field constructor WITHOUT a self-call in field 2 is left alone.
#[test]
fn leaves_non_self_call_constructor() {
    let self_id = VarId::fresh_binding();
    let body = scott_cons(
        PseudoExpr::var_with_id("a", VarId::fresh_binding()),
        PseudoExpr::var_with_id("b", VarId::fresh_binding()), // not a self-call
    );
    let rec = PseudoExpr::RecFn {
        name: Binder::new("f", self_id),
        params: vec![Binder::new("xs", VarId::fresh_binding())],
        body: PBox::new(body),
    };
    let out = recover_scott_list_builder(rec, &decode_on());
    let PseudoExpr::RecFn { body, .. } = out else {
        panic!("expected RecFn")
    };
    assert!(
        matches!(*body, PseudoExpr::Constr { .. }),
        "should stay a Constr"
    );
}

/// No-op when the decode-church flag is off (default byte-stability).
#[test]
fn inert_without_flag() {
    let self_id = VarId::fresh_binding();
    let body = scott_cons(
        PseudoExpr::var_with_id("head", VarId::fresh_binding()),
        self_call(
            self_id,
            PseudoExpr::var_with_id("tail", VarId::fresh_binding()),
        ),
    );
    let rec = PseudoExpr::RecFn {
        name: Binder::new("f", self_id),
        params: vec![Binder::new("xs", VarId::fresh_binding())],
        body: PBox::new(body.clone()),
    };
    let out = recover_scott_list_builder(rec, &decode_off());
    let PseudoExpr::RecFn { body: out_body, .. } = out else {
        panic!("expected RecFn")
    };
    assert!(
        matches!(*out_body, PseudoExpr::Constr { .. }),
        "flag off → unchanged"
    );
}
