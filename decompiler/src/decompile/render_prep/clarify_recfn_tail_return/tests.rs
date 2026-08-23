use super::*;
use crate::pseudo::ast::Binder;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn with_marker(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("ctx", 2)],
            body: PBox::new(body),
        }),
        body: PBox::new(PseudoExpr::var_with_id("decompiled", VarId::new(1))),
    }
}

/// `fn h(a) { rec fn r(x) { r(x) } }` gains the trailing reference.
#[test]
fn wraps_bare_recfn_lambda_body() {
    let rec_fn = PseudoExpr::RecFn {
        name: binder("r", 10),
        params: vec![binder("x", 11)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("r", VarId::new(10))),
            args: vec![PseudoExpr::var_with_id("x", VarId::new(11))].into(),
        }),
    };
    let input = with_marker(PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("a", 21)],
            body: PBox::new(rec_fn),
        }),
        body: PBox::new(PseudoExpr::Bool(true)),
    });
    let out = clarify_recfn_tail_return(input);
    let PseudoExpr::Let { value, .. } = &out else {
        panic!()
    };
    let PseudoExpr::Lambda { body, .. } = value.as_ref() else {
        panic!()
    };
    let PseudoExpr::Let { value: h_value, .. } = body.as_ref() else {
        panic!("expected outer-h untouched: {body:?}")
    };
    let PseudoExpr::Lambda { body: h_body, .. } = h_value.as_ref() else {
        panic!()
    };
    let PseudoExpr::Let {
        name,
        id: Some(let_id),
        value: rec_value,
        body: tail,
    } = h_body.as_ref()
    else {
        panic!("expected define-then-reference, got: {h_body:?}");
    };
    assert_eq!(name, "r");
    assert!(matches!(rec_value.as_ref(), PseudoExpr::RecFn { .. }));
    assert_eq!(
        tail.as_ref(),
        &PseudoExpr::Var {
            name: "r".to_string(),
            id: Some(*let_id),
        }
    );
    assert_ne!(*let_id, VarId::new(10), "let binder must be fresh");
}

/// Second run is a no-op: the gate no longer matches the wrapped
/// `Lambda{body: Let}` shape. Re-exposing a bare-RecFn body, or
/// dropping the reference let, would re-fire the pass.
#[test]
fn idempotent_under_second_run() {
    let rec_fn = PseudoExpr::RecFn {
        name: binder("r", 10),
        params: vec![binder("x", 11)],
        body: PBox::new(PseudoExpr::var_with_id("x", VarId::new(11))),
    };
    let input = with_marker(PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("a", 21)],
            body: PBox::new(rec_fn),
        }),
        body: PBox::new(PseudoExpr::Bool(true)),
    });
    let once = clarify_recfn_tail_return(input);
    let twice = clarify_recfn_tail_return(once.clone());
    assert_eq!(once, twice);
}

/// A Lambda whose body is a Let-chain (already readable) is untouched.
#[test]
fn leaves_let_chain_bodies_alone() {
    let input = with_marker(PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(VarId::new(20)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("a", 21)],
            body: PBox::new(PseudoExpr::Let {
                name: "t".to_string(),
                id: Some(VarId::new(30)),
                value: PBox::new(PseudoExpr::int(1)),
                body: PBox::new(PseudoExpr::var_with_id("t", VarId::new(30))),
            }),
        }),
        body: PBox::new(PseudoExpr::Bool(true)),
    });
    let out = clarify_recfn_tail_return(input.clone());
    assert_eq!(out, input);
}
