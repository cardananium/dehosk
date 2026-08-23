use super::*;
use crate::pseudo::ast::PVec;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

fn zero_arg_constr(tag: usize) -> PseudoExpr {
    PseudoExpr::Constr {
        tag,
        shape: ConstructorShape::unknown_data(tag, 0),
        fields: PVec::new(),
        type_hint: None,
    }
}

#[test]
fn strips_void_apply_on_zero_arg_constr() {
    // `const c1 = Constr(tag=2, []); c1(Void)` — must become `c1`.
    let c1_id = VarId::new(40000);
    let expr = PseudoExpr::Let {
        name: "c1".into(),
        id: Some(c1_id),
        value: PBox::new(zero_arg_constr(2)),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("c1", c1_id)),
            args: vec![PseudoExpr::Unit].into(),
        }),
    };

    let rewritten = strip_void_apply_on_constr(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!()
    };
    // body should be Var("c1", c1_id) — Apply stripped.
    let body = body.into_inner();
    let PseudoExpr::Var { name, id: Some(id) } = body else {
        panic!("expected Var body, got {:?}", body);
    };
    assert_eq!(name, "c1");
    assert_eq!(id, c1_id);
}

#[test]
fn leaves_non_void_apply_alone() {
    // `c1(some_arg)` — non-Unit arg — must stay an Apply.
    let c1_id = VarId::new(41000);
    let expr = PseudoExpr::Let {
        name: "c1".into(),
        id: Some(c1_id),
        value: PBox::new(zero_arg_constr(0)),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("c1", c1_id)),
            args: vec![PseudoExpr::int(42)].into(),
        }),
    };

    let rewritten = strip_void_apply_on_constr(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!()
    };
    assert!(
        matches!(*body, PseudoExpr::Apply { .. }),
        "non-Unit apply must not be stripped"
    );
}

#[test]
fn leaves_void_apply_on_non_constr_let() {
    // `let f = fn(x) { x }; f(Void)` — f isn't a Constr-const, so
    // the Apply stays.
    let f_id = VarId::new(42000);
    let x_id = VarId::new(42001);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    let expr = PseudoExpr::Let {
        name: "f".into(),
        id: Some(f_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
            args: vec![PseudoExpr::Unit].into(),
        }),
    };

    let rewritten = strip_void_apply_on_constr(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!()
    };
    assert!(
        matches!(*body, PseudoExpr::Apply { .. }),
        "Lambda-bound let must not trigger strip, got {:?}",
        body
    );
}

#[test]
fn leaves_multi_arg_apply_alone() {
    // `c1(Void, X)` — 2 args — must not be stripped (only 1-arg Unit
    // matches the force-thunk pattern).
    let c1_id = VarId::new(43000);
    let expr = PseudoExpr::Let {
        name: "c1".into(),
        id: Some(c1_id),
        value: PBox::new(zero_arg_constr(1)),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("c1", c1_id)),
            args: vec![PseudoExpr::Unit, PseudoExpr::int(1)].into(),
        }),
    };
    let rewritten = strip_void_apply_on_constr(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!()
    };
    assert!(matches!(body.into_inner(), PseudoExpr::Apply { args, .. } if args.len() == 2));
}

#[test]
fn does_not_strip_apply_on_non_zero_arg_constr() {
    // `let c1 = Constr(tag=0, fields=[42, 17]); c1(Void)` — Constr
    // is NON-zero-arity. Strip must NOT fire (the binder isn't a
    // forced-thunk shape).
    let c1_id = VarId::new(44000);
    let constr = PseudoExpr::Constr {
        tag: 0,
        shape: ConstructorShape::unknown_data(0, 2),
        fields: vec![PseudoExpr::int(42), PseudoExpr::int(17)].into(),
        type_hint: None,
    };
    let expr = PseudoExpr::Let {
        name: "c1".into(),
        id: Some(c1_id),
        value: PBox::new(constr),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("c1", c1_id)),
            args: vec![PseudoExpr::Unit].into(),
        }),
    };
    let rewritten = strip_void_apply_on_constr(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!()
    };
    assert!(
        matches!(*body, PseudoExpr::Apply { .. }),
        "non-zero-arity Constr must not trigger strip"
    );
}
