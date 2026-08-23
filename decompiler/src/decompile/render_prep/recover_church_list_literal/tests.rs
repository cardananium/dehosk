use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PVec;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

fn cons_helper_let(cons_id: VarId, body: PseudoExpr) -> PseudoExpr {
    // `let cons = fn(h, t, _, k) { k(h, t) } in body`.
    let h_id = VarId::new(9000);
    let t_id = VarId::new(9001);
    let dead_id = VarId::new(9002);
    let k_id = VarId::new(9003);
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("h", h_id),
            Binder::new("t", t_id),
            Binder::new("_", dead_id),
            Binder::new("k", k_id),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
            args: vec![
                PseudoExpr::var_with_id("h", h_id),
                PseudoExpr::var_with_id("t", t_id),
            ]
            .into(),
        }),
    };
    PseudoExpr::Let {
        name: "cons".into(),
        id: Some(cons_id),
        value: PBox::new(lambda),
        body: PBox::new(body),
    }
}

fn nil_value() -> PseudoExpr {
    // Nullary constructor — looks like Nil.
    PseudoExpr::Constr {
        tag: 0,
        shape: ConstructorShape::unknown_data(0, 0),
        fields: PVec::new(),
        type_hint: None,
    }
}

#[test]
fn recovers_3_element_list_chain_with_nil_terminator() {
    // `cons(1, cons(2, cons(3, NIL)))` → `[1, 2, 3]`.
    let cons_id = VarId::new(9100);
    let make_call = |head: PseudoExpr, tail: PseudoExpr| PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("cons", cons_id)),
        args: vec![head, tail].into(),
    };
    let chain = make_call(
        PseudoExpr::int(1),
        make_call(
            PseudoExpr::int(2),
            make_call(PseudoExpr::int(3), nil_value()),
        ),
    );
    let expr = cons_helper_let(cons_id, chain);

    let rewritten = recover_church_list_literals(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!("expected outer Let, got something else");
    };
    let body = body.into_inner();
    let PseudoExpr::List { elements, tail } = body else {
        panic!("expected List body, got {:?}", body);
    };
    assert_eq!(elements.len(), 3);
    assert!(tail.is_none(), "Nil terminator should be dropped");
    for (i, el) in elements.iter().enumerate() {
        let PseudoExpr::Int(n) = el else {
            panic!("expected Int element, got {:?}", el);
        };
        assert_eq!(*n, ((i + 1) as i64).into());
    }
}

#[test]
fn recovers_chain_with_non_nil_tail() {
    // `cons(1, cons(2, tail_var))` → `[1, 2 | tail_var]`.
    let cons_id = VarId::new(9200);
    let tail_id = VarId::new(9201);
    let make_call = |head: PseudoExpr, t: PseudoExpr| PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("cons", cons_id)),
        args: vec![head, t].into(),
    };
    let chain = make_call(
        PseudoExpr::int(1),
        make_call(
            PseudoExpr::int(2),
            PseudoExpr::var_with_id("tail_var", tail_id),
        ),
    );
    let expr = cons_helper_let(cons_id, chain);

    let rewritten = recover_church_list_literals(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!()
    };
    let body = body.into_inner();
    let PseudoExpr::List { elements, tail } = body else {
        panic!("expected List, got {:?}", body)
    };
    assert_eq!(elements.len(), 2);
    let tail = tail.expect("non-nil tail expected");
    let PseudoExpr::Var { id: Some(id), .. } = *tail else {
        panic!()
    };
    assert_eq!(id, tail_id);
}

#[test]
fn does_not_collapse_single_cons() {
    // A single `cons(1, NIL)` is left alone: the threshold is
    // chain depth >= 2, avoiding noise on trivial cases.
    let cons_id = VarId::new(9300);
    let single = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("cons", cons_id)),
        args: vec![PseudoExpr::int(42), nil_value()].into(),
    };
    let expr = cons_helper_let(cons_id, single);

    let rewritten = recover_church_list_literals(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!()
    };
    // Body should remain an Apply (no rewrite).
    assert!(
        matches!(*body, PseudoExpr::Apply { .. }),
        "single cons must not collapse, got {:?}",
        body
    );
}

#[test]
fn does_not_collapse_when_head_is_impure() {
    // If any head in the chain is an impure expression (Apply / Builtin),
    // refuse — the rewrite would change evaluation order.
    let cons_id = VarId::new(9400);
    let impure_head = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("compute_head")),
        args: vec![PseudoExpr::int(0)].into(),
    };
    let make_call = |h: PseudoExpr, t: PseudoExpr| PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("cons", cons_id)),
        args: vec![h, t].into(),
    };
    let chain = make_call(impure_head, make_call(PseudoExpr::int(2), nil_value()));
    let expr = cons_helper_let(cons_id, chain);

    let rewritten = recover_church_list_literals(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!()
    };
    assert!(
        matches!(*body, PseudoExpr::Apply { .. }),
        "impure head must prevent collapse, got {:?}",
        body
    );
}

#[test]
fn does_not_match_helper_with_wrong_shape() {
    // A let-bound helper with the WRONG shape (not church-cons)
    // — e.g., 3 params instead of 4 — must not be collected.
    let helper_id = VarId::new(9500);
    let h_id = VarId::new(9501);
    let t_id = VarId::new(9502);
    let k_id = VarId::new(9503);
    let wrong_lambda = PseudoExpr::Lambda {
        // 3 params, no dead slot — not the Cons shape.
        params: vec![
            Binder::new("h", h_id),
            Binder::new("t", t_id),
            Binder::new("k", k_id),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("k", k_id)),
            args: vec![
                PseudoExpr::var_with_id("h", h_id),
                PseudoExpr::var_with_id("t", t_id),
            ]
            .into(),
        }),
    };
    let chain = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("h_wrong", helper_id)),
        args: vec![
            PseudoExpr::int(1),
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("h_wrong", helper_id)),
                args: vec![PseudoExpr::int(2), nil_value()].into(),
            },
        ]
        .into(),
    };
    let expr = PseudoExpr::Let {
        name: "h_wrong".into(),
        id: Some(helper_id),
        value: PBox::new(wrong_lambda),
        body: PBox::new(chain),
    };

    let rewritten = recover_church_list_literals(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!()
    };
    // Helper not recognized → chain stays as nested Apply.
    assert!(
        matches!(*body, PseudoExpr::Apply { .. }),
        "wrong helper shape must not trigger list recovery, got {:?}",
        body
    );
}

#[test]
fn recovers_chain_when_helper_apply_is_force_wrapped() {
    // A thunked church-cons helper appears at call sites as
    // `Apply { function: Force(Var(cons)), args: [head, tail] }`; the
    // matcher must peel through Force and still recover the literal.
    let cons_id = VarId::new(9600);
    let inner_h_id = VarId::new(9610);
    let inner_t_id = VarId::new(9611);
    let inner_dead_id = VarId::new(9612);
    let inner_k_id = VarId::new(9613);
    // Helper definition `let cons = fn(h, t, _, k) { force(k)(h, t) }` —
    // the Force wraps `k` in the BODY too, mirroring the call sites.
    let force_wrapped_body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id(
            "k", inner_k_id,
        )))),
        args: vec![
            PseudoExpr::var_with_id("h", inner_h_id),
            PseudoExpr::var_with_id("t", inner_t_id),
        ]
        .into(),
    };
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("h", inner_h_id),
            Binder::new("t", inner_t_id),
            Binder::new("_", inner_dead_id),
            Binder::new("k", inner_k_id),
        ],
        body: PBox::new(force_wrapped_body),
    };
    // Chain call sites: `Apply { function: Force(Var(cons)), args }`
    let make_call = |head: PseudoExpr, tail: PseudoExpr| PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id(
            "cons", cons_id,
        )))),
        args: vec![head, tail].into(),
    };
    let chain = make_call(
        PseudoExpr::int(7),
        make_call(
            PseudoExpr::int(8),
            make_call(PseudoExpr::int(9), nil_value()),
        ),
    );
    let expr = PseudoExpr::Let {
        name: "cons".into(),
        id: Some(cons_id),
        value: PBox::new(lambda),
        body: PBox::new(chain),
    };
    let rewritten = recover_church_list_literals(expr);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!()
    };
    let body = body.into_inner();
    let PseudoExpr::List { elements, tail } = body else {
        panic!("expected List body via Force-peel, got {:?}", body)
    };
    assert_eq!(elements.len(), 3);
    assert!(tail.is_none());
}
