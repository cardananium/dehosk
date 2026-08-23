use super::*;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

fn cons(head: PseudoExpr, tail: PseudoExpr) -> PseudoExpr {
    PseudoExpr::constr(ConstructorShape::unknown_data(1, 2), vec![head, tail])
}

fn pair(a: PseudoExpr, b: PseudoExpr) -> PseudoExpr {
    // The Unknown_E_2_0 (enum, list) pair: tag 0, arity 2 — must never fold.
    PseudoExpr::constr(ConstructorShape::unknown_data(0, 2), vec![a, b])
}

fn nil() -> PseudoExpr {
    PseudoExpr::constr_known(crate::pseudo::constructor::KnownConstructor::Nil, vec![])
}

fn stub_nil() -> PseudoExpr {
    // A generic nullary stub — NOT a genuine list terminator.
    PseudoExpr::constr(ConstructorShape::unknown_data(0, 0), vec![])
}

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn int(n: i64) -> PseudoExpr {
    PseudoExpr::int(n)
}

/// `const k = [0]; Constr<1>(30, k)` -> `[30, ..k]`.
#[test]
fn cons_onto_list_const_becomes_spread() {
    let k = PseudoExpr::List {
        elements: vec![int(0)].into(),
        tail: None,
    };
    let body = cons(int(30), varref("k", 1));
    let input = PseudoExpr::let_bind_with_id("k", VarId::new(1), k, body);

    let out = recover_constr_cons_spread(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected let");
    };
    match body.into_inner() {
        PseudoExpr::List { elements, tail } => {
            assert_eq!(elements.len(), 1);
            assert_eq!(elements[0], int(30));
            match tail.as_deref() {
                Some(PseudoExpr::Var { name, .. }) => assert_eq!(name, "k"),
                other => panic!("expected spread tail Var(k), got {other:?}"),
            }
        }
        other => panic!("expected List spread, got {other:?}"),
    }
}

/// The `Unknown_E_2_0(enum, list)` PAIR (tag 0, arity 2) must be left alone
/// even though its second field is a list.
#[test]
fn pair_at_tag0_is_never_folded() {
    let input = pair(
        varref("enum", 5),
        PseudoExpr::List {
            elements: vec![int(1)].into(),
            tail: None,
        },
    );
    let out = recover_constr_cons_spread(input.clone());
    assert_eq!(out, input, "the (enum, list) pair must not fold");
}

/// A cons cell whose tail is opaque (no binding, not a list) stays a stub.
#[test]
fn cons_onto_opaque_var_stays_stub() {
    let input = cons(int(30), varref("opaque", 9));
    let out = recover_constr_cons_spread(input.clone());
    assert_eq!(
        out, input,
        "opaque tail is not provably a list — leave stub"
    );
}

/// A tail bound to a non-list value (a pair) is NOT provably a list.
#[test]
fn cons_onto_nonlist_const_stays_stub() {
    let value = pair(varref("a", 2), varref("b", 3));
    let body = cons(int(30), varref("p", 1));
    let input = PseudoExpr::let_bind_with_id("p", VarId::new(1), value, body);

    let out = recover_constr_cons_spread(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected let");
    };
    // body must still be the stub cons Constr, not a List
    assert!(
        matches!(*body, PseudoExpr::Constr { tag: 1, .. }),
        "non-list tail must leave the stub cons untouched"
    );
}

/// A cons cell whose tail resolves to a bare nullary STUB (`Unknown_E_0_0`,
/// not the genuine `Known(Nil)`) is left alone — the stub's surface is not
/// `[]`, so folding would just make a spread with a stub tail.
#[test]
fn cons_onto_stub_nil_const_stays_stub() {
    let body = cons(int(30), varref("e", 1));
    let input = PseudoExpr::let_bind_with_id("e", VarId::new(1), stub_nil(), body);

    let out = recover_constr_cons_spread(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected let");
    };
    assert!(
        matches!(*body, PseudoExpr::Constr { tag: 1, .. }),
        "a bare nullary stub tail must not be treated as a list terminator"
    );
}

/// Inline cons chain terminating in nil collapses fully to `[a, b]`.
#[test]
fn inline_chain_to_nil_collapses() {
    let input = cons(int(1), cons(int(2), nil()));
    let out = recover_constr_cons_spread(input);
    match out {
        PseudoExpr::List { elements, tail } => {
            assert_eq!(elements, vec![int(1), int(2)].into());
            assert!(tail.is_none());
        }
        other => panic!("expected [1, 2], got {other:?}"),
    }
}

/// Inline cons chain terminating in a list-const tail becomes a chained spread.
/// `Constr<1>(1, Constr<1>(2, l))` with `const l = [9]` -> `[1, 2, ..l]`.
#[test]
fn inline_chain_onto_const_becomes_spread() {
    let l = PseudoExpr::List {
        elements: vec![int(9)].into(),
        tail: None,
    };
    let body = cons(int(1), cons(int(2), varref("l", 1)));
    let input = PseudoExpr::let_bind_with_id("l", VarId::new(1), l, body);

    let out = recover_constr_cons_spread(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected let");
    };
    match body.into_inner() {
        PseudoExpr::List { elements, tail } => {
            assert_eq!(elements, vec![int(1), int(2)].into());
            match tail.as_deref() {
                Some(PseudoExpr::Var { name, .. }) => assert_eq!(name, "l"),
                other => panic!("expected tail Var(l), got {other:?}"),
            }
        }
        other => panic!("expected [1, 2, ..l], got {other:?}"),
    }
}

/// Transitive const chain: `const a = [0]; const b = a; Constr<1>(7, b)`
/// -> `[7, ..b]` (b resolves through a to a list).
#[test]
fn transitive_const_chain_resolves() {
    let a = PseudoExpr::List {
        elements: vec![int(0)].into(),
        tail: None,
    };
    let inner_body = cons(int(7), varref("b", 2));
    let b_let = PseudoExpr::let_bind_with_id("b", VarId::new(2), varref("a", 1), inner_body);
    let input = PseudoExpr::let_bind_with_id("a", VarId::new(1), a, b_let);

    let out = recover_constr_cons_spread(input);
    // dig to the innermost body
    let PseudoExpr::Let { body, .. } = out else {
        panic!("outer let");
    };
    let PseudoExpr::Let { body, .. } = body.into_inner() else {
        panic!("inner let");
    };
    assert!(
        matches!(*body, PseudoExpr::List { tail: Some(_), .. }),
        "transitive list const should yield a spread"
    );
}
