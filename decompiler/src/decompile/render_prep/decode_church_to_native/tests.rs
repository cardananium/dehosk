use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::var_id::VarId;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// The pass's `rewrite` core runs unconditionally; only the entry
/// point consults the ctx, so these tests call `rewrite` directly and
/// build a decode-on ctx for the one entry-point case.
fn decode_on() -> RenderCtx {
    RenderCtx::default().with_decode_church(true)
}

/// `fn(x) { x(a, b) }` → `Pair(a, b)`.
#[test]
fn rewrites_church_pair_pack_to_pair() {
    let a = PseudoExpr::int(1);
    let b = PseudoExpr::int(2);
    let x = binder("x", 100);
    let expr = PseudoExpr::Lambda {
        params: vec![x],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("x", 100)),
            args: vec![a.clone(), b.clone()].into(),
        }),
    };
    let out = rewrite(expr, &mut ChurchLetComments::default());
    match out {
        PseudoExpr::Pair(p_a, p_b) => {
            assert_eq!(*p_a, a);
            assert_eq!(*p_b, b);
        }
        _ => panic!("expected Pair, got {:?}", out),
    }
}

/// `fn(t, _) { t }` → `True`.
#[test]
fn rewrites_church_true_to_bool_true() {
    let t = binder("t", 100);
    let f = binder("_", 101);
    let expr = PseudoExpr::Lambda {
        params: vec![t, f],
        body: PBox::new(varref("t", 100)),
    };
    let out = rewrite(expr, &mut ChurchLetComments::default());
    assert_eq!(out, PseudoExpr::Bool(true));
}

/// `fn(_, f) { f }` → `False`.
#[test]
fn rewrites_church_false_to_bool_false() {
    let t = binder("_", 100);
    let f = binder("f", 101);
    let expr = PseudoExpr::Lambda {
        params: vec![t, f],
        body: PBox::new(varref("f", 101)),
    };
    let out = rewrite(expr, &mut ChurchLetComments::default());
    assert_eq!(out, PseudoExpr::Bool(false));
}

/// `fn(x) { x(a, b, c) }` (arity 3) → `(a, b, c)` (Tuple).
#[test]
fn rewrites_church_pack_3_to_tuple() {
    let x = binder("x", 100);
    let args = vec![PseudoExpr::int(1), PseudoExpr::int(2), PseudoExpr::int(3)];
    let expr = PseudoExpr::Lambda {
        params: vec![x],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("x", 100)),
            args: (args.clone()).into(),
        }),
    };
    let out = rewrite(expr, &mut ChurchLetComments::default());
    match out {
        PseudoExpr::Tuple(items) => assert_eq!(items, args.into()),
        _ => panic!("expected Tuple, got {:?}", out),
    }
}

/// `fn(_, k) { k(h, t) }` → `[h, ..t]` (church-cons).
#[test]
fn rewrites_church_cons_to_list() {
    let n = binder("_", 100);
    let k = binder("k", 101);
    let h = PseudoExpr::int(42);
    let t = varref("tail", 200);
    let expr = PseudoExpr::Lambda {
        params: vec![n, k],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("k", 101)),
            args: vec![h.clone(), t.clone()].into(),
        }),
    };
    let out = rewrite(expr, &mut ChurchLetComments::default());
    match out {
        PseudoExpr::List { elements, tail } => {
            assert_eq!(elements, vec![h].into());
            assert_eq!(tail.as_deref(), Some(&t));
        }
        _ => panic!("expected List, got {:?}", out),
    }
}

/// `fn(y) { y(a, b) }` where the body's Var id ≠ params[0].id is NOT
/// rewritten — the inner Var must reference the bound param.
#[test]
fn does_not_rewrite_when_var_id_mismatches() {
    let x = binder("x", 100);
    let expr = PseudoExpr::Lambda {
        params: vec![x],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("y", 999)), // different id
            args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
        }),
    };
    let out = decode_church_to_native(
        expr.clone(),
        &decode_on(),
        &mut ChurchLetComments::default(),
    );
    assert_eq!(out, expr);
}
