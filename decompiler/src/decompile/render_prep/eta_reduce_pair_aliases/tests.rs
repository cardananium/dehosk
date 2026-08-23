use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;
use crate::pseudo::var_id::VarId;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `Pair(fn(a, b) { p.fst(a, b) }, p.snd)` → `p`.
#[test]
fn rewrites_direct_eta() {
    let p_id = 100;
    let a_id = 1;
    let b_id = 2;
    let input = PseudoExpr::Pair(
        PBox::new(PseudoExpr::Lambda {
            params: vec![binder("a", a_id), binder("b", b_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::FieldAccess {
                    record: PBox::new(var("p", p_id)),
                    selector: FieldSelector::PairFst,
                }),
                args: vec![var("a", a_id), var("b", b_id)].into(),
            }),
        }),
        PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(var("p", p_id)),
            selector: FieldSelector::PairSnd,
        }),
    );
    let out = eta_reduce_pair_aliases(input);
    match out {
        PseudoExpr::Var { name, id } => {
            assert_eq!(name, "p");
            assert_eq!(id, Some(VarId::new(p_id)));
        }
        other => panic!("expected Var(p), got {:?}", other),
    }
}

/// Arg swap (`p.fst(b, a)` instead of `p.fst(a, b)`) — no rewrite.
#[test]
fn rejects_arg_swap() {
    let p_id = 100;
    let a_id = 1;
    let b_id = 2;
    let input = PseudoExpr::Pair(
        PBox::new(PseudoExpr::Lambda {
            params: vec![binder("a", a_id), binder("b", b_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::FieldAccess {
                    record: PBox::new(var("p", p_id)),
                    selector: FieldSelector::PairFst,
                }),
                // SWAPPED:
                args: vec![var("b", b_id), var("a", a_id)].into(),
            }),
        }),
        PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(var("p", p_id)),
            selector: FieldSelector::PairSnd,
        }),
    );
    let out = eta_reduce_pair_aliases(input.clone());
    assert_eq!(out, input);
}

/// Different `p` in .fst and .snd — no rewrite.
#[test]
fn rejects_different_pair_record() {
    let p1_id = 100;
    let p2_id = 200;
    let a_id = 1;
    let b_id = 2;
    let input = PseudoExpr::Pair(
        PBox::new(PseudoExpr::Lambda {
            params: vec![binder("a", a_id), binder("b", b_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::FieldAccess {
                    record: PBox::new(var("p1", p1_id)),
                    selector: FieldSelector::PairFst,
                }),
                args: vec![var("a", a_id), var("b", b_id)].into(),
            }),
        }),
        PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(var("p2", p2_id)),
            selector: FieldSelector::PairSnd,
        }),
    );
    let out = eta_reduce_pair_aliases(input.clone());
    assert_eq!(out, input);
}

/// Force wrapper around `p.fst` — peeled, rewrite proceeds.
#[test]
fn handles_force_wrapper() {
    let p_id = 100;
    let a_id = 1;
    let b_id = 2;
    let input = PseudoExpr::Pair(
        PBox::new(PseudoExpr::Lambda {
            params: vec![binder("a", a_id), binder("b", b_id)],
            body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::FieldAccess {
                    record: PBox::new(var("p", p_id)),
                    selector: FieldSelector::PairFst,
                }),
                args: vec![var("a", a_id), var("b", b_id)].into(),
            }))),
        }),
        PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(var("p", p_id)),
            selector: FieldSelector::PairSnd,
        }),
    );
    let out = eta_reduce_pair_aliases(input);
    assert!(matches!(out, PseudoExpr::Var { .. }));
}
