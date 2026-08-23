use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;

fn entry_binder() -> Binder {
    Binder::new("entry", VarId::new(42))
}
fn evar() -> PseudoExpr {
    PseudoExpr::var_with_id("entry", VarId::new(42))
}
fn proj(sel: FieldSelector) -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: PBox::new(evar()),
        selector: sel,
    }
}
fn list_map(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "list.map".to_string(),
            id: None,
        }),
        args: vec![
            PseudoExpr::var_with_id("xs", VarId::new(1)),
            PseudoExpr::Lambda {
                params: vec![entry_binder()],
                body: PBox::new(body),
            },
        ]
        .into(),
    }
}
fn pair(a: PseudoExpr, b: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::PairNew,
        args: vec![a, b].into(),
    }
}

#[test]
fn identity_pair_map_collapses_to_xs() {
    let e = list_map(pair(
        proj(FieldSelector::PairFst),
        proj(FieldSelector::PairSnd),
    ));
    assert_eq!(
        fold_identity_pair_map(e),
        PseudoExpr::var_with_id("xs", VarId::new(1))
    );
}

#[test]
fn swapped_projection_is_not_identity() {
    // Pair(e.snd, e.fst) reorders → NOT the identity → unchanged.
    let e = list_map(pair(
        proj(FieldSelector::PairSnd),
        proj(FieldSelector::PairFst),
    ));
    assert_eq!(fold_identity_pair_map(e.clone()), e);
}

#[test]
fn different_var_not_folded() {
    // .fst/.snd on a var other than the lambda param → unchanged.
    let other = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::var_with_id("z", VarId::new(99))),
        selector: FieldSelector::PairFst,
    };
    let e = list_map(pair(other, proj(FieldSelector::PairSnd)));
    assert_eq!(fold_identity_pair_map(e.clone()), e);
}

#[test]
fn non_pair_body_not_folded() {
    // body isn't a Pair reconstruction → unchanged.
    let e = list_map(proj(FieldSelector::PairFst));
    assert_eq!(fold_identity_pair_map(e.clone()), e);
}
