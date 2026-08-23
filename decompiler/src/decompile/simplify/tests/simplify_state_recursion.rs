use super::delayed_rec_force_expansion::{
    delayed_y_combinator_with_ids, force_twice, y_combinator_with_ids,
};
use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_simplify_state_carries_rec_vars_between_passes() {
    let rec_id = VarId::from_raw(29120);
    let learn_rec = PseudoExpr::Let {
        name: "recur".to_string(),
        id: Some(rec_id),
        value: PBox::new(y_combinator_with_ids(29121)),
        body: PBox::new(PseudoExpr::Unit),
    };

    let mut state = SimplifyState::default();
    let _ = simplify_with_state(learn_rec, None, false, None, &mut state);
    assert!(
        state.recursion.rec_vars.contains(rec_id),
        "first pass should harvest persistent rec_vars metadata"
    );

    let _ = simplify_with_state(PseudoExpr::Unit, None, false, None, &mut state);
    assert!(
        state.recursion.rec_vars.contains(rec_id),
        "later passes should seed and re-harvest persistent rec_vars metadata"
    );
}

#[test]
fn test_simplify_state_keeps_delayed_rec_vars_pass_local() {
    let delayed_id = VarId::from_raw(29130);
    let mut state = SimplifyState::default();

    let same_pass = simplify_with_state(
        PseudoExpr::Let {
            name: "f".to_string(),
            id: Some(delayed_id),
            value: PBox::new(delayed_y_combinator_with_ids(29131)),
            body: PBox::new(force_twice(PseudoExpr::var_with_id("f", delayed_id))),
        },
        None,
        false,
        None,
        &mut state,
    )
    .expr;
    assert_eq!(
        Simplifier::count_force_chain_uses_by_id(&same_pass, "f", Some(delayed_id), 2),
        0,
        "same-pass delayed-rec metadata should still unwrap force(force(f))"
    );

    let later_pass = simplify_with_state(
        force_twice(PseudoExpr::var_with_id("f", delayed_id)),
        None,
        false,
        None,
        &mut state,
    )
    .expr;
    assert_eq!(
        Simplifier::count_force_chain_uses_by_id(&later_pass, "f", Some(delayed_id), 2),
        1,
        "delayed_rec_vars must stay pass-local; a later pass without the let binding must not unwrap stale force(force(f))"
    );
}
