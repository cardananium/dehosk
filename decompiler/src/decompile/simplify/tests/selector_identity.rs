use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_selector_signature_rejects_same_name_foreign_body_id() {
    let param_id = VarId::new(710);
    let foreign_id = VarId::new(711);
    let params = vec![
        Binder::new("x", param_id),
        Binder::new("_", VarId::new(712)),
    ];

    assert_eq!(
        Simplifier::selector_signature(&params, &PseudoExpr::var_with_id("x", foreign_id)),
        None,
        "same-name foreign-id body ref must not classify as a selector over the lambda param"
    );
    assert_eq!(
        Simplifier::selector_signature(&params, &PseudoExpr::compat_var("x")),
        Some((2, 0)),
        "compat refs keep the legacy name fallback"
    );
}

#[test]
fn test_is_nth_selector_rejects_same_name_foreign_body_id() {
    let x_id = VarId::new(730);
    let y_id = VarId::new(731);
    let foreign_id = VarId::new(732);
    let selector = |body| PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id), Binder::new("y", y_id)],
        body: PBox::new(body),
    };

    assert_eq!(
        Simplifier::is_nth_selector(&selector(PseudoExpr::var_with_id("x", foreign_id)), 2),
        None,
        "same-name foreign-id body ref must not classify as an nth selector"
    );
    assert_eq!(
        Simplifier::is_nth_selector(&selector(PseudoExpr::var_with_id("x", x_id)), 2),
        Some(0)
    );
    assert_eq!(
        Simplifier::is_nth_selector(&selector(PseudoExpr::compat_var("x")), 2),
        Some(0),
        "compat refs keep the legacy name fallback"
    );
}

#[test]
fn test_selector_predicates_reject_same_name_foreign_body_id() {
    let x_id = VarId::new(713);
    let y_id = VarId::new(714);
    let foreign_id = VarId::new(715);

    let foreign_fst = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id), Binder::new("_", VarId::new(716))],
        body: PBox::new(PseudoExpr::var_with_id("x", foreign_id)),
    };
    assert!(
        !Simplifier::is_fst_selector(&foreign_fst),
        "same-name foreign body ref must not classify as fst selector"
    );

    let matching_fst = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id), Binder::new("_", VarId::new(717))],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    assert!(Simplifier::is_fst_selector(&matching_fst));

    let compat_fst = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id), Binder::new("_", VarId::new(718))],
        body: PBox::new(PseudoExpr::compat_var("x")),
    };
    assert!(
        Simplifier::is_fst_selector(&compat_fst),
        "compat body refs keep the legacy name fallback"
    );

    let foreign_snd = PseudoExpr::Lambda {
        params: vec![Binder::new("_", VarId::new(719)), Binder::new("y", y_id)],
        body: PBox::new(PseudoExpr::var_with_id("y", foreign_id)),
    };
    assert!(
        !Simplifier::is_snd_selector(&foreign_snd),
        "same-name foreign body ref must not classify as snd selector"
    );

    let matching_snd = PseudoExpr::Lambda {
        params: vec![Binder::new("_", VarId::new(722)), Binder::new("y", y_id)],
        body: PBox::new(PseudoExpr::var_with_id("y", y_id)),
    };
    assert!(Simplifier::is_snd_selector(&matching_snd));
}
