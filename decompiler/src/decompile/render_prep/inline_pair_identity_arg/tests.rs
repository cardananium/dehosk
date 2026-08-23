use super::*;
use crate::pseudo::ast::Binder;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn identity_lambda(param_name: &str, param_id: u32) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder(param_name, param_id)],
        body: PBox::new(varref(param_name, param_id)),
    }
}

/// Hoisted pair_pack call → recognized.
#[test]
fn classifier_recognizes_hoisted_pair_pack_with_identity_snd() {
    let value = PseudoExpr::Apply {
        function: PBox::new(varref("pair_pack", 50)),
        args: vec![varref("composer", 60), identity_lambda("x", 100)].into(),
    };
    let slots = classify_pair_let_value(&value).unwrap();
    assert!(!slots.fst);
    assert!(slots.snd);
}

/// Inline church-pair-pack with identity at .fst.
#[test]
fn classifier_recognizes_inline_church_pair_pack_with_identity_fst() {
    // Lambda{[x], Apply{Var(x), [identity_lambda, composer]}}
    let x_id = 200;
    let value = PseudoExpr::Lambda {
        params: vec![binder("x", x_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("x", x_id)),
            args: vec![identity_lambda("inner", 100), varref("composer", 60)].into(),
        }),
    };
    let slots = classify_pair_let_value(&value).unwrap();
    assert!(slots.fst);
    assert!(!slots.snd);
}

/// Native Pair(_, identity) → recognized.
#[test]
fn classifier_recognizes_native_pair() {
    let value = PseudoExpr::Pair(
        PBox::new(varref("composer", 60)),
        PBox::new(identity_lambda("x", 100)),
    );
    let slots = classify_pair_let_value(&value).unwrap();
    assert!(!slots.fst);
    assert!(slots.snd);
}

/// Identity-lambda body Var has WRONG id → not an identity.
#[test]
fn classifier_rejects_lambda_with_mismatched_var_id() {
    let bad_identity = PseudoExpr::Lambda {
        params: vec![binder("x", 100)],
        body: PBox::new(varref("y", 999)),
    };
    let value = PseudoExpr::Pair(PBox::new(varref("composer", 60)), PBox::new(bad_identity));
    assert!(classify_pair_let_value(&value).is_none());
}

/// Pair with NO identity in either slot → not recognized.
#[test]
fn classifier_rejects_pair_with_no_identity_slot() {
    let value = PseudoExpr::Pair(PBox::new(varref("a", 60)), PBox::new(varref("b", 61)));
    assert!(classify_pair_let_value(&value).is_none());
}

/// End-to-end: hoisted pair_pack + .snd(arg) call → collapsed to arg.
#[test]
fn rewrites_pair_snd_apply_to_arg() {
    let binder_id = VarId::new(500);
    let pair_value = PseudoExpr::Apply {
        function: PBox::new(varref("pair_pack", 50)),
        args: vec![varref("composer", 60), identity_lambda("x", 100)].into(),
    };
    let use_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(varref("p", 500)),
            selector: FieldSelector::PairSnd,
        }),
        args: vec![PseudoExpr::int(42)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "p".into(),
        id: Some(binder_id),
        value: PBox::new(pair_value),
        body: PBox::new(use_site),
    };
    let out = inline_pair_identity_arg(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!()
    };
    assert_eq!(*body, PseudoExpr::int(42));
}

/// .fst access with identity at .snd → unchanged (wrong slot).
#[test]
fn does_not_rewrite_wrong_slot() {
    let binder_id = VarId::new(500);
    let pair_value = PseudoExpr::Pair(
        PBox::new(varref("composer", 60)),
        PBox::new(identity_lambda("x", 100)),
    );
    let use_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(varref("p", 500)),
            selector: FieldSelector::PairFst,
        }),
        args: vec![PseudoExpr::int(42)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "p".into(),
        id: Some(binder_id),
        value: PBox::new(pair_value.clone()),
        body: PBox::new(use_site.clone()),
    };
    let out = inline_pair_identity_arg(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!()
    };
    assert_eq!(*body, use_site);
}

/// Bare selector (no Apply) → unchanged.
#[test]
fn does_not_rewrite_bare_selector() {
    let binder_id = VarId::new(500);
    let pair_value = PseudoExpr::Pair(
        PBox::new(varref("composer", 60)),
        PBox::new(identity_lambda("x", 100)),
    );
    let use_site = PseudoExpr::FieldAccess {
        record: PBox::new(varref("p", 500)),
        selector: FieldSelector::PairSnd,
    };
    let expr = PseudoExpr::Let {
        name: "p".into(),
        id: Some(binder_id),
        value: PBox::new(pair_value),
        body: PBox::new(use_site.clone()),
    };
    let out = inline_pair_identity_arg(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!()
    };
    assert_eq!(*body, use_site);
}

/// Multi-arg call `p.snd(a, b)` → unchanged (identity expects 1 arg).
#[test]
fn does_not_rewrite_multi_arg_call() {
    let binder_id = VarId::new(500);
    let pair_value = PseudoExpr::Pair(
        PBox::new(varref("composer", 60)),
        PBox::new(identity_lambda("x", 100)),
    );
    let use_site = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(varref("p", 500)),
            selector: FieldSelector::PairSnd,
        }),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "p".into(),
        id: Some(binder_id),
        value: PBox::new(pair_value),
        body: PBox::new(use_site.clone()),
    };
    let out = inline_pair_identity_arg(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!()
    };
    assert_eq!(*body, use_site);
}
