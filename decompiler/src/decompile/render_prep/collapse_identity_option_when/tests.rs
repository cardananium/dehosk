use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}
fn some_pat(binder_id: u32) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: vec![Binder::new("p", VarId::new(binder_id))],
        shape: ConstructorShape::Known(KnownConstructor::Some),
    }
}
fn none_pat() -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: vec![],
        shape: ConstructorShape::Known(KnownConstructor::None),
    }
}
fn some_ctor(inner: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Constr {
        tag: 0,
        shape: ConstructorShape::Known(KnownConstructor::Some),
        fields: vec![inner].into(),
        type_hint: None,
    }
}
fn none_ctor() -> PseudoExpr {
    PseudoExpr::Constr {
        tag: 0,
        shape: ConstructorShape::Known(KnownConstructor::None),
        fields: vec![].into(),
        type_hint: None,
    }
}
fn when(subject: PseudoExpr, clauses: Vec<(WhenPattern, PseudoExpr)>) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: clauses
            .into_iter()
            .map(|(pattern, body)| WhenClause {
                pattern,
                guard: None,
                body,
            })
            .collect(),
    }
}

#[test]
fn identity_option_collapses_to_subject() {
    let e = when(
        var("x", 1),
        vec![
            (some_pat(7), some_ctor(var("p", 7))),
            (none_pat(), none_ctor()),
        ],
    );
    assert_eq!(collapse_identity_option_when(e), var("x", 1));
}

#[test]
fn both_none_folds_to_none() {
    let e = when(
        var("x", 1),
        vec![(some_pat(7), none_ctor()), (none_pat(), none_ctor())],
    );
    assert_eq!(collapse_identity_option_when(e), none_ctor());
}

#[test]
fn leading_wildcard_not_collapsed() {
    // `_ -> W` first shadows the Some/None arms → must NOT collapse to X.
    let e = when(
        var("x", 1),
        vec![
            (WhenPattern::Wildcard, var("w", 5)),
            (some_pat(7), some_ctor(var("p", 7))),
            (none_pat(), none_ctor()),
        ],
    );
    assert!(matches!(
        collapse_identity_option_when(e),
        PseudoExpr::When { .. }
    ));
}

#[test]
fn impure_subject_both_none_not_folded() {
    // both-None over an IMPURE subject must NOT drop the subject's evaluation.
    let impure = PseudoExpr::Apply {
        function: PBox::new(var("effectful", 3)),
        args: vec![var("z", 4)].into(),
    };
    let e = when(
        impure,
        vec![(some_pat(7), none_ctor()), (none_pat(), none_ctor())],
    );
    assert!(matches!(
        collapse_identity_option_when(e),
        PseudoExpr::When { .. }
    ));
}

#[test]
fn identity_collapse_ok_with_impure_subject() {
    // Identity RETURNS the subject, so its evaluation is preserved → fine.
    let impure = PseudoExpr::Apply {
        function: PBox::new(var("f", 3)),
        args: vec![var("z", 4)].into(),
    };
    let e = when(
        impure.clone(),
        vec![
            (some_pat(7), some_ctor(var("p", 7))),
            (none_pat(), none_ctor()),
        ],
    );
    assert_eq!(collapse_identity_option_when(e), impure);
}

#[test]
fn some_of_other_var_not_collapsed() {
    // `Some(p) -> Some(q)` (q != p) is not the identity → unchanged.
    let e = when(
        var("x", 1),
        vec![
            (some_pat(7), some_ctor(var("q", 8))),
            (none_pat(), none_ctor()),
        ],
    );
    assert!(matches!(
        collapse_identity_option_when(e),
        PseudoExpr::When { .. }
    ));
}

#[test]
fn some_field_access_not_collapsed() {
    // `Some(payload) -> Some(payload.snd)` is a real projection → unchanged.
    let proj = PseudoExpr::FieldAccess {
        record: PBox::new(var("p", 7)),
        selector: crate::pseudo::field_selector::FieldSelector::PairSnd,
    };
    let e = when(
        var("x", 1),
        vec![(some_pat(7), some_ctor(proj)), (none_pat(), none_ctor())],
    );
    assert!(matches!(
        collapse_identity_option_when(e),
        PseudoExpr::When { .. }
    ));
}
