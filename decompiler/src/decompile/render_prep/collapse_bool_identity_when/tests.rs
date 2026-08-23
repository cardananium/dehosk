use super::*;
use crate::pseudo::ast::PVec;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

fn true_pat() -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 1,
        fields: Vec::new(),
        shape: ConstructorShape::Known(KnownConstructor::True),
    }
}

fn false_pat() -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: Vec::new(),
        shape: ConstructorShape::Known(KnownConstructor::False),
    }
}

fn true_ctor() -> PseudoExpr {
    PseudoExpr::Constr {
        tag: 1,
        shape: ConstructorShape::Known(KnownConstructor::True),
        fields: PVec::new(),
        type_hint: None,
    }
}

fn false_ctor() -> PseudoExpr {
    PseudoExpr::Constr {
        tag: 0,
        shape: ConstructorShape::Known(KnownConstructor::False),
        fields: PVec::new(),
        type_hint: None,
    }
}

#[test]
fn collapses_canonical_bool_identity_pattern_with_fail_arm() {
    // `when x is { True -> True; False -> False; _ -> fail }` -> `x`.
    let x_id = VarId::new(5000);
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(true_pat(), true_ctor()),
            WhenClause::new(false_pat(), false_ctor()),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
        ],
    };

    let rewritten = collapse_bool_identity_when(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::Var { id: Some(id), .. } if id == x_id),
        "should collapse to `x` (the subject), got {:?}",
        rewritten
    );
}

#[test]
fn collapses_without_fail_arm() {
    // `when x is { True -> True; False -> False }` (exhaustive without
    // fallback) -> `x`.
    let x_id = VarId::new(5001);
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(true_pat(), true_ctor()),
            WhenClause::new(false_pat(), false_ctor()),
        ],
    };

    let rewritten = collapse_bool_identity_when(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::Var { id: Some(id), .. } if id == x_id),
        "should collapse without fail arm, got {:?}",
        rewritten
    );
}

#[test]
fn collapses_with_literal_bool_arm_bodies() {
    // `when x is { True -> PseudoExpr::Bool(true); ... }` -> `x`.
    let x_id = VarId::new(5002);
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(true_pat(), PseudoExpr::bool(true)),
            WhenClause::new(false_pat(), PseudoExpr::bool(false)),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
        ],
    };

    let rewritten = collapse_bool_identity_when(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::Var { id: Some(id), .. } if id == x_id),
        "should accept Bool literal bodies, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_collapse_when_arm_body_differs() {
    // `when x is { True -> False; False -> True }` is NOT identity
    // (it's negation). Must NOT collapse.
    let x_id = VarId::new(5003);
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(true_pat(), false_ctor()),
            WhenClause::new(false_pat(), true_ctor()),
        ],
    };

    let rewritten = collapse_bool_identity_when(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::When { .. }),
        "non-identity match must NOT collapse, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_collapse_when_subject_is_complex() {
    // Subject must be a Var (so the rewrite preserves evaluation
    // order). A FieldAccess subject is left in the When form.
    let x_id = VarId::new(5004);
    use crate::pseudo::field_selector::FieldSelector;
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("x", x_id)),
            selector: FieldSelector::NamedField("flag".to_string()),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause::new(true_pat(), true_ctor()),
            WhenClause::new(false_pat(), false_ctor()),
        ],
    };

    let rewritten = collapse_bool_identity_when(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::When { .. }),
        "non-Var subject must NOT collapse, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_collapse_when_only_one_bool_arm() {
    // `when x is { True -> True; _ -> fail }` is missing the False
    // arm — not exhaustive Bool identity, must NOT collapse.
    let x_id = VarId::new(5005);
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(true_pat(), true_ctor()),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
        ],
    };

    let rewritten = collapse_bool_identity_when(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::When { .. }),
        "incomplete Bool match must NOT collapse, got {:?}",
        rewritten
    );
}

#[test]
fn does_not_collapse_when_guard_present() {
    // Guards are out of scope.
    let x_id = VarId::new(5006);
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: true_pat(),
                guard: Some(PseudoExpr::bool(true)),
                body: true_ctor(),
            },
            WhenClause::new(false_pat(), false_ctor()),
        ],
    };

    let rewritten = collapse_bool_identity_when(when_expr);
    assert!(
        matches!(rewritten, PseudoExpr::When { .. }),
        "guarded When must NOT collapse, got {:?}",
        rewritten
    );
}
