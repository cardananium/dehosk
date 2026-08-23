use super::*;
use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// A Bool-producing `when key is { Some(b) -> b == True; _ -> False }`
/// (a comparison tail leaf makes it provably Bool).
fn bool_predicate_value() -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(var("key", 5)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(
                    KnownConstructor::Some,
                    vec![Binder::new("b".to_string(), VarId::new(60))],
                ),
                guard: None,
                body: PseudoExpr::BinOp {
                    op: crate::pseudo::ast::BinaryOp::Eq,
                    left: PBox::new(var("b", 60)),
                    right: PBox::new(PseudoExpr::Bool(true)),
                },
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Bool(false),
            },
        ],
    }
}

/// The church-residue outer `when ok is { tag1 -> True; tag0 -> recurse }`
/// — both arms NULLARY, however the printer labels them (None/Some(_)).
fn bool_when_over_ok() -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(var("ok", 10)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::False, vec![]),
                guard: None,
                body: var("tail", 80),
            },
        ],
    }
}

#[test]
fn recovers_if_when_subject_is_provably_bool() {
    let input = PseudoExpr::Let {
        name: "ok".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(bool_predicate_value()),
        body: PBox::new(bool_when_over_ok()),
    };
    let out = recover_if_from_bool_option_when(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let")
    };
    let body = body.into_inner();
    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = body
    else {
        panic!("expected If body, got {body:?}");
    };
    // condition is `ok`; tag1(True) -> THEN; tag0(False) -> ELSE
    assert!(
        matches!(condition.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == VarId::new(10))
    );
    assert_eq!(*then_branch, PseudoExpr::Bool(true), "tag1 body -> then");
    assert_eq!(*else_branch, var("tail", 80), "tag0 body -> else");
}

#[test]
fn recovers_if_for_inline_bool_subject() {
    // No `let` for the subject — the subject IS the inline Bool when. The
    // structural Bool witness must still fire.
    let input = PseudoExpr::When {
        subject: PBox::new(bool_predicate_value()),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::False, vec![]),
                guard: None,
                body: var("tail", 80),
            },
        ],
    };
    let out = recover_if_from_bool_option_when(input);
    let PseudoExpr::If { condition, .. } = out else {
        panic!("expected If, got {out:?}");
    };
    assert!(
        matches!(condition.as_ref(), PseudoExpr::When { .. }),
        "inline Bool subject becomes the if condition"
    );
}

#[test]
fn leaves_when_subject_not_provably_bool() {
    // value has no definite-Bool tail leaf (an opaque var) -> not Bool.
    let value = var("lookup_result", 1);
    let input = PseudoExpr::Let {
        name: "ok".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(value),
        body: PBox::new(bool_when_over_ok()),
    };
    let out = recover_if_from_bool_option_when(input.clone());
    assert_eq!(out, input, "non-provably-Bool subject must keep its when");
}

#[test]
fn leaves_mixed_bool_and_constructor_producer() {
    // `if c { a == b } else { Some(p) }` is Bool on one path, a constructor
    // on the other — NOT provably Bool. Must not convert.
    let value = PseudoExpr::If {
        condition: PBox::new(var("c", 1)),
        then_branch: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Eq,
            left: PBox::new(var("a", 2)),
            right: PBox::new(var("b", 3)),
        }),
        else_branch: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![var("p", 4)],
        )),
    };
    let input = PseudoExpr::Let {
        name: "ok".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(value),
        body: PBox::new(bool_when_over_ok()),
    };
    let out = recover_if_from_bool_option_when(input.clone());
    assert_eq!(
        out, input,
        "mixed Bool/constructor producer must not convert"
    );
}

#[test]
fn leaves_leading_wildcard_fail() {
    // `when ok is { _ -> fail; tag1 -> A; tag0 -> B }` is unconditionally
    // `fail` (first-match-wins). Dropping the leading wildcard would change
    // semantics — must not convert.
    let body = PseudoExpr::When {
        subject: PBox::new(var("ok", 10)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::False, vec![]),
                guard: None,
                body: var("tail", 80),
            },
        ],
    };
    let input = PseudoExpr::Let {
        name: "ok".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(bool_predicate_value()),
        body: PBox::new(body),
    };
    let out = recover_if_from_bool_option_when(input.clone());
    assert_eq!(out, input, "leading _ -> fail must block the rewrite");
}

#[test]
fn tolerates_trailing_wildcard_fail() {
    let mut when = bool_when_over_ok();
    if let PseudoExpr::When { clauses, .. } = &mut when {
        clauses.push(WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: PseudoExpr::Error { message: None },
        });
    }
    let input = PseudoExpr::Let {
        name: "ok".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(bool_predicate_value()),
        body: PBox::new(when),
    };
    let out = recover_if_from_bool_option_when(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let")
    };
    assert!(
        matches!(*body, PseudoExpr::If { .. }),
        "trailing _ -> fail should be dropped"
    );
}
