use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};

fn nil_val() -> PseudoExpr {
    PseudoExpr::constr(ConstructorShape::Known(KnownConstructor::Nil), vec![])
}
fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}
fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::Var {
        name: name.to_string(),
        id: Some(VarId::new(id)),
    }
}

/// `rec fn f(x) { when x is { [] -> Nil; [_, ..t] -> if true { f(t) }
/// else { false } } }` — a Bool `all`-predicate. The `[] -> Nil` is
/// church_true → must become `True`.
fn bool_predicate_fn(self_id: u32) -> PseudoExpr {
    let cons_body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(true)),
        then_branch: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("f", self_id)),
            args: vec![var("t", 3)].into(),
        }),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    PseudoExpr::RecFn {
        name: binder("f", self_id),
        params: vec![binder("x", 2)],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("x", 2)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    guard: None,
                    body: nil_val(),
                },
                WhenClause {
                    pattern: WhenPattern::List {
                        elements: vec![binder("_", 4)],
                        tail: Some(binder("t", 3)),
                    },
                    guard: None,
                    body: cons_body,
                },
            ],
        }),
    }
}

#[test]
fn relabels_nil_in_bool_predicate_under_inverse_cip() {
    let ctx = RenderCtx::default().with_church_polarity(ChurchPolarity::InverseCip);
    let out = recover_inverse_cip_nil_as_true(bool_predicate_fn(1), &ctx);
    // The `[] -> Nil` arm must now be `True`.
    let PseudoExpr::RecFn { body, .. } = out else {
        panic!("expected RecFn")
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected When")
    };
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::Constr {
                shape: ConstructorShape::Known(KnownConstructor::True),
                ..
            }
        ),
        "nil arm should be relabelled to True, got {:?}",
        clauses[0].body
    );
}

#[test]
fn no_op_under_cip() {
    let ctx = RenderCtx::default().with_church_polarity(ChurchPolarity::Cip);
    let out = recover_inverse_cip_nil_as_true(bool_predicate_fn(1), &ctx);
    let PseudoExpr::RecFn { body, .. } = out else {
        panic!("expected RecFn")
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected When")
    };
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::Constr {
                shape: ConstructorShape::Known(KnownConstructor::Nil),
                ..
            }
        ),
        "under CIP the Nil must be untouched"
    );
}

/// A genuine list-map fold `{ [] -> Nil; [h, ..t] -> [h, ..g(t)] }` must
/// NOT be relabelled (its cons arm is a List cell → vetoed).
#[test]
fn leaves_genuine_list_fold_alone() {
    let ctx = RenderCtx::default().with_church_polarity(ChurchPolarity::InverseCip);
    let list_fold = PseudoExpr::RecFn {
        name: binder("g", 1),
        params: vec![binder("x", 2)],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("x", 2)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    guard: None,
                    body: nil_val(),
                },
                WhenClause {
                    pattern: WhenPattern::List {
                        elements: vec![binder("h", 4)],
                        tail: Some(binder("t", 3)),
                    },
                    guard: None,
                    body: PseudoExpr::List {
                        elements: vec![var("h", 4)].into(),
                        tail: Some(PBox::new(PseudoExpr::Apply {
                            function: PBox::new(var("g", 1)),
                            args: vec![var("t", 3)].into(),
                        })),
                    },
                },
            ],
        }),
    };
    let out = recover_inverse_cip_nil_as_true(list_fold, &ctx);
    let PseudoExpr::RecFn { body, .. } = out else {
        panic!("expected RecFn")
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected When")
    };
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::Constr {
                shape: ConstructorShape::Known(KnownConstructor::Nil),
                ..
            }
        ),
        "a genuine list fold's Nil must be left alone"
    );
}
