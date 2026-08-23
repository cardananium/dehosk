use super::*;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

/// D1 positive: `expect!.fst` (bare helper, id:None) → `fail`.
#[test]
fn d1_rewrites_bare_expect_dot_fst() {
    let input = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Var {
            name: "expect!".to_string(),
            id: None,
        }),
        selector: FieldSelector::PairFst,
    };
    let out = rewrite_expect_field_access(input);
    assert!(matches!(out, PseudoExpr::Error { message: None }));
}

/// D1 positive: `expect!.snd` (bare helper) → `fail`.
#[test]
fn d1_rewrites_bare_expect_dot_snd() {
    let input = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Var {
            name: "expect!".to_string(),
            id: None,
        }),
        selector: FieldSelector::PairSnd,
    };
    let out = rewrite_expect_field_access(input);
    assert!(matches!(out, PseudoExpr::Error { message: None }));
}

#[test]
fn d1_rewrites_bare_expect_with_any_selector() {
    for selector in [
        FieldSelector::PairFst,
        FieldSelector::PairSnd,
        FieldSelector::ListHead,
    ] {
        let label = format!("{selector:?}");
        let input = PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::Var {
                name: "expect!".to_string(),
                id: None,
            }),
            selector,
        };
        let out = rewrite_expect_field_access(input);
        assert!(
            matches!(out, PseudoExpr::Error { message: None }),
            "selector {label} should still rewrite"
        );
    }
}

/// D1 refusal: `Var "expect!"` with `Some(id)` is NOT the
/// synthetic helper — leave it alone.
#[test]
fn d1_refuses_expect_with_concrete_var_id() {
    let id = VarId::fresh_binding();
    let input = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Var {
            name: "expect!".to_string(),
            id: Some(id),
        }),
        selector: FieldSelector::PairFst,
    };
    let out = rewrite_expect_field_access(input.clone());
    match out {
        PseudoExpr::FieldAccess { record, selector } => {
            assert_eq!(selector, FieldSelector::PairFst);
            match record.as_ref() {
                PseudoExpr::Var { name, id: Some(_) } => {
                    assert_eq!(name, "expect!");
                }
                other => panic!("expected unchanged Var, got {other:?}"),
            }
        }
        other => panic!("expected FieldAccess preserved, got {other:?}"),
    }
}

/// D1 refusal: unrelated bare `Var` (`x.fst`) untouched.
#[test]
fn d1_refuses_unrelated_var() {
    let input = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: None,
        }),
        selector: FieldSelector::PairFst,
    };
    let out = rewrite_expect_field_access(input);
    assert!(matches!(out, PseudoExpr::FieldAccess { .. }));
}

/// D1 refusal: bare `Var "expect!"` outside FieldAccess
/// position (e.g. as an apply function) is left alone.
#[test]
fn d1_refuses_bare_expect_var_outside_field_access() {
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "expect!".to_string(),
            id: None,
        }),
        args: vec![PseudoExpr::Int(1.into())].into(),
    };
    let out = rewrite_expect_field_access(input);
    match out {
        PseudoExpr::Apply { function, .. } => {
            assert!(matches!(
                *function,
                PseudoExpr::Var { ref name, id: None } if name == "expect!"
            ));
        }
        other => panic!("expected Apply preserved, got {other:?}"),
    }
}

/// D1: rewrite fires inside a `when` arm — the typical shape
/// `Constr<1> -> expect!.fst`.
#[test]
fn d1_rewrites_inside_when_arm() {
    let input = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: None,
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::Var {
                    name: "expect!".to_string(),
                    id: None,
                }),
                selector: FieldSelector::PairFst,
            },
        }],
    };
    let out = rewrite_expect_field_access(input);
    match out {
        PseudoExpr::When { clauses, .. } => {
            assert!(matches!(
                clauses[0].body,
                PseudoExpr::Error { message: None }
            ));
        }
        other => panic!("expected When preserved, got {other:?}"),
    }
}

#[test]
fn d1_rewrites_inside_let_body() {
    let input = PseudoExpr::Let {
        name: "x".to_string(),
        id: None,
        value: PBox::new(PseudoExpr::Int(1.into())),
        body: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::Var {
                name: "expect!".to_string(),
                id: None,
            }),
            selector: FieldSelector::PairFst,
        }),
    };
    let out = rewrite_expect_field_access(input);
    match out {
        PseudoExpr::Let { body, .. } => {
            assert!(matches!(*body, PseudoExpr::Error { message: None }));
        }
        other => panic!("expected Let preserved, got {other:?}"),
    }
}

/// Nested `(expect!.fst).snd` must FULLY collapse to `fail`,
/// not `fail.snd`: the inner rewrite yields `Error` and the
/// post_field_access cascade collapses the outer.
#[test]
fn d1_handles_nested_field_access_cascades_to_fail() {
    let input = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::Var {
                name: "expect!".to_string(),
                id: None,
            }),
            selector: FieldSelector::PairFst,
        }),
        selector: FieldSelector::PairSnd,
    };
    let out = rewrite_expect_field_access(input);
    assert!(
        matches!(out, PseudoExpr::Error { message: None }),
        "nested `(expect!.fst).snd` must cascade to `fail`, got {out:?}"
    );
}

/// Cascade fires for any `FieldAccess` wrapping an `Error`,
/// not only the ones this pass produced.
#[test]
fn d1_cascades_field_access_over_arbitrary_error() {
    let input = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Error {
            message: Some("from upstream".to_string()),
        }),
        selector: FieldSelector::PairFst,
    };
    let out = rewrite_expect_field_access(input);
    match out {
        PseudoExpr::Error { message } => {
            // Cascade preserves the message — original abort context
            // is more informative than the synthesized `None`.
            assert_eq!(message, Some("from upstream".to_string()));
        }
        other => panic!("expected cascaded Error, got {other:?}"),
    }
}

/// D1: the cascade also covers `IndexAccess` over an
/// `Error`; otherwise the renderer emits `fail[N]`.
#[test]
fn d1_cascades_index_access_over_error() {
    let input = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::Error {
            message: Some("abort".to_string()),
        }),
        index: 2,
    };
    let out = rewrite_expect_field_access(input);
    match out {
        PseudoExpr::Error { message } => {
            assert_eq!(message, Some("abort".to_string()));
        }
        other => panic!("expected cascaded Error, got {other:?}"),
    }
}

/// D1 idempotence: running the pass twice produces the same
/// result. `Error` is a leaf, so a second pass is a no-op.
#[test]
fn d1_is_idempotent() {
    let input = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Var {
            name: "expect!".to_string(),
            id: None,
        }),
        selector: FieldSelector::PairFst,
    };
    let once = rewrite_expect_field_access(input);
    let twice = rewrite_expect_field_access(once.clone());
    assert_eq!(once, twice);
}
