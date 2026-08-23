use super::*;
use crate::pseudo::ast::Binder;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn y_comb_literal(v_id: u32, self_id: u32, x_id: u32) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder("v", v_id)],
        body: PBox::new(PseudoExpr::RecFn {
            name: binder("self", self_id),
            params: vec![binder("x", x_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("v", v_id)),
                args: vec![var("self", self_id), var("x", x_id)].into(),
            }),
        }),
    }
}

/// Canonical V1 shape: a let-bound Y-combinator literal consumed as
/// `when YC is { Pair(a, b) → body }` rewrites to
/// `rec fn a(b) { body }`, leaving the surrounding tree intact.
#[test]
fn unfolds_let_bound_y_comb_pair_destructure() {
    let yc_id = 100;
    let a_id = 200;
    let b_id = 201;
    let body = PseudoExpr::Apply {
        function: PBox::new(var("a", a_id)),
        args: vec![var("b", b_id)].into(),
    };
    let input = PseudoExpr::Let {
        name: "ms".to_string(),
        id: Some(VarId::new(yc_id)),
        value: PBox::new(y_comb_literal(101, 102, 103)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("ms", yc_id)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Pair(binder("a", a_id), binder("b", b_id)),
                guard: None,
                body: body.clone(),
            }],
        }),
    };
    let out = unfold_y_comb_through_let_pair_when(input);
    let PseudoExpr::Let {
        body: outer_body, ..
    } = out
    else {
        panic!("expected outer Let")
    };
    match outer_body.into_inner() {
        PseudoExpr::RecFn {
            name,
            params,
            body: rfn_body,
        } => {
            assert_eq!(name.id, VarId::new(a_id));
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].id, VarId::new(b_id));
            assert_eq!(*rfn_body, body);
        }
        other => panic!("expected RecFn, got {:?}", other),
    }
}

/// The `when` body calls `a` recursively; after the rewrite that
/// `Var { id: a_id }` still resolves to the `RecFn` self-name
/// binder, so the call survives without name substitution.
#[test]
fn preserves_self_recursion_by_var_id() {
    let yc_id = 100;
    let a_id = 200;
    let b_id = 201;
    let body = PseudoExpr::Apply {
        function: PBox::new(var("a", a_id)),
        args: vec![var("b", b_id)].into(),
    };
    let input = PseudoExpr::Let {
        name: "ms".to_string(),
        id: Some(VarId::new(yc_id)),
        value: PBox::new(y_comb_literal(101, 102, 103)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("ms", yc_id)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Pair(binder("a", a_id), binder("b", b_id)),
                guard: None,
                body,
            }],
        }),
    };
    let out = unfold_y_comb_through_let_pair_when(input);
    let PseudoExpr::Let {
        body: outer_body, ..
    } = out
    else {
        panic!("expected outer Let")
    };
    let PseudoExpr::RecFn {
        name,
        body: rfn_body,
        ..
    } = outer_body.into_inner()
    else {
        panic!("expected RecFn")
    };
    let PseudoExpr::Apply { function, args } = rfn_body.into_inner() else {
        panic!("expected Apply body")
    };
    let PseudoExpr::Var {
        id: Some(call_id), ..
    } = function.into_inner()
    else {
        panic!("expected Var function")
    };
    assert_eq!(
        call_id, name.id,
        "recursive call must point at the new self-binder"
    );
    assert_eq!(args.len(), 1);
}

/// A swapped-arg Y-comb shape (`v(x, self)` instead of `v(self, x)`)
/// is NOT a real Y-combinator and must NOT trigger the unfold.
#[test]
fn rejects_y_comb_with_swapped_args() {
    let yc_id = 100;
    let v_id = 101;
    let self_id = 102;
    let x_id = 103;
    let swapped_yc = PseudoExpr::Lambda {
        params: vec![binder("v", v_id)],
        body: PBox::new(PseudoExpr::RecFn {
            name: binder("self", self_id),
            params: vec![binder("x", x_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("v", v_id)),
                args: vec![var("x", x_id), var("self", self_id)].into(),
            }),
        }),
    };
    let input = PseudoExpr::Let {
        name: "ms".to_string(),
        id: Some(VarId::new(yc_id)),
        value: PBox::new(swapped_yc),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("ms", yc_id)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Pair(binder("a", 200), binder("b", 201)),
                guard: None,
                body: PseudoExpr::Unit,
            }],
        }),
    };
    let out = unfold_y_comb_through_let_pair_when(input.clone());
    assert_eq!(out, input);
}

/// A `when Var(...)` whose binding is NOT a Y-comb literal must not
/// trigger the unfold.
#[test]
fn rejects_non_y_comb_subject() {
    let id = 100;
    let input = PseudoExpr::Let {
        name: "ms".to_string(),
        id: Some(VarId::new(id)),
        value: PBox::new(PseudoExpr::Pair(
            PBox::new(PseudoExpr::Int(1.into())),
            PBox::new(PseudoExpr::Int(2.into())),
        )),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("ms", id)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Pair(binder("a", 200), binder("b", 201)),
                guard: None,
                body: PseudoExpr::Unit,
            }],
        }),
    };
    let out = unfold_y_comb_through_let_pair_when(input.clone());
    assert_eq!(out, input);
}

/// Multi-arm `when` clauses are out of scope — the unfold only
/// fires for the single guard-less `Pair(a, b)` form.
#[test]
fn rejects_multi_arm_when() {
    let yc_id = 100;
    let input = PseudoExpr::Let {
        name: "ms".to_string(),
        id: Some(VarId::new(yc_id)),
        value: PBox::new(y_comb_literal(101, 102, 103)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("ms", yc_id)),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::Pair(binder("a", 200), binder("b", 201)),
                    guard: None,
                    body: PseudoExpr::Unit,
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::Unit,
                },
            ],
        }),
    };
    let out = unfold_y_comb_through_let_pair_when(input.clone());
    assert_eq!(out, input);
}

/// A `when` clause with a guard is out of scope.
#[test]
fn rejects_clause_with_guard() {
    let yc_id = 100;
    let input = PseudoExpr::Let {
        name: "ms".to_string(),
        id: Some(VarId::new(yc_id)),
        value: PBox::new(y_comb_literal(101, 102, 103)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("ms", yc_id)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Pair(binder("a", 200), binder("b", 201)),
                guard: Some(PseudoExpr::Bool(true)),
                body: PseudoExpr::Unit,
            }],
        }),
    };
    let out = unfold_y_comb_through_let_pair_when(input.clone());
    assert_eq!(out, input);
}

/// The simplifier may emit `WhenPattern::Constructor` with
/// `KnownConstructor::Pair` and two fields instead of the
/// dedicated `WhenPattern::Pair`; both must trigger the unfold.
#[test]
fn unfolds_constructor_pair_pattern_variant() {
    use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
    let yc_id = 100;
    let a_id = 200;
    let b_id = 201;
    let input = PseudoExpr::Let {
        name: "ms".to_string(),
        id: Some(VarId::new(yc_id)),
        value: PBox::new(y_comb_literal(101, 102, 103)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("ms", yc_id)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Constructor {
                    tag: 0,
                    shape: ConstructorShape::Known(KnownConstructor::Pair),
                    fields: vec![binder("a", a_id), binder("b", b_id)],
                    type_hint: None,
                },
                guard: None,
                body: var("a", a_id),
            }],
        }),
    };
    let out = unfold_y_comb_through_let_pair_when(input);
    let PseudoExpr::Let { body: outer, .. } = out else {
        panic!("expected outer Let")
    };
    match outer.into_inner() {
        PseudoExpr::RecFn { name, params, .. } => {
            assert_eq!(name.id, VarId::new(a_id));
            assert_eq!(params[0].id, VarId::new(b_id));
        }
        other => panic!("expected RecFn, got {:?}", other),
    }
}

/// A `When` with an explicit `subject_name` binder (`when X is
/// X_alias { … }`) is out of scope: a named subject signals a
/// user-meaningful destructure, not the V1 Scott-data shape.
#[test]
fn rejects_when_with_explicit_subject_name() {
    let yc_id = 100;
    let input = PseudoExpr::Let {
        name: "ms".to_string(),
        id: Some(VarId::new(yc_id)),
        value: PBox::new(y_comb_literal(101, 102, 103)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("ms", yc_id)),
            subject_name: Some(binder("ms_alias", 999)),
            clauses: vec![WhenClause {
                pattern: WhenPattern::Pair(binder("a", 200), binder("b", 201)),
                guard: None,
                body: PseudoExpr::Unit,
            }],
        }),
    };
    let out = unfold_y_comb_through_let_pair_when(input.clone());
    assert_eq!(out, input);
}

/// A top-level YC literal is still unfolded from inside a nested
/// `Lambda` body: the VarId set finds the binder at any depth.
#[test]
fn unfolds_inside_nested_lambda() {
    let yc_id = 100;
    let a_id = 200;
    let b_id = 201;
    let when_inside_lambda = PseudoExpr::Lambda {
        params: vec![binder("p", 300)],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("ms", yc_id)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Pair(binder("a", a_id), binder("b", b_id)),
                guard: None,
                body: var("a", a_id),
            }],
        }),
    };
    let input = PseudoExpr::Let {
        name: "ms".to_string(),
        id: Some(VarId::new(yc_id)),
        value: PBox::new(y_comb_literal(101, 102, 103)),
        body: PBox::new(when_inside_lambda),
    };
    let out = unfold_y_comb_through_let_pair_when(input);
    let PseudoExpr::Let { body: outer, .. } = out else {
        panic!("expected outer Let")
    };
    let PseudoExpr::Lambda { body: lam_body, .. } = outer.into_inner() else {
        panic!("expected nested Lambda")
    };
    assert!(matches!(*lam_body, PseudoExpr::RecFn { .. }));
}
