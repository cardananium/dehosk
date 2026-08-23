use super::*;
use crate::pseudo::ast::Binder;
use num_bigint::BigInt;

fn y_comb_lambda() -> PseudoExpr {
    // Lambda(acc) { rec fn self(x) { acc(self, x) } }
    let acc = Binder::new("acc", VarId::fresh_binding());
    let self_b = Binder::new("self", VarId::fresh_binding());
    let x = Binder::new("x", VarId::fresh_binding());
    PseudoExpr::Lambda {
        params: vec![acc.clone()],
        body: PBox::new(PseudoExpr::RecFn {
            name: self_b.clone(),
            params: vec![x.clone()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("acc", acc.var_id())),
                args: vec![
                    PseudoExpr::var_with_id("self", self_b.var_id()),
                    PseudoExpr::var_with_id("x", x.var_id()),
                ]
                .into(),
            }),
        }),
    }
}

#[test]
fn cse_dedupes_two_y_comb_lambdas_meaningful_name_kept() {
    // Two Y-combs: `y_combinator` is not transient, so it
    // stays as the canonical binder name.
    let a_id = VarId::new(1001);
    let b_id = VarId::new(1002);
    let expr = PseudoExpr::Let {
        name: "y_combinator".to_string(),
        id: Some(a_id),
        value: PBox::new(y_comb_lambda()),
        body: PBox::new(PseudoExpr::Let {
            name: "second".to_string(),
            id: Some(b_id),
            value: PBox::new(y_comb_lambda()),
            body: PBox::new(PseudoExpr::Pair(
                PBox::new(PseudoExpr::var_with_id("y_combinator", a_id)),
                PBox::new(PseudoExpr::var_with_id("second", b_id)),
            )),
        }),
    };
    let out = cse_y_comb_consts(expr);

    let PseudoExpr::Let { name, id, body, .. } = out else {
        panic!("expected let")
    };
    // "y_combinator" is not transient — kept as canonical name.
    assert_eq!(name, "y_combinator");
    assert_eq!(id, Some(a_id));
    match body.into_inner() {
        PseudoExpr::Pair(a, b) => {
            assert!(matches!(a.into_inner(), PseudoExpr::Var { id, .. } if id == Some(a_id)));
            assert!(matches!(b.into_inner(), PseudoExpr::Var { name, id, .. }
                if name == "y_combinator" && id == Some(a_id)));
        }
        other => panic!("expected pair after dedup, got: {other:?}"),
    }
}

#[test]
fn cse_renames_transient_canonical_to_neutral() {
    // A transient first binder like `match_subject_5` renames
    // the canonical to `y_combinator`.
    let a_id = VarId::new(2001);
    let b_id = VarId::new(2002);
    let expr = PseudoExpr::Let {
        name: "match_subject_5".to_string(),
        id: Some(a_id),
        value: PBox::new(y_comb_lambda()),
        body: PBox::new(PseudoExpr::Let {
            name: "match_subject_2".to_string(),
            id: Some(b_id),
            value: PBox::new(y_comb_lambda()),
            body: PBox::new(PseudoExpr::Pair(
                PBox::new(PseudoExpr::var_with_id("match_subject_5", a_id)),
                PBox::new(PseudoExpr::var_with_id("match_subject_2", b_id)),
            )),
        }),
    };
    let out = cse_y_comb_consts(expr);

    let PseudoExpr::Let { name, id, body, .. } = out else {
        panic!("expected let")
    };
    // First binder's name was transient — renamed to neutral.
    assert_eq!(name, "y_combinator");
    assert_eq!(id, Some(a_id));
    match body.into_inner() {
        PseudoExpr::Pair(a, b) => {
            // Both refs now point to canonical's id with neutral name.
            assert!(matches!(a.into_inner(), PseudoExpr::Var { name, id, .. }
                if name == "y_combinator" && id == Some(a_id)));
            assert!(matches!(b.into_inner(), PseudoExpr::Var { name, id, .. }
                if name == "y_combinator" && id == Some(a_id)));
        }
        other => panic!("expected pair after rename, got: {other:?}"),
    }
}

#[test]
fn cse_preserves_non_y_comb_let() {
    // let a = Y; let b = Int(42); (a, b) — b is not Y-comb so untouched.
    let a_id = VarId::new(2001);
    let b_id = VarId::new(2002);
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(a_id),
        value: PBox::new(y_comb_lambda()),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(b_id),
            value: PBox::new(PseudoExpr::Int(BigInt::from(42))),
            body: PBox::new(PseudoExpr::Pair(
                PBox::new(PseudoExpr::var_with_id("a", a_id)),
                PBox::new(PseudoExpr::var_with_id("b", b_id)),
            )),
        }),
    };
    let out = cse_y_comb_consts(expr);

    // Both lets present; no rewrite.
    let PseudoExpr::Let { name, body, .. } = &out else {
        panic!("expected let")
    };
    assert_eq!(name, "a");
    match body.as_ref() {
        PseudoExpr::Let { name, .. } => assert_eq!(name, "b"),
        other => panic!("expected inner let preserved, got: {other:?}"),
    }
}

#[test]
fn cse_no_op_with_single_y_comb() {
    // let a = Y; a — only one, nothing to dedupe.
    let a_id = VarId::new(3001);
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(a_id),
        value: PBox::new(y_comb_lambda()),
        body: PBox::new(PseudoExpr::var_with_id("a", a_id)),
    };
    let out = cse_y_comb_consts(expr);
    // Unchanged.
    let PseudoExpr::Let { name, id, .. } = out else {
        panic!("expected let")
    };
    assert_eq!(name, "a");
    assert_eq!(id, Some(a_id));
}

#[test]
fn canonicalize_helper_name_allowlist() {
    // Digits-only suffix required for the
    // transient prefixes. Single-letter names are NOT transient.
    assert_eq!(canonicalize_helper_name("match_subject_5"), "y_combinator");
    assert_eq!(canonicalize_helper_name("match_subject_42"), "y_combinator");
    assert_eq!(canonicalize_helper_name("x_3"), "y_combinator");
    assert_eq!(canonicalize_helper_name("v_7"), "y_combinator");
    // Should NOT rename:
    assert_eq!(
        canonicalize_helper_name("match_subject_user"),
        "match_subject_user"
    );
    assert_eq!(canonicalize_helper_name("x_squared"), "x_squared");
    assert_eq!(canonicalize_helper_name("f"), "f"); // user-given short helper
    assert_eq!(canonicalize_helper_name("x"), "x"); // user-given
    assert_eq!(canonicalize_helper_name("y_combinator"), "y_combinator"); // already neutral
    assert_eq!(canonicalize_helper_name("y_helper"), "y_helper");
    // Edge case: empty digit suffix → not transient.
    assert_eq!(canonicalize_helper_name("match_subject_"), "match_subject_");
    assert_eq!(canonicalize_helper_name("x_"), "x_");
}

#[test]
fn cse_handles_three_y_combs() {
    // let a = Y; let b = Y; let c = Y; (a, b, c) — single-letter
    // names are not transient, so "a" stays the canonical name.
    let a_id = VarId::new(4001);
    let b_id = VarId::new(4002);
    let c_id = VarId::new(4003);
    let inner_pair = PseudoExpr::Tuple(
        vec![
            PseudoExpr::var_with_id("a", a_id),
            PseudoExpr::var_with_id("b", b_id),
            PseudoExpr::var_with_id("c", c_id),
        ]
        .into(),
    );
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(a_id),
        value: PBox::new(y_comb_lambda()),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(b_id),
            value: PBox::new(y_comb_lambda()),
            body: PBox::new(PseudoExpr::Let {
                name: "c".to_string(),
                id: Some(c_id),
                value: PBox::new(y_comb_lambda()),
                body: PBox::new(inner_pair),
            }),
        }),
    };
    let out = cse_y_comb_consts(expr);
    let PseudoExpr::Let { name, body, .. } = &out else {
        panic!("expected let")
    };
    // Canonical name "a" preserved (single-letter not transient).
    assert_eq!(name, "a");
    match body.as_ref() {
        PseudoExpr::Tuple(items) => {
            assert_eq!(items.len(), 3);
            for item in items {
                assert!(
                    matches!(item, PseudoExpr::Var { name, id, .. }
                        if name == "a" && *id == Some(a_id)),
                    "all 3 tuple items should point to canonical `a`, got: {item:?}"
                );
            }
        }
        other => panic!("expected tuple, got: {other:?}"),
    }
}
