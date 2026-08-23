use super::*;
use crate::pseudo::ast::Binder;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `rec fn self(_unused) { fn(x, y, z) { body using self(...) } }`
/// → `rec fn self(x, y, z) { body }`.
#[test]
fn flattens_unused_outer_param() {
    let input = PseudoExpr::RecFn {
        name: Binder::new("self".to_string(), VarId::new(100)),
        params: vec![Binder::new("v".to_string(), VarId::new(1))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("x".to_string(), VarId::new(2)),
                Binder::new("y".to_string(), VarId::new(3)),
                Binder::new("z".to_string(), VarId::new(4)),
            ],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("self", 100)),
                args: vec![var("x", 2), var("y", 3), var("z", 4)].into(),
            }),
        }),
    };
    let out = flatten_recfn_unused_self(input);
    let PseudoExpr::RecFn { name, params, body } = out else {
        panic!("RecFn");
    };
    assert_eq!(name.name, "self");
    assert_eq!(params.len(), 3);
    assert_eq!(params[0].name, "x");
    assert_eq!(params[1].name, "y");
    assert_eq!(params[2].name, "z");
    // Body should be the inner body (Apply), not Lambda
    assert!(matches!(*body, PseudoExpr::Apply { .. }));
}

/// Outer param IS used — no flatten.
#[test]
fn skips_when_outer_used() {
    let input = PseudoExpr::RecFn {
        name: Binder::new("self".to_string(), VarId::new(100)),
        params: vec![Binder::new("v".to_string(), VarId::new(1))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x".to_string(), VarId::new(2))],
            body: PBox::new(var("v", 1)), // ← uses outer param
        }),
    };
    let out = flatten_recfn_unused_self(input.clone());
    assert_eq!(out, input);
}

/// Body references self bare (not as Apply.function) — flatten
/// would change the rec-fn's runtime value, so skip.
#[test]
fn skips_when_self_used_bare() {
    let input = PseudoExpr::RecFn {
        name: Binder::new("self".to_string(), VarId::new(100)),
        params: vec![Binder::new("v".to_string(), VarId::new(1))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x".to_string(), VarId::new(2))],
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    var("self", 100), // ← bare self ref
                    var("x", 2),
                ]
                .into(),
            )),
        }),
    };
    let out = flatten_recfn_unused_self(input.clone());
    assert_eq!(out, input);
}

/// Body has an under-applied recursive call (fewer args than
/// inner arity) — flatten would over-apply, so skip.
#[test]
fn skips_when_self_under_applied() {
    let input = PseudoExpr::RecFn {
        name: Binder::new("self".to_string(), VarId::new(100)),
        params: vec![Binder::new("v".to_string(), VarId::new(1))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("x".to_string(), VarId::new(2)),
                Binder::new("y".to_string(), VarId::new(3)),
            ],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("self", 100)),
                args: vec![var("x", 2)].into(), // ← only 1 arg, inner arity is 2
            }),
        }),
    };
    let out = flatten_recfn_unused_self(input.clone());
    assert_eq!(out, input);
}

/// Body is NOT a single Lambda — no flatten.
#[test]
fn skips_non_lambda_body() {
    let input = PseudoExpr::RecFn {
        name: Binder::new("self".to_string(), VarId::new(100)),
        params: vec![Binder::new("v".to_string(), VarId::new(1))],
        body: PBox::new(var("constant", 999)),
    };
    let out = flatten_recfn_unused_self(input.clone());
    assert_eq!(out, input);
}
