use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::var_id::VarId;
use num_bigint::BigInt;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `(fn(x) { x + 1 })(42)` → `let x = 42; x + 1`.
#[test]
fn rewrites_single_arg() {
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("x", 1)],
            body: PBox::new(PseudoExpr::BinOp {
                op: crate::pseudo::ast::BinaryOp::Add,
                left: PBox::new(var("x", 1)),
                right: PBox::new(PseudoExpr::Int(BigInt::from(1))),
            }),
        }),
        args: vec![PseudoExpr::Int(BigInt::from(42))].into(),
    };
    let out = beta_reduce_lambda_apply(input);
    match out {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "x");
            assert!(matches!(*body, PseudoExpr::BinOp { .. }));
        }
        other => panic!("expected Let, got {:?}", other),
    }
}

/// `(fn(a, b) { a + b })(1, 2)` → `let a = 1; let b = 2; a + b`.
#[test]
fn rewrites_two_args() {
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("a", 1), binder("b", 2)],
            body: PBox::new(PseudoExpr::BinOp {
                op: crate::pseudo::ast::BinaryOp::Add,
                left: PBox::new(var("a", 1)),
                right: PBox::new(var("b", 2)),
            }),
        }),
        args: vec![
            PseudoExpr::Int(BigInt::from(1)),
            PseudoExpr::Int(BigInt::from(2)),
        ]
        .into(),
    };
    let out = beta_reduce_lambda_apply(input);
    let PseudoExpr::Let {
        name: n1, body: b1, ..
    } = out
    else {
        panic!("outer Let");
    };
    assert_eq!(n1, "a");
    let PseudoExpr::Let { name: n2, .. } = b1.into_inner() else {
        panic!("inner Let");
    };
    assert_eq!(n2, "b");
}

/// Arity mismatch (3 params, 2 args) — no rewrite.
#[test]
fn rejects_arity_mismatch() {
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("a", 1), binder("b", 2), binder("c", 3)],
            body: PBox::new(var("a", 1)),
        }),
        args: vec![
            PseudoExpr::Int(BigInt::from(1)),
            PseudoExpr::Int(BigInt::from(2)),
        ]
        .into(),
    };
    let out = beta_reduce_lambda_apply(input.clone());
    assert_eq!(out, input);
}

/// `(rec fn self(x) { ... })(arg)` — never beta-reduce RecFn.
#[test]
fn skips_recfn() {
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::RecFn {
            name: binder("self", 100),
            params: vec![binder("x", 1)],
            body: PBox::new(var("x", 1)),
        }),
        args: vec![PseudoExpr::Int(BigInt::from(42))].into(),
    };
    let out = beta_reduce_lambda_apply(input.clone());
    assert_eq!(out, input);
}

/// Validator entry param names (`redeemer`, `datum`, etc.) — skip.
#[test]
fn skips_validator_entry() {
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("redeemer", 1), binder("script_context", 2)],
            body: PBox::new(var("redeemer", 1)),
        }),
        args: vec![var("r_val", 10), var("ctx_val", 11)].into(),
    };
    let out = beta_reduce_lambda_apply(input.clone());
    assert_eq!(out, input);
}

/// Disambiguated variant `redeemer_2` still recognized as
/// validator entry param.
#[test]
fn skips_validator_entry_disambiguated() {
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("redeemer_2", 1), binder("script_context_1", 2)],
            body: PBox::new(var("redeemer_2", 1)),
        }),
        args: vec![var("r_val", 10), var("ctx_val", 11)].into(),
    };
    let out = beta_reduce_lambda_apply(input.clone());
    assert_eq!(out, input);
}

/// Bottom-up: inner redex resolves first, then outer.
#[test]
fn reduces_nested_redexes() {
    // Apply(Lambda(y, Apply(Lambda(x, x), [y])), [42])
    let inner = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("x", 1)],
            body: PBox::new(var("x", 1)),
        }),
        args: vec![var("y", 2)].into(),
    };
    let outer = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("y", 2)],
            body: PBox::new(inner),
        }),
        args: vec![PseudoExpr::Int(BigInt::from(42))].into(),
    };
    let out = beta_reduce_lambda_apply(outer);
    // Expected: Let y = 42 in Let x = y in x
    let PseudoExpr::Let {
        name: n1, body: b1, ..
    } = out
    else {
        panic!()
    };
    assert_eq!(n1, "y");
    let PseudoExpr::Let {
        name: n2, body: b2, ..
    } = b1.into_inner()
    else {
        panic!()
    };
    assert_eq!(n2, "x");
    assert!(matches!(*b2, PseudoExpr::Var { ref name, .. } if name == "x"));
}
