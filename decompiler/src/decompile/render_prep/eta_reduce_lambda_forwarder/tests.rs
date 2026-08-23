use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::field_selector::FieldSelector;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `fn(x, y) { p.fst(x, y) }` → `p.fst`.
#[test]
fn rewrites_field_access_forwarder() {
    let input = PseudoExpr::Lambda {
        params: vec![binder("x", 1), binder("y", 2)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(var("p", 100)),
                selector: FieldSelector::PairFst,
            }),
            args: vec![var("x", 1), var("y", 2)].into(),
        }),
    };
    let out = eta_reduce_lambda_forwarder(input);
    match out {
        PseudoExpr::FieldAccess { selector, .. } => {
            assert!(matches!(selector, FieldSelector::PairFst));
        }
        other => panic!("expected FieldAccess, got {:?}", other),
    }
}

/// `fn(a) { helper(a) }` → `helper`.
#[test]
fn rewrites_var_forwarder() {
    let input = PseudoExpr::Lambda {
        params: vec![binder("a", 1)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("helper", 99)),
            args: vec![var("a", 1)].into(),
        }),
    };
    let out = eta_reduce_lambda_forwarder(input);
    assert!(matches!(out, PseudoExpr::Var { ref name, .. } if name == "helper"));
}

/// Arg swap — no eta.
#[test]
fn rejects_arg_swap() {
    let input = PseudoExpr::Lambda {
        params: vec![binder("x", 1), binder("y", 2)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("F", 99)),
            args: vec![var("y", 2), var("x", 1)].into(),
        }),
    };
    let out = eta_reduce_lambda_forwarder(input.clone());
    assert_eq!(out, input);
}

/// F captures one of the params — no eta.
#[test]
fn rejects_capture() {
    // F is `fn(z) { x }`, which captures the outer `x`.
    let f = PseudoExpr::Lambda {
        params: vec![binder("z", 5)],
        body: PBox::new(var("x", 1)), // references outer x
    };
    let input = PseudoExpr::Lambda {
        params: vec![binder("x", 1)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(f),
            args: vec![var("x", 1)].into(),
        }),
    };
    let out = eta_reduce_lambda_forwarder(input.clone());
    assert_eq!(out, input);
}

/// F is an Apply (unsafe to eta-reduce) — no eta.
#[test]
fn rejects_apply_as_f() {
    let input = PseudoExpr::Lambda {
        params: vec![binder("x", 1)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("g", 99)),
                args: vec![var("ctx", 88)].into(),
            }),
            args: vec![var("x", 1)].into(),
        }),
    };
    let out = eta_reduce_lambda_forwarder(input.clone());
    assert_eq!(out, input);
}

/// Arity mismatch — Lambda has 2 params but Apply has 1 arg.
#[test]
fn rejects_arity_mismatch() {
    let input = PseudoExpr::Lambda {
        params: vec![binder("x", 1), binder("y", 2)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("F", 99)),
            args: vec![var("x", 1)].into(),
        }),
    };
    let out = eta_reduce_lambda_forwarder(input.clone());
    assert_eq!(out, input);
}
