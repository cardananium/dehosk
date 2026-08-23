use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;
use crate::pseudo::var_id::VarId;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `If { cond: fn(a,b,c){c(a,b)}, then: literal, else: literal }`
/// → `Apply(cond, [then, else])`.
#[test]
fn reverses_if_on_lambda_condition_with_pure_branches() {
    let cond = PseudoExpr::Lambda {
        params: vec![binder("a", 1), binder("b", 2), binder("c", 3)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("c", 3)),
            args: vec![var("a", 1), var("b", 2)].into(),
        }),
    };
    let input = PseudoExpr::If {
        condition: PBox::new(cond.clone()),
        then_branch: PBox::new(PseudoExpr::String("TOKEN".to_string())),
        else_branch: PBox::new(PseudoExpr::ByteArray(vec![0x42])),
    };
    let out = undo_if_on_function_condition(input);
    match out {
        PseudoExpr::Apply { function, args } => {
            assert!(matches!(*function, PseudoExpr::Lambda { .. }));
            assert_eq!(args.len(), 2);
            assert!(matches!(&args[0], PseudoExpr::String(s) if s == "TOKEN"));
            assert!(matches!(&args[1], PseudoExpr::ByteArray(b) if b == &[0x42]));
        }
        other => panic!("expected Apply, got {other:?}"),
    }
}

/// Force-wrapped function condition is also reversed.
#[test]
fn reverses_force_wrapped_lambda_condition() {
    let cond = PseudoExpr::Force(PBox::new(PseudoExpr::RecFn {
        name: binder("self", 10),
        params: vec![binder("x", 11)],
        body: PBox::new(var("x", 11)),
    }));
    let input = PseudoExpr::If {
        condition: PBox::new(cond),
        then_branch: PBox::new(var("t", 20)),
        else_branch: PBox::new(var("e", 21)),
    };
    let out = undo_if_on_function_condition(input);
    assert!(
        matches!(out, PseudoExpr::Apply { .. }),
        "expected Apply, got {out:?}"
    );
}

/// A genuine Bool-condition `if` is untouched.
#[test]
fn leaves_native_bool_if_untouched() {
    let input = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Eq,
            left: PBox::new(var("x", 1)),
            right: PBox::new(var("y", 2)),
        }),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let out = undo_if_on_function_condition(input.clone());
    assert_eq!(out, input);
}

/// When a branch is impure (an `Apply` that may evaluate / fail),
/// the rewrite is skipped to avoid an eager-evaluation change.
#[test]
fn skips_when_branch_impure() {
    let cond = PseudoExpr::Lambda {
        params: vec![binder("a", 1), binder("b", 2)],
        body: PBox::new(var("a", 1)),
    };
    let impure_then = PseudoExpr::Apply {
        function: PBox::new(var("f", 30)),
        args: vec![var("x", 31)].into(),
    };
    let input = PseudoExpr::If {
        condition: PBox::new(cond),
        then_branch: PBox::new(impure_then),
        else_branch: PBox::new(var("e", 21)),
    };
    let out = undo_if_on_function_condition(input.clone());
    assert_eq!(out, input);
}
