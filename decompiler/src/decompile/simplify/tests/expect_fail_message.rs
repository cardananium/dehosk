use super::*;
use crate::pseudo::ast::PBox;

// === B5: fail-message carry-through into 3-arg expect! ===

#[test]
fn test_b5_fail_message_lifts_into_three_arg_expect() {
    // if cond { value } else { fail @"msg" } should become
    // Apply(expect!, [cond, value, String("msg")])
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::var("value")),
        else_branch: PBox::new(PseudoExpr::Error {
            message: Some("redeemer too large".to_string()),
        }),
    };

    match simplify(expr) {
        PseudoExpr::Apply { function, args } => {
            assert_expect_helper_head(function.as_ref());
            assert_eq!(args.len(), 3, "expected 3-arg expect!, got: {args:?}");
            assert!(
                matches!(&args[0], PseudoExpr::Var { name, .. } if name == "cond"),
                "expected cond at args[0], got: {:?}",
                args[0]
            );
            assert!(
                matches!(&args[1], PseudoExpr::Var { name, .. } if name == "value"),
                "expected value at args[1], got: {:?}",
                args[1]
            );
            assert!(
                matches!(&args[2], PseudoExpr::String(s) if s == "redeemer too large"),
                "expected message string at args[2], got: {:?}",
                args[2]
            );
        }
        other => panic!("expected expect! Apply, got: {other:?}"),
    }
}

#[test]
fn test_b5_inverted_fail_message_lifts_into_three_arg_expect() {
    // if cond { fail @"msg" } else { value } -> expect!(!cond, value, "msg")
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::Error {
            message: Some("negative".to_string()),
        }),
        else_branch: PBox::new(PseudoExpr::var("value")),
    };

    match simplify(expr) {
        PseudoExpr::Apply { function, args } => {
            assert_expect_helper_head(function.as_ref());
            assert_eq!(args.len(), 3, "expected 3-arg expect!, got: {args:?}");
            assert!(
                matches!(&args[0],
                    PseudoExpr::UnOp { op: UnaryOp::Not, operand }
                        if matches!(operand.as_ref(), PseudoExpr::Var { name, .. } if name == "cond")
                ),
                "expected !cond at args[0], got: {:?}",
                args[0]
            );
            assert!(
                matches!(&args[1], PseudoExpr::Var { name, .. } if name == "value"),
                "expected value at args[1], got: {:?}",
                args[1]
            );
            assert!(
                matches!(&args[2], PseudoExpr::String(s) if s == "negative"),
                "expected message string at args[2], got: {:?}",
                args[2]
            );
        }
        other => panic!("expected expect! Apply, got: {other:?}"),
    }
}

#[test]
fn test_b5_no_message_keeps_two_arg_expect() {
    // bare fail (no msg) - 2-arg expect! is still produced
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::var("value")),
        else_branch: PBox::new(PseudoExpr::Error { message: None }),
    };

    match simplify(expr) {
        PseudoExpr::Apply { function, args } => {
            assert_expect_helper_head(function.as_ref());
            assert_eq!(args.len(), 2, "expected 2-arg expect!, got: {args:?}");
        }
        other => panic!("expected expect! Apply, got: {other:?}"),
    }
}

#[test]
fn test_b5_three_arg_expect_renders_with_message_trailer() {
    // The pretty-printer renders 3-arg expect! as `expect cond, @"msg"`: the
    // rendered keyword is `expect` while the internal helper symbol stays
    // `expect!`, so the input `Var("expect!")` prints without the bang.
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::var("cond"),
            PseudoExpr::Unit,
            PseudoExpr::String("redeemer too large".to_string()),
        ]
        .into(),
    };
    let output = expr.to_pretty();
    // The chain's final value is printed even when it is `Void` — a
    // chain ending the surrounding block must not close on a dangling
    // `expect …` with no result expression.
    assert_eq!(
        output, "expect cond, @\"redeemer too large\"\nVoid",
        "expected `expect cond, @\"...\"` + `Void` value rendering, got:\n{}",
        output
    );
}
