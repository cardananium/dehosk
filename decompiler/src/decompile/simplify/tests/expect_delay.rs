use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_expect_unwraps_delayed_value_arg() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::var("cond"),
            PseudoExpr::Delay(PBox::new(PseudoExpr::Let {
                name: "x".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::int(1)),
                body: PBox::new(PseudoExpr::var("x")),
            })),
        ]
        .into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Apply { function, args } => {
            assert_expect_helper_head(function.as_ref());
            assert_eq!(args.len(), 2);
            assert!(!matches!(args[1], PseudoExpr::Delay(_)));
        }
        _ => panic!("expected expect apply"),
    }
}

#[test]
fn test_expect_delay_unwrap_moves_args_and_preserves_ids() {
    let cond_id = VarId::new(9241);
    let value_id = VarId::new(9242);
    let message_id = VarId::new(9243);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::var_with_id("cond", cond_id),
            PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("value", value_id)],
                body: PBox::new(PseudoExpr::var_with_id("value", value_id)),
            })),
            PseudoExpr::var_with_id("message", message_id),
        ]
        .into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Apply { function, args } => {
            assert_expect_helper_head(function.as_ref());
            assert_eq!(args.len(), 3);
            assert!(
                matches!(&args[0], PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
                "expected moved condition arg with original id, got: {:?}",
                args[0]
            );
            assert!(
                matches!(
                    &args[1],
                    PseudoExpr::Lambda { params, body }
                        if matches!(params.as_slice(), [binder] if binder.as_str() == "value" && binder.id == value_id)
                            && matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "value" && *id == Some(value_id))
                ),
                "expected unwrapped delayed value with original binder ids, got: {:?}",
                args[1]
            );
            assert!(
                matches!(&args[2], PseudoExpr::Var { name, id } if name == "message" && *id == Some(message_id)),
                "expected moved message arg with original id, got: {:?}",
                args[2]
            );
        }
        other => panic!("expected expect apply, got: {other:?}"),
    }
}
