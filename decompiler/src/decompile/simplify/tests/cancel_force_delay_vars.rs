use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_cancel_force_delay_vars_eliminates_alias() {
    use super::super::postprocess::cancel_force_delay_vars;

    // Simulates: let k = delay(j) in force(k).tag == 0
    // After cancel_force_delay_vars, should become: j.tag == 0
    // (not: let k = j in k.tag == 0)
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("j")))),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::field_access(
                PseudoExpr::Force(PBox::new(PseudoExpr::var("k"))),
                "tag".to_string(),
            )),
            right: PBox::new(PseudoExpr::int(0)),
        }),
    };

    let result = cancel_force_delay_vars(expr);

    // Should NOT contain a Let binding — the alias should be eliminated
    match &result {
        PseudoExpr::Let { name, value, .. } => {
            // If it's still a Let, the value must NOT be a bare Var (alias)
            assert!(
                !matches!(value.as_ref(), PseudoExpr::Var { .. }),
                "alias should be eliminated, but got: let {} = {:?}",
                name,
                value
            );
        }
        PseudoExpr::BinOp { left, .. } => {
            // Correct: alias was eliminated, body uses j directly
            match left.as_ref() {
                PseudoExpr::FieldAccess {
                    record, selector, ..
                } => {
                    assert_eq!(selector.as_pretty_name(), "tag");
                    assert!(
                        matches!(record.as_ref(), PseudoExpr::Var { name, .. } if name == "j"),
                        "expected Var(j), got: {:?}",
                        record
                    );
                }
                _ => panic!("expected FieldAccess, got: {:?}", left),
            }
        }
        _ => panic!("expected BinOp, got: {:?}", result),
    }
}

#[test]
fn test_cancel_force_delay_vars_trivial_let() {
    use super::super::postprocess::cancel_force_delay_vars;

    // Simulates: let k = delay(expr) in force(k) → expr
    // After cancel_force_delay_vars: let k = expr in k → expr (trivial let)
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::int(42)))),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("k")))),
    };

    let result = cancel_force_delay_vars(expr);

    // Should be just Int(42) — both delay/force cancelled and trivial let eliminated
    assert!(
        matches!(result, PseudoExpr::Int(_)),
        "expected Int, got: {:?}",
        result
    );
}

#[test]
fn test_cancel_force_delay_vars_collapses_plain_var_alias() {
    use super::super::postprocess::cancel_force_delay_vars;

    // let a = 1 in let b = a in b == 1
    // > let a = 1 in a == 1
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::var("a")),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::var("b")),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
    };

    let result = cancel_force_delay_vars(expr);
    match result {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "a");
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::BinOp {
                        left,
                        right,
                        op: BinaryOp::Eq
                    } if matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == "a")
                        && matches!(right.as_ref(), PseudoExpr::Int(_))
                ),
                "expected b alias collapsed in body, got: {:?}",
                body
            );
        }
        _ => panic!("expected outer Let(a), got: {:?}", result),
    }
}

#[test]
fn test_cancel_force_delay_vars_collapses_identity_let_value() {
    use super::super::postprocess::cancel_force_delay_vars;

    // let x = (let y = Data.to_bytes(field_0) in y) in x
    // > Data.to_bytes(field_0)
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.to_bytes"),
                args: vec![PseudoExpr::var("field_0")].into(),
            }),
            body: PBox::new(PseudoExpr::var("y")),
        }),
        body: PBox::new(PseudoExpr::var("x")),
    };

    let result = cancel_force_delay_vars(expr);
    assert!(
        matches!(
            result,
            PseudoExpr::BuiltinCall { ref name, .. } if name == "Data.to_bytes"
        ),
        "expected identity let-value collapsed, got: {:?}",
        result
    );
}
