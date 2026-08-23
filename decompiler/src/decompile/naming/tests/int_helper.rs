use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_add_int_wrapper() {
    let value = PseudoExpr::Lambda {
        params: vec!["x".to_string().into(), "y".to_string().into()],
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.Int"),
            args: vec![PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_int"),
                    args: vec![PseudoExpr::var("x")].into(),
                }),
                right: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_int"),
                    args: vec![PseudoExpr::var("y")].into(),
                }),
            }]
            .into(),
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_9", &value),
        Some("add_int".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_lte_int_helper() {
    let value = PseudoExpr::Lambda {
        params: vec!["x".to_string().into(), "y".to_string().into()],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Lte,
            left: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.un_int"),
                args: vec![PseudoExpr::var("x")].into(),
            }),
            right: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.un_int"),
                args: vec![PseudoExpr::var("y")].into(),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_10", &value),
        Some("lte_int".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_negated_lt_int_helper() {
    let value = PseudoExpr::Lambda {
        params: vec!["x".to_string().into(), "y".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "cond_ok".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Lt,
                left: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_int"),
                    args: vec![PseudoExpr::var("x")].into(),
                }),
                right: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_int"),
                    args: vec![PseudoExpr::var("y")].into(),
                }),
            }),
            body: PBox::new(PseudoExpr::UnOp {
                op: crate::pseudo::ast::UnaryOp::Not,
                operand: PBox::new(PseudoExpr::var("cond_ok")),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_7", &value),
        Some("gte_int".to_string())
    );
}
