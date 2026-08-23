use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::var_id::VarId;

fn dummy_var(name: &str) -> PseudoExpr {
    PseudoExpr::Var {
        name: name.to_string(),
        id: Some(VarId::from_raw(0)),
    }
}

#[test]
fn test_literal_int() {
    assert_eq!(
        infer_value_type_hint(&PseudoExpr::Int(42.into())),
        Some(PseudoType::Int)
    );
}

#[test]
fn test_literal_bool() {
    assert_eq!(
        infer_value_type_hint(&PseudoExpr::Bool(true)),
        Some(PseudoType::Bool)
    );
}

#[test]
fn test_literal_string() {
    assert_eq!(
        infer_value_type_hint(&PseudoExpr::String("hi".into())),
        Some(PseudoType::String)
    );
}

#[test]
fn test_literal_bytearray() {
    assert_eq!(
        infer_value_type_hint(&PseudoExpr::ByteArray(vec![1, 2])),
        Some(PseudoType::ByteArray)
    );
}

#[test]
fn test_literal_unit() {
    assert_eq!(
        infer_value_type_hint(&PseudoExpr::Unit),
        Some(PseudoType::Unit)
    );
}

#[test]
fn test_arithmetic_binop_returns_int() {
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(PseudoExpr::Int(1.into())),
        right: PBox::new(PseudoExpr::Int(2.into())),
    };
    assert_eq!(infer_value_type_hint(&expr), Some(PseudoType::Int));
}

#[test]
fn test_comparison_binop_returns_bool() {
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::Int(1.into())),
        right: PBox::new(PseudoExpr::Int(2.into())),
    };
    assert_eq!(infer_value_type_hint(&expr), Some(PseudoType::Bool));
}

#[test]
fn test_cons_returns_none() {
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Cons,
        left: PBox::new(PseudoExpr::Int(1.into())),
        right: PBox::new(dummy_var("xs")),
    };
    assert_eq!(infer_value_type_hint(&expr), None);
}

#[test]
fn test_not_returns_bool() {
    let expr = PseudoExpr::UnOp {
        op: UnaryOp::Not,
        operand: PBox::new(PseudoExpr::Bool(true)),
    };
    assert_eq!(infer_value_type_hint(&expr), Some(PseudoType::Bool));
}

#[test]
fn test_negate_returns_int() {
    let expr = PseudoExpr::UnOp {
        op: UnaryOp::Negate,
        operand: PBox::new(PseudoExpr::Int(5.into())),
    };
    assert_eq!(infer_value_type_hint(&expr), Some(PseudoType::Int));
}

#[test]
fn test_let_looks_through_to_body() {
    let expr = PseudoExpr::Let {
        name: "x".into(),
        id: Some(VarId::from_raw(1)),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Int(99.into())),
    };
    assert_eq!(infer_value_type_hint(&expr), Some(PseudoType::Int));
}

#[test]
fn test_trace_looks_through_to_value() {
    let expr = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("log".into())),
        value: PBox::new(PseudoExpr::Bool(false)),
    };
    assert_eq!(infer_value_type_hint(&expr), Some(PseudoType::Bool));
}

#[test]
fn test_if_branches_agree() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(true)),
        then_branch: PBox::new(PseudoExpr::Int(1.into())),
        else_branch: PBox::new(PseudoExpr::Int(2.into())),
    };
    assert_eq!(infer_value_type_hint(&expr), Some(PseudoType::Int));
}

#[test]
fn test_if_branches_disagree() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(true)),
        then_branch: PBox::new(PseudoExpr::Int(1.into())),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    assert_eq!(infer_value_type_hint(&expr), None);
}

#[test]
fn test_var_returns_none() {
    // A `Var` has no self-evident type — `type_resolution()` is Unknown for it
    assert_eq!(infer_value_type_hint(&dummy_var("x")), None);
}
