use super::*;
use crate::pseudo::ast::PBox;

fn un_b_data(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnByteArray,
        args: vec![arg].into(),
    }
}
fn un_i_data(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnInt,
        args: vec![arg].into(),
    }
}

#[test]
fn un_b_data_of_bytearray_literal_drops_wrapper() {
    // A Data.B constant decoded to a native ByteArray literal, then
    // re-unwrapped.
    let folded = fold_un_data_scalar_const(un_b_data(PseudoExpr::ByteArray(vec![0xf5, 0x80])));
    assert_eq!(folded, PseudoExpr::ByteArray(vec![0xf5, 0x80]));
}

#[test]
fn un_b_data_of_empty_bytearray_literal_drops_wrapper() {
    let folded = fold_un_data_scalar_const(un_b_data(PseudoExpr::ByteArray(vec![])));
    assert_eq!(folded, PseudoExpr::ByteArray(vec![]));
}

#[test]
fn un_b_data_of_data_bytestring_also_folds() {
    let arg = PseudoExpr::Data(Box::new(PseudoData::ByteString(vec![1, 2, 3])));
    let folded = fold_un_data_scalar_const(un_b_data(arg));
    assert_eq!(folded, PseudoExpr::ByteArray(vec![1, 2, 3]));
}

#[test]
fn un_i_data_of_int_literal_drops_wrapper() {
    let folded = fold_un_data_scalar_const(un_i_data(PseudoExpr::Int(BigInt::from(42))));
    assert_eq!(folded, PseudoExpr::Int(BigInt::from(42)));
}

#[test]
fn un_b_data_of_int_literal_kind_mismatch_not_folded() {
    // `un_b_data` of an Int literal is a kind mismatch — leave it faithful.
    let e = un_b_data(PseudoExpr::Int(BigInt::from(7)));
    assert_eq!(fold_un_data_scalar_const(e.clone()), e);
}

#[test]
fn un_b_data_of_index_access_not_folded() {
    // `un_b_data(x_13[0])` — a genuine runtime unwrap — is untouched.
    let e = un_b_data(PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::var("x_13")),
        index: 0,
    });
    assert_eq!(fold_un_data_scalar_const(e.clone()), e);
}

#[test]
fn nested_bottom_up() {
    // The fold target inside an `if` condition exercises recursion.
    let outer = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Eq,
            left: PBox::new(un_b_data(PseudoExpr::ByteArray(vec![1, 2]))),
            right: PBox::new(PseudoExpr::ByteArray(vec![1, 2])),
        }),
        then_branch: PBox::new(PseudoExpr::Unit),
        else_branch: PBox::new(PseudoExpr::Unit),
    };
    if let PseudoExpr::If { condition, .. } = fold_un_data_scalar_const(outer)
        && let PseudoExpr::BinOp { left, .. } = condition.into_inner()
    {
        assert_eq!(*left, PseudoExpr::ByteArray(vec![1, 2]));
        return;
    }
    panic!("expected folded If/BinOp");
}

fn un_list_data(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnList,
        args: vec![arg].into(),
    }
}

#[test]
fn folds_un_list_data_on_a_literal_list() {
    let literal = PseudoExpr::List {
        elements: vec![
            PseudoExpr::ByteArray(vec![0xab]),
            PseudoExpr::ByteArray(vec![0xcd]),
        ]
        .into(),
        tail: None,
    };
    assert_eq!(
        fold_un_data_scalar_const(un_list_data(literal.clone())),
        literal
    );
}

#[test]
fn refuses_a_list_with_a_spread() {
    // `[x, ..rest]` is not a constant — its tail is computed.
    let partial = PseudoExpr::List {
        elements: vec![PseudoExpr::ByteArray(vec![0xab])].into(),
        tail: Some(PBox::new(PseudoExpr::var("rest"))),
    };
    let expr = un_list_data(partial);
    assert_eq!(fold_un_data_scalar_const(expr.clone()), expr);
}

#[test]
fn refuses_un_list_data_on_a_runtime_value() {
    let expr = un_list_data(PseudoExpr::var("xs"));
    assert_eq!(fold_un_data_scalar_const(expr.clone()), expr);
}
