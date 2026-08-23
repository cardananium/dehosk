use super::*;
use crate::pseudo::var_id::VarId;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}
fn list_data(inner: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataList,
        args: vec![inner].into(),
    }
}
fn eq(l: PseudoExpr, r: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(l),
        right: PBox::new(r),
    }
}

#[test]
fn both_sides_list_data_unwrap() {
    let folded = fold_data_eq_roundtrip(eq(list_data(var("a", 1)), list_data(var("b", 2))));
    assert_eq!(folded, eq(var("a", 1), var("b", 2)));
}

#[test]
fn neq_also_unwraps() {
    let e = PseudoExpr::BinOp {
        op: BinaryOp::Neq,
        left: PBox::new(list_data(var("a", 1))),
        right: PBox::new(list_data(var("b", 2))),
    };
    let folded = fold_data_eq_roundtrip(e);
    assert_eq!(
        folded,
        PseudoExpr::BinOp {
            op: BinaryOp::Neq,
            left: PBox::new(var("a", 1)),
            right: PBox::new(var("b", 2)),
        }
    );
}

#[test]
fn one_sided_not_folded() {
    // `field == list_data(b)` is a genuine Data comparison — unchanged.
    let e = eq(var("field", 5), list_data(var("b", 2)));
    assert_eq!(fold_data_eq_roundtrip(e.clone()), e);
}

#[test]
fn empty_list_form_not_folded() {
    // `list_data(v) == []` is not both-list_data — left alone.
    let empty = PseudoExpr::List {
        elements: vec![].into(),
        tail: None,
    };
    let e = eq(list_data(var("v", 3)), empty);
    assert_eq!(fold_data_eq_roundtrip(e.clone()), e);
}

#[test]
fn nested_bottom_up() {
    // wrap the fold target inside an `if` condition to exercise recursion.
    let inner = eq(list_data(var("a", 1)), list_data(var("b", 2)));
    let outer = PseudoExpr::If {
        condition: PBox::new(inner),
        then_branch: PBox::new(PseudoExpr::Unit),
        else_branch: PBox::new(PseudoExpr::Unit),
    };
    if let PseudoExpr::If { condition, .. } = fold_data_eq_roundtrip(outer) {
        assert_eq!(*condition, eq(var("a", 1), var("b", 2)));
    } else {
        panic!("expected If");
    }
}
