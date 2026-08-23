use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::var_id::VarId;

fn var() -> PBox {
    PBox::new(PseudoExpr::Var {
        name: "x".to_string(),
        id: Some(VarId::new(1)),
    })
}

fn access(sel: &str) -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: var(),
        selector: FieldSelector::NamedField(sel.to_string()),
    }
}

fn sel_of(e: &PseudoExpr) -> &str {
    match e {
        PseudoExpr::FieldAccess { selector, .. } => selector.as_pretty_name(),
        _ => panic!("not a field access"),
    }
}

#[test]
fn maps_zero_based_index_to_ordinal() {
    assert_eq!(sel_of(&normalize_tuple_field_ordinals(access("0"))), "1st");
    assert_eq!(sel_of(&normalize_tuple_field_ordinals(access("1"))), "2nd");
    assert_eq!(sel_of(&normalize_tuple_field_ordinals(access("2"))), "3rd");
    assert_eq!(sel_of(&normalize_tuple_field_ordinals(access("7"))), "8th");
    assert_eq!(
        sel_of(&normalize_tuple_field_ordinals(access("10"))),
        "11th"
    );
    assert_eq!(
        sel_of(&normalize_tuple_field_ordinals(access("12"))),
        "13th"
    );
}

#[test]
fn leaves_non_numeric_selectors_untouched() {
    assert_eq!(
        sel_of(&normalize_tuple_field_ordinals(access("fields"))),
        "fields"
    );
    // already-ordinal selectors are not numeric → untouched (idempotent).
    assert_eq!(
        sel_of(&normalize_tuple_field_ordinals(access("1st"))),
        "1st"
    );
}

#[test]
fn leaves_pair_accessors_untouched() {
    let e = PseudoExpr::FieldAccess {
        record: var(),
        selector: FieldSelector::PairFst,
    };
    assert_eq!(sel_of(&normalize_tuple_field_ordinals(e)), "fst");
}

#[test]
fn rewrites_nested_record() {
    // x.fst.7 -> x.fst.8th (recurse into the record)
    let inner = PseudoExpr::FieldAccess {
        record: var(),
        selector: FieldSelector::PairFst,
    };
    let outer = PseudoExpr::FieldAccess {
        record: PBox::new(inner),
        selector: FieldSelector::NamedField("7".to_string()),
    };
    let out = normalize_tuple_field_ordinals(outer);
    assert_eq!(sel_of(&out), "8th");
    match &out {
        PseudoExpr::FieldAccess { record, .. } => assert_eq!(sel_of(record), "fst"),
        _ => panic!(),
    }
}
