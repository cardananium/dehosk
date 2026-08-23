use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_data_constr_fields_inline() {
    // Data.Constr(0, [a, b]).fields → [a, b]
    let data_constr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::Int(0.into()),
            PseudoExpr::List {
                elements: vec![PseudoExpr::var("a"), PseudoExpr::var("b")].into(),
                tail: None,
            },
        ]
        .into(),
    };
    let expr = PseudoExpr::field_access(data_constr, "fields".to_string());
    let simplified = simplify(expr);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::List { elements, tail: None }
                if matches!(elements.as_slice(), [
                    PseudoExpr::Var { name: a, .. },
                    PseudoExpr::Var { name: b, .. },
                ] if a == "a" && b == "b")
        ),
        "expected [a, b] list, got: {:?}",
        simplified
    );
}

#[test]
fn test_direct_field_access_mismatch_preserves_owned_record() {
    let data_constr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::Int(0.into()),
            PseudoExpr::list(vec![PseudoExpr::var("a")]),
        ]
        .into(),
    };
    let simplified = simplify(PseudoExpr::field_access(data_constr, "other".to_string()));
    assert!(
        matches!(
            &simplified,
            PseudoExpr::FieldAccess { record, selector }
                if selector.as_pretty_name() == "other"
                    && matches!(
                        record.as_ref(),
                        PseudoExpr::Constr { tag: 0, fields, .. }
                            if matches!(
                                fields.as_slice(),
                                [PseudoExpr::Var { name, .. }] if name == "a"
                            )
                    )
        ),
        "expected mismatched Data.Constr field access to fall back after normalizing the record, got: {simplified:?}"
    );

    let pair_new = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Pair.new"),
        args: vec![PseudoExpr::var("left"), PseudoExpr::var("right")].into(),
    };
    let simplified = simplify(PseudoExpr::field_access(pair_new, "other".to_string()));
    assert!(
        matches!(
            &simplified,
            PseudoExpr::FieldAccess { record, selector }
                if selector.as_pretty_name() == "other"
                    && matches!(
                        record.as_ref(),
                        PseudoExpr::BuiltinCall { name, args }
                            if name == "Pair.new" && args.len() == 2
                    )
        ),
        "expected mismatched Pair.new field access to fall back intact, got: {simplified:?}"
    );

    let pair = PseudoExpr::Pair(
        PBox::new(PseudoExpr::var("left")),
        PBox::new(PseudoExpr::var("right")),
    );
    let simplified = simplify(PseudoExpr::field_access(pair, "other".to_string()));
    assert!(
        matches!(
            &simplified,
            PseudoExpr::FieldAccess { record, selector }
                if selector.as_pretty_name() == "other"
                    && matches!(record.as_ref(), PseudoExpr::Pair(_, _))
        ),
        "expected mismatched Pair field access to fall back intact, got: {simplified:?}"
    );
}
