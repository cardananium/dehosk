use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_bytearray_to_data_data_to_bytes_roundtrip() {
    // ByteArray.to_data(Data.to_bytes(x)) -> x
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("ByteArray.to_data"),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.to_bytes"),
            args: vec![PseudoExpr::var("x")].into(),
        }]
        .into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "x"),
        "expected Var(x), got: {:?}",
        simplified
    );
}

#[test]
fn test_data_to_bytes_bytearray_to_data_roundtrip() {
    // Data.to_bytes(ByteArray.to_data(x)) -> x
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.to_bytes"),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("ByteArray.to_data"),
            args: vec![PseudoExpr::var("x")].into(),
        }]
        .into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "x"),
        "expected Var(x), got: {:?}",
        simplified
    );
}

#[test]
fn test_int_to_data_data_to_int_roundtrip() {
    // Int.to_data(Data.to_int(x)) -> x
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Int.to_data"),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.to_int"),
            args: vec![PseudoExpr::var("x")].into(),
        }]
        .into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "x"),
        "expected Var(x), got: {:?}",
        simplified
    );
}

#[test]
fn test_canonical_data_bytearray_roundtrip() {
    // Data.ByteArray(Data.un_bytearray(x)) -> x
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.ByteArray"),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var("x")].into(),
        }]
        .into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "x"),
        "expected Var(x), got: {:?}",
        simplified
    );
}

#[test]
fn test_canonical_data_un_int_roundtrip() {
    // Data.un_int(Data.Int(x)) -> x
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.un_int"),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.Int"),
            args: vec![PseudoExpr::var("x")].into(),
        }]
        .into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "x"),
        "expected Var(x), got: {:?}",
        simplified
    );
}

#[test]
fn test_data_un_constr_pair_second_becomes_fields_access() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Pair.second"),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_constr"),
            args: vec![PseudoExpr::var("script_context")].into(),
        }]
        .into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(
            simplified,
            PseudoExpr::FieldAccess { ref selector, .. } if selector.as_pretty_name() == "fields"
        ),
        "expected .fields access, got: {:?}",
        simplified
    );
}

#[test]
fn test_data_un_constr_raw_snd_field_access_becomes_fields_access() {
    let expr = PseudoExpr::field_access(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_constr"),
            args: vec![PseudoExpr::var("script_context")].into(),
        },
        "snd".to_string(),
    );
    let simplified = simplify(expr);
    assert!(
        matches!(
            simplified,
            PseudoExpr::FieldAccess { ref record, ref selector, .. }
                if selector.as_pretty_name() == "fields"
                    && matches!(record.as_ref(), PseudoExpr::Var { name, .. } if name == "script_context")
        ),
        "expected script_context.fields access, got: {:?}",
        simplified
    );
}

#[test]
fn test_tracked_constr_unpack_var_snd_field_access_becomes_fields_access() {
    let expr = PseudoExpr::Let {
        name: "u".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Constr.unpack"),
            args: vec![PseudoExpr::var("script_context")].into(),
        }),
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("u"),
            "snd".to_string(),
        )),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(
            simplified,
            PseudoExpr::FieldAccess { ref record, ref selector, .. }
                if selector.as_pretty_name() == "fields"
                    && matches!(record.as_ref(), PseudoExpr::Var { name, .. } if name == "script_context")
        ),
        "expected tracked unpack var to simplify to script_context.fields, got: {:?}",
        simplified
    );
}
