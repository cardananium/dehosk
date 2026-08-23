use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_roundtrip_with_uplc_names() {
    // b_data(un_b_data(x)) -> x (using UPLC builtin names)
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("b_data"),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("un_b_data"),
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
fn test_roundtrip_apply_form_with_canonical_names() {
    // Apply(BuiltinCall("Data.ByteArray", []), [BuiltinCall("Data.un_bytearray", [x])]) -> x
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.ByteArray"),
            args: vec![].into(),
        }),
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
fn test_roundtrip_apply_form() {
    // Apply(BuiltinCall("ByteArray.to_data", []), [BuiltinCall("Data.to_bytes", [x])]) -> x
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("ByteArray.to_data"),
            args: vec![].into(),
        }),
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
fn test_roundtrip_apply_form_moves_payload_and_preserves_ids() {
    let direct_id = VarId::new(9261);
    let direct = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.ByteArray"),
            args: vec![].into(),
        }),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var_with_id("payload", direct_id)].into(),
        }]
        .into(),
    };
    let direct = simplify(direct);
    assert!(
        matches!(&direct, PseudoExpr::Var { name, id } if name == "payload" && *id == Some(direct_id)),
        "expected direct Apply-form round-trip to move payload id, got: {direct:?}"
    );

    let apply_id = VarId::new(9262);
    let apply = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("ByteArray.to_data"),
            args: vec![].into(),
        }),
        args: vec![PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.to_bytes"),
                args: vec![].into(),
            }),
            args: vec![PseudoExpr::var_with_id("payload", apply_id)].into(),
        }]
        .into(),
    };
    let apply = simplify(apply);
    assert!(
        matches!(&apply, PseudoExpr::Var { name, id } if name == "payload" && *id == Some(apply_id)),
        "expected nested Apply-form round-trip to move payload id, got: {apply:?}"
    );
}

#[test]
fn test_no_roundtrip_different_builtins() {
    // ByteArray.to_data(Data.to_int(x)) should NOT simplify (different types)
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("ByteArray.to_data"),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.to_int"),
            args: vec![PseudoExpr::var("x")].into(),
        }]
        .into(),
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::BuiltinCall { .. }),
        "expected BuiltinCall (no simplification), got: {:?}",
        simplified
    );
}
