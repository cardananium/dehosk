use super::*;

#[test]
fn test_analyze_temporary_value_binding_names_bytearray_extractor_alias() {
    let value = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.un_bytearray"),
        args: vec![PseudoExpr::var("datum")].into(),
    };

    assert_eq!(
        analyze_extractor_temp_binding(&value),
        Some("datum_bytes".to_string())
    );
}

#[test]
fn test_analyze_temporary_value_binding_names_numeric_suffix_extractor_alias() {
    let value = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.un_bytearray"),
        args: vec![PseudoExpr::var("datum")].into(),
    };

    assert_eq!(
        analyze_extractor_temp_binding(&value),
        Some("datum_bytes".to_string())
    );
}
