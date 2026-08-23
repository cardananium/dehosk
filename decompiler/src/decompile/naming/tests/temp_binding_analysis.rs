use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_unit_check_temp_binding_with_consistency_names_variant_from_consistent_field_access()
 {
    let subject_id = VarId::fresh_binding();
    let value = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("value_2", subject_id)),
        subject_name: Some(Binder::new("value_2", subject_id)),
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::field_access(
                    PseudoExpr::var_with_id("value_2", subject_id),
                    "fields".to_string(),
                ),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
        ],
    };

    assert_eq!(
        analyze_unit_check_temp_binding_with_consistency(
            &value,
            Some(&HashSet::from([subject_id])),
        ),
        Some("check_variant".to_string())
    );
}

#[test]
fn test_analyze_unit_check_temp_binding_with_consistency_ignores_inconsistent_field_access() {
    let subject_id = VarId::fresh_binding();
    let value = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("value_2", subject_id)),
        subject_name: Some(Binder::new("value_2", subject_id)),
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::field_access(
                    PseudoExpr::var_with_id("value_2", subject_id),
                    "fields".to_string(),
                ),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
        ],
    };

    assert_eq!(
        analyze_unit_check_temp_binding_with_consistency(&value, Some(&HashSet::new())),
        Some("check_value".to_string())
    );
}

#[test]
fn test_analyze_temporary_value_binding_names_sum_alias() {
    let value = PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(PseudoExpr::var("int")),
        right: PBox::new(PseudoExpr::var("int_2")),
    };

    assert_eq!(
        analyze_arithmetic_temp_binding(&value),
        Some("sum".to_string())
    );
}

#[test]
fn test_analyze_temporary_value_binding_names_int_option_wrapper() {
    let value = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::constr_known(KnownConstructor::None, vec![])),
        else_branch: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.Int"),
                args: vec![PseudoExpr::var("t2")].into(),
            }],
        )),
    };

    assert_eq!(
        analyze_option_wrapper_temp_binding(&value),
        Some("int_option".to_string())
    );
}

#[test]
fn test_analyze_temporary_value_binding_names_map_option_wrapper() {
    let value = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::constr_known(KnownConstructor::None, vec![])),
        else_branch: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.Map"),
                args: vec![PseudoExpr::var("pairs")].into(),
            }],
        )),
    };

    assert_eq!(
        analyze_option_wrapper_temp_binding(&value),
        Some("map_option".to_string())
    );
}

#[test]
fn test_analyze_value_binding_with_known_renames_names_option_passthrough_result() {
    let mut rename_map = HashMap::new();
    rename_map.insert("lookup_4".to_string(), "lookup_2".to_string());

    let value = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("lookup_result")),
        subject_name: Some("lookup_result".into()),
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                PseudoExpr::constr_known(KnownConstructor::None, vec![]),
            ),
            WhenClause::new(
                WhenPattern::Wildcard,
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("lookup_4")),
                    args: vec![PseudoExpr::var("pairs")].into(),
                },
            ),
        ],
    };

    assert_eq!(
        analyze_value_binding_with_known_renames("l2", &value, &rename_map),
        Some("lookup_2_result".to_string())
    );
}
