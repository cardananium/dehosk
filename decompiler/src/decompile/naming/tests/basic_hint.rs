use super::*;

#[test]
fn test_trace_message_to_name() {
    assert_eq!(
        trace_message_to_name("Signer is not eligible to claim"),
        "check_signer_eligibility"
    );
    assert_eq!(
        trace_message_to_name("Tx validity range exceeds 12 hours"),
        "check_validity_range"
    );
}

#[test]
fn test_fold_result_rename() {
    assert!(is_generic_name("fold_result_0"));
    let hint = analyze_function_binding(
        "fold_result_3",
        &PseudoExpr::int(0), // non-function, should still rename
    );
    assert_eq!(hint, Some("fold_3".to_string()));
}
