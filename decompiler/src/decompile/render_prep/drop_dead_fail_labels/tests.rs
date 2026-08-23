use super::*;
use crate::pseudo::ast::PseudoExpr;

fn label_fail(label: &str) -> PseudoExpr {
    PseudoExpr::Error {
        message: Some(label.to_string()),
    }
}

#[test]
fn drops_unreferenced_let_bound_source_label_fail() {
    let body = PseudoExpr::var("body_value");
    let expr = PseudoExpr::let_bind("a", label_fail("L155;3"), body.clone());
    let result = drop_dead_fail_labels(expr);
    assert_eq!(result, body);
}

#[test]
fn drops_chain_of_unreferenced_labels() {
    let body = PseudoExpr::var("kept");
    let chain = vec![("a", "L155;3"), ("b", "L144;13"), ("c", "L107;7")];
    let mut expr = body.clone();
    for (name, label) in chain.into_iter().rev() {
        expr = PseudoExpr::let_bind(name, label_fail(label), expr);
    }
    let result = drop_dead_fail_labels(expr);
    assert_eq!(result, body);
}

#[test]
fn keeps_let_when_binder_is_referenced() {
    let expr = PseudoExpr::let_bind("a", label_fail("L1;1"), PseudoExpr::var("a"));
    let result = drop_dead_fail_labels(expr.clone());
    assert_eq!(result, expr);
}

#[test]
fn keeps_let_when_rhs_is_not_a_source_label_fail() {
    let expr = PseudoExpr::let_bind(
        "a",
        PseudoExpr::Error {
            message: Some("custom message".to_string()),
        },
        PseudoExpr::var("body"),
    );
    let result = drop_dead_fail_labels(expr.clone());
    assert_eq!(result, expr);
}

#[test]
fn keeps_let_when_rhs_is_bare_fail_without_message() {
    let expr = PseudoExpr::let_bind(
        "a",
        PseudoExpr::Error { message: None },
        PseudoExpr::var("body"),
    );
    let result = drop_dead_fail_labels(expr.clone());
    assert_eq!(result, expr);
}

#[test]
fn handles_shadowed_binder_correctly() {
    let inner = PseudoExpr::let_bind("a", PseudoExpr::int(5), PseudoExpr::var("a"));
    let expr = PseudoExpr::let_bind("a", label_fail("L1;1"), inner.clone());
    let result = drop_dead_fail_labels(expr);
    assert_eq!(result, inner);
}

#[test]
fn recurses_into_nested_bodies() {
    let lambda_body = PseudoExpr::let_bind("a", label_fail("L1;1"), PseudoExpr::var("body"));
    let expr = PseudoExpr::Lambda {
        params: vec![],
        body: PBox::new(lambda_body),
    };
    let result = drop_dead_fail_labels(expr);
    let expected = PseudoExpr::Lambda {
        params: vec![],
        body: PBox::new(PseudoExpr::var("body")),
    };
    assert_eq!(result, expected);
}

#[test]
fn is_source_label_matches_canonical_forms() {
    assert!(is_source_label("L1;1"));
    assert!(is_source_label("L155;3"));
    assert!(is_source_label("L9999;99"));
    assert!(!is_source_label(""));
    assert!(!is_source_label("L"));
    assert!(!is_source_label("L155"));
    assert!(!is_source_label("L155;"));
    assert!(!is_source_label(";3"));
    assert!(!is_source_label("L1a;3"));
    assert!(!is_source_label("L1;3a"));
    assert!(!is_source_label("custom"));
}
