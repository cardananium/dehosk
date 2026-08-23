use super::*;
use crate::pseudo::ast::Binder;

#[test]
fn collapses_let_fail_in_fail() {
    // let __20 = fail in fail   →   fail
    let dead_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "__20".to_string(),
        id: Some(dead_id),
        value: PBox::new(PseudoExpr::Error { message: None }),
        body: PBox::new(PseudoExpr::Error { message: None }),
    };
    let collapsed = collapse_dead_fail_chain(expr);
    assert!(matches!(collapsed, PseudoExpr::Error { .. }));
}

#[test]
fn preserves_message_from_value_side() {
    // let __20 = fail @"value msg" in fail   →   fail @"value msg"
    let dead_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "__20".to_string(),
        id: Some(dead_id),
        value: PBox::new(PseudoExpr::Error {
            message: Some("value msg".into()),
        }),
        body: PBox::new(PseudoExpr::Error { message: None }),
    };
    let collapsed = collapse_dead_fail_chain(expr);
    let PseudoExpr::Error { message } = collapsed else {
        panic!("expected Error")
    };
    assert_eq!(message.as_deref(), Some("value msg"));
}

#[test]
fn leaves_let_when_binder_is_referenced() {
    // let __X = fail in __X  →  unchanged (binder is used)
    let id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "__X".to_string(),
        id: Some(id),
        value: PBox::new(PseudoExpr::Error { message: None }),
        body: PBox::new(PseudoExpr::var_with_id("__X", id)),
    };
    let result = collapse_dead_fail_chain(expr);
    // Body is a Var, not Error, so the both-error precondition
    // already blocks this; the binder gate is not isolated.
    assert!(matches!(result, PseudoExpr::Let { .. }));
}

#[test]
fn leaves_let_when_body_is_not_error() {
    let id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "__X".to_string(),
        id: Some(id),
        value: PBox::new(PseudoExpr::Error { message: None }),
        body: PBox::new(PseudoExpr::int(42)),
    };
    let result = collapse_dead_fail_chain(expr);
    assert!(matches!(result, PseudoExpr::Let { .. }));
}

#[test]
fn leaves_let_when_value_is_not_error() {
    let id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "__X".to_string(),
        id: Some(id),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::Error { message: None }),
    };
    let result = collapse_dead_fail_chain(expr);
    assert!(matches!(result, PseudoExpr::Let { .. }));
}

#[test]
fn collapses_recursively_within_nested_lambda() {
    let dead_id = VarId::fresh_binding();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("a", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Let {
            name: "__20".to_string(),
            id: Some(dead_id),
            value: PBox::new(PseudoExpr::Error { message: None }),
            body: PBox::new(PseudoExpr::Error { message: None }),
        }),
    };
    let collapsed = collapse_dead_fail_chain(expr);
    let PseudoExpr::Lambda { body, .. } = collapsed else {
        panic!("expected Lambda")
    };
    assert!(matches!(*body, PseudoExpr::Error { .. }));
}
