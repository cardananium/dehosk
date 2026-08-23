use super::*;
use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

#[test]
fn collapses_empty_when_to_subject() {
    // when (fail @"PT2") is { }   →   fail @"PT2"
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Error {
            message: Some("PT2".into()),
        }),
        subject_name: None,
        clauses: vec![],
    };
    let out = collapse_empty_when(expr);
    match out {
        PseudoExpr::Error { message } => assert_eq!(message.as_deref(), Some("PT2")),
        _ => panic!("expected the subject `fail @\"PT2\"`, got {:?}", out),
    }
}

#[test]
fn collapses_empty_when_over_var_subject() {
    // when variant_24 is { }   →   variant_24
    let vid = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("variant_24", vid)),
        subject_name: Some(Binder::new("s", VarId::fresh_binding())),
        clauses: vec![],
    };
    let out = collapse_empty_when(expr);
    assert!(matches!(out, PseudoExpr::Var { .. }));
}

#[test]
fn leaves_non_empty_when_untouched() {
    let vid = VarId::fresh_binding();
    let when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", vid)),
        subject_name: None,
        clauses: vec![WhenClause::new(WhenPattern::Wildcard, PseudoExpr::int(1))],
    };
    let out = collapse_empty_when(when);
    assert!(matches!(out, PseudoExpr::When { .. }));
}

#[test]
fn collapses_recursively_in_nested_position() {
    // f(when Y is { }) with Y = fail   →   f(fail)
    let inner = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Error { message: None }),
        subject_name: None,
        clauses: vec![],
    };
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", VarId::fresh_binding())),
        args: vec![inner].into(),
    };
    let out = collapse_empty_when(expr);
    let PseudoExpr::Apply { args, .. } = out else {
        panic!("expected Apply")
    };
    assert!(matches!(args[0], PseudoExpr::Error { .. }));
}
