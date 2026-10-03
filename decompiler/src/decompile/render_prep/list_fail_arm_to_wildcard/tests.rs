use super::*;
use crate::pseudo::ast::{Binder, PBox};
use crate::pseudo::var_id::VarId;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}
fn clause(pattern: WhenPattern, body: PseudoExpr) -> WhenClause {
    WhenClause {
        pattern,
        guard: None,
        body,
    }
}
fn nil() -> WhenPattern {
    WhenPattern::List {
        elements: vec![],
        tail: None,
    }
}
fn cons() -> WhenPattern {
    WhenPattern::List {
        elements: vec![Binder::new("h", VarId::new(2))],
        tail: Some(Binder::new("t", VarId::new(3))),
    }
}
fn fail() -> PseudoExpr {
    PseudoExpr::Error { message: None }
}
fn when(clauses: Vec<WhenClause>) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(var("xs", 1)),
        subject_name: None,
        clauses,
    }
}

#[test]
fn nil_fail_arm_becomes_wildcard_fallthrough() {
    let before = when(vec![
        clause(nil(), fail()),
        clause(cons(), var("h", 2)),
    ]);
    let after = when(vec![
        clause(cons(), var("h", 2)),
        clause(WhenPattern::Wildcard, fail()),
    ]);
    assert_eq!(list_fail_arm_to_wildcard(before), after);
}

#[test]
fn non_failing_nil_arm_is_kept() {
    let e = when(vec![
        clause(nil(), var("z", 9)),
        clause(cons(), var("h", 2)),
    ]);
    assert_eq!(list_fail_arm_to_wildcard(e.clone()), e);
}
