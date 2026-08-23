use super::*;
use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `when subject is { _ -> Void; _ -> fail }` — a total-match assertion.
fn check() -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(var("datum", 5)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::error(),
            },
        ],
    }
}

fn entry(inner: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("script_context", VarId::new(2))],
            body: PBox::new(inner),
        }),
        body: PBox::new(PseudoExpr::Unit),
    }
}

fn bind(value: PseudoExpr, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "check_variant".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(value),
        body: PBox::new(body),
    }
}

fn is_seq(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Apply { function, args }
        if args.len() == 2
            && matches!(function.as_ref(), PseudoExpr::BuiltinCall { name, args: ba }
                if *name == crate::BuiltinId::Seq && ba.is_empty()))
}

fn inner_of(entry_expr: &PseudoExpr) -> &PseudoExpr {
    let PseudoExpr::Let { value, .. } = entry_expr else {
        panic!("expected the entry Let");
    };
    let PseudoExpr::Lambda { body, .. } = value.as_ref() else {
        panic!("expected the entry Lambda");
    };
    body
}

#[test]
fn unnames_an_unread_check() {
    let out = unname_discarded_check(entry(bind(check(), PseudoExpr::Unit)));
    assert!(
        is_seq(inner_of(&out)),
        "the check must become a statement: {out:?}"
    );
}

/// The check still runs — it is the first statement, not dropped.
#[test]
fn keeps_the_check_itself() {
    let out = unname_discarded_check(entry(bind(check(), PseudoExpr::Unit)));
    let PseudoExpr::Apply { args, .. } = inner_of(&out) else {
        panic!("expected the Seq");
    };
    assert!(
        matches!(args[0], PseudoExpr::When { .. }),
        "the assertion must survive as statement one: {out:?}"
    );
}

#[test]
fn keeps_a_binding_something_reads() {
    let out = unname_discarded_check(entry(bind(check(), var("check_variant", 10))));
    assert!(
        matches!(inner_of(&out), PseudoExpr::Let { .. }),
        "a read binder keeps its name: {out:?}"
    );
}

/// A `Var` may carry no id and resolve by name, so the name tally has to
/// agree too.
#[test]
fn keeps_a_binding_read_only_by_name() {
    let by_name = PseudoExpr::Var {
        name: "check_variant".to_string(),
        id: None,
    };
    let out = unname_discarded_check(entry(bind(check(), by_name)));
    assert!(
        matches!(inner_of(&out), PseudoExpr::Let { .. }),
        "an id-less read is still a read: {out:?}"
    );
}

/// A scalar value printed bare reads like a mistake — and if it were
/// pure the dead-let sweep would already have removed the binding.
#[test]
fn leaves_a_scalar_value_named() {
    let out = unname_discarded_check(entry(bind(PseudoExpr::int(1), PseudoExpr::Unit)));
    assert!(
        matches!(inner_of(&out), PseudoExpr::Let { .. }),
        "only block-shaped checks are unnamed: {out:?}"
    );
}

/// Without the validator marker the tree may be a fragment whose readers
/// live outside it.
#[test]
fn abstains_without_the_validator_marker() {
    let expr = bind(check(), PseudoExpr::Unit);
    let out = unname_discarded_check(expr);
    assert!(matches!(out, PseudoExpr::Let { .. }), "{out:?}");
}
