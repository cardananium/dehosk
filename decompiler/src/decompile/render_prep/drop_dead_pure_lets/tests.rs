use super::*;
use crate::pseudo::ast::{Binder, WhenClause};

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name, VarId::new(id))
}
fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}
/// `fn match_subject(v) { rec fn self(x) { v(self, x) } }` — a dead
/// helper: a Lambda wrapping a RecFn.
fn lambda_recfn() -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder("v", 1)],
        body: PBox::new(PseudoExpr::RecFn {
            name: binder("self", 2),
            params: vec![binder("x", 3)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("v", 1)),
                args: vec![var("self", 2), var("x", 3)].into(),
            }),
        }),
    }
}

#[test]
fn lambda_with_recfn_body_is_droppable() {
    assert!(is_pure(&lambda_recfn()));
}

/// The BUILTIN encoding of `fail` (`BuiltinCall(Error)`) is a runtime
/// abort, never pure: a dead strict `let x = <builtin error>` must not
/// be deleted, or the program is silently un-failed.
#[test]
fn builtin_error_call_is_not_pure() {
    let e = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::Error,
        args: vec![].into(),
    };
    assert!(!is_pure(&e));
    assert!(!is_pure(&PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::Trace,
        args: vec![PseudoExpr::int(1)].into(),
    }));
}

#[test]
fn lambda_with_if_body_is_droppable() {
    // `fn c_46(x, y) { if x < y { e } else { b } }`
    let l = PseudoExpr::Lambda {
        params: vec![binder("x", 1), binder("y", 2)],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: crate::pseudo::ast::BinaryOp::Lt,
                left: PBox::new(var("x", 1)),
                right: PBox::new(var("y", 2)),
            }),
            then_branch: PBox::new(var("e", 10)),
            else_branch: PBox::new(var("b", 11)),
        }),
    };
    assert!(is_pure(&l));
}

#[test]
fn lambda_with_trace_body_is_kept() {
    let l = PseudoExpr::Lambda {
        params: vec![],
        body: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::String("m".into())),
            value: PBox::new(var("x", 1)),
        }),
    };
    assert!(!is_pure(&l), "a dead fn carrying a trace must be kept");
}

#[test]
fn lambda_with_error_body_is_kept() {
    let l = PseudoExpr::Lambda {
        params: vec![],
        body: PBox::new(PseudoExpr::Error {
            message: Some("boom".into()),
        }),
    };
    assert!(!is_pure(&l), "a dead fn carrying a fail must be kept");
}

#[test]
fn builtin_form_fail_in_lambda_body_is_kept() {
    // `fn f() { fail }` where fail is the builtin form `BuiltinCall(Error)`.
    let l = PseudoExpr::Lambda {
        params: vec![],
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::Error,
            args: vec![].into(),
        }),
    };
    assert!(
        !is_pure(&l),
        "a dead fn carrying a builtin fail must be kept"
    );
}

#[test]
fn trace_inside_when_literal_pattern_is_detected() {
    // A `trace` hidden in a `WhenPattern::Literal` must keep the dead fn.
    let l = PseudoExpr::Lambda {
        params: vec![binder("x", 1)],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(var("x", 1)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Literal(PseudoExpr::Trace {
                    message: PBox::new(PseudoExpr::String("m".into())),
                    value: PBox::new(PseudoExpr::Bool(true)),
                }),
                guard: None,
                body: var("x", 1),
            }],
        }),
    };
    assert!(
        !is_pure(&l),
        "a trace inside a When literal pattern must be detected"
    );
}

#[test]
fn binder_referenced_only_in_when_literal_pattern_is_not_dead() {
    // The drop guard must see a ref inside a `WhenPattern::Literal`.
    let body = PseudoExpr::When {
        subject: PBox::new(var("subj", 5)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Literal(var("match_subject_44", 44)),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };
    assert!(contains_var_id(&body, VarId::new(44)));
    assert!(contains_var_name(&body, "match_subject_44"));
}

#[test]
fn bare_recfn_value_is_still_refused() {
    // A RecFn bound DIRECTLY (not wrapped in a Lambda) stays excluded —
    // dropping a recursive helper risks a hoisted/inlined external use.
    let rf = PseudoExpr::RecFn {
        name: binder("self", 1),
        params: vec![binder("x", 2)],
        body: PBox::new(var("x", 2)),
    };
    assert!(!is_pure(&rf));
}

#[test]
fn dead_lambda_def_is_dropped_end_to_end() {
    // `let match_subject_44 = <lambda>; <body not referencing it>` under a
    // `decompiled` marker → the dead def is removed.
    let dead = PseudoExpr::Let {
        name: "match_subject_44".into(),
        id: Some(VarId::new(44)),
        value: PBox::new(lambda_recfn()),
        body: PBox::new(var("keep", 99)),
    };
    let wrapped = PseudoExpr::Let {
        name: "decompiled".into(),
        id: Some(VarId::new(1000)),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(dead),
    };
    let out = drop_dead_pure_lets(wrapped);
    assert_eq!(
        out,
        PseudoExpr::Let {
            name: "decompiled".into(),
            id: Some(VarId::new(1000)),
            value: PBox::new(PseudoExpr::Unit),
            body: PBox::new(var("keep", 99)),
        }
    );
}

#[test]
fn used_lambda_def_is_kept_end_to_end() {
    // If the body references the binder, it must NOT be dropped.
    let used = PseudoExpr::Let {
        name: "match_subject_44".into(),
        id: Some(VarId::new(44)),
        value: PBox::new(lambda_recfn()),
        body: PBox::new(var("match_subject_44", 44)),
    };
    let wrapped = PseudoExpr::Let {
        name: "decompiled".into(),
        id: Some(VarId::new(1000)),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(used.clone()),
    };
    let out = drop_dead_pure_lets(wrapped);
    if let PseudoExpr::Let { body, .. } = out {
        assert!(
            matches!(*body, PseudoExpr::Let { .. }),
            "used def must survive"
        );
    } else {
        panic!("expected outer decompiled Let");
    }
}
