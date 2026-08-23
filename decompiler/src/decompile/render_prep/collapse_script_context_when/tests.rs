use super::*;
use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

fn entry_let(sc_id: VarId, body: PseudoExpr, name: &str) -> PseudoExpr {
    PseudoExpr::Let {
        name: name.to_string(),
        id: Some(VarId::fresh_binding()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("redeemer", VarId::fresh_binding()),
                Binder::new("script_context", sc_id),
            ],
            body: PBox::new(body),
        }),
        body: PBox::new(PseudoExpr::Unit),
    }
}

fn single_arm_when(sc_id: VarId, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![],
                shape: ConstructorShape::unknown_data(0, 0),
            },
            body,
        )],
    }
}

#[test]
fn collapses_inside_validator_block() {
    // let decompiled = fn(redeemer, script_context) {
    //   when script_context is { K -> body }
    // } in Unit
    let sc_id = VarId::fresh_binding();
    let body = PseudoExpr::int(42);
    let when_expr = single_arm_when(sc_id, body.clone());
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    // Drill into the wrapped lambda to confirm the when is gone.
    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(
        matches!(*body, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(42)),
        "expected body to collapse to Int(42), got: {body:?}"
    );
}

#[test]
fn leaves_when_when_no_validator_block() {
    // Enclosing let is `helper`, not `decompiled` — no
    // validator block was emitted, so nothing collapses.
    let sc_id = VarId::fresh_binding();
    let body = PseudoExpr::int(42);
    let when_expr = single_arm_when(sc_id, body);
    let expr = entry_let(sc_id, when_expr, "helper");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    // when stays intact
    assert!(matches!(*body, PseudoExpr::When { .. }));
}

#[test]
fn leaves_when_with_multiple_clauses() {
    // when script_context is { K1 -> a; K2 -> b }
    // — two-clause when must not collapse.
    let sc_id = VarId::fresh_binding();
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(0, 0),
                },
                PseudoExpr::int(1),
            ),
            WhenClause::new(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 1,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(1, 0),
                },
                PseudoExpr::int(2),
            ),
        ],
    };
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(matches!(*body, PseudoExpr::When { .. }));
}

#[test]
fn collapses_when_trailing_wildcard_has_arbitrary_body() {
    // when script_context is { K -> 1; _ -> 2 }
    // — the wildcard is unreachable for single-variant
    // ScriptContext, so the productive arm wins whatever the
    // wildcard body holds.
    let sc_id = VarId::fresh_binding();
    let productive_body = PseudoExpr::int(1);
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(0, 0),
                },
                productive_body.clone(),
            ),
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::int(2)),
        ],
    };
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(
        matches!(*body, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(1)),
        "expected body to collapse to productive arm Int(1), got: {body:?}"
    );
}

#[test]
fn leaves_when_when_pattern_binds_fields() {
    // when script_context is { K(field1, field2) -> body }
    // — pattern binds fields; collapsing would drop the bindings.
    let sc_id = VarId::fresh_binding();
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![
                    Binder::new("field1", VarId::fresh_binding()),
                    Binder::new("field2", VarId::fresh_binding()),
                ],
                shape: ConstructorShape::unknown_data(0, 2),
            },
            PseudoExpr::var("field1"),
        )],
    };
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(matches!(*body, PseudoExpr::When { .. }));
}

#[test]
fn leaves_when_when_subject_is_not_script_context() {
    // when other_var is { K -> body } — subject is not the
    // validator's script_context param.
    let sc_id = VarId::fresh_binding();
    let other_id = VarId::fresh_binding();
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("other_var", other_id)),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![],
                shape: ConstructorShape::unknown_data(0, 0),
            },
            PseudoExpr::int(42),
        )],
    };
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(matches!(*body, PseudoExpr::When { .. }));
}

#[test]
fn collapses_when_trailing_wildcard_is_fail() {
    // when script_context is { K -> body; _ -> fail }
    // — trailing wildcard bodied by `error`, the usual
    // exhaustiveness filler, unreachable here; collapse.
    let sc_id = VarId::fresh_binding();
    let body = PseudoExpr::int(42);
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(0, 0),
                },
                body.clone(),
            ),
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::Error { message: None }),
        ],
    };
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body: lam_body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(
        matches!(*lam_body, PseudoExpr::Int(ref n) if n == &num_bigint::BigInt::from(42)),
        "expected body to collapse to Int(42), got: {lam_body:?}"
    );
}

#[test]
fn leaves_when_with_two_productive_arms_and_one_fail() {
    // when script_context is { K1 -> a; K2 -> b; _ -> fail }
    // — two productive arms: no collapse, fail tail or not.
    let sc_id = VarId::fresh_binding();
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(0, 0),
                },
                PseudoExpr::int(1),
            ),
            WhenClause::new(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 1,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(1, 0),
                },
                PseudoExpr::int(2),
            ),
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::Error { message: None }),
        ],
    };
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(matches!(*body, PseudoExpr::When { .. }));
}

#[test]
fn leaves_when_with_wildcard_before_constructor() {
    // when script_context is { _ -> a; K -> b }
    // — the wildcard matches first, shadowing the productive
    // Constructor, so no collapse.
    let sc_id = VarId::fresh_binding();
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::int(99)),
            WhenClause::new(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(0, 0),
                },
                PseudoExpr::int(1),
            ),
        ],
    };
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(matches!(*body, PseudoExpr::When { .. }));
}

#[test]
fn leaves_when_with_subject_alias() {
    // when script_context as ctx is { K -> body }
    // — alias `ctx` would dangle if the when collapsed. Bail.
    let sc_id = VarId::fresh_binding();
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
        subject_name: Some(Binder::new("ctx", VarId::fresh_binding())),
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![],
                shape: ConstructorShape::unknown_data(0, 0),
            },
            PseudoExpr::int(42),
        )],
    };
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(matches!(*body, PseudoExpr::When { .. }));
}

#[test]
fn leaves_when_with_nonzero_constructor_tag() {
    // when script_context is { K1 -> body; _ -> fail }
    // — tag=1 is impossible for ScriptContext (only variant is
    // tag=0), so collapsing would select unreachable code.
    let sc_id = VarId::fresh_binding();
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::Constructor {
                    type_hint: None,
                    tag: 1,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(1, 0),
                },
                PseudoExpr::int(1),
            ),
            WhenClause::new(WhenPattern::wildcard(), PseudoExpr::Error { message: None }),
        ],
    };
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(matches!(*body, PseudoExpr::When { .. }));
}

#[test]
fn leaves_when_with_guard() {
    // when script_context is { K if cond -> body } — guarded
    // clause, don't collapse.
    let sc_id = VarId::fresh_binding();
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![],
                shape: ConstructorShape::unknown_data(0, 0),
            },
            guard: Some(PseudoExpr::Bool(true)),
            body: PseudoExpr::int(42),
        }],
    };
    let expr = entry_let(sc_id, when_expr, "decompiled");
    let result = collapse_script_context_when(expr);

    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected Let")
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!("expected Lambda")
    };
    assert!(matches!(*body, PseudoExpr::When { .. }));
}
