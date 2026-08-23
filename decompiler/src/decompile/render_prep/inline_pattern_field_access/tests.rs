use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

fn fields_head(record: PseudoExpr) -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(record),
            selector: FieldSelector::NamedField("fields".to_string()),
        }),
        selector: FieldSelector::ListHead,
    }
}

fn fields_index(record: PseudoExpr, idx: usize) -> PseudoExpr {
    PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(record),
            selector: FieldSelector::NamedField("fields".to_string()),
        }),
        index: idx,
    }
}

#[test]
fn substitutes_fields_head_with_pattern_binder_0() {
    let subject_id = VarId::new(20000);
    let arg0_id = VarId::new(20001);
    let arg1_id = VarId::new(20002);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("ctx", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![
                    Binder::new("tx_info", arg0_id),
                    Binder::new("purpose", arg1_id),
                ],
                shape: ConstructorShape::unknown_data(0, 2),
            },
            guard: None,
            body: fields_head(PseudoExpr::var_with_id("ctx", subject_id)),
        }],
    };

    let rewritten = inline_pattern_field_access(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let body = &clauses[0].body;
    // body should be `Var("tx_info", arg0_id)`.
    let PseudoExpr::Var { name, id: Some(id) } = body else {
        panic!("expected Var, got {:?}", body);
    };
    assert_eq!(name, "tx_info");
    assert_eq!(*id, arg0_id);
}

#[test]
fn substitutes_fields_index_with_pattern_binder_n() {
    let subject_id = VarId::new(21000);
    let arg0_id = VarId::new(21001);
    let arg1_id = VarId::new(21002);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("ctx", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![
                    Binder::new("first", arg0_id),
                    Binder::new("second", arg1_id),
                ],
                shape: ConstructorShape::unknown_data(0, 2),
            },
            guard: None,
            // body = ctx.fields[1] — should become Var("second", arg1_id).
            body: fields_index(PseudoExpr::var_with_id("ctx", subject_id), 1),
        }],
    };

    let rewritten = inline_pattern_field_access(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let PseudoExpr::Var { name, id: Some(id) } = &clauses[0].body else {
        panic!("expected Var, got {:?}", clauses[0].body);
    };
    assert_eq!(name, "second");
    assert_eq!(*id, arg1_id);
}

#[test]
fn promotes_underscore_binder_when_field_is_accessed() {
    // Promote the `_` binder to `field_{i}` and substitute the
    // access, recovering a name for the otherwise-discarded field.
    let subject_id = VarId::new(22000);
    let arg0_id = VarId::new(22001);
    let arg1_id = VarId::new(22002);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("ctx", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![Binder::new("_", arg0_id), Binder::new("named", arg1_id)],
                shape: ConstructorShape::unknown_data(0, 2),
            },
            guard: None,
            body: fields_head(PseudoExpr::var_with_id("ctx", subject_id)),
        }],
    };

    let rewritten = inline_pattern_field_access(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    // The binder at field 0 should be renamed from "_" to "field_0".
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!()
    };
    assert_eq!(
        fields[0].to_string(),
        "field_0",
        "underscore binder must be promoted"
    );
    // Body should now be `Var("field_0", arg0_id)`.
    let PseudoExpr::Var { name, id: Some(id) } = &clauses[0].body else {
        panic!(
            "expected Var after promotion + substitution, got {:?}",
            clauses[0].body
        );
    };
    assert_eq!(name, "field_0");
    assert_eq!(*id, arg0_id);
}

#[test]
fn does_not_promote_underscore_when_field_is_not_accessed() {
    // `_` binder stays as `_` if the body doesn't access that field.
    // Avoids spurious renames in the pattern.
    let subject_id = VarId::new(22100);
    let arg0_id = VarId::new(22101);
    let arg1_id = VarId::new(22102);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("ctx", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![Binder::new("_", arg0_id), Binder::new("named", arg1_id)],
                shape: ConstructorShape::unknown_data(0, 2),
            },
            guard: None,
            // Body uses `named` but NOT subject.fields.head.
            body: PseudoExpr::var_with_id("named", arg1_id),
        }],
    };

    let rewritten = inline_pattern_field_access(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!()
    };
    assert_eq!(fields[0].to_string(), "_", "underscore stays when unused");
}

#[test]
fn does_not_substitute_outside_when_clause() {
    // FieldAccess at top level (no enclosing When) — no substitution.
    let subject_id = VarId::new(23000);
    let expr = fields_head(PseudoExpr::var_with_id("ctx", subject_id));

    let rewritten = inline_pattern_field_access(expr);
    assert!(
        matches!(rewritten, PseudoExpr::FieldAccess { .. }),
        "field access outside When must NOT substitute"
    );
}

#[test]
fn substitution_inside_let_value_drops_alias() {
    // `when ctx is { C(payload) -> let head = ctx.fields.head in head }`
    // After substitution the let is a redundant alias and is dropped,
    // leaving `payload`.
    let subject_id = VarId::new(24000);
    let arg0_id = VarId::new(24001);
    let head_id = VarId::new(24002);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("ctx", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![Binder::new("payload", arg0_id)],
                shape: ConstructorShape::unknown_data(0, 1),
            },
            guard: None,
            body: PseudoExpr::Let {
                name: "head".to_string(),
                id: Some(head_id),
                value: PBox::new(fields_head(PseudoExpr::var_with_id("ctx", subject_id))),
                body: PBox::new(PseudoExpr::var_with_id("head", head_id)),
            },
        }],
    };

    let rewritten = inline_pattern_field_access(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    // After alias drop: body IS the substituted Var(payload).
    let PseudoExpr::Var { name, id: Some(id) } = &clauses[0].body else {
        panic!(
            "expected let alias collapsed to Var, got {:?}",
            clauses[0].body
        );
    };
    assert_eq!(name, "payload");
    assert_eq!(*id, arg0_id);
}

#[test]
fn alias_drop_skips_self_referential_let() {
    // `let X = Var(X)` self-reference must NOT drop — that would
    // erase a value the renderer may still need.
    let x_id = VarId::new(24100);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    let rewritten = inline_pattern_field_access(expr);
    // Self-referential let must remain as a Let, not be collapsed.
    assert!(
        matches!(rewritten, PseudoExpr::Let { .. }),
        "self-referential let must not be dropped, got {:?}",
        rewritten
    );
}

#[test]
fn nested_when_clauses_extend_scope() {
    // `when outer is { C(a) -> when inner is { D(b) -> outer.fields.head } }`
    // Should substitute the outer.fields.head with Var(a) even from inside
    // the inner clause.
    let outer_id = VarId::new(25000);
    let inner_id = VarId::new(25001);
    let a_id = VarId::new(25002);
    let b_id = VarId::new(25003);
    let inner_when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("inner", inner_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![Binder::new("b", b_id)],
                shape: ConstructorShape::unknown_data(0, 1),
            },
            guard: None,
            body: fields_head(PseudoExpr::var_with_id("outer", outer_id)),
        }],
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("outer", outer_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![Binder::new("a", a_id)],
                shape: ConstructorShape::unknown_data(0, 1),
            },
            guard: None,
            body: inner_when,
        }],
    };

    let rewritten = inline_pattern_field_access(expr);
    let PseudoExpr::When {
        clauses: outer_clauses,
        ..
    } = rewritten
    else {
        panic!()
    };
    let PseudoExpr::When {
        clauses: inner_clauses,
        ..
    } = &outer_clauses[0].body
    else {
        panic!("expected nested When");
    };
    let PseudoExpr::Var { name, id: Some(id) } = &inner_clauses[0].body else {
        panic!("expected Var, got {:?}", inner_clauses[0].body);
    };
    assert_eq!(
        name, "a",
        "outer scope `a` should be reachable from inner When"
    );
    assert_eq!(*id, a_id);
}

#[test]
fn expands_pattern_when_body_accesses_field_beyond_declared_arity() {
    // `when subject is { Constructor() -> subject.fields[2] }` — the
    // pattern declares arity 0 but the body accesses field 2. Must
    // expand the pattern to `Constructor(field_0, field_1, field_2)`
    // and substitute the access with `Var(field_2)`.
    let subject_id = VarId::new(26000);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: Vec::new(), // declared arity 0
                shape: ConstructorShape::unknown_data(0, 0),
            },
            guard: None,
            body: fields_index(PseudoExpr::var_with_id("subject", subject_id), 2),
        }],
    };

    let rewritten = inline_pattern_field_access(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let WhenPattern::Constructor { fields, shape, .. } = &clauses[0].pattern else {
        panic!()
    };
    // Pattern expanded to 3 binders: field_0, field_1, field_2.
    assert_eq!(fields.len(), 3, "expected expansion to arity 3");
    assert_eq!(fields[2].to_string(), "field_2");
    // Shape's arity must also be updated.
    assert!(
        matches!(shape, ConstructorShape::Unknown { arity: 3, .. }),
        "shape arity must be 3 after expansion, got {:?}",
        shape
    );
    // Body should be `Var("field_2", ...)`.
    let PseudoExpr::Var { name, id: Some(_) } = &clauses[0].body else {
        panic!("expected Var after expansion, got {:?}", clauses[0].body);
    };
    assert_eq!(name, "field_2");
}

#[test]
fn inlines_subject_fields_alias_then_expands_pattern() {
    // `when subject is { Constructor() ->
    //   let fields = subject.fields
    //   let f_0 = fields[0]
    //   ... }` — the pre-pass replaces the hoisted `fields` alias
    // with `subject.fields` and drops the let; the main pass then
    // expands the 0-arity pattern with a `field_0` binder and
    // substitutes the access.
    let subject_id = VarId::new(27000);
    let fields_alias_id = VarId::new(27001);
    let f0_id = VarId::new(27002);
    let fields_alias = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
        selector: FieldSelector::NamedField("fields".to_string()),
    };
    let body = PseudoExpr::Let {
        name: "fields".to_string(),
        id: Some(fields_alias_id),
        value: PBox::new(fields_alias),
        body: PBox::new(PseudoExpr::Let {
            name: "f_0".to_string(),
            id: Some(f0_id),
            value: PBox::new(PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::var_with_id("fields", fields_alias_id)),
                index: 0,
            }),
            body: PBox::new(PseudoExpr::var_with_id("f_0", f0_id)),
        }),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: Vec::new(),
                shape: ConstructorShape::unknown_data(0, 0),
            },
            guard: None,
            body,
        }],
    };

    let rewritten = inline_pattern_field_access(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    // Pattern should be expanded to arity 1 with a `field_0` binder.
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!()
    };
    assert_eq!(fields.len(), 1, "pattern must be expanded to arity 1");
    assert_eq!(fields[0].to_string(), "field_0");
    // Both lets are gone: the `fields` alias inlined, `let f_0 =
    // field_0` collapsed as a redundant alias, leaving Var(field_0).
    let PseudoExpr::Var { name, .. } = &clauses[0].body else {
        panic!(
            "expected fully-collapsed Var body, got {:?}",
            clauses[0].body
        );
    };
    assert_eq!(name, "field_0");
}

#[test]
fn does_not_expand_when_no_overflow_accesses() {
    // Body accesses field 0; pattern already declares 2 binders.
    // No expansion needed.
    let subject_id = VarId::new(26100);
    let arg0_id = VarId::new(26101);
    let arg1_id = VarId::new(26102);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![Binder::new("a", arg0_id), Binder::new("b", arg1_id)],
                shape: ConstructorShape::unknown_data(0, 2),
            },
            guard: None,
            body: fields_head(PseudoExpr::var_with_id("subject", subject_id)),
        }],
    };

    let rewritten = inline_pattern_field_access(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!()
    };
    assert_eq!(fields.len(), 2, "pattern must not be expanded");
}
