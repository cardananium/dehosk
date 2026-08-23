use super::*;
use crate::pseudo::nameless::{NamelessExpr, VarMetadata};
use num_bigint::BigInt;

fn id() -> VarId {
    VarId::fresh_compat_placeholder()
}

#[test]
fn closed_int_literal_passes() {
    let expr = NamelessExpr::Int(BigInt::from(7));
    let result = validate_nameless_invariants(&expr, &HashSet::new());
    assert!(result.is_ok());
}

#[test]
fn lambda_param_binds_body_var() {
    let p = id();
    let expr = NamelessExpr::Lambda {
        params: vec![p],
        body: Box::new(NamelessExpr::Var(p)),
    };
    let result = validate_nameless_invariants(&expr, &HashSet::new());
    assert!(
        result.is_ok(),
        "expected closed: free={:?}",
        result.free_vars
    );
}

#[test]
fn unbound_var_is_flagged_as_free() {
    let unknown = id();
    let expr = NamelessExpr::Var(unknown);
    let result = validate_nameless_invariants(&expr, &HashSet::new());
    assert!(!result.is_ok());
    assert_eq!(result.free_vars, vec![unknown]);
}

#[test]
fn entry_params_are_treated_as_bound() {
    let entry = id();
    let mut entry_set = HashSet::new();
    entry_set.insert(entry);

    let expr = NamelessExpr::Var(entry);
    let result = validate_nameless_invariants(&expr, &entry_set);
    assert!(result.is_ok());
}

#[test]
fn let_binding_scopes_body() {
    let x = id();
    let expr = NamelessExpr::Let {
        binder: x,
        value: Box::new(NamelessExpr::Int(BigInt::from(1))),
        body: Box::new(NamelessExpr::Var(x)),
    };
    let result = validate_nameless_invariants(&expr, &HashSet::new());
    assert!(result.is_ok());
}

#[test]
fn let_binding_does_not_scope_value() {
    // let x = x in 0 — `x` in the value position is free
    let x = id();
    let expr = NamelessExpr::Let {
        binder: x,
        value: Box::new(NamelessExpr::Var(x)),
        body: Box::new(NamelessExpr::Int(BigInt::from(0))),
    };
    let result = validate_nameless_invariants(&expr, &HashSet::new());
    assert!(!result.is_ok());
    assert!(result.free_vars.contains(&x));
}

#[test]
fn when_constructor_pattern_binds_clause_body() {
    let payload = id();
    let pattern = NamelessPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: vec![payload],
        shape: crate::pseudo::constructor::ConstructorShape::unknown_data(0, 1),
    };
    let when = NamelessExpr::When {
        subject: Box::new(NamelessExpr::Unit),
        subject_name: None,
        clauses: vec![NamelessClause {
            pattern,
            guard: None,
            body: NamelessExpr::Var(payload),
        }],
    };
    let result = validate_nameless_invariants(&when, &HashSet::new());
    assert!(result.is_ok(), "free={:?}", result.free_vars);
}

#[test]
fn when_clause_scope_does_not_leak_to_sibling() {
    // when subject is { Constr<0>(x) -> x; _ -> x } — second arm's
    // `x` is free since it's bound only in the Constr arm.
    let x = id();
    let when = NamelessExpr::When {
        subject: Box::new(NamelessExpr::Unit),
        subject_name: None,
        clauses: vec![
            NamelessClause {
                pattern: NamelessPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![x],
                    shape: crate::pseudo::constructor::ConstructorShape::unknown_data(0, 1),
                },
                guard: None,
                body: NamelessExpr::Var(x),
            },
            NamelessClause {
                pattern: NamelessPattern::Wildcard,
                guard: None,
                body: NamelessExpr::Var(x),
            },
        ],
    };
    let result = validate_nameless_invariants(&when, &HashSet::new());
    assert!(!result.is_ok());
    assert!(result.free_vars.contains(&x));
}

#[test]
fn list_pattern_head_and_tail_bind_clause_body() {
    let h = id();
    let t = id();
    let when = NamelessExpr::When {
        subject: Box::new(NamelessExpr::Unit),
        subject_name: None,
        clauses: vec![NamelessClause {
            pattern: NamelessPattern::List {
                elements: vec![h],
                tail: Some(t),
            },
            guard: None,
            body: NamelessExpr::Apply {
                function: Box::new(NamelessExpr::Var(h)),
                args: vec![NamelessExpr::Var(t)],
            },
        }],
    };
    let result = validate_nameless_invariants(&when, &HashSet::new());
    assert!(result.is_ok(), "free={:?}", result.free_vars);
}

#[test]
fn render_name_sets_prefer_display_name_hint_over_source_hint() {
    let binder = id();
    let orphan = id();
    let mut table = VarTable::new();
    table.insert(binder, VarMetadata::user(Some("tmp_field".to_string())));
    table.get_mut(binder).unwrap().display_name_hint = Some("field_2".to_string());
    table.insert(orphan, VarMetadata::user(Some("tmp_orphan".to_string())));
    table.get_mut(orphan).unwrap().display_name_hint = Some("field_2".to_string());

    let expr = NamelessExpr::Let {
        binder,
        value: Box::new(NamelessExpr::Unit),
        body: Box::new(NamelessExpr::Var(orphan)),
    };

    let binder_names = nameless_render_binder_name_set(&expr, &table);
    let var_names = nameless_render_var_name_set(&expr, &table);
    let orphan_names = nameless_render_orphan_name_set(&expr, &table);

    assert!(binder_names.contains("field_2"));
    assert!(!binder_names.contains("tmp_field"));
    assert!(var_names.contains("field_2"));
    assert!(!var_names.contains("tmp_orphan"));
    assert!(orphan_names.contains("field_2"));
    assert!(!orphan_names.contains("tmp_orphan"));
}

#[test]
fn render_binder_name_set_includes_when_pattern_binders() {
    let subject = id();
    let constructor_field = id();
    let list_head = id();
    let list_tail = id();
    let pair_left = id();
    let pair_right = id();
    let mut table = VarTable::new();
    for (id, name) in [
        (subject, "subject"),
        (constructor_field, "payload"),
        (list_head, "head"),
        (list_tail, "tail"),
        (pair_left, "left"),
        (pair_right, "right"),
    ] {
        table.insert(id, VarMetadata::user(Some(name.to_string())));
    }

    let when = NamelessExpr::When {
        subject: Box::new(NamelessExpr::Unit),
        subject_name: Some(subject),
        clauses: vec![
            NamelessClause {
                pattern: NamelessPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![constructor_field],
                    shape: crate::pseudo::constructor::ConstructorShape::unknown_data(0, 1),
                },
                guard: None,
                body: NamelessExpr::Unit,
            },
            NamelessClause {
                pattern: NamelessPattern::List {
                    elements: vec![list_head],
                    tail: Some(list_tail),
                },
                guard: None,
                body: NamelessExpr::Unit,
            },
            NamelessClause {
                pattern: NamelessPattern::Pair(pair_left, pair_right),
                guard: None,
                body: NamelessExpr::Unit,
            },
        ],
    };

    let binder_names = nameless_render_binder_name_set(&when, &table);
    for name in ["subject", "payload", "head", "tail", "left", "right"] {
        assert!(binder_names.contains(name), "missing binder name {name}");
    }
}

#[test]
fn stable_orphan_count_with_new_var_id_trips_guard() {
    let baseline_orphan = id();
    let introduced_orphan = id();
    let before = NamelessExpr::Var(baseline_orphan);
    let after = NamelessExpr::Var(introduced_orphan);
    let baseline_free_vars = nameless_free_var_id_set(&before);

    assert_eq!(baseline_free_vars.len(), 1);
    assert_eq!(nameless_free_var_id_set(&after).len(), 1);
    assert!(
        nameless_introduces_new_free_var_ids(&after, &baseline_free_vars),
        "stable orphan count with a different VarId must still trip the nameless guard"
    );
}

#[test]
fn rec_fn_self_reference_resolves() {
    let f = id();
    let p = id();
    let expr = NamelessExpr::RecFn {
        name: f,
        params: vec![p],
        body: Box::new(NamelessExpr::Apply {
            function: Box::new(NamelessExpr::Var(f)),
            args: vec![NamelessExpr::Var(p)],
        }),
    };
    let result = validate_nameless_invariants(&expr, &HashSet::new());
    assert!(result.is_ok(), "free={:?}", result.free_vars);
}
