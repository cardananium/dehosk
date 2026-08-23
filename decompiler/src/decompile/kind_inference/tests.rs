use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::nameless::{VarMetadata, VarOrigin};

fn id() -> VarId {
    VarId::fresh_binding()
}

fn field_alias_value(parent: VarId, index: usize) -> PseudoExpr {
    PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::Var {
                name: "parent".to_string(),
                id: Some(parent),
            }),
            selector: FieldSelector::NamedField("fields".to_string()),
        }),
        index,
    }
}

fn seed_kind(table: &mut VarTable, id: VarId, name_hint: &str, kind: VarKind) {
    table.insert(
        id,
        VarMetadata {
            origin: VarOrigin::Synthetic {
                producer_pass: "test_seed",
            },
            name_hint: Some(name_hint.to_string()),
            display_name_hint: None,
            kind,
        },
    );
}

fn assert_clean_verifier_report(report: &KindVerificationReport) {
    assert!(
        report.conflicts.is_empty(),
        "unexpected verifier conflicts: {:?}",
        report.conflicts
    );
}

#[test]
fn field_n_alias_requires_mint_site_annotation() {
    let parent = id();
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "field_3".to_string(),
        id: Some(alias),
        value: PBox::new(field_alias_value(parent, 3)),
        body: PBox::new(PseudoExpr::Var {
            name: "field_3".to_string(),
            id: Some(alias),
        }),
    };

    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert!(
        report.conflicts.is_empty(),
        "missing mint-site FieldIndexAlias should not create verifier conflicts: {:?}",
        report.conflicts
    );
    assert!(
        !matches!(
            table.get(alias).map(|m| &m.kind),
            Some(VarKind::FieldIndexAlias { .. })
        ),
        "FieldIndexAlias should be populated only by the mint-site annotation"
    );
}

#[test]
fn skips_non_synthetic_name() {
    // Same shape but the binder name doesn't follow the
    // `field_N` convention — should NOT be tagged.
    let parent = id();
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "foo".to_string(),
        id: Some(alias),
        value: PBox::new(field_alias_value(parent, 1)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
    assert!(!matches!(
        table.get(alias).map(|m| &m.kind),
        Some(VarKind::FieldIndexAlias { .. })
    ));
}

#[test]
fn skips_field_n_with_wrong_value_shape() {
    // Name matches but the value is a plain Var, not the
    // index access shape — a user binding, don't tag.
    let parent = id();
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "field_5".to_string(),
        id: Some(alias),
        value: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(parent),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
}

#[test]
fn does_not_populate_nested_field_aliases_without_mint_site_annotations() {
    let parent = id();
    let alias_a = id();
    let alias_b = id();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("p", parent)],
        body: PBox::new(PseudoExpr::Let {
            name: "field_0".to_string(),
            id: Some(alias_a),
            value: PBox::new(field_alias_value(parent, 0)),
            body: PBox::new(PseudoExpr::Let {
                name: "field_2".to_string(),
                id: Some(alias_b),
                value: PBox::new(field_alias_value(parent, 2)),
                body: PBox::new(PseudoExpr::Unit),
            }),
        }),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
    assert!(!matches!(
        table.get(alias_a).map(|m| &m.kind),
        Some(VarKind::FieldIndexAlias { .. })
    ));
    assert!(!matches!(
        table.get(alias_b).map(|m| &m.kind),
        Some(VarKind::FieldIndexAlias { .. })
    ));
}

#[test]
fn does_not_overwrite_existing_specific_kind() {
    let parent = id();
    let alias = id();
    let mut table = VarTable::new();
    // Pre-populate with a different kind.
    table.insert(
        alias,
        VarMetadata {
            origin: VarOrigin::Synthetic {
                producer_pass: "test_seed",
            },
            name_hint: Some("preserved".to_string()),
            display_name_hint: None,
            kind: VarKind::DataLiteralHoist,
        },
    );

    let expr = PseudoExpr::Let {
        name: "field_1".to_string(),
        id: Some(alias),
        value: PBox::new(field_alias_value(parent, 1)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let report = verify_var_kinds(&expr, &table);
    assert_eq!(report.conflicts.len(), 1);
    let conflict = &report.conflicts[0];
    assert_eq!(conflict.id, alias);
    assert!(matches!(conflict.existing, VarKind::DataLiteralHoist));
    match conflict.inferred {
        VarKind::FieldIndexAlias {
            parent: actual_parent,
            index,
        } => {
            assert_eq!(actual_parent, parent);
            assert_eq!(index, 1);
        }
        _ => panic!("expected inferred FieldIndexAlias conflict"),
    }
    match table.get(alias).unwrap().kind {
        VarKind::DataLiteralHoist => {}
        _ => panic!("kind was overwritten"),
    }
    assert_eq!(
        table.get(alias).unwrap().name_hint.as_deref(),
        Some("preserved")
    );
}

#[test]
fn verifier_accepts_matching_existing_specific_kind() {
    let parent = id();
    let alias = id();
    let mut table = VarTable::new();
    table.insert(
        alias,
        VarMetadata {
            origin: VarOrigin::Synthetic {
                producer_pass: "test_seed",
            },
            name_hint: Some("field_1".to_string()),
            display_name_hint: None,
            kind: VarKind::FieldIndexAlias { parent, index: 1 },
        },
    );

    let expr = PseudoExpr::Let {
        name: "field_1".to_string(),
        id: Some(alias),
        value: PBox::new(field_alias_value(parent, 1)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let report = verify_var_kinds(&expr, &table);

    assert!(
        report.conflicts.is_empty(),
        "matching mint-site kind should not be reported as conflict: {:?}",
        report.conflicts
    );
    match table.get(alias).unwrap().kind {
        VarKind::FieldIndexAlias {
            parent: actual_parent,
            index,
        } => {
            assert_eq!(actual_parent, parent);
            assert_eq!(index, 1);
        }
        _ => panic!("existing kind was overwritten"),
    }
}

#[test]
fn does_not_promote_user_kind_to_field_index_alias() {
    // The verifier reports conflicts for existing specific kinds but
    // never promotes generic `User` metadata into FieldIndexAlias.
    let parent = id();
    let alias = id();
    let mut table = VarTable::new();
    table.insert(alias, VarMetadata::user(Some("field_4".to_string())));

    let expr = PseudoExpr::Let {
        name: "field_4".to_string(),
        id: Some(alias),
        value: PBox::new(field_alias_value(parent, 4)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
    assert!(matches!(table.get(alias).unwrap().kind, VarKind::User));
    assert_eq!(
        table.get(alias).unwrap().name_hint.as_deref(),
        Some("field_4")
    );
}

// =============================================================
// SliceTailAlias verification
// =============================================================

fn list_tail_call(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::builtins::BuiltinId::expect_known("List.tail"),
            args: vec![].into(),
        }),
        args: vec![arg].into(),
    }
}

#[test]
fn slice_tail_alias_requires_mint_site_annotation() {
    let parent = id();
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(alias),
        value: PBox::new(list_tail_call(PseudoExpr::Var {
            name: "fields".to_string(),
            id: Some(parent),
        })),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert!(
        report.conflicts.is_empty(),
        "missing mint-site SliceTailAlias should not create verifier conflicts: {:?}",
        report.conflicts
    );
    assert!(
        !matches!(
            table.get(alias).map(|m| &m.kind),
            Some(VarKind::SliceTailAlias { .. })
        ),
        "SliceTailAlias should be populated only by mint-site annotations"
    );
}

#[test]
fn verifier_accepts_matching_existing_slice_tail_alias_depth_1() {
    let parent = id();
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(alias),
        value: PBox::new(list_tail_call(PseudoExpr::Var {
            name: "fields".to_string(),
            id: Some(parent),
        })),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        alias,
        "r",
        VarKind::SliceTailAlias { parent, depth: 1 },
    );

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
}

#[test]
fn verifier_accepts_matching_existing_nested_slice_tail_chain_depth_3() {
    let parent = id();
    let alias = id();
    let value = list_tail_call(list_tail_call(list_tail_call(PseudoExpr::Var {
        name: "fields".to_string(),
        id: Some(parent),
    })));
    let expr = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(alias),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        alias,
        "r",
        VarKind::SliceTailAlias { parent, depth: 3 },
    );

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
}

#[test]
fn verifier_accumulates_depth_through_existing_slice_alias() {
    // Seed r = List.tail(fields) → depth 1.
    // Verify t = List.tail(r) → depth 2 (transitive).
    let parent = id();
    let r = id();
    let t = id();
    let expr = PseudoExpr::Let {
        name: "t".to_string(),
        id: Some(t),
        value: PBox::new(list_tail_call(PseudoExpr::Var {
            name: "r".to_string(),
            id: Some(r),
        })),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        r,
        "r",
        VarKind::SliceTailAlias { parent, depth: 1 },
    );
    seed_kind(
        &mut table,
        t,
        "t",
        VarKind::SliceTailAlias { parent, depth: 2 },
    );

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
}

#[test]
fn verifier_accepts_alias_propagation_let_y_eq_x() {
    // Seed r = List.tail(fields) → depth 1.
    // Verify s = r also carries depth 1.
    let parent = id();
    let r = id();
    let s = id();
    let expr = PseudoExpr::Let {
        name: "s".to_string(),
        id: Some(s),
        value: PBox::new(PseudoExpr::Var {
            name: "r".to_string(),
            id: Some(r),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        r,
        "r",
        VarKind::SliceTailAlias { parent, depth: 1 },
    );
    seed_kind(
        &mut table,
        s,
        "s",
        VarKind::SliceTailAlias { parent, depth: 1 },
    );

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
}

#[test]
fn verifier_reports_conflicting_slice_tail_alias_depth() {
    let parent = id();
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(alias),
        value: PBox::new(list_tail_call(PseudoExpr::Var {
            name: "fields".to_string(),
            id: Some(parent),
        })),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        alias,
        "r",
        VarKind::SliceTailAlias { parent, depth: 2 },
    );

    let report = verify_var_kinds(&expr, &table);

    assert_eq!(report.conflicts.len(), 1);
    assert!(matches!(
        report.conflicts[0].inferred,
        VarKind::SliceTailAlias { depth: 1, .. }
    ));
}

#[test]
fn does_not_promote_user_kind_to_slice_tail_alias() {
    let parent = id();
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(alias),
        value: PBox::new(list_tail_call(PseudoExpr::Var {
            name: "fields".to_string(),
            id: Some(parent),
        })),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    table.insert(alias, VarMetadata::user(Some("r".to_string())));

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
    assert!(matches!(table.get(alias).unwrap().kind, VarKind::User));
}

#[test]
fn skips_non_slice_value_shape() {
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(alias),
        value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(42))),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
}

// DataLiteralHoist verification

/// Build a Constr with `n` Int fields. Node count = 1 + n.
fn big_constr(n: usize) -> PseudoExpr {
    let fields: Vec<PseudoExpr> = (0..n)
        .map(|i| PseudoExpr::Int(num_bigint::BigInt::from(i as i64)))
        .collect();
    PseudoExpr::Constr {
        type_hint: None,
        tag: 0,
        fields: fields.into(),
        shape: crate::pseudo::ConstructorShape::unknown_data(0, n),
    }
}

#[test]
fn data_literal_hoist_requires_mint_site_annotation() {
    // 12 fields → node count 13 > 8 — qualifies.
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "data_literal_0".to_string(),
        id: Some(alias),
        value: PBox::new(big_constr(12)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert!(
        report.conflicts.is_empty(),
        "missing mint-site DataLiteralHoist should not create verifier conflicts: {:?}",
        report.conflicts
    );
    assert!(
        !matches!(
            table.get(alias).map(|m| &m.kind),
            Some(VarKind::DataLiteralHoist)
        ),
        "DataLiteralHoist should be populated only by mint-site annotations"
    );
}

#[test]
fn verifier_accepts_matching_existing_data_literal_hoist() {
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "data_literal_0".to_string(),
        id: Some(alias),
        value: PBox::new(big_constr(12)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        alias,
        "data_literal_0",
        VarKind::DataLiteralHoist,
    );

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
}

#[test]
fn verifier_reports_conflicting_data_literal_hoist_kind() {
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "data_literal_0".to_string(),
        id: Some(alias),
        value: PBox::new(big_constr(12)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        alias,
        "data_literal_0",
        VarKind::CallResult { callee: id() },
    );

    let report = verify_var_kinds(&expr, &table);

    assert_eq!(report.conflicts.len(), 1);
    assert!(matches!(
        report.conflicts[0].inferred,
        VarKind::DataLiteralHoist
    ));
}

#[test]
fn skips_data_literal_hoist_below_threshold() {
    // 5 fields → node count 6, NOT > 8 — should not qualify
    // even with the `data_literal_N` name.
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "data_literal_1".to_string(),
        id: Some(alias),
        value: PBox::new(big_constr(5)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
    assert!(table.get(alias).is_none());
}

#[test]
fn skips_data_literal_hoist_when_value_has_var_inside() {
    // Value contains a Var → not a static data literal,
    // never qualifies regardless of size.
    let alias = id();
    let inner_var = id();
    let value = PseudoExpr::Constr {
        type_hint: None,
        tag: 0,
        fields: vec![
            PseudoExpr::Var {
                name: "leak".to_string(),
                id: Some(inner_var),
            },
            PseudoExpr::Int(num_bigint::BigInt::from(1)),
            PseudoExpr::Int(num_bigint::BigInt::from(2)),
            PseudoExpr::Int(num_bigint::BigInt::from(3)),
            PseudoExpr::Int(num_bigint::BigInt::from(4)),
            PseudoExpr::Int(num_bigint::BigInt::from(5)),
            PseudoExpr::Int(num_bigint::BigInt::from(6)),
            PseudoExpr::Int(num_bigint::BigInt::from(7)),
            PseudoExpr::Int(num_bigint::BigInt::from(8)),
            PseudoExpr::Int(num_bigint::BigInt::from(9)),
        ]
        .into(),
        shape: crate::pseudo::ConstructorShape::unknown_data(0, 10),
    };
    let expr = PseudoExpr::Let {
        name: "data_literal_2".to_string(),
        id: Some(alias),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
}

#[test]
fn skips_data_literal_hoist_with_user_name() {
    // Same large data literal but bound under a non-synthetic
    // name — should NOT be tagged.
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "my_constants".to_string(),
        id: Some(alias),
        value: PBox::new(big_constr(12)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
}

#[test]
fn does_not_promote_user_kind_to_data_literal_hoist() {
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "data_literal_4".to_string(),
        id: Some(alias),
        value: PBox::new(big_constr(12)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    table.insert(alias, VarMetadata::user(Some("data_literal_4".to_string())));

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
    assert!(matches!(table.get(alias).unwrap().kind, VarKind::User));
}

// CallResult verification

fn apply_var(name: &str, callee: VarId, args: Vec<PseudoExpr>) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: name.to_string(),
            id: Some(callee),
        }),
        args: args.into(),
    }
}

#[test]
fn call_result_requires_mint_site_annotation() {
    // `let foo_result = foo(arg)` → CallResult { callee: foo_id }.
    let foo_id = id();
    let alias = id();
    let arg = PseudoExpr::Int(num_bigint::BigInt::from(7));
    let expr = PseudoExpr::Let {
        name: "foo_result".to_string(),
        id: Some(alias),
        value: PBox::new(apply_var("foo", foo_id, vec![arg])),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert!(
        report.conflicts.is_empty(),
        "missing mint-site CallResult should not create verifier conflicts: {:?}",
        report.conflicts
    );
    assert!(
        !matches!(
            table.get(alias).map(|m| &m.kind),
            Some(VarKind::CallResult { .. })
        ),
        "CallResult should be populated only by mint-site annotations"
    );
}

#[test]
fn verifier_accepts_matching_existing_call_result() {
    let foo_id = id();
    let alias = id();
    let arg = PseudoExpr::Int(num_bigint::BigInt::from(7));
    let expr = PseudoExpr::Let {
        name: "foo_result".to_string(),
        id: Some(alias),
        value: PBox::new(apply_var("foo", foo_id, vec![arg])),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        alias,
        "foo_result",
        VarKind::CallResult { callee: foo_id },
    );

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
}

#[test]
fn verifier_reports_conflicting_call_result_callee() {
    let foo_id = id();
    let wrong_callee = id();
    let alias = id();
    let arg = PseudoExpr::Int(num_bigint::BigInt::from(7));
    let expr = PseudoExpr::Let {
        name: "foo_result".to_string(),
        id: Some(alias),
        value: PBox::new(apply_var("foo", foo_id, vec![arg])),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        alias,
        "foo_result",
        VarKind::CallResult {
            callee: wrong_callee,
        },
    );

    let report = verify_var_kinds(&expr, &table);

    assert_eq!(report.conflicts.len(), 1);
    assert!(matches!(
        report.conflicts[0].inferred,
        VarKind::CallResult { callee } if callee == foo_id
    ));
}

#[test]
fn does_not_promote_user_kind_to_call_result() {
    let foo_id = id();
    let alias = id();
    let arg = PseudoExpr::Int(num_bigint::BigInt::from(7));
    let expr = PseudoExpr::Let {
        name: "foo_result".to_string(),
        id: Some(alias),
        value: PBox::new(apply_var("foo", foo_id, vec![arg])),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    table.insert(alias, VarMetadata::user(Some("foo_result".to_string())));

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
    assert!(matches!(table.get(alias).unwrap().kind, VarKind::User));
}

#[test]
fn skips_call_result_when_name_mismatches_callee() {
    // `let bar_result = foo(arg)` — the stem doesn't match
    // the callee, so the simplifier never minted it: user
    // code or a simplifier bug, either way not tagged.
    let foo_id = id();
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "bar_result".to_string(),
        id: Some(alias),
        value: PBox::new(apply_var("foo", foo_id, vec![PseudoExpr::Unit])),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
}

#[test]
fn skips_call_result_for_bare_generic_callee_f_2() {
    // `let f_2_result = f_2(arg)` — the simplifier refuses to
    // name a bare generic callee; the verifier mirrors it.
    let f2_id = id();
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "f_2_result".to_string(),
        id: Some(alias),
        value: PBox::new(apply_var("f_2", f2_id, vec![PseudoExpr::Unit])),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
}

#[test]
fn skips_call_result_when_callee_is_not_a_var() {
    // `let lambda_result = (\x -> x)(arg)` — not a Var head.
    let alias = id();
    let x_id = id();
    let value = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(x_id),
            }),
        }),
        args: vec![PseudoExpr::Unit].into(),
    };
    let expr = PseudoExpr::Let {
        name: "lambda_result".to_string(),
        id: Some(alias),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
}

#[test]
fn skips_call_result_for_zero_arg_apply() {
    // `let foo_result = foo()` — Apply with no args.
    // The simplifier only mints `_result` for a real call.
    let foo_id = id();
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "foo_result".to_string(),
        id: Some(alias),
        value: PBox::new(apply_var("foo", foo_id, vec![])),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
}

// CardanoContext tests

#[test]
fn cardano_context_param_requires_mint_site_annotation() {
    let p_id = id();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", p_id)],
        body: PBox::new(PseudoExpr::Var {
            name: "script_context".to_string(),
            id: Some(p_id),
        }),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
    assert!(table.get(p_id).is_none());
}

#[test]
fn cardano_context_let_requires_mint_site_annotation() {
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "tx_info".to_string(),
        id: Some(alias),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
    assert!(table.get(alias).is_none());
}

#[test]
fn does_not_tag_non_context_name_as_cardano_context() {
    // `let inputs = ...` is a *field* name, not a context
    // type — never a CardanoContext. Its kind comes from
    // the field-extraction path, not schema naming.
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "inputs".to_string(),
        id: Some(alias),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Unit),
    };
    let table = VarTable::new();
    let report = verify_var_kinds(&expr, &table);
    assert_clean_verifier_report(&report);
    assert!(table.get(alias).is_none());
}

#[test]
fn verifier_accepts_matching_existing_cardano_context_param() {
    let p_id = id();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("purpose", p_id)],
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        p_id,
        "purpose",
        VarKind::CardanoContext {
            context_type: "purpose".to_string(),
        },
    );

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
}

#[test]
fn verifier_accepts_matching_existing_cardano_context_let() {
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "tx_info".to_string(),
        id: Some(alias),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        alias,
        "tx_info",
        VarKind::CardanoContext {
            context_type: "tx_info".to_string(),
        },
    );

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
}

#[test]
fn verifier_reports_conflicting_cardano_context_type() {
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "script_context".to_string(),
        id: Some(alias),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        alias,
        "script_context",
        VarKind::CardanoContext {
            context_type: "tx_info".to_string(),
        },
    );

    let report = verify_var_kinds(&expr, &table);

    assert_eq!(report.conflicts.len(), 1);
    assert!(matches!(
        &report.conflicts[0].inferred,
        VarKind::CardanoContext { context_type } if context_type == "script_context"
    ));
}

#[test]
fn does_not_promote_user_kind_to_cardano_context() {
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "tx_info".to_string(),
        id: Some(alias),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    table.insert(alias, VarMetadata::user(Some("tx_info".to_string())));

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
    assert!(matches!(table.get(alias).unwrap().kind, VarKind::User));
}

#[test]
fn verifier_accepts_nested_cardano_context_chain() {
    let ctx_id = id();
    let txi_id = id();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", ctx_id)],
        body: PBox::new(PseudoExpr::Let {
            name: "tx_info".to_string(),
            id: Some(txi_id),
            value: PBox::new(PseudoExpr::Var {
                name: "script_context".to_string(),
                id: Some(ctx_id),
            }),
            body: PBox::new(PseudoExpr::Var {
                name: "tx_info".to_string(),
                id: Some(txi_id),
            }),
        }),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        ctx_id,
        "script_context",
        VarKind::CardanoContext {
            context_type: "script_context".to_string(),
        },
    );
    seed_kind(
        &mut table,
        txi_id,
        "tx_info",
        VarKind::CardanoContext {
            context_type: "tx_info".to_string(),
        },
    );

    let report = verify_var_kinds(&expr, &table);

    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
}

#[test]
fn data_literal_hoist_recognises_big_list_of_pairs() {
    // List of 5 Pairs of Ints → 1 (list) + 5 * (1 + 1 + 1)
    // = 16 node count > 8 → qualifies.
    let pairs: Vec<PseudoExpr> = (0..5)
        .map(|i| {
            PseudoExpr::Pair(
                PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(i as i64))),
                PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(i as i64 + 1))),
            )
        })
        .collect();
    let value = PseudoExpr::List {
        elements: pairs.into(),
        tail: None,
    };
    let alias = id();
    let expr = PseudoExpr::Let {
        name: "data_literal_3".to_string(),
        id: Some(alias),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut table = VarTable::new();
    seed_kind(
        &mut table,
        alias,
        "data_literal_3",
        VarKind::DataLiteralHoist,
    );
    let report = verify_var_kinds(&expr, &table);
    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
}

#[test]
fn constr_payload_pattern_requires_mint_site_annotation() {
    let subject_id = id();
    let payload_id = id();
    let payload = Binder::new("item_0", payload_id);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: "constr".to_string(),
            id: Some(subject_id),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::constructor(ConstructorShape::unknown_data(0, 1), vec![payload]),
            guard: None,
            body: PseudoExpr::Var {
                name: "item_0".to_string(),
                id: Some(payload_id),
            },
        }],
    };

    let mut table = VarTable::new();
    table.insert(payload_id, VarMetadata::user(Some("item_0".to_string())));

    let report = verify_var_kinds(&expr, &table);

    assert!(
        report.conflicts.is_empty(),
        "missing mint-site ConstrPayload should not create verifier conflicts: {:?}",
        report.conflicts
    );
    assert!(
        matches!(table.get(payload_id).map(|m| &m.kind), Some(VarKind::User)),
        "ConstrPayload should be populated only by an explicit producer design"
    );
}
