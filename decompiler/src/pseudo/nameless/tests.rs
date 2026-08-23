use super::*;

#[test]
fn nameless_var_carries_only_var_id() {
    let id = VarId::fresh_compat_placeholder();
    let var = NamelessExpr::Var(id);
    match var {
        NamelessExpr::Var(actual) => assert_eq!(actual, id),
        _ => panic!("expected Var"),
    }
}

#[test]
fn var_table_round_trip_metadata() {
    let id = VarId::fresh_compat_placeholder();
    let mut table = VarTable::new();
    table.insert(
        id,
        VarMetadata {
            origin: VarOrigin::UserBinder,
            name_hint: Some("script_context".to_string()),
            display_name_hint: None,
            kind: VarKind::CardanoContext {
                context_type: "script_context".to_string(),
            },
        },
    );

    let stored = table.get(id).expect("metadata should be present");
    assert_eq!(stored.name_hint.as_deref(), Some("script_context"));
    assert_eq!(stored.render_name_hint(), Some("script_context"));
    assert!(matches!(stored.kind, VarKind::CardanoContext { .. }));
}

#[test]
fn var_kind_field_index_alias_holds_parent_and_index() {
    let parent = VarId::fresh_compat_placeholder();
    let kind = VarKind::FieldIndexAlias { parent, index: 3 };
    match kind {
        VarKind::FieldIndexAlias {
            parent: p,
            index: i,
        } => {
            assert_eq!(p, parent);
            assert_eq!(i, 3);
        }
        _ => panic!("expected FieldIndexAlias"),
    }
}

#[test]
fn empty_var_table_reports_zero_entries() {
    let table = VarTable::new();
    assert!(table.is_empty());
    assert_eq!(table.len(), 0);
}

#[test]
fn nameless_let_carries_var_id_binder() {
    let binder = VarId::fresh_compat_placeholder();
    let let_expr = NamelessExpr::Let {
        binder,
        value: Box::new(NamelessExpr::Int(BigInt::from(42))),
        body: Box::new(NamelessExpr::Var(binder)),
    };
    match let_expr {
        NamelessExpr::Let {
            binder: actual_binder,
            ..
        } => assert_eq!(actual_binder, binder),
        _ => panic!("expected Let"),
    }
}
