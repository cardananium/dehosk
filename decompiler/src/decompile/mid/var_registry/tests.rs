use super::*;

#[test]
fn test_register_and_lookup() {
    let mut reg = VarRegistry::new();
    let id = VarId::new(0);
    reg.register(
        id,
        "x".to_string(),
        VarOrigin::LambdaParam {
            lambda_term_id: 42,
            position: 0,
        },
    );

    let entry = reg.get(id).unwrap();
    assert_eq!(entry.display_name, "x");
    assert!(matches!(
        entry.origin,
        VarOrigin::LambdaParam {
            lambda_term_id: 42,
            ..
        }
    ));
}

#[test]
fn test_debruijn_mapping() {
    let mut reg = VarRegistry::new();
    let id = VarId::new(0);
    reg.register(
        id,
        "y".to_string(),
        VarOrigin::LambdaParam {
            lambda_term_id: 10,
            position: 0,
        },
    );
    reg.record_debruijn(id, 10, 0);

    assert_eq!(reg.find_by_debruijn(10, 0), Some(id));
    assert_eq!(reg.find_by_debruijn(10, 1), None);
}

#[test]
fn test_find_by_origin_term() {
    let mut reg = VarRegistry::new();
    let id1 = VarId::new(0);
    let id2 = VarId::new(1);
    reg.register(
        id1,
        "a".to_string(),
        VarOrigin::LambdaParam {
            lambda_term_id: 5,
            position: 0,
        },
    );
    reg.register(
        id2,
        "b".to_string(),
        VarOrigin::LambdaParam {
            lambda_term_id: 5,
            position: 1,
        },
    );

    let vars = reg.find_by_origin_term(5);
    assert_eq!(vars.len(), 2);
    assert!(vars.contains(&id1));
    assert!(vars.contains(&id2));
}

#[test]
fn test_unique_by_origin_term_returns_none_for_ambiguous_origin() {
    let mut reg = VarRegistry::new();
    let id1 = VarId::new(0);
    let id2 = VarId::new(1);
    reg.register(
        id1,
        "a".to_string(),
        VarOrigin::LambdaParam {
            lambda_term_id: 5,
            position: 0,
        },
    );
    reg.register(
        id2,
        "b".to_string(),
        VarOrigin::LambdaParam {
            lambda_term_id: 5,
            position: 1,
        },
    );

    assert!(reg.unique_by_origin_term(5).is_none());
}

#[test]
fn test_unique_by_origin_term_returns_entry_when_unique() {
    let mut reg = VarRegistry::new();
    let id = VarId::new(0);
    reg.register(
        id,
        "f".to_string(),
        VarOrigin::LambdaParam {
            lambda_term_id: 9,
            position: 0,
        },
    );

    let entry = reg
        .unique_by_origin_term(9)
        .expect("expected unique origin lookup");
    assert_eq!(entry.display_name, "f");
}

#[test]
fn test_set_semantic_role() {
    let mut reg = VarRegistry::new();
    let id = VarId::new(0);
    reg.register(id, "ctx".to_string(), VarOrigin::Synthetic);
    reg.set_semantic_role(id, "script_context".to_string());

    let entry = reg.get(id).unwrap();
    assert_eq!(entry.semantic_role.as_deref(), Some("script_context"));
}
