use super::*;
use crate::pseudo::ast::PBox;

/// The scope-aware filter in `improve_variable_names` leaves a
/// Var ref alone when its id does not match the binder whose
/// name it shares: renaming by name alone would orphan the ref
/// against the renamed outer binder.
#[test]
fn scope_aware_filter_leaves_inconsistent_refs_alone() {
    let outer_foo_id = VarId::fresh_binding();
    let orphan_id = VarId::fresh_binding();

    // let foo[outer_foo_id] = 42 in foo[orphan_id] + foo[outer_foo_id]
    // The first body ref is orphan, the second bound.
    let expr = PseudoExpr::Let {
        name: "foo".to_string(),
        id: Some(outer_foo_id),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::Var {
                name: "foo".to_string(),
                id: Some(orphan_id),
            }),
            right: PBox::new(PseudoExpr::Var {
                name: "foo".to_string(),
                id: Some(outer_foo_id),
            }),
        }),
    };

    let mut rename_map: HashMap<String, String> = HashMap::new();
    rename_map.insert("foo".to_string(), "bar".to_string());
    let mut binder_rename_map: HashMap<VarId, String> = HashMap::new();
    binder_rename_map.insert(outer_foo_id, "bar".to_string());

    let consistent = collect_consistent_ref_ids(&expr);
    // Nearest "foo" binder has id=outer_foo_id ≠ orphan_id.
    assert!(!consistent.contains(&orphan_id));
    // outer_foo_id: ref "foo" with matching id → consistent.
    assert!(consistent.contains(&outer_foo_id));

    let result = MapRenamer {
        fallback_rename_map: &rename_map,
        let_rename_map: &HashMap::new(),
        binder_rename_map: &binder_rename_map,
        consistent_ref_ids: &consistent,
    }
    .fold(expr);

    match result {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "bar", "outer binder renamed");
            if let PseudoExpr::BinOp { left, right, .. } = body.into_inner() {
                match left.into_inner() {
                    PseudoExpr::Var { name, id } => {
                        assert_eq!(name, "foo", "orphan ref kept original name");
                        assert_eq!(id, Some(orphan_id));
                    }
                    _ => panic!("expected Var"),
                }
                match right.into_inner() {
                    PseudoExpr::Var { name, id } => {
                        assert_eq!(name, "bar", "consistent ref renamed");
                        assert_eq!(id, Some(outer_foo_id));
                    }
                    _ => panic!("expected Var"),
                }
            } else {
                panic!("expected BinOp");
            }
        }
        _ => panic!("expected Let"),
    }
}

#[test]
fn collect_consistent_ref_ids_treats_when_subject_name_as_clause_scope_binder() {
    let subject_id = VarId::new(9310);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::int(0)),
        subject_name: Some(Binder::new("payload", subject_id)),
        clauses: vec![WhenClause::with_guard(
            WhenPattern::Wildcard,
            PseudoExpr::var_with_id("payload", subject_id),
            PseudoExpr::var_with_id("payload", subject_id),
        )],
    };

    let consistent = collect_consistent_ref_ids(&expr);

    assert!(
        consistent.contains(&subject_id),
        "when subject_name should bind refs in clause guards and bodies"
    );
}
