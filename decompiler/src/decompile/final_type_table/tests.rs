use super::*;

fn int_ty() -> Rc<PseudoType> {
    Rc::new(PseudoType::Int)
}

fn bool_ty() -> Rc<PseudoType> {
    Rc::new(PseudoType::Bool)
}

#[test]
fn new_is_empty_and_mutable() {
    let table = FinalTypeTable::new();
    assert!(!table.is_frozen());
    assert_eq!(table.var_type_count(), 0);
}

#[test]
fn bind_and_lookup_by_final_var_id() {
    let mut table = FinalTypeTable::new();
    let id = VarId::fresh_binding();
    table.bind_var(id, int_ty());
    assert_eq!(table.type_of_var(id), Some(int_ty()));
    assert!(table.contains_var(id));
    assert_eq!(table.var_type_count(), 1);
}

#[test]
fn missing_id_returns_none() {
    let table = FinalTypeTable::new();
    let id = VarId::fresh_binding();
    assert!(table.type_of_var(id).is_none());
    assert!(!table.contains_var(id));
}

#[test]
fn last_write_wins() {
    let mut table = FinalTypeTable::new();
    let id = VarId::fresh_binding();
    table.bind_var(id, int_ty());
    table.bind_var(id, bool_ty());
    assert_eq!(table.type_of_var(id), Some(bool_ty()));
}

#[test]
fn distinct_ids_are_independent() {
    let mut table = FinalTypeTable::new();
    let a = VarId::fresh_binding();
    let b = VarId::fresh_binding();
    table.bind_var(a, int_ty());
    table.bind_var(b, bool_ty());
    assert_eq!(table.type_of_var(a), Some(int_ty()));
    assert_eq!(table.type_of_var(b), Some(bool_ty()));
}

#[test]
fn freeze_allows_reads() {
    let mut table = FinalTypeTable::new();
    let id = VarId::fresh_binding();
    table.bind_var(id, int_ty());
    table.freeze();
    assert!(table.is_frozen());
    assert_eq!(table.type_of_var(id), Some(int_ty()));
}

#[test]
#[should_panic(expected = "after freeze")]
fn freeze_blocks_further_writes() {
    let mut table = FinalTypeTable::new();
    table.freeze();
    table.bind_var(VarId::fresh_binding(), int_ty());
}

#[test]
fn freeze_flag_survives_clone() {
    let mut table = FinalTypeTable::new();
    table.freeze();
    let mut cloned = table.clone();
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        cloned.bind_var(VarId::fresh_binding(), int_ty());
    }))
    .expect_err("bind_var on a frozen clone must panic");
    let msg = if let Some(s) = panic.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = panic.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic>".to_string()
    };
    assert!(msg.contains("bind_var"));
    assert!(msg.contains("after freeze"));
}

#[test]
fn is_structurally_distinct_from_mir_type_environment() {
    // `FinalTypeTable` and `mid::type_env::TypeEnvironment` must be
    // different types, so a consumer needing final-AST types cannot
    // be handed a frozen MIR env by accident.
    use crate::decompile::mid::type_env::TypeEnvironment;
    fn assert_disjoint<A: 'static, B: 'static>() {
        assert_ne!(
            std::any::TypeId::of::<A>(),
            std::any::TypeId::of::<B>(),
            "FinalTypeTable and TypeEnvironment must not alias"
        );
    }
    assert_disjoint::<FinalTypeTable, TypeEnvironment>();
}
