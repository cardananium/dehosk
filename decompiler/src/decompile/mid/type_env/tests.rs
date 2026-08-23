use super::*;
use crate::pseudo::ast::PBox;

fn int() -> Rc<PseudoType> {
    Rc::new(PseudoType::Int)
}

fn bool_t() -> Rc<PseudoType> {
    Rc::new(PseudoType::Bool)
}

#[test]
fn new_is_empty_and_mutable() {
    let env = TypeEnvironment::new();
    assert!(!env.is_frozen());
    assert_eq!(env.var_type_count(), 0);
    assert_eq!(env.expr_type_count(), 0);
    assert_eq!(env.signature_count(), 0);
}

#[test]
fn bind_and_lookup_variable() {
    let mut env = TypeEnvironment::new();
    let id = VarId::fresh_binding();
    env.bind_var(id, int());
    assert_eq!(env.type_of_var(id), Some(int()));
    assert_eq!(env.var_type_count(), 1);
}

#[test]
fn bind_and_lookup_expression() {
    let mut env = TypeEnvironment::new();
    let mid_id = MidExprId::new(42);
    env.bind_expr(mid_id, int());
    assert_eq!(env.type_of_expr(mid_id), Some(int()));
}

#[test]
fn last_write_wins_on_variable() {
    let mut env = TypeEnvironment::new();
    let id = VarId::fresh_binding();
    env.bind_var(id, int());
    env.bind_var(id, bool_t());
    assert_eq!(env.type_of_var(id), Some(bool_t()));
}

#[test]
fn unknown_var_returns_none() {
    let env = TypeEnvironment::new();
    let id = VarId::fresh_binding();
    assert!(env.type_of_var(id).is_none());
}

#[test]
fn signature_round_trips() {
    let mut env = TypeEnvironment::new();
    let fn_id = VarId::fresh_binding();
    let p = VarId::fresh_binding();
    let sig = FnSignature::new(vec![(p, int())], bool_t(), false);
    env.bind_signature(fn_id, sig.clone());
    assert_eq!(env.signature_of(fn_id), Some(&sig));
    assert!(env.is_function(fn_id));
    assert_eq!(env.signature_count(), 1);
}

#[test]
fn signature_arity_matches_params() {
    let p1 = VarId::fresh_binding();
    let p2 = VarId::fresh_binding();
    let sig = FnSignature::new(vec![(p1, int()), (p2, bool_t())], int(), false);
    assert_eq!(sig.arity(), 2);
}

#[test]
fn freeze_blocks_further_writes() {
    let mut env = TypeEnvironment::new();
    let id = VarId::fresh_binding();
    env.bind_var(id, int());
    env.freeze();
    assert!(env.is_frozen());

    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut env = env.clone();
        env.bind_var(VarId::fresh_binding(), int());
    }))
    .expect_err("bind_var after freeze must panic");
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
#[should_panic(expected = "after freeze")]
fn freeze_blocks_same_instance_mutation() {
    // Fires the check on the authoritative (non-cloned) instance;
    // #[should_panic] avoids catch_unwind's unwind-safety wrapper.
    let mut env = TypeEnvironment::new();
    env.freeze();
    env.bind_var(VarId::fresh_binding(), int());
}

#[test]
fn freeze_does_not_block_reads() {
    let mut env = TypeEnvironment::new();
    let id = VarId::fresh_binding();
    env.bind_var(id, int());
    env.freeze();
    assert_eq!(env.type_of_var(id), Some(int()));
}

#[test]
fn freeze_blocks_expr_and_signature_writes() {
    let mut env = TypeEnvironment::new();
    env.freeze();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut env = env.clone();
        env.bind_expr(MidExprId::new(1), int());
    }));
    assert!(result.is_err(), "bind_expr after freeze should panic");

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut env = env.clone();
        let fn_id = VarId::fresh_binding();
        env.bind_signature(fn_id, FnSignature::new(vec![], int(), false));
    }));
    assert!(result.is_err(), "bind_signature after freeze should panic");
}

#[test]
fn effective_type_for_var_prefers_refined_inline() {
    use crate::pseudo::ast::TypeResolution;
    let mut env = TypeEnvironment::new();
    let id = VarId::fresh_binding();
    env.bind_var(id, int()); // env knows Int
    let inline = TypeResolution::known(bool_t()); // inline is refined Bool
    let out = env.effective_type_for_var(id, &inline);
    assert!(
        matches!(out.as_deref(), Some(t) if matches!(t, PseudoType::Bool)),
        "refined inline Bool should win over env Int"
    );
}

#[test]
fn effective_type_for_var_falls_back_to_env_when_inline_unknown() {
    use crate::pseudo::ast::TypeResolution;
    let mut env = TypeEnvironment::new();
    let id = VarId::fresh_binding();
    env.bind_var(id, int());
    let inline = TypeResolution::known(Rc::new(PseudoType::Unknown));
    let out = env.effective_type_for_var(id, &inline);
    assert!(
        matches!(out.as_deref(), Some(t) if matches!(t, PseudoType::Int)),
        "Unknown inline should give way to env Int"
    );
}

#[test]
fn effective_type_for_var_falls_back_to_inline_when_env_empty() {
    use crate::pseudo::ast::TypeResolution;
    let env = TypeEnvironment::new();
    let id = VarId::fresh_binding();
    let inline = TypeResolution::Unknown;
    let out = env.effective_type_for_var(id, &inline);
    // Neither env nor inline is concrete; result mirrors inline
    // (Unknown) rather than panicking.
    assert_eq!(out, TypeResolution::Unknown);
}

#[test]
fn distinct_ids_are_independent() {
    let mut env = TypeEnvironment::new();
    let a = VarId::fresh_binding();
    let b = VarId::fresh_binding();
    env.bind_var(a, int());
    env.bind_var(b, bool_t());
    assert_eq!(env.type_of_var(a), Some(int()));
    assert_eq!(env.type_of_var(b), Some(bool_t()));
}

#[test]
fn resolve_type_with_env_var_uses_env() {
    let mut env = TypeEnvironment::new();
    let id = VarId::fresh_binding();
    env.bind_var(id, int());

    let var = PseudoExpr::Var {
        name: "x".to_string(),
        id: Some(id),
    };
    let result = resolve_type_with_env(&var, Some(&env));
    assert!(
        matches!(result.as_deref(), Some(PseudoType::Int)),
        "Var should resolve to env Int"
    );
}

#[test]
fn resolve_type_with_env_let_uses_env() {
    let mut env = TypeEnvironment::new();
    let id = VarId::fresh_binding();
    env.bind_var(id, bool_t());

    let let_expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(id),
        value: PBox::new(PseudoExpr::Bool(true)),
        body: PBox::new(PseudoExpr::Unit),
    };
    let result = resolve_type_with_env(&let_expr, Some(&env));
    assert!(
        matches!(result.as_deref(), Some(PseudoType::Bool)),
        "Let should resolve to env Bool"
    );
}

#[test]
fn resolve_type_with_env_literal_ignores_env() {
    let mut env = TypeEnvironment::new();
    env.bind_var(VarId::fresh_binding(), bool_t());

    let result = resolve_type_with_env(&PseudoExpr::Int(42.into()), Some(&env));
    assert!(matches!(result.as_deref(), Some(PseudoType::Int)));
}

#[test]
fn resolve_type_with_env_none_env_returns_unknown_for_var() {
    let id = VarId::fresh_binding();
    let var = PseudoExpr::Var {
        name: "x".to_string(),
        id: Some(id),
    };
    let result = resolve_type_with_env(&var, None);
    assert!(
        matches!(result, TypeResolution::Unknown),
        "None env should return Unknown for Var without inline tipo"
    );
}
