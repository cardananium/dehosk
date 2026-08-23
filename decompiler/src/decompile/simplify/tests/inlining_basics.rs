use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_small_function_inlining() {
    // let f = fn(x) { x.fields } in f(arg) -> arg.fields
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("x"),
                "fields".to_string(),
            )),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::var("arg")].into(),
        }),
    };

    let simplified = simplify(expr);
    // Should be inlined to arg.fields
    assert!(
        matches!(simplified, PseudoExpr::FieldAccess { .. }),
        "Expected FieldAccess, got: {:?}",
        simplified
    );
}

#[test]
fn test_preserved_helper_id_blocks_small_function_inlining() {
    // Same shape as `test_small_function_inlining`: without preservation
    // the tiny `fn(x) { x.fields }` helper is inlined into the call site,
    // collapsing to `arg.fields`. Seeding the binding's VarId into
    // `SimplifyState.helpers.preserved_helper_ids` — as
    // `build_pipeline_seed` does for user-declared helpers with a
    // fully-concrete MIR signature — must leave the Let intact.
    //
    // Use `fresh_binding` (authoritative), not a compat placeholder: only
    // authoritative ids survive `state.var_id = id.get()` inside the
    // simplify loop, where the preserved lookup happens.
    let helper_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "is_small".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("x"),
                "fields".to_string(),
            )),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("is_small")),
            args: vec![PseudoExpr::var("arg")].into(),
        }),
    };

    let mut state = SimplifyState::default();
    state.helpers.preserved_helper_ids.insert(helper_id);
    let simplified = simplify_with_state(expr, None, false, None, &mut state).expr;

    match simplified {
        PseudoExpr::Let {
            ref name,
            ref value,
            ..
        } => {
            assert_eq!(name, "is_small");
            assert!(
                matches!(value.as_ref(), PseudoExpr::Lambda { .. }),
                "Preserved helper value must still be a Lambda, got: {:?}",
                value
            );
        }
        other => panic!(
            "Preserved helper let binding must survive simplification, got: {:?}",
            other
        ),
    }
}
