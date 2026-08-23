use super::*;
use crate::decompile::mid::type_env::{FnSignature, TypeEnvironment};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, PseudoType};
use crate::pseudo::var_id::VarId;
use std::rc::Rc;

fn fresh_id() -> VarId {
    VarId::fresh_binding()
}

fn int_fn_signature() -> FnSignature {
    FnSignature::new(
        vec![(fresh_id().get().unwrap(), Rc::new(PseudoType::Int))],
        Rc::new(PseudoType::Bool),
        false,
    )
}

#[test]
fn preserves_let_bound_lambda_with_signature() {
    let helper_id = fresh_id();
    let helper_vid = helper_id.get().expect("fresh binder has id");

    let mut env = TypeEnvironment::new();
    env.bind_signature(helper_vid, int_fn_signature());
    env.freeze();

    let expr = PseudoExpr::Let {
        name: "is_small".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::synthetic("n")],
            body: PBox::new(PseudoExpr::var("n")),
        }),
        body: PBox::new(PseudoExpr::var("is_small")),
    };

    let preserved = preserved_helper_ids(&expr, &env);
    assert!(preserved.contains(&helper_vid));
    assert_eq!(preserved.len(), 1);
}

#[test]
fn skips_let_bound_lambda_without_signature() {
    let other_id = fresh_id();

    let env = {
        let mut e = TypeEnvironment::new();
        e.freeze();
        e
    };

    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(other_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::synthetic("n")],
            body: PBox::new(PseudoExpr::var("n")),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };

    let preserved = preserved_helper_ids(&expr, &env);
    assert!(preserved.is_empty());
}

#[test]
fn skips_non_lambda_let_with_signature() {
    // Degenerate case: a non-lambda binder that somehow has a
    // signature recorded. The pass must only keep lambdas/recfns.
    let id = fresh_id();
    let vid = id.get().expect("fresh binder has id");
    let mut env = TypeEnvironment::new();
    env.bind_signature(vid, int_fn_signature());
    env.freeze();

    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(id),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::var("x")),
    };

    let preserved = preserved_helper_ids(&expr, &env);
    assert!(preserved.is_empty());
}

#[test]
fn preserves_recfn_with_signature() {
    let rec_id = fresh_id();
    let vid = rec_id.get().expect("fresh binder has id");
    let mut env = TypeEnvironment::new();
    env.bind_signature(vid, int_fn_signature());
    env.freeze();

    let expr = PseudoExpr::Let {
        name: "loop".to_string(),
        id: Some(rec_id),
        value: PBox::new(PseudoExpr::RecFn {
            name: Binder::synthetic("loop"),
            params: vec![Binder::synthetic("n")],
            body: PBox::new(PseudoExpr::var("n")),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };

    let preserved = preserved_helper_ids(&expr, &env);
    assert!(preserved.contains(&vid));
}

fn unknown_return_signature() -> FnSignature {
    FnSignature::new(
        vec![(fresh_id().get().unwrap(), Rc::new(PseudoType::Int))],
        Rc::new(PseudoType::Unknown),
        false,
    )
}

fn unknown_param_signature() -> FnSignature {
    FnSignature::new(
        vec![(fresh_id().get().unwrap(), Rc::new(PseudoType::Unknown))],
        Rc::new(PseudoType::Bool),
        false,
    )
}

#[test]
fn skips_lambda_with_unknown_return_type() {
    // Compiler-synthesized closures often have an `Unknown` return
    // type because the MIR type inferencer can't pin down their
    // usage-polymorphic shape. Such signatures must not be preserved.
    let helper_id = fresh_id();
    let helper_vid = helper_id.get().expect("fresh binder has id");

    let mut env = TypeEnvironment::new();
    env.bind_signature(helper_vid, unknown_return_signature());
    env.freeze();

    let expr = PseudoExpr::Let {
        name: "synth".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::synthetic("n")],
            body: PBox::new(PseudoExpr::var("n")),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };

    let preserved = preserved_helper_ids(&expr, &env);
    assert!(
        preserved.is_empty(),
        "helper with Unknown return type must not be preserved, got: {:?}",
        preserved
    );
}

#[test]
fn skips_lambda_with_unknown_param_type() {
    let helper_id = fresh_id();
    let helper_vid = helper_id.get().expect("fresh binder has id");

    let mut env = TypeEnvironment::new();
    env.bind_signature(helper_vid, unknown_param_signature());
    env.freeze();

    let expr = PseudoExpr::Let {
        name: "synth".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::synthetic("n")],
            body: PBox::new(PseudoExpr::var("n")),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };

    let preserved = preserved_helper_ids(&expr, &env);
    assert!(
        preserved.is_empty(),
        "helper with Unknown param type must not be preserved, got: {:?}",
        preserved
    );
}

#[test]
fn walks_into_nested_lets() {
    let outer_id = fresh_id();
    let inner_id = fresh_id();
    let outer_vid = outer_id.get().expect("fresh binder has id");
    let inner_vid = inner_id.get().expect("fresh binder has id");
    let mut env = TypeEnvironment::new();
    env.bind_signature(outer_vid, int_fn_signature());
    env.bind_signature(inner_vid, int_fn_signature());
    env.freeze();

    let expr = PseudoExpr::Let {
        name: "outer".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::synthetic("a")],
            body: PBox::new(PseudoExpr::var("a")),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "inner".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::synthetic("b")],
                body: PBox::new(PseudoExpr::var("b")),
            }),
            body: PBox::new(PseudoExpr::var("inner")),
        }),
    };

    let preserved = preserved_helper_ids(&expr, &env);
    assert!(preserved.contains(&outer_vid));
    assert!(preserved.contains(&inner_vid));
    assert_eq!(preserved.len(), 2);
}
