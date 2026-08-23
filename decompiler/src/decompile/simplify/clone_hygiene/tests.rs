use super::*;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};

fn new_id() -> VarId {
    VarId::fresh_binding()
}

/// 1. `let x[A] = 1 in x[A]` → binder gets fresh id B, ref
///    retargets to B.
#[test]
fn let_with_self_ref_renumbers() {
    let a = new_id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(a),
        value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(a),
        }),
    };
    let cloned = clone_with_fresh_binder_ids(&expr, VarId::fresh_binding);
    let PseudoExpr::Let {
        id: Some(new_binder_id),
        body,
        ..
    } = &cloned
    else {
        panic!("expected Let");
    };
    assert_ne!(*new_binder_id, a, "binder should be renumbered");
    let PseudoExpr::Var { id: ref_id, .. } = body.as_ref() else {
        panic!("expected Var body");
    };
    assert_eq!(
        *ref_id,
        Some(*new_binder_id),
        "body ref should be retargeted to fresh binder id"
    );
}

/// 2. `let x[A] = 1 in let x[C] = 2 in x[C]` — inner shadows
///    outer. The inner ref must retarget to the inner binder's
///    fresh id, and the two binders must get distinct fresh ids.
#[test]
fn shadowing_preserved_with_distinct_fresh_ids() {
    let a = new_id();
    let c = new_id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(a),
        value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(c),
            value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(2))),
            body: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(c),
            }),
        }),
    };
    let cloned = clone_with_fresh_binder_ids(&expr, VarId::fresh_binding);
    let PseudoExpr::Let {
        id: outer_new,
        body: outer_body,
        ..
    } = &cloned
    else {
        panic!("outer Let");
    };
    let PseudoExpr::Let {
        id: inner_new,
        body: inner_body,
        ..
    } = outer_body.as_ref()
    else {
        panic!("inner Let");
    };
    assert_ne!(*outer_new, *inner_new, "distinct fresh ids");
    assert_ne!(*outer_new, Some(a));
    assert_ne!(*inner_new, Some(c));
    let PseudoExpr::Var { id: ref_id, .. } = inner_body.as_ref() else {
        panic!("body ref");
    };
    assert_eq!(*ref_id, *inner_new, "ref retargets to inner fresh id");
}

/// 3. `(fn x[A] -> x[A] + y[ext]) applied ...` — external
///    capture `y[ext]` must stay unchanged; `x[A]` param and
///    its body ref must renumber together.
#[test]
fn external_captures_untouched() {
    let a = new_id();
    let ext = new_id();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x", a)],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(a),
            }),
            right: PBox::new(PseudoExpr::Var {
                name: "y".to_string(),
                id: Some(ext),
            }),
        }),
    };
    let cloned = clone_with_fresh_binder_ids(&expr, VarId::fresh_binding);
    let PseudoExpr::Lambda { params, body } = &cloned else {
        panic!("Lambda");
    };
    assert_eq!(params.len(), 1);
    assert_ne!(params[0].var_id(), a, "param renumbered");
    let PseudoExpr::BinOp { left, right, .. } = body.as_ref() else {
        panic!("BinOp");
    };
    let PseudoExpr::Var { id: l_id, .. } = left.as_ref() else {
        panic!();
    };
    let PseudoExpr::Var { id: r_id, .. } = right.as_ref() else {
        panic!();
    };
    assert_eq!(*l_id, Some(params[0].var_id()), "internal ref retargets");
    assert_eq!(*r_id, Some(ext), "external ref untouched");
}

/// 4. `when s is { Some(v[A]) -> v[A] }` — pattern binder and
///    body ref must renumber together.
#[test]
fn when_pattern_binder_and_ref_renumber_together() {
    let a = new_id();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("s")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Tuple(vec![Binder::new("v", a)]),
            guard: None,
            body: PseudoExpr::Var {
                name: "v".to_string(),
                id: Some(a),
            },
        }],
    };
    let cloned = clone_with_fresh_binder_ids(&expr, VarId::fresh_binding);
    let PseudoExpr::When { clauses, .. } = &cloned else {
        panic!("When");
    };
    let WhenPattern::Tuple(fs) = &clauses[0].pattern else {
        panic!("Tuple pattern");
    };
    assert_ne!(fs[0].var_id(), a, "pattern binder renumbered");
    let PseudoExpr::Var { id: ref_id, .. } = &clauses[0].body else {
        panic!("body");
    };
    assert_eq!(
        *ref_id,
        Some(fs[0].var_id()),
        "body ref retargets to pattern binder's fresh id"
    );
}

/// 5. `rec fn f[A](x[B]) { f[A](x[B]) }` — both self-name and
///    param renumber, recursive call retargets.
#[test]
fn recfn_self_name_and_params_renumber() {
    let a = new_id();
    let b = new_id();
    let expr = PseudoExpr::RecFn {
        name: Binder::new("f", a),
        params: vec![Binder::new("x", b)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Var {
                name: "f".to_string(),
                id: Some(a),
            }),
            args: vec![PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(b),
            }]
            .into(),
        }),
    };
    let cloned = clone_with_fresh_binder_ids(&expr, VarId::fresh_binding);
    let PseudoExpr::RecFn { name, params, body } = &cloned else {
        panic!("RecFn");
    };
    assert_ne!(name.var_id(), a);
    assert_ne!(params[0].var_id(), b);
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        panic!();
    };
    let PseudoExpr::Var { id: fn_id, .. } = function.as_ref() else {
        panic!();
    };
    let PseudoExpr::Var { id: arg_id, .. } = &args[0] else {
        panic!();
    };
    assert_eq!(*fn_id, Some(name.var_id()), "self-call retargets");
    assert_eq!(*arg_id, Some(params[0].var_id()), "param ref retargets");
}

/// 6. Expression with no binders — deep-equals input.
#[test]
fn no_binders_is_deep_equal() {
    let ext = new_id();
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
        right: PBox::new(PseudoExpr::Var {
            name: "y".to_string(),
            id: Some(ext),
        }),
    };
    let cloned = clone_with_fresh_binder_ids(&expr, VarId::fresh_binding);
    assert_eq!(format!("{:?}", cloned), format!("{:?}", expr));
}

/// 7. Compat-placeholder ids pass through unchanged.
#[test]
fn compat_placeholder_binders_unchanged() {
    let compat = VarId::fresh_compat_placeholder();
    assert!(
        compat.get().is_none(),
        "sanity: fresh_synthetic is compat placeholder"
    );
    let expr = PseudoExpr::Let {
        name: "t".to_string(),
        id: Some(compat),
        value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(0))),
        body: PBox::new(PseudoExpr::Var {
            name: "t".to_string(),
            id: Some(compat),
        }),
    };
    let cloned = clone_with_fresh_binder_ids(&expr, VarId::fresh_binding);
    let PseudoExpr::Let { id, body, .. } = &cloned else {
        panic!("Let");
    };
    assert_eq!(*id, Some(compat), "compat binder id unchanged");
    let PseudoExpr::Var { id: ref_id, .. } = body.as_ref() else {
        panic!();
    };
    assert_eq!(*ref_id, Some(compat), "compat ref unchanged");
}
