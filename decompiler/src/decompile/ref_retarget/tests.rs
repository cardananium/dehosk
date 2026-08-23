use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder};

fn new_id() -> VarId {
    VarId::fresh_binding()
}

/// `let x[A] = 1 in x[B]` → body ref retargets to A.
#[test]
fn retargets_stale_ref_to_in_scope_binder() {
    let a = new_id();
    let b = new_id();
    assert_ne!(a, b);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(a),
        value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(b),
        }),
    };
    let out = retarget_refs_by_scope(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("Let");
    };
    let PseudoExpr::Var { id, .. } = *body else {
        panic!("Var");
    };
    assert_eq!(
        id,
        Some(a),
        "stale ref should retarget to the in-scope binder"
    );
}

/// Shadowing: inner ref retargets to inner binder, outer stays.
#[test]
fn shadowing_picks_nearest_binder() {
    let a = new_id();
    let c = new_id();
    let stale = new_id();
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
                id: Some(stale),
            }),
        }),
    };
    let out = retarget_refs_by_scope(expr);
    let PseudoExpr::Let {
        id: Some(outer_id),
        body,
        ..
    } = out
    else {
        panic!("outer")
    };
    assert_eq!(outer_id, a);
    let PseudoExpr::Let {
        id: Some(inner_id),
        body: inner_body,
        ..
    } = body.into_inner()
    else {
        panic!("inner")
    };
    assert_eq!(inner_id, c);
    let PseudoExpr::Var { id: ref_id, .. } = *inner_body else {
        panic!("ref")
    };
    assert_eq!(
        ref_id,
        Some(c),
        "body ref should retarget to NEAREST (inner) binder, not outer"
    );
}

/// Free ref (no same-name binder in scope) is untouched.
#[test]
fn free_ref_untouched() {
    let stale = new_id();
    let expr = PseudoExpr::Var {
        name: "y".to_string(),
        id: Some(stale),
    };
    let out = retarget_refs_by_scope(expr);
    let PseudoExpr::Var { id, .. } = out else {
        panic!()
    };
    assert_eq!(id, Some(stale));
}

/// Lambda param shadowing.
#[test]
fn lambda_param_retargets_body_ref() {
    let a = new_id();
    let stale = new_id();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x", a)],
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(stale),
        }),
    };
    let out = retarget_refs_by_scope(expr);
    let PseudoExpr::Lambda { body, .. } = out else {
        panic!()
    };
    let PseudoExpr::Var { id, .. } = *body else {
        panic!()
    };
    assert_eq!(id, Some(a));
}

/// RecFn self-name retargets recursive call.
#[test]
fn recfn_name_retargets_self_call() {
    let fn_id = new_id();
    let stale = new_id();
    let expr = PseudoExpr::RecFn {
        name: Binder::new("f", fn_id),
        params: vec![],
        body: PBox::new(PseudoExpr::Var {
            name: "f".to_string(),
            id: Some(stale),
        }),
    };
    let out = retarget_refs_by_scope(expr);
    let PseudoExpr::RecFn { body, .. } = out else {
        panic!()
    };
    let PseudoExpr::Var { id, .. } = *body else {
        panic!()
    };
    assert_eq!(id, Some(fn_id));
}

/// When pattern binder shadows outer.
#[test]
fn when_pattern_binder_retargets() {
    use crate::pseudo::ast::WhenPattern;
    let a = new_id();
    let stale = new_id();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("s")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Tuple(vec![Binder::new("v", a)]),
            guard: None,
            body: PseudoExpr::Var {
                name: "v".to_string(),
                id: Some(stale),
            },
        }],
    };
    let out = retarget_refs_by_scope(expr);
    let PseudoExpr::When { clauses, .. } = out else {
        panic!()
    };
    let PseudoExpr::Var { id, .. } = &clauses[0].body else {
        panic!()
    };
    assert_eq!(*id, Some(a));
}

/// Value of a Let is evaluated in OUTER scope — retargeting
/// the let binder's name to itself would be wrong.
#[test]
fn let_value_evaluated_in_outer_scope() {
    let outer = new_id();
    let inner = new_id();
    // `x` is not in scope while its own value is evaluated, so the
    // stale ref must NOT retarget. (The direct shape for this,
    // `let x = y in (let y = 1 in y)`, would need an outer `y` the
    // fixture has no binder for.)
    let stale = new_id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer),
        value: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(stale),
        }),
        body: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
    };
    let out = retarget_refs_by_scope(expr);
    let PseudoExpr::Let { value, .. } = out else {
        panic!()
    };
    let PseudoExpr::Var { id, .. } = *value else {
        panic!()
    };
    assert_eq!(
        id,
        Some(stale),
        "let value is in outer scope; ref should not see self-binder"
    );
    // Keep `inner` referenced so the test name is accurate.
    let _ = inner;
}

/// BinOp / Apply / nested shapes propagate retargeting.
#[test]
fn retargeting_descends_into_composite_shapes() {
    let a = new_id();
    let stale1 = new_id();
    let stale2 = new_id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(a),
        value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(0))),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(stale1),
            }),
            right: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![PseudoExpr::Var {
                    name: "x".to_string(),
                    id: Some(stale2),
                }]
                .into(),
            }),
        }),
    };
    let out = retarget_refs_by_scope(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!()
    };
    let PseudoExpr::BinOp { left, right, .. } = body.into_inner() else {
        panic!()
    };
    let PseudoExpr::Var { id: lid, .. } = *left else {
        panic!()
    };
    let right_arg = match right.into_inner() {
        PseudoExpr::Apply { args, .. } => args.into_iter().next().unwrap(),
        _ => panic!(),
    };
    let PseudoExpr::Var { id: rid, .. } = right_arg else {
        panic!()
    };
    assert_eq!(lid, Some(a));
    assert_eq!(rid, Some(a));
}

#[test]
fn needs_retarget_reports_true_only_for_stale_scope_refs() {
    let binder_id = new_id();
    let stale_id = new_id();
    let consistent_expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binder_id),
        value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(binder_id),
        }),
    };
    let stale_expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binder_id),
        value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(stale_id),
        }),
    };
    let free_expr = PseudoExpr::Var {
        name: "free".to_string(),
        id: Some(stale_id),
    };

    assert!(
        !refs_need_retarget_by_scope(&consistent_expr),
        "already-consistent refs should not trigger the compatibility boundary"
    );
    assert!(
        refs_need_retarget_by_scope(&stale_expr),
        "stale same-name refs should trigger the compatibility boundary"
    );
    assert!(
        !refs_need_retarget_by_scope(&free_expr),
        "true free refs are not retargetable and should not trigger the boundary"
    );
}
