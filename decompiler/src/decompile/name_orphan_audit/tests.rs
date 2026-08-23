use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;

fn id() -> VarId {
    VarId::fresh_binding()
}

#[test]
fn well_formed_let_is_bound() {
    // let x = 1 in x
    let x = id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x),
        value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(x),
        }),
    };
    let report = audit_name_orphans(&expr, &[]);
    assert_eq!(report.bound, 1);
    assert_eq!(report.name_orphans, 0);
    assert_eq!(report.true_free, 0);
}

#[test]
fn mismatched_varid_same_name_is_name_orphan() {
    // let x[id=A] = 1 in x[id=B]
    let a = id();
    let b = id();
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
    let report = audit_name_orphans(&expr, &[]);
    assert_eq!(report.bound, 0);
    assert_eq!(report.name_orphans, 1);
    assert_eq!(report.true_free, 0);
    assert_eq!(report.offenders, vec![("x".to_string(), 1)]);
}

#[test]
fn unknown_name_is_true_free() {
    let expr = PseudoExpr::Var {
        name: "unseen".to_string(),
        id: Some(id()),
    };
    let report = audit_name_orphans(&expr, &[]);
    assert_eq!(report.bound, 0);
    assert_eq!(report.name_orphans, 0);
    assert_eq!(report.true_free, 1);
}

#[test]
fn root_param_makes_reference_bound() {
    let p = id();
    let expr = PseudoExpr::Var {
        name: "p".to_string(),
        id: Some(p),
    };
    let report = audit_name_orphans(&expr, &[("p".to_string(), p)]);
    assert_eq!(report.bound, 1);
    assert_eq!(report.name_orphans, 0);
}

#[test]
fn lambda_param_binds_body() {
    let p = id();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("p", p)],
        body: PBox::new(PseudoExpr::Var {
            name: "p".to_string(),
            id: Some(p),
        }),
    };
    let report = audit_name_orphans(&expr, &[]);
    assert_eq!(report.bound, 1);
    assert_eq!(report.name_orphans, 0);
}

#[test]
fn lambda_param_mismatched_varid_is_name_orphan() {
    let pa = id();
    let pb = id();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("p", pa)],
        body: PBox::new(PseudoExpr::Var {
            name: "p".to_string(),
            id: Some(pb),
        }),
    };
    let report = audit_name_orphans(&expr, &[]);
    assert_eq!(report.bound, 0);
    assert_eq!(report.name_orphans, 1);
}

#[test]
fn offender_counter_aggregates() {
    // let x[A]=1 in x[B] + x[C] (two mismatches, same name)
    let a = id();
    let b = id();
    let c = id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(a),
        value: PBox::new(PseudoExpr::Int(num_bigint::BigInt::from(1))),
        body: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(b),
            }),
            right: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(c),
            }),
        }),
    };
    let report = audit_name_orphans(&expr, &[]);
    assert_eq!(report.name_orphans, 2);
    assert_eq!(report.offenders, vec![("x".to_string(), 2)]);
}

/// `find_binder` names the node that binds a `VarId`. It backs the stranded-ref
/// dump, which only prints, so without this the function had no check at all —
/// and it is on the list of walks being made iterative, where a silent change
/// of which binder is reported would go unnoticed.
#[test]
fn find_binder_names_each_binding_site() {
    let lam = id();
    let rec = id();
    let let_id = id();
    let absent = id();

    // fn(lam) { rec fn rec() { let bound = 1 in bound } }
    let inner_let = PseudoExpr::Let {
        name: "bound".to_string(),
        id: Some(let_id),
        value: PBox::new(PseudoExpr::Int(1.into())),
        body: PBox::new(PseudoExpr::var_with_id("bound", let_id)),
    };
    let recfn = PseudoExpr::RecFn {
        name: Binder::new("rec", rec),
        params: vec![],
        body: PBox::new(inner_let),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("lam", lam)],
        body: PBox::new(recfn),
    };

    assert_eq!(
        find_binder(&expr, lam).as_deref(),
        Some("Lambda param lam"),
        "a lambda parameter is reported by its own name",
    );
    assert_eq!(find_binder(&expr, rec).as_deref(), Some("RecFn name rec"));
    assert_eq!(find_binder(&expr, let_id).as_deref(), Some("Let bound"));
    assert_eq!(
        find_binder(&expr, absent),
        None,
        "an id nothing binds has no binding site",
    );
}

/// The search descends into every child position, not just the spine: a binder
/// buried in an `Apply` argument under an `If` is still found.
#[test]
fn find_binder_reaches_nested_argument_positions() {
    let deep = id();
    let buried = PseudoExpr::Lambda {
        params: vec![Binder::new("deep", deep)],
        body: PBox::new(PseudoExpr::Unit),
    };
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(true)),
        then_branch: PBox::new(PseudoExpr::Unit),
        else_branch: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("f", id())),
            args: vec![PseudoExpr::Unit, buried].into(),
        }),
    };
    assert_eq!(
        find_binder(&expr, deep).as_deref(),
        Some("Lambda param deep")
    );
}
