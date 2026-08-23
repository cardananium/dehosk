use std::collections::HashSet;

use super::*;
use crate::pseudo::mid::expr::{MidExpr, MidLiteral};
use crate::pseudo::mid::expr_id::{MidExprId, ProvenanceBuilder};

fn id(n: u32) -> MidExprId {
    MidExprId::new(n)
}

fn collect_mid_ids(expr: &MidExpr, ids: &mut Vec<MidExprId>) {
    ids.push(expr.id());
    for child in expr.children() {
        collect_mid_ids(child, ids);
    }
}

#[test]
fn test_force_thunk_resolution() {
    // Force(Thunk(Lit(42))) → Force with resolved = Lit(42)
    let mut expr = MidExpr::Force {
        id: id(0),
        body: Box::new(MidExpr::Thunk {
            id: id(1),
            body: Box::new(MidExpr::Lit {
                id: id(2),
                value: MidLiteral::Integer(42.into()),
            }),
            cosmetic: false,
        }),
        resolved: None,
    };

    resolve_force_thunk(&mut expr);

    if let MidExpr::Force { resolved, .. } = &expr {
        assert!(resolved.is_some(), "Force(Thunk) should resolve");
        if let MidExpr::Lit { value, .. } = resolved.as_ref().unwrap().as_ref() {
            assert_eq!(*value, MidLiteral::Integer(42.into()));
        } else {
            panic!("Resolved should be Lit");
        }
    }
}

#[test]
fn test_inverse_cancellation() {
    // UnIData(IData(Var(x))) → Var(x)
    let x = VarId::new(0);
    let mut expr = MidExpr::Builtin {
        id: id(0),
        fun: DefaultFunction::UnIData,
        forces: 0,
        args: vec![MidExpr::Builtin {
            id: id(1),
            fun: DefaultFunction::IData,
            forces: 0,
            args: vec![MidExpr::Var { id: id(2), var: x }],
            folded: None,
        }],
        folded: None,
    };

    let mut provenance = ProvenanceBuilder::new();
    cancel_inverses(&mut expr, &mut provenance);

    match &expr {
        MidExpr::Var { var, .. } => assert_eq!(*var, x),
        other => panic!("Expected Var(x), got {:?}", other),
    }
}

#[test]
fn test_dead_let_elimination() {
    // let x = 42 in 0 (x unused) → 0
    let x = VarId::new(0);
    let expr = MidExpr::Let {
        id: id(0),
        var: x,
        value: Box::new(MidExpr::Lit {
            id: id(1),
            value: MidLiteral::Integer(42.into()),
        }),
        body: Box::new(MidExpr::Lit {
            id: id(2),
            value: MidLiteral::Integer(0.into()),
        }),
        use_count: 0,
    };

    let mut provenance = ProvenanceBuilder::new();
    let mut result = expr;
    eliminate_dead_lets(&mut result, &mut provenance);

    match &result {
        MidExpr::Lit { value, .. } => {
            assert_eq!(value, &MidLiteral::Integer(0.into()));
        }
        other => panic!("Expected Lit(0), got {:?}", other),
    }
}

#[test]
fn test_keep_used_let() {
    // let x = 42 in x (x used once) → kept
    let x = VarId::new(0);
    let expr = MidExpr::Let {
        id: id(0),
        var: x,
        value: Box::new(MidExpr::Lit {
            id: id(1),
            value: MidLiteral::Integer(42.into()),
        }),
        body: Box::new(MidExpr::Var { id: id(2), var: x }),
        use_count: 1,
    };

    let mut provenance = ProvenanceBuilder::new();
    let mut result = expr;
    eliminate_dead_lets(&mut result, &mut provenance);
    assert!(
        matches!(&result, MidExpr::Let { .. }),
        "Used let should be kept"
    );
}

#[test]
fn test_keep_side_effectful_dead_let() {
    // let x = error in 0 (x unused but has side effect) → kept
    let x = VarId::new(0);
    let expr = MidExpr::Let {
        id: id(0),
        var: x,
        value: Box::new(MidExpr::Error { id: id(1) }),
        body: Box::new(MidExpr::Lit {
            id: id(2),
            value: MidLiteral::Integer(0.into()),
        }),
        use_count: 0,
    };

    let mut provenance = ProvenanceBuilder::new();
    let mut result = expr;
    eliminate_dead_lets(&mut result, &mut provenance);
    assert!(
        matches!(&result, MidExpr::Let { .. }),
        "Side-effectful dead let should be kept"
    );
}

/// A `recursive: Some` mark that `ConvertYComb` did NOT convert
/// (`MarkRecursiveLets`' 1-param eta-Z half) must keep its `v(v)` knot:
/// collapsing it deletes the fixpoint and seats a non-function in the
/// self slot.
#[test]
fn cleanup_preserves_unconverted_recursive_knot() {
    let v = VarId::new(0);
    let v3 = VarId::new(1);
    let mut expr = MidExpr::Let {
        id: id(0),
        var: v,
        value: Box::new(MidExpr::Closure {
            id: id(1),
            params: vec![v3],
            // body is irrelevant to the knot collapse; keep it minimal.
            body: Box::new(MidExpr::Var { id: id(2), var: v3 }),
            recursive: Some(v),
        }),
        body: Box::new(MidExpr::Apply {
            id: id(3),
            function: Box::new(MidExpr::Var { id: id(4), var: v }),
            args: vec![MidExpr::Var { id: id(5), var: v }],
        }),
        use_count: 2,
    };
    let mut provenance = ProvenanceBuilder::new();
    for raw in 0..=5 {
        provenance.link(MidExprId::new(raw), raw as isize);
    }
    let empty = HashSet::new();
    cleanup_recursive_call_sites(&mut expr, &mut provenance, &empty);
    let MidExpr::Let { body, .. } = &expr else {
        panic!("expected Let");
    };
    assert!(
        matches!(body.as_ref(), MidExpr::Apply { .. }),
        "unconverted knot v(v) must survive, got {body:?}"
    );
}

/// The mirror: a CONVERTED var (`ConvertYComb` established the RecFn
/// contract) has its `v(v)` knot collapsed to `v`.
#[test]
fn cleanup_collapses_converted_recursive_knot() {
    let v = VarId::new(0);
    let v3 = VarId::new(1);
    let mut expr = MidExpr::Let {
        id: id(0),
        var: v,
        value: Box::new(MidExpr::Closure {
            id: id(1),
            params: vec![v3],
            body: Box::new(MidExpr::Var { id: id(2), var: v3 }),
            recursive: Some(v),
        }),
        body: Box::new(MidExpr::Apply {
            id: id(3),
            function: Box::new(MidExpr::Var { id: id(4), var: v }),
            args: vec![MidExpr::Var { id: id(5), var: v }],
        }),
        use_count: 2,
    };
    let mut provenance = ProvenanceBuilder::new();
    for raw in 0..=5 {
        provenance.link(MidExprId::new(raw), raw as isize);
    }
    let converted: HashSet<VarId> = [v].into_iter().collect();
    cleanup_recursive_call_sites(&mut expr, &mut provenance, &converted);
    let MidExpr::Let { body, .. } = &expr else {
        panic!("expected Let");
    };
    assert!(
        matches!(body.as_ref(), MidExpr::Var { var, .. } if *var == v),
        "converted knot v(v) must collapse to v, got {body:?}"
    );
}

#[test]
fn test_run_precompute_refreshes_mid_ids_after_duplication() {
    let x = VarId::new(0);
    let mut expr = MidExpr::Let {
        id: id(0),
        var: x,
        value: Box::new(MidExpr::Lit {
            id: id(1),
            value: MidLiteral::Integer(42.into()),
        }),
        body: Box::new(MidExpr::Builtin {
            id: id(2),
            fun: DefaultFunction::AddInteger,
            forces: 0,
            args: vec![
                MidExpr::Var { id: id(3), var: x },
                MidExpr::Var { id: id(4), var: x },
            ],
            folded: None,
        }),
        use_count: 0,
    };

    super::super::analyze::run_analysis(&mut expr);

    let mut provenance = ProvenanceBuilder::new();
    for raw_id in 0..=4 {
        let mid_id = MidExprId::new(raw_id);
        provenance.link(mid_id, raw_id as isize + 100);
    }

    run_precompute(&mut expr, &mut provenance, false);

    let mut ids = Vec::new();
    collect_mid_ids(&expr, &mut ids);

    let unique: HashSet<_> = ids.iter().copied().collect();
    assert_eq!(
        ids.len(),
        unique.len(),
        "MidExprIds must be unique after precompute"
    );
}

#[test]
fn test_inline_trivial_let_transfers_each_use_site_var_provenance_to_fresh_clone() {
    let x = VarId::new(0);
    let y = VarId::new(1);
    let expr = MidExpr::Let {
        id: id(0),
        var: x,
        value: Box::new(MidExpr::Var { id: id(1), var: y }),
        body: Box::new(MidExpr::Builtin {
            id: id(2),
            fun: DefaultFunction::AddInteger,
            forces: 0,
            args: vec![
                MidExpr::Var { id: id(3), var: x },
                MidExpr::Var { id: id(4), var: x },
            ],
            folded: None,
        }),
        use_count: 2,
    };

    let mut provenance = ProvenanceBuilder::new();
    for raw_id in 0..=4 {
        let mid_id = MidExprId::new(raw_id);
        provenance.link(mid_id, raw_id as isize);
    }

    let mut result = expr;
    inline_trivial_lets(&mut result, &mut provenance);

    let args = match result {
        MidExpr::Builtin { args, .. } => args,
        other => panic!("expected builtin after inline, got {other:?}"),
    };
    assert_eq!(args.len(), 2);

    let first = match &args[0] {
        MidExpr::Var { id, var, .. } => {
            assert_eq!(*var, y);
            *id
        }
        other => panic!("expected first inlined arg var, got {other:?}"),
    };
    let second = match &args[1] {
        MidExpr::Var { id, var, .. } => {
            assert_eq!(*var, y);
            *id
        }
        other => panic!("expected second inlined arg var, got {other:?}"),
    };

    assert_ne!(
        first, second,
        "each inlined use site should get its own clone owner"
    );
    assert_eq!(provenance.uplc_ids(first), vec![1, 3]);
    assert_eq!(provenance.uplc_ids(second), vec![1, 4]);
}
