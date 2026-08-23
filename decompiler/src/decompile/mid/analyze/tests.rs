use super::*;
use crate::pseudo::mid::expr::{MidExpr, MidLiteral};
use crate::pseudo::mid::expr_id::MidExprId;

fn id(n: u32) -> MidExprId {
    MidExprId::new(n)
}

#[test]
fn test_constant_propagation() {
    let x = VarId::new(0);
    let mut expr = MidExpr::Let {
        id: id(0),
        var: x,
        value: Box::new(MidExpr::Lit {
            id: id(1),
            value: MidLiteral::Integer(42.into()),
        }),
        body: Box::new(MidExpr::Var { id: id(2), var: x }),
        use_count: 0,
    };

    let mut analyzer = Analyzer::new();
    analyzer.analyze(&mut expr);

    // The analyzer keeps abstract values in its own env and writes
    // nothing onto the node, so this only checks that the walk
    // completes and the structure survives.
    if let MidExpr::Let { body, .. } = &expr {
        assert!(matches!(body.as_ref(), MidExpr::Var { .. }));
    } else {
        panic!("expected outer Let, got {:?}", expr);
    }
}

#[test]
fn test_thunk_classification_cosmetic() {
    let mut expr = MidExpr::Thunk {
        id: id(0),
        body: Box::new(MidExpr::Lit {
            id: id(1),
            value: MidLiteral::Integer(42.into()),
        }),
        cosmetic: false,
    };

    let mut analyzer = Analyzer::new();
    analyzer.analyze(&mut expr);

    if let MidExpr::Thunk { cosmetic, .. } = &expr {
        assert!(*cosmetic, "Thunk wrapping a literal should be cosmetic");
    }
}

#[test]
fn test_thunk_classification_lazy() {
    let mut expr = MidExpr::Thunk {
        id: id(0),
        body: Box::new(MidExpr::Apply {
            id: id(1),
            function: Box::new(MidExpr::Var {
                id: id(2),
                var: VarId::new(0),
            }),
            args: vec![],
        }),
        cosmetic: false,
    };

    let mut analyzer = Analyzer::new();
    analyzer.analyze(&mut expr);

    if let MidExpr::Thunk { cosmetic, .. } = &expr {
        assert!(
            !*cosmetic,
            "Thunk wrapping Apply should be lazy, not cosmetic"
        );
    }
}

#[test]
fn test_constant_fold_addition() {
    let mut expr = MidExpr::Builtin {
        id: id(0),
        fun: DefaultFunction::AddInteger,
        forces: 0,
        args: vec![
            MidExpr::Lit {
                id: id(1),
                value: MidLiteral::Integer(3.into()),
            },
            MidExpr::Lit {
                id: id(2),
                value: MidLiteral::Integer(5.into()),
            },
        ],
        folded: None,
    };

    let mut analyzer = Analyzer::new();
    analyzer.analyze(&mut expr);

    if let MidExpr::Builtin { folded, .. } = &expr {
        assert!(folded.is_some(), "AddInteger(3, 5) should be folded");
        match folded.as_ref().unwrap() {
            MidLiteral::Integer(n) => assert_eq!(*n, 8.into()),
            other => panic!("Expected Integer(8), got {:?}", other),
        }
    }
}

#[test]
fn test_constant_fold_equals() {
    let mut expr = MidExpr::Builtin {
        id: id(0),
        fun: DefaultFunction::EqualsInteger,
        forces: 1,
        args: vec![
            MidExpr::Lit {
                id: id(1),
                value: MidLiteral::Integer(5.into()),
            },
            MidExpr::Lit {
                id: id(2),
                value: MidLiteral::Integer(5.into()),
            },
        ],
        folded: None,
    };

    let mut analyzer = Analyzer::new();
    analyzer.analyze(&mut expr);

    if let MidExpr::Builtin { folded, .. } = &expr {
        assert!(folded.is_some(), "EqualsInteger(5, 5) should fold");
        match folded.as_ref().unwrap() {
            MidLiteral::Bool(true) => {}
            other => panic!("Expected Bool(true), got {:?}", other),
        }
    }
}

#[test]
fn test_run_analysis_integration() {
    let x = VarId::new(0);
    let y = VarId::new(1);
    let mut expr = MidExpr::Let {
        id: id(0),
        var: x,
        value: Box::new(MidExpr::Lit {
            id: id(1),
            value: MidLiteral::Integer(10.into()),
        }),
        body: Box::new(MidExpr::Closure {
            id: id(2),
            params: vec![y],
            body: Box::new(MidExpr::Var { id: id(3), var: x }),
            recursive: None,
        }),
        use_count: 0,
    };

    run_analysis(&mut expr);

    if let MidExpr::Let { use_count, .. } = &expr {
        assert_eq!(*use_count, 1);
    } else {
        panic!("expected outer Let after analysis");
    }
}
