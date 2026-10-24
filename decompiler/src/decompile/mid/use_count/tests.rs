use super::*;
use crate::pseudo::mid::expr::{MBox, MidExpr, MidLiteral};
use crate::pseudo::mid::expr_id::MidExprId;
use crate::pseudo::var_id::VarId;

fn id(n: u32) -> MidExprId {
    MidExprId::new(n)
}

#[test]
fn test_count_simple_var() {
    let x = VarId::new(0);
    let expr = MidExpr::Var { id: id(0), var: x };
    let counts = count_uses(&expr);
    assert_eq!(counts.get(&x), Some(&1));
}

#[test]
fn test_count_let_with_use() {
    let x = VarId::new(0);
    let expr = MidExpr::Let {
        id: id(0),
        var: x,
        value: MBox::new(MidExpr::Lit {
            id: id(1),
            value: MidLiteral::Integer(42.into()),
        }),
        body: MBox::new(MidExpr::Var { id: id(2), var: x }),
        use_count: 0,
    };
    let counts = count_uses(&expr);
    assert_eq!(counts.get(&x), Some(&1));
}

#[test]
fn test_count_multiple_uses() {
    let x = VarId::new(0);
    let y = VarId::new(1);
    let expr = MidExpr::Apply {
        id: id(0),
        function: MBox::new(MidExpr::Var { id: id(1), var: x }),
        args: vec![
            MidExpr::Var { id: id(2), var: x },
            MidExpr::Var { id: id(3), var: y },
        ]
        .into(),
    };
    let counts = count_uses(&expr);
    assert_eq!(counts.get(&x), Some(&2));
    assert_eq!(counts.get(&y), Some(&1));
}

#[test]
fn test_apply_use_counts() {
    let x = VarId::new(0);
    let mut expr = MidExpr::Let {
        id: id(0),
        var: x,
        value: MBox::new(MidExpr::Lit {
            id: id(1),
            value: MidLiteral::Integer(1.into()),
        }),
        body: MBox::new(MidExpr::Apply {
            id: id(2),
            function: MBox::new(MidExpr::Var { id: id(3), var: x }),
            args: vec![MidExpr::Var { id: id(4), var: x }].into(),
        }),
        use_count: 0,
    };
    apply_use_counts(&mut expr);
    match &expr {
        MidExpr::Let { use_count, .. } => assert_eq!(*use_count, 2),
        _ => panic!("Expected Let"),
    }
}

#[test]
fn test_dead_variable() {
    let x = VarId::new(0);
    let expr = MidExpr::Let {
        id: id(0),
        var: x,
        value: MBox::new(MidExpr::Lit {
            id: id(1),
            value: MidLiteral::Unit,
        }),
        body: MBox::new(MidExpr::Lit {
            id: id(2),
            value: MidLiteral::Integer(0.into()),
        }),
        use_count: 0,
    };
    let counts = count_uses(&expr);
    assert_eq!(counts.get(&x), None); // dead: not used at all
}
