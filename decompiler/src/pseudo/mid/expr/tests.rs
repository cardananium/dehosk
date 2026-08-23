use super::*;
use crate::pseudo::mid::expr_id::MidExprId;

fn id(n: u32) -> MidExprId {
    MidExprId::new(n)
}

fn var(n: u32) -> VarId {
    VarId::new(n)
}

#[test]
fn test_mid_expr_id() {
    let expr = MidExpr::Lit {
        id: id(0),
        value: MidLiteral::Integer(42.into()),
    };
    assert_eq!(expr.id(), id(0));
}

#[test]
fn test_children_lit() {
    let expr = MidExpr::Lit {
        id: id(0),
        value: MidLiteral::Bool(true),
    };
    assert_eq!(expr.children().len(), 0);
}

#[test]
fn test_children_apply() {
    let expr = MidExpr::Apply {
        id: id(0),
        function: Box::new(MidExpr::Var {
            id: id(1),
            var: var(0),
        }),
        args: vec![
            MidExpr::Lit {
                id: id(2),
                value: MidLiteral::Integer(1.into()),
            },
            MidExpr::Lit {
                id: id(3),
                value: MidLiteral::Integer(2.into()),
            },
        ],
    };
    assert_eq!(expr.children().len(), 3);
    assert_eq!(expr.node_count(), 4);
}

#[test]
fn test_node_count_nested() {
    let inner = MidExpr::Lit {
        id: id(0),
        value: MidLiteral::Unit,
    };
    let thunk = MidExpr::Thunk {
        id: id(1),
        body: Box::new(inner),
        cosmetic: true,
    };
    let force = MidExpr::Force {
        id: id(2),
        body: Box::new(thunk),
        resolved: None,
    };
    assert_eq!(force.node_count(), 3);
}
