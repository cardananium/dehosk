use super::*;
use crate::pseudo::mid::expr::MidExpr;
use crate::pseudo::mid::expr_id::MidExprId;

fn id(n: u32) -> MidExprId {
    MidExprId::new(n)
}

#[test]
fn test_free_vars_var() {
    let x = VarId::new(0);
    let expr = MidExpr::Var { id: id(0), var: x };
    let fv = free_vars(&expr);
    assert!(fv.contains(&x));
}

#[test]
fn test_free_vars_closure_binds() {
    let x = VarId::new(0);
    let expr = MidExpr::Closure {
        id: id(0),
        params: vec![x],
        body: Box::new(MidExpr::Var { id: id(1), var: x }),
        recursive: None,
    };
    let fv = free_vars(&expr);
    assert!(fv.is_empty(), "x is bound by closure, should not be free");
}

#[test]
fn test_free_vars_closure_captures() {
    let x = VarId::new(0);
    let y = VarId::new(1);
    // fn(x) { y } — y is free
    let expr = MidExpr::Closure {
        id: id(0),
        params: vec![x],
        body: Box::new(MidExpr::Var { id: id(1), var: y }),
        recursive: None,
    };
    let fv = free_vars(&expr);
    assert!(!fv.contains(&x));
    assert!(fv.contains(&y));
}
