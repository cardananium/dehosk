use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_force_delay_simplify() {
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::int(42)))));
    let simplified = simplify(expr);
    assert!(matches!(simplified, PseudoExpr::Int(_)));
}

#[test]
fn test_builtin_name() {
    let name = Simplifier::nice_builtin_name("head_list");
    assert_eq!(name, "List.head");
}
