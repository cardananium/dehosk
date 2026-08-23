use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_identity_function_elimination() {
    // f(fn(x) { x }) → f
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }]
        .into(),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(&simplified, PseudoExpr::Var { name, .. } if name == "f"),
        "expected Var(f), got: {:?}",
        simplified
    );
}

#[test]
fn test_identity_function_not_eliminated_with_multiple_args() {
    // f(fn(x) { x }, y) — identity is not the only arg, should NOT eliminate
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![
            PseudoExpr::Lambda {
                params: vec!["x".to_string().into()],
                body: PBox::new(PseudoExpr::var("x")),
            },
            PseudoExpr::var("y"),
        ]
        .into(),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(&simplified, PseudoExpr::Apply { args, .. } if args.len() == 2),
        "expected Apply with 2 args, got: {:?}",
        simplified
    );
}
