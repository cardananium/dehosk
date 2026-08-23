use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_constr_exposer_rewrite() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("__constr_index_exposer")),
        args: vec![PseudoExpr::var("d")].into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::BuiltinCall { name, args } => {
            assert_eq!(name, "Data.constr_index");
            assert_eq!(args.len(), 1);
        }
        _ => panic!("expected builtin call"),
    }
}

#[test]
fn test_force_field_access_removed() {
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::field_access(
        PseudoExpr::var("x"),
        "fst".to_string(),
    )));

    let simplified = simplify(expr);
    assert!(matches!(simplified, PseudoExpr::FieldAccess { .. }));
}

#[test]
fn test_force_fully_applied_builtin_removed() {
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("List.head"),
        args: vec![PseudoExpr::var("xs")].into(),
    }));

    let simplified = simplify(expr);
    // List.head(xs) -> xs[0]
    assert!(
        matches!(simplified, PseudoExpr::IndexAccess { ref collection, index: 0 } if matches!(collection.as_ref(), PseudoExpr::Var { .. }))
    );
}

#[test]
fn test_force_force_builtin_alias_removed() {
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if_then_else"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(
            PseudoExpr::var("a"),
        ))))),
    };

    let simplified = simplify(expr);
    assert!(matches!(
        simplified,
        PseudoExpr::BuiltinCall { ref name, ref args } if name == "if" && args.is_empty()
    ));
}

#[test]
fn test_force_force_transitive_builtin_alias_removed() {
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if_then_else"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::var("a")),
            body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(
                PseudoExpr::var("b"),
            ))))),
        }),
    };

    let simplified = simplify(expr);
    assert!(matches!(
        simplified,
        PseudoExpr::BuiltinCall { ref name, ref args } if name == "if" && args.is_empty()
    ));
}
