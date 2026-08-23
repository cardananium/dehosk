use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;

#[test]
fn pure_literals_qualify() {
    assert!(is_pure_value(&PseudoExpr::Int(0.into())));
    assert!(is_pure_value(&PseudoExpr::Bool(true)));
    assert!(is_pure_value(&PseudoExpr::String("hi".into())));
    assert!(is_pure_value(&PseudoExpr::Unit));
    assert!(is_pure_value(&PseudoExpr::ByteArray(vec![])));
}

#[test]
fn regular_var_is_pure() {
    let user_id = VarId::fresh_binding();
    assert!(is_pure_value(&PseudoExpr::Var {
        name: "user_var".to_string(),
        id: Some(user_id),
    }));
    // Compat-id `Var` with name other than expect! is also pure.
    assert!(is_pure_value(&PseudoExpr::Var {
        name: "compat_name".to_string(),
        id: None,
    }));
}

/// The synthetic abort sentinel must NOT be pure.
#[test]
fn bare_expect_sentinel_is_impure() {
    assert!(!is_pure_value(&PseudoExpr::Var {
        name: "expect!".to_string(),
        id: None,
    }));
}

/// A user-named "expect!" with concrete VarId is not the
/// synthetic sentinel; treat as a regular Var (pure).
#[test]
fn expect_var_with_concrete_id_is_pure() {
    let id = VarId::fresh_binding();
    assert!(is_pure_value(&PseudoExpr::Var {
        name: "expect!".to_string(),
        id: Some(id),
    }));
}

#[test]
fn aggregates_are_pure_iff_components_are_pure() {
    let pure_pair = PseudoExpr::Pair(
        PBox::new(PseudoExpr::Int(1.into())),
        PBox::new(PseudoExpr::Int(2.into())),
    );
    assert!(is_pure_value(&pure_pair));

    let impure_pair = PseudoExpr::Pair(
        PBox::new(PseudoExpr::Int(1.into())),
        PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![].into(),
        }),
    );
    assert!(!is_pure_value(&impure_pair));

    // List with sentinel as an element is impure.
    let list_with_sentinel = PseudoExpr::List {
        elements: vec![
            PseudoExpr::Int(1.into()),
            PseudoExpr::Var {
                name: "expect!".to_string(),
                id: None,
            },
        ]
        .into(),
        tail: None,
    };
    assert!(
        !is_pure_value(&list_with_sentinel),
        "List containing the abort sentinel must NOT be pure"
    );
}

#[test]
fn impure_shapes_refuse() {
    for expr in [
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![].into(),
        },
        PseudoExpr::Force(PBox::new(PseudoExpr::var("x"))),
        PseudoExpr::Delay(PBox::new(PseudoExpr::var("x"))),
        PseudoExpr::Error { message: None },
        PseudoExpr::Let {
            name: "x".to_string(),
            id: None,
            value: PBox::new(PseudoExpr::Int(1.into())),
            body: PBox::new(PseudoExpr::var("x")),
        },
    ] {
        assert!(!is_pure_value(&expr), "expected impure: {expr:?}");
    }
}
