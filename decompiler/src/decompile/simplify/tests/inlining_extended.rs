use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_small_function_inlining_multiple_uses() {
    // let f = fn(x) { x.fields } in let a = f(p) in let b = f(q) in a == b
    // > let a = p.fields in let b = q.fields in a == b
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("x"),
                "fields".to_string(),
            )),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "a".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![PseudoExpr::var("p")].into(),
            }),
            body: PBox::new(PseudoExpr::Let {
                name: "b".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("f")),
                    args: vec![PseudoExpr::var("q")].into(),
                }),
                body: PBox::new(PseudoExpr::BinOp {
                    op: crate::pseudo::ast::BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::var("a")),
                    right: PBox::new(PseudoExpr::var("b")),
                }),
            }),
        }),
    };

    let simplified = simplify(expr);
    // Lambda inlined -> a = p.fields, b = q.fields -> single-use inlined -> p.fields == q.fields
    assert!(
        matches!(
            simplified,
            PseudoExpr::BinOp {
                op: crate::pseudo::ast::BinaryOp::Eq,
                ..
            }
        ),
        "Expected BinOp Eq, got: {:?}",
        simplified
    );
}

#[test]
fn test_delay_field_access_removed_in_default_mode() {
    let expr = PseudoExpr::Delay(PBox::new(PseudoExpr::field_access(
        PseudoExpr::var("x"),
        "fst".to_string(),
    )));

    let simplified = simplify(expr);
    assert!(matches!(simplified, PseudoExpr::FieldAccess { .. }));
}

#[test]
fn test_projection_accessor_lambda_inlines_even_when_hot() {
    let projection = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![].into(),
        }),
        args: vec![PseudoExpr::field_access(
            PseudoExpr::var("x"),
            "fields".to_string(),
        )]
        .into(),
    };
    let call = |arg: &str| PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![PseudoExpr::var(arg)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(projection()),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                call("a1"),
                call("a2"),
                call("a3"),
                call("a4"),
                call("a5"),
                call("a6"),
                call("a7"),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);
    assert_eq!(
        Simplifier::count_var_uses(&simplified, "f"),
        0,
        "expected hot projection accessor to inline fully, got: {:?}",
        simplified
    );
    assert!(
        matches!(simplified, PseudoExpr::Tuple(ref items) if items.len() == 7),
        "expected tuple body after inlining, got: {:?}",
        simplified
    );
}

#[test]
fn test_delay_field_access_kept_in_safe_mode() {
    let expr = PseudoExpr::Delay(PBox::new(PseudoExpr::field_access(
        PseudoExpr::var("x"),
        "fst".to_string(),
    )));

    let simplified = simplify_with_options(expr, true);
    assert!(matches!(simplified, PseudoExpr::Delay(_)));
}
