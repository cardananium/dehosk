use super::*;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};

#[test]
fn test_flatten_simple_nested_let() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::int(42)),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var("y")),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
        body: PBox::new(PseudoExpr::var("x")),
    };

    let result = flatten_let_chains(expr);

    if let PseudoExpr::Let {
        name: outer_name,
        body: outer_body,
        ..
    } = &result
    {
        assert_eq!(outer_name, "y");
        if let PseudoExpr::Let {
            name: inner_name, ..
        } = outer_body.as_ref()
        {
            assert_eq!(inner_name, "x");
        } else {
            panic!("Expected inner Let");
        }
    } else {
        panic!("Expected outer Let");
    }
}

#[test]
fn test_flatten_avoids_deep_outer_self_reference() {
    let inner_let = PseudoExpr::let_bind(
        "tmp_bytes",
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::field_access(
                PseudoExpr::var("entry"),
                "fst".to_string(),
            )]
            .into(),
        },
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Lte,
                left: PBox::new(PseudoExpr::var("needle")),
                right: PBox::new(PseudoExpr::var("bytes")),
            }),
            then_branch: PBox::new(PseudoExpr::var("tmp_bytes")),
            else_branch: PBox::new(PseudoExpr::Bool(false)),
        },
    );
    let expr = PseudoExpr::let_bind("bytes", inner_let, PseudoExpr::var("bytes"));

    let result = flatten_let_chains(expr);

    assert!(
        matches!(
            result,
            PseudoExpr::Let { value, .. }
                if matches!(value.as_ref(), PseudoExpr::Let { .. })
        ),
        "deep free references to the outer binder should block let flattening"
    );
}

#[test]
fn test_no_flatten_when_inner_used_in_outer_body() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::int(42)),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var("y")),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var("x")),
            right: PBox::new(PseudoExpr::var("y")),
        }),
    };

    let result = flatten_let_chains(expr.clone());

    if let PseudoExpr::Let {
        name: outer_name,
        value: outer_val,
        ..
    } = &result
    {
        assert_eq!(outer_name, "x");
        assert!(matches!(outer_val.as_ref(), PseudoExpr::Let { .. }));
    } else {
        panic!("Expected Let");
    }
}

#[test]
fn test_flatten_ignores_shadowed_same_name_in_outer_body() {
    let outer_id = VarId::new(9101);
    let inner_id = VarId::new(9102);
    let shadow_id = VarId::new(9103);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::int(42)),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::Var {
                    name: "y".to_string(),
                    id: Some(inner_id),
                }),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(shadow_id),
            value: PBox::new(PseudoExpr::int(0)),
            body: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(outer_id),
            }),
        }),
    };

    let result = flatten_let_chains(expr);

    match result {
        PseudoExpr::Let { name, id, body, .. } => {
            assert_eq!(name, "y");
            assert_eq!(id, Some(inner_id));
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Let { name, id, .. } if name == "x" && *id == Some(outer_id)
                ),
                "shadowed same-name binders in the outer body should not block flattening"
            );
        }
        other => panic!("Expected flattened let chain, got {other:?}"),
    }
}
