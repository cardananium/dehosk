use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_hoist_let_from_nested_builtin_arg_expression() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Hash.blake2b_256"),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.serialize"),
            args: vec![PseudoExpr::Let {
                name: "x".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("expensive")),
                    args: vec![PseudoExpr::var("v")].into(),
                }),
                body: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(0),
                        PseudoExpr::list(vec![PseudoExpr::var("x"), PseudoExpr::var("x")]),
                    ]
                    .into(),
                }),
            }]
            .into(),
        }]
        .into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "x");
            assert!(
                matches!(body.as_ref(), PseudoExpr::BuiltinCall { name, .. } if name == "Hash.blake2b_256"),
                "expected let-hoisted outer builtin call, got: {:?}",
                body
            );
        }
        _ => panic!("expected Let-wrapped builtin call, got: {:?}", simplified),
    }
}

#[test]
fn test_and_chain_repeated_data_conversion_is_csed() {
    let map_expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.to_map"),
        args: vec![PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("o6")),
            index: 1,
        }]
        .into(),
    };

    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::var("gate")),
        right: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(map_expr.clone()),
                right: PBox::new(PseudoExpr::var("left_map")),
            }),
            right: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(map_expr),
                right: PBox::new(PseudoExpr::var("right_map")),
            }),
        }),
    };

    let simplified = simplify(expr);
    let output = simplified.to_pretty();
    assert!(
        // DEFAULT render (compilable-data-access OFF): `o6[1]` keeps the
        // readable bracket render. (Even with the toggle ON, `o6` is a bare Var
        // — GATE A fail-closed — so the bracket would survive there too.)
        output.contains("let map_cache = Data.to_map(o6[1])"),
        "expected CSE binding for repeated Data.to_map(...), got:\n{}",
        output
    );
    assert!(
        output.contains("map_cache == left_map") && output.contains("map_cache == right_map"),
        "expected comparisons to reuse map_cache, got:\n{}",
        output
    );
}

#[test]
fn test_and_chain_data_conversion_cse_skips_short_circuit_occurrence() {
    let map_expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.to_map"),
        args: vec![PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("o6")),
            index: 1,
        }]
        .into(),
    };

    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(map_expr.clone()),
                right: PBox::new(PseudoExpr::var("left_map")),
            }),
            right: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Or,
                left: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(map_expr.clone()),
                    right: PBox::new(PseudoExpr::var("fallback_map")),
                }),
                right: PBox::new(PseudoExpr::var("fallback_ok")),
            }),
        }),
        right: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(map_expr),
            right: PBox::new(PseudoExpr::var("right_map")),
        }),
    };

    let simplified = simplify(expr);
    let output = simplified.to_pretty();
    assert!(
        !output.contains("map_cache"),
        "short-circuit occurrence must block Data.to_map CSE, got:\n{}",
        output
    );
    assert!(
        // DEFAULT render (compilable-data-access OFF): `o6[1]` keeps the bracket.
        output.matches("Data.to_map(o6[1])").count() >= 3,
        "expected all Data.to_map occurrences to remain inline, got:\n{}",
        output
    );
}

#[test]
fn test_long_and_chain_extracts_named_checks() {
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::var("m6")),
        right: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Hash.blake2b_256"),
                    args: vec![PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.serialize"),
                        args: vec![PseudoExpr::var("ctx")].into(),
                    }]
                    .into(),
                }),
                right: PBox::new(PseudoExpr::var("expected_hash")),
            }),
            right: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Lte,
                    left: PBox::new(PseudoExpr::var("snd")),
                    right: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("fn_129")),
                        args: vec![
                            PseudoExpr::var("m"),
                            PseudoExpr::var("bytes"),
                            PseudoExpr::var("k"),
                        ]
                        .into(),
                    }),
                }),
                right: PBox::new(PseudoExpr::var("done")),
            }),
        }),
    };

    let simplified = simplify(expr);
    let output = simplified.to_pretty();
    assert!(
        output.contains("let snd_ok ="),
        "expected extracted named condition binding, got:\n{}",
        output
    );
}

#[test]
fn test_generated_bool_binding_renamed_to_readable_name() {
    let expr = PseudoExpr::Let {
        name: "m6".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var("amount")),
            right: PBox::new(PseudoExpr::int(1)),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![PseudoExpr::var("m6"), PseudoExpr::var("m6")].into(),
        )),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "amount_ok");
            assert!(
                matches!(body.as_ref(), PseudoExpr::Tuple(items) if matches!(&items[0], PseudoExpr::Var { name, .. } if name == "amount_ok")),
                "expected body to reference renamed binding, got: {:?}",
                body
            );
        }
        _ => panic!("expected Let, got: {:?}", simplified),
    }
}

#[test]
fn test_generated_bool_binding_rename_avoids_value_self_shadow() {
    // The suggested readable name `s_ok` is already referenced by the value, so
    // the rename must pick a fresh variant, not emit `let s_ok = s == s_ok`.
    let expr = PseudoExpr::Let {
        name: "m6".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var("s")),
            right: PBox::new(PseudoExpr::var("s_ok")),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![PseudoExpr::var("m6"), PseudoExpr::var("m6")].into(),
        )),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_ne!(name, "s_ok", "rename must avoid self-shadow");
            assert!(
                name.starts_with("s_ok"),
                "expected readable fresh suffix, got: {}",
                name
            );
            assert!(
                matches!(
                    value.as_ref(),
                    PseudoExpr::BinOp {
                        op: BinaryOp::Eq,
                        left,
                        right
                    } if matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == "s")
                        && matches!(right.as_ref(), PseudoExpr::Var { name, .. } if name == "s_ok")
                ),
                "expected original value to stay unchanged, got: {:?}",
                value
            );
            assert!(
                matches!(body.as_ref(), PseudoExpr::Tuple(items)
                    if items.iter().all(|e| matches!(e, PseudoExpr::Var { name: n, .. } if n == &name))),
                "expected body to reference renamed binding, got: {:?}",
                body
            );
        }
        _ => panic!("expected Let, got: {:?}", simplified),
    }
}

#[test]
fn test_let_binding_name_avoids_value_self_shadow() {
    // let x = x[0] in x == 1
    // should become let x_2 = x[0] in x_2 == 1 (name may vary suffix).
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("x")),
            index: 0,
        }),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var("x")),
            right: PBox::new(PseudoExpr::int(1)),
        }),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_ne!(name, "x", "binding must be fresh to avoid self-shadow");
            assert!(
                matches!(
                    value.as_ref(),
                    PseudoExpr::IndexAccess { collection, index }
                        if *index == 0
                        && matches!(collection.as_ref(), PseudoExpr::Var { name, .. } if name == "x")
                ),
                "expected value to keep outer x reference, got: {:?}",
                value
            );
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::BinOp { op: BinaryOp::Eq, left, right }
                        if matches!(left.as_ref(), PseudoExpr::Var { name: n, .. } if n == &name)
                        && matches!(right.as_ref(), PseudoExpr::Int(_))
                ),
                "expected body to use fresh binding name, got: {:?}",
                body
            );
        }
        _ => panic!("expected Let, got: {:?}", simplified),
    }
}

#[test]
fn test_let_binding_name_ignores_foreign_same_name_value_ref() {
    let binder_id = VarId::new(9360);
    let foreign_id = VarId::new(9361);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binder_id),
        value: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var_with_id("x", foreign_id)),
            index: 0,
        }),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var_with_id("x", binder_id)),
            right: PBox::new(PseudoExpr::int(1)),
        }),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
            ..
        } => {
            assert_eq!(
                name, "x",
                "foreign same-name value refs must not rename the binder"
            );
            assert_eq!(id, Some(binder_id));
            assert!(
                matches!(
                    value.as_ref(),
                    PseudoExpr::IndexAccess { collection, index }
                        if *index == 0
                        && matches!(
                            collection.as_ref(),
                            PseudoExpr::Var { name, id, .. } if name == "x" && *id == Some(foreign_id)
                        )
                ),
                "expected value to keep the foreign same-name ref, got: {:?}",
                value
            );
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::BinOp { op: BinaryOp::Eq, left, right }
                        if matches!(
                            left.as_ref(),
                            PseudoExpr::Var { name, id, .. } if name == "x" && *id == Some(binder_id)
                        )
                        && matches!(right.as_ref(), PseudoExpr::Int(_))
                ),
                "expected body to keep the original binder ref, got: {:?}",
                body
            );
        }
        _ => panic!("expected Let, got: {:?}", simplified),
    }
}

#[test]
fn test_fields_index_accesses_are_aliased() {
    let expr = PseudoExpr::Let {
        name: "o6".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("n6_0"),
            "fields".to_string(),
        )),
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::var("o6")),
                    index: 0,
                }),
                right: PBox::new(PseudoExpr::int(1)),
            }),
            right: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::var("o6")),
                    index: 1,
                }),
                right: PBox::new(PseudoExpr::int(2)),
            }),
        }),
    };

    let simplified = simplify(expr);
    let output = simplified.to_pretty();
    // DEFAULT render (compilable-data-access OFF): the `[N]` index keeps the
    // readable bracket render. (Even with the toggle ON the collection
    // `o6`/`fields` is a bare Var — GATE A fail-closed — so the bracket survives.)
    assert!(
        output.contains("let field_0 = o6[0]") || output.contains("let field_0 = fields[0]"),
        "expected alias for o6[0], got:\n{}",
        output
    );
    assert!(
        output.contains("let field_1 = o6[1]") || output.contains("let field_1 = fields[1]"),
        "expected alias for o6[1], got:\n{}",
        output
    );
}
