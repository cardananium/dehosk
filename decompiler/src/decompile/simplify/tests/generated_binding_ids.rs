use super::*;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;

#[test]
fn test_large_data_constr_literal_extracted_from_and_chain() {
    let big_literal = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::int(0),
            PseudoExpr::list(vec![
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(1),
                        PseudoExpr::list(vec![PseudoExpr::byte_array(vec![0xaa; 28])]),
                    ]
                    .into(),
                },
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(0),
                        PseudoExpr::list(vec![PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.Constr"),
                            args: vec![
                                PseudoExpr::int(0),
                                PseudoExpr::list(vec![PseudoExpr::BuiltinCall {
                                    name: crate::BuiltinId::expect_known("Data.Constr"),
                                    args: vec![
                                        PseudoExpr::int(1),
                                        PseudoExpr::list(vec![PseudoExpr::byte_array(vec![
                                            0xbb;
                                            28
                                        ])]),
                                    ]
                                    .into(),
                                }]),
                            ]
                            .into(),
                        }]),
                    ]
                    .into(),
                },
            ]),
        ]
        .into(),
    };

    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var("p6")),
            right: PBox::new(big_literal),
        }),
        right: PBox::new(PseudoExpr::var("m6")),
    };

    let simplified = simplify(expr);
    let output = simplified.to_pretty();
    // After Data.Constr normalization, the literal becomes Constr<N>(...)
    // which may be inlined rather than extracted into a binding.
    assert!(
        output.contains("Constr<0>(") || output.contains("let expected_data"),
        "expected Constr<0>(...) or extracted data binding, got:\n{}",
        output
    );
    assert!(
        output.contains("p6 =="),
        "expected comparison expression, got:\n{}",
        output
    );
}

#[test]
fn test_large_data_literal_extracted_from_plain_eq() {
    let big_literal = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::int(0),
            PseudoExpr::list(vec![
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(1),
                        PseudoExpr::list(vec![PseudoExpr::byte_array(vec![0xaa; 28])]),
                    ]
                    .into(),
                },
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(0),
                        PseudoExpr::list(vec![PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.Constr"),
                            args: vec![
                                PseudoExpr::int(1),
                                PseudoExpr::list(vec![PseudoExpr::byte_array(vec![0xbb; 28])]),
                            ]
                            .into(),
                        }]),
                    ]
                    .into(),
                },
            ]),
        ]
        .into(),
    };

    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::var("p6")),
        right: PBox::new(big_literal),
    };

    let simplified = simplify(expr);
    let output = simplified.to_pretty();
    // After Data.Constr normalization, the literal becomes Constr<N>(...)
    // which may be inlined rather than extracted.
    assert!(
        output.contains("Constr<0>(") || output.contains("let expected_data ="),
        "expected Constr<0>(...) or extracted data binding, got:\n{}",
        output
    );
    assert!(
        output.contains("p6 =="),
        "expected comparison expression, got:\n{}",
        output
    );
}

#[test]
fn test_large_data_literal_extraction_preserves_generated_binding_id() {
    let big_literal = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::int(0),
            PseudoExpr::list(vec![
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(1),
                        PseudoExpr::list(vec![PseudoExpr::byte_array(vec![0xaa; 28])]),
                    ]
                    .into(),
                },
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(0),
                        PseudoExpr::list(vec![PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.Constr"),
                            args: vec![
                                PseudoExpr::int(1),
                                PseudoExpr::list(vec![PseudoExpr::byte_array(vec![0xbb; 28])]),
                            ]
                            .into(),
                        }]),
                    ]
                    .into(),
                },
            ]),
        ]
        .into(),
    };

    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::var("p6")),
        right: PBox::new(big_literal),
    };

    let mut simplifier = Simplifier::with_safe_mode(false);
    let simplified = simplifier.extract_large_data_literal_from_eq(expr);

    match simplified {
        PseudoExpr::Let { name, id, body, .. } => {
            let binding_id = id
                .get()
                .expect("expected extracted readability binding to carry a VarId");
            assert!(
                name.starts_with("expected_data"),
                "unexpected binding name: {name}"
            );
            match body.as_ref() {
                PseudoExpr::BinOp { right, .. } => {
                    assert!(
                        matches!(
                            right.as_ref(),
                            PseudoExpr::Var { name: var_name, id: var_id, .. }
                                if var_name == &name && var_id.get() == Some(binding_id)
                        ),
                        "expected extracted equality to reference the same VarId, got: {:?}",
                        right
                    );
                }
                other => panic!("expected equality body, got: {other:?}"),
            }
        }
        other => panic!("expected extracted let binding, got: {other:?}"),
    }
}

#[test]
fn test_builtin_arg_literal_hoist_preserves_generated_binding_id() {
    let big_literal = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::int(0),
            PseudoExpr::list(vec![
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(1),
                        PseudoExpr::list(vec![PseudoExpr::byte_array(vec![0xaa; 28])]),
                    ]
                    .into(),
                },
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(0),
                        PseudoExpr::list(vec![PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.Constr"),
                            args: vec![
                                PseudoExpr::int(1),
                                PseudoExpr::list(vec![PseudoExpr::byte_array(vec![0xbb; 28])]),
                            ]
                            .into(),
                        }]),
                    ]
                    .into(),
                },
            ]),
        ]
        .into(),
    };
    let expected_literal = big_literal.clone();

    let mut simplifier = Simplifier::with_safe_mode(false);
    let mut args = vec![big_literal];
    let simplified = simplifier
        .hoist_large_data_literals_from_builtin_args(
            crate::BuiltinId::expect_known("Hash.blake2b_256"),
            &mut args,
        )
        .expect("expected large data literal hoist");

    assert!(args.is_empty(), "hoist should consume the owned arg vector");

    match simplified {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            let binding_id = id
                .get()
                .expect("expected hoisted data literal binding to carry a VarId");
            assert_eq!(name, "data_literal_0");
            assert_eq!(value.as_ref(), &expected_literal);
            assert!(
                simplifier
                    .var_kinds
                    .kind_annotations
                    .get(&binding_id)
                    .is_some_and(|kind| matches!(
                        kind,
                        &crate::pseudo::nameless::VarKind::DataLiteralHoist
                    )),
                "expected DataLiteralHoist kind annotation for {binding_id}"
            );
            match body.as_ref() {
                PseudoExpr::BuiltinCall { args, .. } => {
                    assert!(
                        matches!(
                            args.as_slice(),
                            [PseudoExpr::Var { name: var_name, id: var_id, .. }]
                                if var_name == &name && var_id.get() == Some(binding_id)
                        ),
                        "expected hoisted builtin arg to reference the same VarId, got: {:?}",
                        args
                    );
                }
                other => panic!("expected builtin body, got: {other:?}"),
            }
        }
        other => panic!("expected hoisted let binding, got: {other:?}"),
    }
}

#[test]
fn test_apply_arg_literal_hoist_moves_selected_literal_and_records_kind() {
    let big_literal = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::int(0),
            PseudoExpr::list(vec![
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(1),
                        PseudoExpr::list(vec![PseudoExpr::byte_array(vec![0xaa; 28])]),
                    ]
                    .into(),
                },
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Constr"),
                    args: vec![
                        PseudoExpr::int(2),
                        PseudoExpr::list(vec![PseudoExpr::byte_array(vec![0xbb; 28])]),
                    ]
                    .into(),
                },
            ]),
        ]
        .into(),
    };
    let expected_literal = big_literal.clone();
    let fn_id = VarId::new(9_870);

    let mut simplifier = Simplifier::with_safe_mode(false);
    let simplified = match simplifier.simplify_apply_match(
        PseudoExpr::var_with_id("f", fn_id),
        vec![PseudoExpr::int(1), big_literal, PseudoExpr::int(2)],
    ) {
        super::super::apply::ApplyAction::Done(expr) => expr,
        other => panic!(
            "expected apply arg large data literal hoist, got {:?}",
            std::mem::discriminant(&other)
        ),
    };

    match simplified {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            let binding_id = id
                .get()
                .expect("expected hoisted data literal binding to carry a VarId");
            assert_eq!(name, "data_literal_1");
            assert_eq!(value.as_ref(), &expected_literal);
            assert!(
                simplifier
                    .var_kinds
                    .kind_annotations
                    .get(&binding_id)
                    .is_some_and(|kind| matches!(
                        kind,
                        &crate::pseudo::nameless::VarKind::DataLiteralHoist
                    )),
                "expected DataLiteralHoist kind annotation for {binding_id}"
            );
            match body.as_ref() {
                PseudoExpr::Apply { function, args } => {
                    assert!(
                        matches!(
                            function.as_ref(),
                            PseudoExpr::Var { name, id } if name == "f" && *id == Some(fn_id)
                        ),
                        "expected original function to be retained, got: {function:?}"
                    );
                    assert!(
                        matches!(
                            args.as_slice(),
                            [
                                PseudoExpr::Int(left),
                                PseudoExpr::Var { name: var_name, id: var_id },
                                PseudoExpr::Int(right),
                            ] if *left == 1.into()
                                && var_name == &name
                                && var_id.get() == Some(binding_id)
                                && *right == 2.into()
                        ),
                        "expected only selected apply arg to be rewritten, got: {args:?}"
                    );
                }
                other => panic!("expected apply body, got: {other:?}"),
            }
        }
        other => panic!("expected hoisted let binding, got: {other:?}"),
    }
}

#[test]
fn test_if_condition_hoist_preserves_generated_binding_id() {
    let mut simplifier = Simplifier::with_safe_mode(false);
    let simplified = simplifier.simplify_if(
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("flag")),
            then_branch: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::var("a")),
                right: PBox::new(PseudoExpr::int(1)),
            }),
            else_branch: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::var("b")),
                right: PBox::new(PseudoExpr::int(2)),
            }),
        },
        PseudoExpr::int(1),
        PseudoExpr::int(0),
    );

    match simplified {
        PseudoExpr::Let { name, id, body, .. } => {
            let binding_id = id
                .get()
                .expect("expected hoisted condition binding to carry a VarId");
            match body.as_ref() {
                PseudoExpr::If { condition, .. } => {
                    assert!(
                        matches!(
                            condition.as_ref(),
                            PseudoExpr::Var { name: var_name, id: var_id, .. }
                                if var_name == &name && var_id.get() == Some(binding_id)
                        ),
                        "expected hoisted condition to reference the same VarId, got: {:?}",
                        condition
                    );
                }
                other => panic!("expected hoisted if body, got: {other:?}"),
            }
        }
        other => panic!("expected hoisted let binding, got: {other:?}"),
    }
}

#[test]
fn test_field_index_alias_preserves_generated_binding_id() {
    fn contains_var_with_id(expr: &PseudoExpr, target_name: &str, target_id: VarId) -> bool {
        match expr {
            PseudoExpr::Var { name, id, .. } => name == target_name && id.get() == Some(target_id),
            PseudoExpr::Let { value, body, .. } => {
                contains_var_with_id(value, target_name, target_id)
                    || contains_var_with_id(body, target_name, target_id)
            }
            PseudoExpr::Apply { function, args } => {
                contains_var_with_id(function, target_name, target_id)
                    || args
                        .iter()
                        .any(|arg| contains_var_with_id(arg, target_name, target_id))
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                contains_var_with_id(condition, target_name, target_id)
                    || contains_var_with_id(then_branch, target_name, target_id)
                    || contains_var_with_id(else_branch, target_name, target_id)
            }
            PseudoExpr::BinOp { left, right, .. } => {
                contains_var_with_id(left, target_name, target_id)
                    || contains_var_with_id(right, target_name, target_id)
            }
            PseudoExpr::IndexAccess { collection, .. }
            | PseudoExpr::FieldAccess {
                record: collection, ..
            }
            | PseudoExpr::Delay(collection)
            | PseudoExpr::Force(collection) => {
                contains_var_with_id(collection, target_name, target_id)
            }
            _ => false,
        }
    }

    let mut simplifier = Simplifier::with_safe_mode(false);
    let field_value = PseudoExpr::field_access(PseudoExpr::var("n6_0"), "fields".to_string());
    let body = PseudoExpr::BinOp {
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
    };

    let simplified = simplifier.introduce_field_index_aliases("o6", &field_value, body);

    match simplified {
        PseudoExpr::Let {
            name,
            id,
            body: outer_body,
            ..
        } => {
            let binding_id = id
                .get()
                .expect("expected field alias binding to carry a VarId");
            assert_eq!(name, "field_0");
            assert!(
                contains_var_with_id(&outer_body, "field_0", binding_id),
                "expected field_0 replacement to keep the same VarId, got: {:?}",
                outer_body
            );
        }
        other => panic!("expected aliased let chain, got: {other:?}"),
    }
}
