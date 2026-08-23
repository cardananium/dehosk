use super::*;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

#[test]
fn test_normalize_display_rewrites_inlines_when_adapter() {
    let expr = PseudoExpr::Let {
        name: "adapt".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("x")),
            subject_name: None,
            clauses: vec![WhenClause::new(
                WhenPattern::Wildcard,
                PseudoExpr::Bool(true),
            )],
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["y".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("adapt")),
                args: vec![PseudoExpr::var("y")].into(),
            }),
        }),
    };

    let result = normalize_display_rewrites(expr);
    assert!(matches!(result, PseudoExpr::Lambda { .. }));
}

#[test]
fn test_normalize_display_rewrites_lifts_inline_condition_let() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Let {
            name: "data_const_0".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

            value: PBox::new(PseudoExpr::ByteArray(vec![0xaa; 32])),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::var("x")),
                right: PBox::new(PseudoExpr::var("data_const_0")),
            }),
        }),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };

    let result = normalize_display_rewrites(expr);
    match result {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "data_const_0");
            assert!(matches!(body.as_ref(), PseudoExpr::If { .. }));
        }
        _ => panic!("expected inline condition let to be hoisted"),
    }
}

#[test]
fn test_normalize_display_rewrites_rewrites_sorted_lookup_if() {
    let head_fst = PseudoExpr::field_access(PseudoExpr::var("pair"), "fst".to_string());
    let payload = PseudoExpr::constr(
        ConstructorShape::unknown_data(0, 1),
        vec![PseudoExpr::field_access(
            PseudoExpr::var("pair"),
            "snd".to_string(),
        )],
    );
    let none_like = PseudoExpr::constr_known(KnownConstructor::None, vec![]);

    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Lte,
            left: PBox::new(PseudoExpr::var("needle")),
            right: PBox::new(head_fst.clone()),
        }),
        then_branch: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::var("needle")),
                right: PBox::new(head_fst.clone()),
            }),
            then_branch: PBox::new(payload.clone()),
            else_branch: PBox::new(none_like.clone()),
        }),
        else_branch: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("lookup")),
            args: vec![PseudoExpr::var("tail"), PseudoExpr::var("needle")].into(),
        }),
    };

    let result = normalize_display_rewrites(expr);
    match result {
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            assert!(matches!(
                condition.as_ref(),
                PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    ..
                }
            ));
            assert!(then_branch.as_ref().structural_eq(&payload));
            assert!(matches!(
                else_branch.as_ref(),
                PseudoExpr::If {
                    condition,
                    then_branch,
                    ..
                } if matches!(
                    condition.as_ref(),
                    PseudoExpr::BinOp {
                        op: BinaryOp::Lt,
                        ..
                    }
                ) && then_branch.as_ref().structural_eq(&none_like)
            ));
        }
        _ => panic!("expected sorted lookup if to be normalized"),
    }
}

#[test]
fn test_normalize_display_rewrites_repairs_self_referenced_let_rhs() {
    let expr = PseudoExpr::Let {
        name: "bytes".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),

        value: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Lte,
                left: PBox::new(PseudoExpr::var("needle")),
                right: PBox::new(PseudoExpr::var("bytes")),
            }),
            then_branch: PBox::new(PseudoExpr::constr_known(
                KnownConstructor::Some,
                vec![PseudoExpr::var("payload")],
            )),
            else_branch: PBox::new(PseudoExpr::bool(false)),
        }),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::field_access(
                PseudoExpr::var("entry"),
                "fst".to_string(),
            )]
            .into(),
        }),
    };

    let result = normalize_display_rewrites(expr);
    match result {
        PseudoExpr::Let { value, body, .. } => {
            assert!(matches!(
                value.as_ref(),
                PseudoExpr::BuiltinCall { name, .. } if name == "Data.un_bytearray"
            ));
            assert!(matches!(body.as_ref(), PseudoExpr::If { .. }));
        }
        other => panic!("expected repaired let, got: {other:?}"),
    }
}

#[test]
fn test_normalize_display_rewrites_inlines_add_int_helper_calls() {
    let expr = PseudoExpr::let_bind(
        "add_int",
        PseudoExpr::Lambda {
            params: vec!["x".to_string().into(), "y".to_string().into()],
            body: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.Int"),
                args: vec![PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_int"),
                        args: vec![PseudoExpr::var("x")].into(),
                    }),
                    right: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_int"),
                        args: vec![PseudoExpr::var("y")].into(),
                    }),
                }]
                .into(),
            }),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("add_int")),
            args: vec![PseudoExpr::var("lhs"), PseudoExpr::var("rhs")].into(),
        },
    );

    let result = normalize_display_rewrites(expr);

    assert!(matches!(
        result,
        PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left,
            right,
        } if matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == "lhs")
            && matches!(right.as_ref(), PseudoExpr::Var { name, .. } if name == "rhs")
    ));
}

#[test]
fn test_normalize_display_rewrites_drops_int_helper_when_only_foreign_same_name_ref_remains() {
    let helper_id = VarId::new(9461);
    let foreign_id = VarId::new(9462);
    let expr = PseudoExpr::let_bind_with_id(
        "add_int",
        helper_id,
        PseudoExpr::Lambda {
            params: vec!["x".to_string().into(), "y".to_string().into()],
            body: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.Int"),
                args: vec![PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_int"),
                        args: vec![PseudoExpr::var("x")].into(),
                    }),
                    right: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_int"),
                        args: vec![PseudoExpr::var("y")].into(),
                    }),
                }]
                .into(),
            }),
        },
        PseudoExpr::Tuple(
            vec![
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("add_int", helper_id)),
                    args: vec![PseudoExpr::var("lhs"), PseudoExpr::var("rhs")].into(),
                },
                PseudoExpr::var_with_id("add_int", foreign_id),
            ]
            .into(),
        ),
    );

    let result = normalize_display_rewrites(expr);

    assert!(
        matches!(
            result,
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[0],
                    PseudoExpr::BinOp {
                        op: BinaryOp::Add,
                        left,
                        right,
                    } if matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == "lhs")
                        && matches!(right.as_ref(), PseudoExpr::Var { name, .. } if name == "rhs")
                )
                && matches!(&items[1], PseudoExpr::Var { name, id, .. }
                    if name == "add_int" && *id == Some(foreign_id))
        ),
        "foreign same-name ref must not keep the rewritten helper let alive"
    );
}

#[test]
fn test_normalize_display_rewrites_does_not_inline_foreign_same_name_helper_call() {
    let helper_id = VarId::new(9463);
    let foreign_id = VarId::new(9464);
    let expr = PseudoExpr::let_bind_with_id(
        "add_int",
        helper_id,
        PseudoExpr::Lambda {
            params: vec!["x".to_string().into(), "y".to_string().into()],
            body: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.Int"),
                args: vec![PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_int"),
                        args: vec![PseudoExpr::var("x")].into(),
                    }),
                    right: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_int"),
                        args: vec![PseudoExpr::var("y")].into(),
                    }),
                }]
                .into(),
            }),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("add_int", foreign_id)),
            args: vec![PseudoExpr::var("lhs"), PseudoExpr::var("rhs")].into(),
        },
    );

    let result = normalize_display_rewrites(expr);

    assert!(
        matches!(
            &result,
            PseudoExpr::Apply { function, args }
                if matches!(
                    function.as_ref(),
                    PseudoExpr::Var { name, id, .. }
                        if name == "add_int" && *id == Some(foreign_id)
                )
                    && matches!(
                        args.as_slice(),
                        [
                            PseudoExpr::Var { name: lhs, .. },
                            PseudoExpr::Var { name: rhs, .. },
                        ] if lhs == "lhs" && rhs == "rhs"
                    )
        ),
        "foreign same-name helper call must not be rewritten by helper name, got: {result:?}"
    );
}

#[test]
fn test_normalize_display_rewrites_keeps_int_helper_for_compat_placeholder_same_name_ref() {
    let helper_id = VarId::new(9471);
    let expr = PseudoExpr::let_bind_with_id(
        "add_int",
        helper_id,
        PseudoExpr::Lambda {
            params: vec!["x".to_string().into(), "y".to_string().into()],
            body: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.Int"),
                args: vec![PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_int"),
                        args: vec![PseudoExpr::var("x")].into(),
                    }),
                    right: PBox::new(PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_int"),
                        args: vec![PseudoExpr::var("y")].into(),
                    }),
                }]
                .into(),
            }),
        },
        PseudoExpr::Tuple(
            vec![
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("add_int", helper_id)),
                    args: vec![PseudoExpr::var("lhs"), PseudoExpr::var("rhs")].into(),
                },
                PseudoExpr::compat_var("add_int"),
            ]
            .into(),
        ),
    );

    let result = normalize_display_rewrites(expr);

    assert!(
        matches!(
            result,
            PseudoExpr::Let { name, id, body, .. }
                if name == "add_int"
                    && id == Some(helper_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Tuple(items)
                            if matches!(&items[0], PseudoExpr::BinOp { op: BinaryOp::Add, .. })
                                && matches!(&items[1], PseudoExpr::Var { name, id, .. }
                                    if name == "add_int" && id.is_none())
                    )
        ),
        "compat placeholder same-name refs should keep the helper let via fallback"
    );
}

#[test]
fn test_normalize_display_rewrites_inlines_lte_int_helper_calls() {
    let expr = PseudoExpr::let_bind(
        "lte_int",
        PseudoExpr::Lambda {
            params: vec!["x".to_string().into(), "y".to_string().into()],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Lte,
                left: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_int"),
                    args: vec![PseudoExpr::var("x")].into(),
                }),
                right: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_int"),
                    args: vec![PseudoExpr::var("y")].into(),
                }),
            }),
        },
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("lte_int")),
                args: vec![PseudoExpr::var("lhs"), PseudoExpr::Int(0.into())].into(),
            }),
            then_branch: PBox::new(PseudoExpr::Bool(true)),
            else_branch: PBox::new(PseudoExpr::Bool(false)),
        },
    );

    let result = normalize_display_rewrites(expr);

    assert!(matches!(
        result,
        PseudoExpr::If { condition, .. }
            if matches!(
                condition.as_ref(),
                PseudoExpr::BinOp {
                    op: BinaryOp::Lte,
                    left,
                    right,
                } if matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == "lhs")
                    && matches!(right.as_ref(), PseudoExpr::Int(value) if *value == 0.into())
            )
    ));
}

#[test]
fn test_normalize_display_rewrites_deduplicates_identical_separated_lets() {
    let xs_id = VarId::fresh_binding();
    let keep_id = VarId::fresh_binding();
    let ys_id = VarId::fresh_binding();
    let shared = PseudoExpr::list(vec![PseudoExpr::int(1), PseudoExpr::int(2)]);
    let expr = PseudoExpr::let_bind_with_id(
        "xs",
        xs_id,
        shared.clone(),
        PseudoExpr::let_bind_with_id(
            "keep",
            keep_id,
            PseudoExpr::int(0),
            PseudoExpr::let_bind_with_id(
                "ys",
                ys_id,
                shared,
                PseudoExpr::Pair(
                    PBox::new(PseudoExpr::var_with_id("xs", xs_id)),
                    PBox::new(PseudoExpr::var_with_id("ys", ys_id)),
                ),
            ),
        ),
    );

    let result = normalize_display_rewrites(expr);

    match result {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "xs");
            assert!(matches!(value.as_ref(), PseudoExpr::List { .. }));
            match body.as_ref() {
                PseudoExpr::Let { name, body, .. } => {
                    assert_eq!(name, "keep");
                    match body.as_ref() {
                        PseudoExpr::Pair(left, right) => {
                            assert!(matches!(
                                left.as_ref(),
                                PseudoExpr::Var { name, .. } if name == "xs"
                            ));
                            assert!(matches!(
                                right.as_ref(),
                                PseudoExpr::Var { name, .. } if name == "xs"
                            ));
                        }
                        other => {
                            panic!("expected duplicate let to collapse into Pair, got: {other:?}")
                        }
                    }
                }
                other => panic!("expected intervening keep let to remain, got: {other:?}"),
            }
        }
        other => panic!("expected outer xs let to remain, got: {other:?}"),
    }
}

#[test]
fn test_normalize_display_rewrites_renames_pair_lookup_head_binder_to_entry() {
    let head_id = VarId::fresh_binding();
    let tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("pairs")),
        subject_name: Some("pairs".to_string().into()),
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::constr_known(KnownConstructor::None, vec![]),
            ),
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::new("acc_2_h", head_id)],
                    tail: Some(Binder::new("acc_2_t", tail_id)),
                },
                PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::BinOp {
                        op: BinaryOp::Eq,
                        left: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id("acc_2_h", head_id),
                            "fst".to_string(),
                        )),
                        right: PBox::new(PseudoExpr::var("needle")),
                    }),
                    then_branch: PBox::new(PseudoExpr::constr_known(
                        KnownConstructor::Some,
                        vec![PseudoExpr::field_access(
                            PseudoExpr::var_with_id("acc_2_h", head_id),
                            "snd".to_string(),
                        )],
                    )),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("lookup")),
                        args: vec![
                            PseudoExpr::var_with_id("acc_2_t", tail_id),
                            PseudoExpr::var("needle"),
                        ]
                        .into(),
                    }),
                },
            ),
        ],
    };

    let result = normalize_display_rewrites(expr);

    match result {
        PseudoExpr::When { clauses, .. } => match &clauses[1] {
            WhenClause {
                pattern:
                    WhenPattern::List {
                        elements,
                        tail: Some(tail),
                    },
                body,
                ..
            } => {
                assert_eq!(elements.len(), 1);
                assert_eq!(elements[0].as_str(), "entry");
                assert_eq!(elements[0].id, head_id);
                assert_eq!(tail.as_str(), "tail");
                let body_str = format!("{body:?}");
                assert!(
                    body_str.contains("entry")
                        && body_str.contains("tail")
                        && !body_str.contains("acc_2_h")
                        && !body_str.contains("acc_2_t"),
                    "expected pair lookup head binder to be renamed in clause body, got: {body_str}"
                );
            }
            other => panic!("expected non-empty list clause, got: {other:?}"),
        },
        other => panic!("expected when, got: {other:?}"),
    }
}

#[test]
fn test_normalize_display_rewrites_ignores_same_name_different_id_pair_lookup_ref() {
    let outer_head_id = VarId::fresh_binding();
    let clause_head_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "k1".to_string(),
        id: Some(outer_head_id),
        value: PBox::new(PseudoExpr::Pair(
            PBox::new(PseudoExpr::Int(1.into())),
            PBox::new(PseudoExpr::Int(2.into())),
        )),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("pairs")),
            subject_name: Some("pairs".to_string().into()),
            clauses: vec![WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::new("k1", clause_head_id)],
                    tail: None,
                },
                PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::BinOp {
                        op: BinaryOp::Eq,
                        left: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id("k1", outer_head_id),
                            "fst".to_string(),
                        )),
                        right: PBox::new(PseudoExpr::var("needle")),
                    }),
                    then_branch: PBox::new(PseudoExpr::Bool(true)),
                    else_branch: PBox::new(PseudoExpr::Bool(false)),
                },
            )],
        }),
    };

    let result = normalize_display_rewrites(expr);

    match result {
        PseudoExpr::Let { body, .. } => match body.as_ref() {
            PseudoExpr::When { clauses, .. } => match &clauses[0] {
                WhenClause {
                    pattern:
                        WhenPattern::List {
                            elements,
                            tail: None,
                        },
                    ..
                } => {
                    assert_eq!(elements.len(), 1);
                    assert_eq!(elements[0].as_str(), "k1");
                    assert_eq!(elements[0].id, clause_head_id);
                }
                other => panic!("expected single-element list clause, got: {other:?}"),
            },
            other => panic!("expected when under outer let, got: {other:?}"),
        },
        other => panic!("expected outer let, got: {other:?}"),
    }
}

#[test]
fn test_normalize_display_rewrites_hoisted_apply_let_leaves_ref_repair_to_pipeline() {
    let outer_x_id = VarId::fresh_binding();
    let inner_x_id = VarId::fresh_binding();
    let expr = PseudoExpr::let_bind_with_id(
        "x",
        outer_x_id,
        PseudoExpr::int(0),
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![
                PseudoExpr::let_bind_with_id(
                    "x",
                    inner_x_id,
                    PseudoExpr::int(1),
                    PseudoExpr::var_with_id("x", inner_x_id),
                ),
                PseudoExpr::var_with_id("x", outer_x_id),
            ]
            .into(),
        },
    );

    let result = normalize_display_rewrites(expr);

    assert!(
        crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "normalize_display_rewrites should leave same-name apply-hoist ref repair to the pipeline boundary"
    );
    assert!(
        matches!(
            result,
            PseudoExpr::Let { id, body, .. }
                if id == Some(outer_x_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Let { id, body, .. }
                            if *id == Some(inner_x_id)
                                && matches!(
                                    body.as_ref(),
                                    PseudoExpr::Apply { args, .. }
                                        if matches!(
                                            args.first(),
                                            Some(PseudoExpr::Var { id, .. }) if *id == Some(inner_x_id)
                                        )
                                        && matches!(
                                            args.get(1),
                                            Some(PseudoExpr::Var { id, .. }) if *id == Some(outer_x_id)
                                        )
                                )
                    )
        ),
        "expected direct display rewrite to preserve the pre-repair outer ref id"
    );
}

#[test]
fn test_normalize_display_rewrites_leaves_consistent_input_unchanged() {
    let binding_id = VarId::fresh_binding();
    let expr = PseudoExpr::let_bind_with_id(
        "x",
        binding_id,
        PseudoExpr::int(0),
        PseudoExpr::var_with_id("x", binding_id),
    );

    let result = normalize_display_rewrites(expr.clone());

    assert!(
        result.structural_eq(&expr),
        "already-consistent input should stay structurally unchanged: {result:?}"
    );
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "already-consistent input should stay scope-consistent"
    );
}

#[test]
fn test_normalize_display_rewrites_renames_generic_pair_lookup_binders_to_entry_and_tail() {
    let head_id = VarId::fresh_binding();
    let tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("pairs")),
        subject_name: Some("pairs".to_string().into()),
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::constr_known(KnownConstructor::None, vec![]),
            ),
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::new("acc_4_0", head_id)],
                    tail: Some(Binder::new("k2", tail_id)),
                },
                PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::BinOp {
                        op: BinaryOp::Eq,
                        left: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id("acc_4_0", head_id),
                            "fst".to_string(),
                        )),
                        right: PBox::new(PseudoExpr::var("needle")),
                    }),
                    then_branch: PBox::new(PseudoExpr::constr_known(
                        KnownConstructor::Some,
                        vec![PseudoExpr::field_access(
                            PseudoExpr::var_with_id("acc_4_0", head_id),
                            "snd".to_string(),
                        )],
                    )),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("lookup")),
                        args: vec![
                            PseudoExpr::var_with_id("k2", tail_id),
                            PseudoExpr::var("needle"),
                        ]
                        .into(),
                    }),
                },
            ),
        ],
    };

    let result = normalize_display_rewrites(expr);

    match result {
        PseudoExpr::When { clauses, .. } => match &clauses[1] {
            WhenClause {
                pattern:
                    WhenPattern::List {
                        elements,
                        tail: Some(tail),
                    },
                body,
                ..
            } => {
                assert_eq!(elements.len(), 1);
                assert_eq!(elements[0].as_str(), "entry");
                assert_eq!(elements[0].id, head_id);
                assert_eq!(tail.as_str(), "tail");
                assert_eq!(tail.id, tail_id);
                let body_str = format!("{body:?}");
                assert!(
                    body_str.contains("entry")
                        && body_str.contains("tail")
                        && !body_str.contains("acc_4_0")
                        && !body_str.contains("k2"),
                    "expected generic pair lookup binders to be renamed in clause body, got: {body_str}"
                );
            }
            other => panic!("expected non-empty list clause, got: {other:?}"),
        },
        other => panic!("expected when, got: {other:?}"),
    }
}

#[test]
fn test_normalize_display_rewrites_renames_generated_list_binders_to_head_and_tail() {
    let head_id = VarId::fresh_binding();
    let tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("xs")),
        subject_name: Some("xs".to_string().into()),
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::var("done"),
            ),
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::new("y_4_h", head_id)],
                    tail: Some(Binder::new("y_4_t", tail_id)),
                },
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("recur")),
                    args: vec![
                        PseudoExpr::var_with_id("y_4_t", tail_id),
                        PseudoExpr::var_with_id("y_4_h", head_id),
                    ]
                    .into(),
                },
            ),
        ],
    };

    let result = normalize_display_rewrites(expr);

    match result {
        PseudoExpr::When { clauses, .. } => match &clauses[1] {
            WhenClause {
                pattern:
                    WhenPattern::List {
                        elements,
                        tail: Some(tail),
                    },
                body,
                ..
            } => {
                assert_eq!(elements.len(), 1);
                assert_eq!(elements[0].as_str(), "head");
                assert_eq!(elements[0].id, head_id);
                assert_eq!(tail.as_str(), "tail");
                assert_eq!(tail.id, tail_id);
                let body_str = format!("{body:?}");
                assert!(
                    body_str.contains("head")
                        && body_str.contains("tail")
                        && !body_str.contains("y_4_h")
                        && !body_str.contains("y_4_t"),
                    "expected generated list binders to be renamed in clause body, got: {body_str}"
                );
            }
            other => panic!("expected non-empty list clause, got: {other:?}"),
        },
        other => panic!("expected when, got: {other:?}"),
    }
}

#[test]
fn test_normalize_display_rewrites_renames_generic_list_binders_to_head_and_tail() {
    let head_id = VarId::fresh_binding();
    let tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("xs")),
        subject_name: Some("xs".to_string().into()),
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::var("done"),
            ),
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::new("list_2_h", head_id)],
                    tail: Some(Binder::new("list_2_t", tail_id)),
                },
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("recur")),
                    args: vec![
                        PseudoExpr::var_with_id("list_2_t", tail_id),
                        PseudoExpr::var_with_id("list_2_h", head_id),
                    ]
                    .into(),
                },
            ),
        ],
    };

    let result = normalize_display_rewrites(expr);

    match result {
        PseudoExpr::When { clauses, .. } => match &clauses[1] {
            WhenClause {
                pattern:
                    WhenPattern::List {
                        elements,
                        tail: Some(tail),
                    },
                body,
                ..
            } => {
                assert_eq!(elements.len(), 1);
                assert_eq!(elements[0].as_str(), "head");
                assert_eq!(elements[0].id, head_id);
                assert_eq!(tail.as_str(), "tail");
                assert_eq!(tail.id, tail_id);
                let body_str = format!("{body:?}");
                assert!(
                    body_str.contains("head")
                        && body_str.contains("tail")
                        && !body_str.contains("list_2_h")
                        && !body_str.contains("list_2_t"),
                    "expected generic list binders to be renamed in clause body, got: {body_str}"
                );
            }
            other => panic!("expected non-empty list clause, got: {other:?}"),
        },
        other => panic!("expected when, got: {other:?}"),
    }
}

#[test]
fn test_normalize_display_rewrites_rebinds_legacy_generated_list_head_alias_to_pattern_binder() {
    let head_id = VarId::fresh_binding();
    let tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("xs")),
        subject_name: Some("xs".to_string().into()),
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::var("done"),
            ),
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::new("list_4_h", head_id)],
                    tail: Some(Binder::new("list_4_t", tail_id)),
                },
                PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::field_access(PseudoExpr::var("list_4_0"), "fst".to_string()),
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("recur")),
                            args: vec![PseudoExpr::var_with_id("list_4_t", tail_id)].into(),
                        },
                    ]
                    .into(),
                ),
            ),
        ],
    };

    let result = normalize_display_rewrites(expr);

    match result {
        PseudoExpr::When { clauses, .. } => match &clauses[1] {
            WhenClause {
                pattern:
                    WhenPattern::List {
                        elements,
                        tail: Some(tail),
                    },
                body,
                ..
            } => {
                assert_eq!(elements.len(), 1);
                assert_eq!(elements[0].as_str(), "entry");
                assert_eq!(elements[0].id, head_id);
                assert_eq!(tail.as_str(), "tail");
                assert_eq!(tail.id, tail_id);
                let body_str = format!("{body:?}");
                assert!(
                    body_str.contains("entry")
                        && body_str.contains("tail")
                        && !body_str.contains("list_4_0"),
                    "expected legacy generated list head alias to be rebound to the clause binder, got: {body_str}"
                );
            }
            other => panic!("expected non-empty list clause, got: {other:?}"),
        },
        other => panic!("expected when, got: {other:?}"),
    }
}
