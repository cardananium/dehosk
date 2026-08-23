use super::{
    RenderCtx, debug_deduplicate_constr_pattern_binders, debug_disambiguate_shadowed_lets,
    debug_expr_contains_var_name, debug_inline_slice_chain_aliases,
    debug_prefix_bare_extractor_lets_with_field_name,
    debug_repair_underscore_lambda_params_with_dangling_uses, prepare_for_render,
    rename_var_use_by_id_in_expr,
};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

#[test]
fn prefix_renames_only_matching_binding_id() {
    let map_id = VarId::new(750);
    let foreign_map_id = VarId::new(751);
    let expr = PseudoExpr::Let {
        name: "map".to_string(),
        id: Some(map_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: "Data.un_map".to_string().into(),
            args: vec![PseudoExpr::field_access(PseudoExpr::var("tx_info"), "mint")].into(),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("map", map_id),
                PseudoExpr::var_with_id("map", foreign_map_id),
            ]
            .into(),
        )),
    };

    let renamed = debug_prefix_bare_extractor_lets_with_field_name(expr);

    assert!(
        matches!(
            &renamed,
            PseudoExpr::Let { name, id, body, .. }
                if name == "mint_map"
                    && *id == Some(map_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Tuple(items)
                            if matches!(&items[0], PseudoExpr::Var { name, id } if name == "mint_map" && *id == Some(map_id))
                                && matches!(&items[1], PseudoExpr::Var { name, id } if name == "map" && *id == Some(foreign_map_id))
                    )
        ),
        "extractor prefix rename must only retarget refs owned by the renamed let id, got: {renamed:?}"
    );
}

#[test]
fn prefix_compat_extractor_renames_only_compat_refs() {
    let map_id = VarId::fresh_compat_placeholder();
    let foreign_map_id = VarId::new(752);
    let expr = PseudoExpr::Let {
        name: "map".to_string(),
        id: Some(map_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: "Data.un_map".to_string().into(),
            args: vec![PseudoExpr::field_access(PseudoExpr::var("tx_info"), "mint")].into(),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::compat_var("map"),
                PseudoExpr::var_with_id("map", foreign_map_id),
            ]
            .into(),
        )),
    };

    let renamed = debug_prefix_bare_extractor_lets_with_field_name(expr);

    assert!(
        matches!(
            &renamed,
            PseudoExpr::Let { name, id, body, .. }
                if name == "mint_map"
                    && *id == Some(map_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Tuple(items)
                            if matches!(&items[0], PseudoExpr::Var { name, id } if name == "mint_map" && id.get().is_none())
                                && matches!(&items[1], PseudoExpr::Var { name, id } if name == "map" && *id == Some(foreign_map_id))
                    )
        ),
        "compat extractor prefix rename must not retarget authoritative foreign refs by name, got: {renamed:?}"
    );
}

/// Duplicate `map` binders in one Constructor pattern: the earlier
/// occurrence is renamed so the pattern is valid surface syntax.
#[test]
fn dedup_renames_earlier_duplicate_constr_binders() {
    let pattern = WhenPattern::Constructor {
        type_hint: None,
        tag: 2,
        fields: vec![
            Binder::new("items", VarId::fresh_binding()),
            Binder::new("map", VarId::fresh_binding()), // rename
            Binder::new("_", VarId::fresh_binding()),
            Binder::new("int_value", VarId::fresh_binding()),
            Binder::new("map", VarId::fresh_binding()), // keep
        ],
        shape: ConstructorShape::unknown_data(2, 5),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern,
            guard: None,
            body: PseudoExpr::var("map"),
        }],
    };

    let result = debug_deduplicate_constr_pattern_binders(when_expr);
    let (pat, _body) = match result {
        PseudoExpr::When { mut clauses, .. } => {
            let c = clauses.remove(0);
            (c.pattern, c.body)
        }
        _ => panic!("expected When"),
    };
    match pat {
        WhenPattern::Constructor { fields, .. } => {
            assert_eq!(
                fields
                    .iter()
                    .map(|b| b.as_str().to_string())
                    .collect::<Vec<_>>(),
                vec!["items", "map_1", "_", "int_value", "map"],
            );
        }
        other => panic!("expected Constructor, got {:?}", other),
    }
}

#[test]
fn dedup_renames_body_refs_for_renamed_duplicate_binder_ids() {
    let first_map_id = VarId::new(770);
    let second_map_id = VarId::new(771);
    let pattern = WhenPattern::Constructor {
        type_hint: None,
        tag: 2,
        fields: vec![
            Binder::new("map", first_map_id),
            Binder::new("map", second_map_id),
        ],
        shape: ConstructorShape::unknown_data(2, 2),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern,
            guard: None,
            body: PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("map", first_map_id),
                    PseudoExpr::var_with_id("map", second_map_id),
                ]
                .into(),
            ),
        }],
    };

    let result = debug_deduplicate_constr_pattern_binders(when_expr);

    assert!(
        matches!(
            &result,
            PseudoExpr::When { clauses, .. }
                if matches!(
                    &clauses[0].pattern,
                    WhenPattern::Constructor { fields, .. }
                        if matches!(
                            fields.as_slice(),
                            [first, second]
                                if first.as_str() == "map_0"
                                    && first.id == first_map_id
                                    && second.as_str() == "map"
                                    && second.id == second_map_id
                        )
                )
                && matches!(
                    &clauses[0].body,
                    PseudoExpr::Tuple(items)
                        if matches!(&items[0], PseudoExpr::Var { name, id } if name == "map_0" && *id == Some(first_map_id))
                            && matches!(&items[1], PseudoExpr::Var { name, id } if name == "map" && *id == Some(second_map_id))
                )
        ),
        "dedup should rename body refs owned by renamed duplicate binders, got: {result:?}"
    );
}

#[test]
fn dedup_leaves_unique_pattern_untouched() {
    let pattern = WhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: vec![
            Binder::new("a", VarId::fresh_binding()),
            Binder::new("b", VarId::fresh_binding()),
            Binder::new("c", VarId::fresh_binding()),
        ],
        shape: ConstructorShape::unknown_data(0, 3),
    };
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern,
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };

    let result = debug_deduplicate_constr_pattern_binders(when_expr);
    let pat = match result {
        PseudoExpr::When { mut clauses, .. } => clauses.remove(0).pattern,
        _ => panic!("expected When"),
    };
    match pat {
        WhenPattern::Constructor { fields, .. } => {
            assert_eq!(
                fields
                    .iter()
                    .map(|b| b.as_str().to_string())
                    .collect::<Vec<_>>(),
                vec!["a", "b", "c"],
            );
        }
        other => panic!("expected Constructor, got {:?}", other),
    }
}

#[test]
fn nested_recfn_params_keep_readable_shadowing_names() {
    let expr = PseudoExpr::RecFn {
        name: "outer".to_string().into(),
        params: vec!["list".to_string().into(), "acc".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "inner".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "inner".to_string().into(),
                params: vec!["list".to_string().into(), "acc".to_string().into()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("inner")),
                    args: vec![PseudoExpr::var("list"), PseudoExpr::var("acc")].into(),
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("inner")),
                args: vec![PseudoExpr::var("list"), PseudoExpr::var("acc")].into(),
            }),
        }),
    };

    let disambiguated = debug_disambiguate_shadowed_lets(&expr);
    let rendered = format!("{disambiguated:?}");

    assert!(
        rendered.contains("params: [Binder { name: \"list\"")
            && rendered.contains("Binder { name: \"acc\"")
            && !rendered.contains("list_2")
            && !rendered.contains("acc_2"),
        "nested recfn params should keep readable shadowing names, got: {rendered}"
    );
}

#[test]
fn recfn_param_shadowing_function_name_is_renamed() {
    use crate::pseudo::ast::Binder;
    use crate::pseudo::var_id::VarId;
    // `let helper = rec fn helper(x) { x }` then `rec fn caller(helper) { helper(1) }`:
    // caller's param `helper` shadows the function `helper`, so a use reads as a call
    // to it. The param has a distinct VarId, so it is renamed to `helper_2` by id.
    let fn_id = VarId::new(8001);
    let param_id = VarId::new(8002);
    let expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(8000)),
        value: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("helper", fn_id),
            params: vec![Binder::new("x", VarId::new(8003))],
            body: PBox::new(PseudoExpr::var_with_id("x", VarId::new(8003))),
        }),
        body: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("caller", VarId::new(8004)),
            params: vec![Binder::new("helper", param_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("helper", param_id)),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };

    let disambiguated = debug_disambiguate_shadowed_lets(&expr);
    let rendered = format!("{disambiguated:?}");
    assert!(
        rendered.contains("Binder { name: \"helper_2\""),
        "the param shadowing the function name must be renamed to helper_2, got: {rendered}"
    );
    // The function binding itself keeps its name.
    assert!(
        rendered.contains("name: \"helper\""),
        "the `helper` function name must be preserved, got: {rendered}"
    );
}

#[test]
fn duplicate_recfn_param_names_still_disambiguate() {
    let expr = PseudoExpr::RecFn {
        name: "outer".to_string().into(),
        params: vec!["list".to_string().into(), "list".to_string().into()],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("outer")),
            args: vec![PseudoExpr::var("list"), PseudoExpr::var("list")].into(),
        }),
    };

    let disambiguated = debug_disambiguate_shadowed_lets(&expr);
    let rendered = format!("{disambiguated:?}");

    assert!(
        rendered.contains("Binder { name: \"list\"")
            && rendered.contains("Binder { name: \"list_2\""),
        "duplicate recfn params should still disambiguate within the same signature, got: {rendered}"
    );
}

#[test]
fn nested_recfn_param_does_not_rename_against_outer_let() {
    let expr = PseudoExpr::Let {
        name: "list".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::var("outer_list")),
        body: PBox::new(PseudoExpr::Let {
            name: "decode_credential".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "decode_credential".to_string().into(),
                params: vec!["list".to_string().into(), "acc".to_string().into()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("decode_credential")),
                    args: vec![PseudoExpr::var("list"), PseudoExpr::var("acc")].into(),
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("decode_credential")),
                args: vec![PseudoExpr::var("list")].into(),
            }),
        }),
    };

    let disambiguated = debug_disambiguate_shadowed_lets(&expr);
    let rendered = format!("{disambiguated:?}");

    assert!(
        rendered.contains("params: [Binder { name: \"list\"")
            && rendered.contains("Binder { name: \"acc\"")
            && !rendered.contains("list_2")
            && !rendered.contains("list_3"),
        "nested recfn param should not rename against outer lets, got: {rendered}"
    );
}

#[test]
fn lambda_param_rename_does_not_capture_outer_function_refs() {
    let outer_acc_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let lambda_acc_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let list_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();

    let expr = PseudoExpr::Let {
        name: "acc".to_string(),
        id: Some(outer_acc_id),
        value: PBox::new(PseudoExpr::var("outer_acc")),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("acc", lambda_acc_id),
                Binder::new("list", list_id),
            ],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("acc", outer_acc_id)),
                args: vec![
                    PseudoExpr::BinOp {
                        op: BinaryOp::Add,
                        left: PBox::new(PseudoExpr::var_with_id("acc", lambda_acc_id)),
                        right: PBox::new(PseudoExpr::int(1)),
                    },
                    PseudoExpr::var_with_id("list", list_id),
                ]
                .into(),
            }),
        }),
    };

    let disambiguated = debug_disambiguate_shadowed_lets(&expr);
    let rendered = format!("{disambiguated:?}");

    assert!(
        rendered.contains("params: [Binder { name: \"acc_2\"")
            && rendered.contains("function: Var { name: \"acc\"")
            && rendered.contains("left: Var { name: \"acc_2\""),
        "lambda param rename should keep outer function refs untouched, got: {rendered}"
    );
}

#[test]
fn let_disambiguation_keeps_outer_capture_refs_by_id() {
    let outer_value_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let inner_value_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();

    let expr = PseudoExpr::Let {
        name: "value".to_string(),
        id: Some(outer_value_id),
        value: PBox::new(PseudoExpr::var("outer_value")),
        body: PBox::new(PseudoExpr::Let {
            name: "value".to_string(),
            id: Some(inner_value_id),
            value: PBox::new(PseudoExpr::var("inner_value")),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("value", outer_value_id),
                    PseudoExpr::var_with_id("value", inner_value_id),
                ]
                .into(),
            )),
        }),
    };

    let disambiguated = debug_disambiguate_shadowed_lets(&expr);
    let rendered = format!("{disambiguated:?}");

    assert!(
        rendered.contains("Tuple([Var { name: \"value\", id:")
            && rendered.contains("Var { name: \"value_2\", id:"),
        "let disambiguation should rename only the shadowing binder uses, got: {rendered}"
    );
}

#[test]
fn let_disambiguation_does_not_rename_same_name_foreign_ref_when_binder_unused() {
    let outer_value_id = VarId::new(610);
    let inner_value_id = VarId::new(611);

    let expr = PseudoExpr::Let {
        name: "value".to_string(),
        id: Some(outer_value_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Let {
            name: "value".to_string(),
            id: Some(inner_value_id),
            value: PBox::new(PseudoExpr::Unit),
            body: PBox::new(PseudoExpr::var_with_id("value", outer_value_id)),
        }),
    };

    let disambiguated = debug_disambiguate_shadowed_lets(&expr);

    match disambiguated {
        PseudoExpr::Let { body, .. } => match body.into_inner() {
            PseudoExpr::Let {
                name,
                id,
                body: inner_body,
                ..
            } => {
                assert_eq!(name, "value_2");
                assert_eq!(id, Some(inner_value_id));
                assert!(matches!(
                    inner_body.as_ref(),
                    PseudoExpr::Var { name, id } if name == "value" && *id == Some(outer_value_id)
                ));
            }
            other => panic!("expected inner let after disambiguation, got {other:?}"),
        },
        other => panic!("expected outer let after disambiguation, got {other:?}"),
    }
}

#[test]
fn let_disambiguation_fallback_renames_only_compat_refs() {
    let outer_value_id = VarId::new(612);
    let inner_value_id = VarId::new(613);
    let foreign_value_id = VarId::new(614);

    let expr = PseudoExpr::Let {
        name: "value".to_string(),
        id: Some(outer_value_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Let {
            name: "value".to_string(),
            id: Some(inner_value_id),
            value: PBox::new(PseudoExpr::Unit),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::compat_var("value"),
                    PseudoExpr::var_with_id("value", foreign_value_id),
                ]
                .into(),
            )),
        }),
    };

    let disambiguated = debug_disambiguate_shadowed_lets(&expr);

    match disambiguated {
        PseudoExpr::Let { body, .. } => match body.into_inner() {
            PseudoExpr::Let {
                name,
                id,
                body: inner_body,
                ..
            } => {
                assert_eq!(name, "value_2");
                assert_eq!(id, Some(inner_value_id));
                assert!(
                    matches!(
                        inner_body.as_ref(),
                        PseudoExpr::Tuple(items)
                            if matches!(
                                &items[0],
                                PseudoExpr::Var { name, id } if name == "value_2" && id.get().is_none()
                            )
                            && matches!(
                                &items[1],
                                PseudoExpr::Var { name, id } if name == "value" && *id == Some(foreign_value_id)
                            )
                    ),
                    "fallback should rename only compat same-name refs, got: {inner_body:?}"
                );
            }
            other => panic!("expected inner let after disambiguation, got {other:?}"),
        },
        other => panic!("expected outer let after disambiguation, got {other:?}"),
    }
}

#[test]
fn let_disambiguation_fallback_respects_when_subject_name_shadow() {
    let outer_x_id = VarId::new(615);
    let inner_x_id = VarId::new(616);
    let subject_id = VarId::new(617);

    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_x_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(inner_x_id),
            value: PBox::new(PseudoExpr::Unit),
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::compat_var("x")),
                subject_name: Some(Binder::new("x", subject_id)),
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: Some(PseudoExpr::compat_var("x")),
                    body: PseudoExpr::compat_var("x"),
                }],
            }),
        }),
    };

    let disambiguated = debug_disambiguate_shadowed_lets(&expr);

    match disambiguated {
        PseudoExpr::Let { body, .. } => match body.into_inner() {
            PseudoExpr::Let {
                name,
                id,
                body: inner_body,
                ..
            } => {
                assert_eq!(name, "x_2");
                assert_eq!(id, Some(inner_x_id));
                assert!(
                    matches!(
                        inner_body.as_ref(),
                        PseudoExpr::When { subject, subject_name, clauses }
                            if matches!(subject.as_ref(), PseudoExpr::Var { name, id } if name == "x_2" && id.get().is_none())
                                && matches!(
                                    subject_name,
                                    Some(binder) if binder.name == "x" && binder.id == subject_id
                                )
                                && matches!(
                                    clauses.as_slice(),
                                    [WhenClause { guard: Some(guard), body, .. }]
                                        if matches!(guard, PseudoExpr::Var { name, id } if name == "x" && id.get().is_none())
                                            && matches!(body, PseudoExpr::Var { name, id } if name == "x" && id.get().is_none())
                                )
                    ),
                    "fallback must still rename the when subject but not compat refs bound by when subject_name, got: {inner_body:?}"
                );
            }
            other => panic!("expected inner let after disambiguation, got {other:?}"),
        },
        other => panic!("expected outer let after disambiguation, got {other:?}"),
    }
}

#[test]
fn let_disambiguation_fallback_respects_when_pattern_shadow() {
    let outer_x_id = VarId::new(618);
    let inner_x_id = VarId::new(619);
    let pattern_x_id = VarId::new(620);

    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_x_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(inner_x_id),
            value: PBox::new(PseudoExpr::Unit),
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::compat_var("x")),
                subject_name: None,
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Var(Binder::new("x", pattern_x_id)),
                    guard: Some(PseudoExpr::compat_var("x")),
                    body: PseudoExpr::compat_var("x"),
                }],
            }),
        }),
    };

    let disambiguated = debug_disambiguate_shadowed_lets(&expr);

    match disambiguated {
        PseudoExpr::Let { body, .. } => match body.into_inner() {
            PseudoExpr::Let {
                name,
                id,
                body: inner_body,
                ..
            } => {
                assert_eq!(name, "x_2");
                assert_eq!(id, Some(inner_x_id));
                assert!(
                    matches!(
                        inner_body.as_ref(),
                        PseudoExpr::When { subject, clauses, .. }
                            if matches!(subject.as_ref(), PseudoExpr::Var { name, id } if name == "x_2" && id.get().is_none())
                                && matches!(
                                    clauses.as_slice(),
                                    [WhenClause {
                                        pattern: WhenPattern::Var(binder),
                                        guard: Some(guard),
                                        body,
                                    }]
                                        if binder.name == "x"
                                            && binder.id == pattern_x_id
                                            && matches!(guard, PseudoExpr::Var { name, id } if name == "x" && id.get().is_none())
                                            && matches!(body, PseudoExpr::Var { name, id } if name == "x" && id.get().is_none())
                                )
                    ),
                    "fallback must still rename the when subject but not compat refs bound by when pattern, got: {inner_body:?}"
                );
            }
            other => panic!("expected inner let after disambiguation, got {other:?}"),
        },
        other => panic!("expected outer let after disambiguation, got {other:?}"),
    }
}

#[test]
fn prepare_for_render_applies_final_naming_before_disambiguation() {
    let expr = PseudoExpr::RecFn {
        name: "rec_fn_15".to_string().into(),
        params: vec!["v_365".to_string().into()],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("List.is_empty")),
                args: vec![PseudoExpr::var("v_365")].into(),
            }),
            then_branch: PBox::new(PseudoExpr::int(0)),
            else_branch: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("rec_fn_15")),
                    args: vec![PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("List.tail")),
                        args: vec![PseudoExpr::var("v_365")].into(),
                    }]
                    .into(),
                }),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
    };

    let prepared = prepare_for_render(&expr, &RenderCtx::default());
    let rendered = format!("{prepared:?}");

    assert!(
        rendered.contains("name: \"count\"")
            && rendered.contains("Binder { name: \"list\"")
            && !rendered.contains("rec_fn_15")
            && !rendered.contains("v_365"),
        "final render prep should rename late generic helpers before disambiguation, got: {rendered}"
    );
}

#[test]
fn expr_contains_var_name_still_walks_literal_pattern_outside_clause_scope() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: Some("x".into()),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Literal(PseudoExpr::var("x")),
            guard: Some(PseudoExpr::var("x")),
            body: PseudoExpr::var("x"),
        }],
    };

    assert!(debug_expr_contains_var_name(&expr, "x"));
}

#[test]
fn expr_contains_var_name_blocks_guard_and_body_when_clause_binds_target() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: Some("x".into()),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: Some(PseudoExpr::var("x")),
            body: PseudoExpr::var("x"),
        }],
    };

    assert!(!debug_expr_contains_var_name(&expr, "x"));
}

#[test]
fn rename_var_use_by_id_in_expr_only_renames_target_id() {
    let target_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let other_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();

    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::var_with_id("item", target_id),
            PseudoExpr::var_with_id("item", other_id),
        ]
        .into(),
    );

    let renamed = rename_var_use_by_id_in_expr(&expr, target_id, "payload");

    assert_eq!(
        renamed,
        PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("payload", target_id),
                PseudoExpr::var_with_id("item", other_id),
            ]
            .into()
        )
    );
}

#[test]
fn rename_var_use_by_id_in_expr_renames_when_subject_name_and_uses() {
    let subject_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: Some(Binder::new("ctx", subject_id)),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: Some(PseudoExpr::var_with_id("ctx", subject_id)),
            body: PseudoExpr::var_with_id("ctx", subject_id),
        }],
    };

    let renamed = rename_var_use_by_id_in_expr(&expr, subject_id, "purpose");

    assert_eq!(
        renamed,
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("subject")),
            subject_name: Some(Binder::new("purpose", subject_id)),
            clauses: vec![WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: Some(PseudoExpr::var_with_id("purpose", subject_id)),
                body: PseudoExpr::var_with_id("purpose", subject_id),
            }],
        }
    );
}

#[test]
fn rename_var_use_by_id_in_expr_preserves_let_value_and_body_order() {
    let target_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let body_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let binding_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();

    let expr = PseudoExpr::Let {
        name: "binding".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::var_with_id("value_ref", target_id)),
        body: PBox::new(PseudoExpr::var_with_id("body_ref", body_id)),
    };

    let renamed = rename_var_use_by_id_in_expr(&expr, target_id, "renamed_value");

    assert_eq!(
        renamed,
        PseudoExpr::Let {
            name: "binding".to_string(),
            id: Some(binding_id),
            value: PBox::new(PseudoExpr::var_with_id("renamed_value", target_id)),
            body: PBox::new(PseudoExpr::var_with_id("body_ref", body_id)),
        }
    );
}

#[test]
fn does_not_inline_slice_alias_into_same_name_foreign_param() {
    let alias_id = VarId::new(760);
    let param_id = VarId::new(761);
    let list_tail = PseudoExpr::BuiltinCall {
        name: "List.tail".to_string().into(),
        args: vec![].into(),
    };
    let expr = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(alias_id),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(list_tail),
            args: vec![PseudoExpr::var("fields")].into(),
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("r", param_id)],
            body: PBox::new(PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::var_with_id("r", param_id)),
                index: 0,
            }),
        }),
    };

    let folded = debug_inline_slice_chain_aliases(expr);

    assert!(
        matches!(
            &folded,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::Lambda { params, body }
                        if matches!(params.as_slice(), [param] if param.as_str() == "r" && param.id == param_id)
                            && matches!(
                                body.as_ref(),
                                PseudoExpr::IndexAccess { collection, index }
                                    if *index == 0
                                        && matches!(collection.as_ref(), PseudoExpr::Var { name, id } if name == "r" && *id == Some(param_id))
                            )
                )
        ),
        "slice alias must not inline into same-name foreign lambda param refs, got: {folded:?}"
    );
}

/// Chain `let X = Y[k..]; let head = X[0]` collapses so the `head`
/// binding reads directly from the base: `let head = Y[k]`.
#[test]
fn inlines_single_slice_alias_then_index_zero() {
    let list_head = PseudoExpr::BuiltinCall {
        name: "List.tail".to_string().into(),
        args: vec![].into(),
    };
    let r18_value = PseudoExpr::Apply {
        function: PBox::new(list_head.clone()),
        args: vec![PseudoExpr::var("fields")].into(),
    };
    let body = PseudoExpr::Let {
        name: "s18".to_string(),
        id: VarId::fresh_binding().into(),
        value: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("r18")),
            index: 0,
        }),
        body: PBox::new(PseudoExpr::var("s18")),
    };
    let expr = PseudoExpr::Let {
        name: "r18".to_string(),
        id: VarId::fresh_binding().into(),
        value: PBox::new(r18_value),
        body: PBox::new(body),
    };

    let folded = debug_inline_slice_chain_aliases(expr);

    // Expected: `let s18 = fields[1]` inside the outer Let.
    let inner_let = match folded {
        PseudoExpr::Let { body, .. } => body.into_inner(),
        _ => panic!("expected Let"),
    };
    let s18_value = match inner_let {
        PseudoExpr::Let { value, .. } => value.into_inner(),
        _ => panic!("expected inner Let"),
    };
    match s18_value {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 1);
            match collection.into_inner() {
                PseudoExpr::Var { name, .. } => assert_eq!(name, "fields"),
                other => panic!("expected Var(fields), got {:?}", other),
            }
        }
        other => panic!("expected IndexAccess, got {:?}", other),
    }
}

/// Nested slice chain `let r = fields[1..]; let t = r[1..]; let u = t[0]`
/// collapses so that `u` reads `fields[2]`.
#[test]
fn inlines_nested_slice_chain_then_index() {
    fn list_tail(arg: PseudoExpr) -> PseudoExpr {
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::BuiltinCall {
                name: "List.tail".to_string().into(),
                args: vec![].into(),
            }),
            args: vec![arg].into(),
        }
    }

    let u_let = PseudoExpr::Let {
        name: "u".to_string(),
        id: VarId::fresh_binding().into(),
        value: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("t")),
            index: 0,
        }),
        body: PBox::new(PseudoExpr::var("u")),
    };
    let t_let = PseudoExpr::Let {
        name: "t".to_string(),
        id: VarId::fresh_binding().into(),
        value: PBox::new(list_tail(PseudoExpr::var("r"))),
        body: PBox::new(u_let),
    };
    let expr = PseudoExpr::Let {
        name: "r".to_string(),
        id: VarId::fresh_binding().into(),
        value: PBox::new(list_tail(PseudoExpr::var("fields"))),
        body: PBox::new(t_let),
    };

    let folded = debug_inline_slice_chain_aliases(expr);

    // Descend through Let(r) / Let(t) and find the u's value.
    let u_value = match folded {
        PseudoExpr::Let { body, .. } => match body.into_inner() {
            PseudoExpr::Let { body: inner, .. } => match inner.into_inner() {
                PseudoExpr::Let { value, .. } => value.into_inner(),
                other => panic!("expected u's Let, got {:?}", other),
            },
            other => panic!("expected t's Let, got {:?}", other),
        },
        other => panic!("expected r's Let, got {:?}", other),
    };
    match u_value {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 2);
            match collection.into_inner() {
                PseudoExpr::Var { name, .. } => assert_eq!(name, "fields"),
                other => panic!("expected Var(fields), got {:?}", other),
            }
        }
        other => panic!("expected IndexAccess(fields, 2), got {:?}", other),
    }
}

/// The simplifier's `fn(_) { v_NNN.tag }` leaves the body
/// reference dangling; renaming `_` back to `v_NNN` binds it.
#[test]
fn b17b_repairs_underscore_lambda_with_single_dangling_v_temp() {
    let param_id = VarId::fresh_binding();
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("_", param_id)],
        body: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var("v_450")),
            selector: crate::pseudo::field_selector::FieldSelector::NamedField("tag".to_string()),
        }),
    };
    let repaired = debug_repair_underscore_lambda_params_with_dangling_uses(lambda);
    match repaired {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "v_450");
            assert_eq!(params[0].id, param_id);
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::FieldAccess { record, .. }
                        if matches!(
                            record.as_ref(),
                            PseudoExpr::Var { name, id, .. } if name == "v_450" && *id == Some(param_id)
                        )
                ),
                "expected dangling temp ref to retarget to the repaired binder id, got {body:?}"
            );
        }
        other => panic!("expected Lambda, got {:?}", other),
    }
}

#[test]
fn b17b_repairs_underscore_lambda_with_authoritative_dangling_v_temp_id() {
    let param_id = VarId::fresh_binding();
    let body_id = VarId::new(6111);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("_", param_id)],
        body: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("v_450", body_id)),
            selector: crate::pseudo::field_selector::FieldSelector::NamedField("tag".to_string()),
        }),
    };
    let repaired = debug_repair_underscore_lambda_params_with_dangling_uses(lambda);
    match repaired {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "v_450");
            assert_eq!(
                params[0].id, body_id,
                "expected repaired binder to adopt the authoritative dangling ref id"
            );
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::FieldAccess { record, .. }
                        if matches!(
                            record.as_ref(),
                            PseudoExpr::Var { name, id, .. } if name == "v_450" && *id == Some(body_id)
                        )
                ),
                "expected repaired body ref to keep the authoritative dangling id, got {body:?}"
            );
        }
        other => panic!("expected Lambda, got {:?}", other),
    }
}

#[test]
fn prepare_for_render_can_change_binder_id_after_solver_boundary() {
    let param_id = VarId::fresh_binding();
    let body_id = VarId::new(6112);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("_", param_id)],
        body: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("v_612", body_id)),
            selector: crate::pseudo::field_selector::FieldSelector::NamedField("tag".to_string()),
        }),
    };

    let prepared = prepare_for_render(&lambda, &RenderCtx::default());

    match prepared {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "v_612");
            assert_eq!(
                params[0].id, body_id,
                "render-prep may adopt a dangling ref id for a repaired binder"
            );
            assert_ne!(
                params[0].id, param_id,
                "FinalTypeTable coverage cannot assume render-prep keeps solver-input binder ids"
            );
            // `lower_constr_field_sugar` is gated on compilable-data-access,
            // OFF by default, so `record.tag` stays `NamedField("tag")`. The
            // VarId retargeting under test is unaffected either way.
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::FieldAccess { record, .. }
                        if matches!(
                            record.as_ref(),
                            PseudoExpr::Var { name, id, .. } if name == "v_612" && *id == Some(body_id)
                        )
                ),
                "expected render-prep to retarget the repaired body ref, got {body:?}"
            );
        }
        other => panic!("expected Lambda, got {:?}", other),
    }
}

/// Multi-arg shape: `fn(_, _, _) { v_5 + v_42 }` → `fn(v_5, v_42, _)`.
/// Sorted ascending so leftmost slot binds smallest temp.
#[test]
fn b17b_repairs_multi_underscore_lambda_with_multiple_temps() {
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("_", VarId::fresh_binding()),
            Binder::new("_", VarId::fresh_binding()),
            Binder::new("_", VarId::fresh_binding()),
        ],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var("v_42")),
            right: PBox::new(PseudoExpr::var("v_5")),
        }),
    };
    let repaired = debug_repair_underscore_lambda_params_with_dangling_uses(lambda);
    match repaired {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 3);
            let names: Vec<&str> = params.iter().map(|p| p.as_str()).collect();
            assert_eq!(names, vec!["v_5", "v_42", "_"]);
        }
        other => panic!("expected Lambda, got {:?}", other),
    }
}

/// No repair when there are no dangling temps.
#[test]
fn b17b_leaves_clean_underscore_lambda_alone() {
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("_", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let repaired = debug_repair_underscore_lambda_params_with_dangling_uses(lambda);
    match repaired {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params[0].as_str(), "_");
        }
        other => panic!("expected Lambda, got {:?}", other),
    }
}

// =====================================================================
// The validator-entry binder is minted as `decompiled`, not `validator`,
// so `sanitize_identifier`'s keyword guard doesn't append a trailing `_`.
// =====================================================================

#[test]
fn p2_3_promote_finds_validator_entry_under_new_decompiled_name() {
    let entry_id = VarId::fresh_binding();
    let entry = PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(entry_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["script_context".into()],
            body: PBox::new(PseudoExpr::Bool(true)),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };
    let prepared = prepare_for_render(&entry, &RenderCtx::default());
    match prepared {
        PseudoExpr::Let { name, .. } => {
            assert_eq!(
                name, "decompiled",
                "promote_validator_entry_first must keep the `decompiled` marker name; \
                 if this fails the pass is no longer finding the entry"
            );
        }
        other => panic!("expected Let entry, got {other:?}"),
    }
}

#[test]
fn p2_3_renders_fn_decompiled_not_fn_validator_underscore() {
    // End-to-end: the wrapped AST renders `fn decompiled(...)`, never
    // the keyword-collision `fn validator_(...)`.
    let entry_id = VarId::fresh_binding();
    let entry = PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(entry_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["script_context".into()],
            body: PBox::new(PseudoExpr::Bool(true)),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };
    let output = entry.to_pretty();
    assert!(
        !output.contains("fn validator_("),
        "rendered output must not contain the legacy `fn validator_(` form:\n{output}"
    );
    assert!(
        output.contains("fn decompiled(") || output.contains("decompiled = fn"),
        "rendered output must contain a `decompiled` entry function:\n{output}"
    );
}

// =====================================================================
// `coll[N..][K]` → `coll[N+K]` must collapse for BOTH `List.tail` AST
// shapes `strip_list_tail` accepts: the curried
// `Apply(BuiltinCall(List.tail, []), [arg])` and the direct
// `BuiltinCall(List.tail, [arg])`.
// =====================================================================

#[test]
fn p5_3_collapses_direct_form_list_tail_with_index() {
    // Direct form: `BuiltinCall(List.tail, [arg])`.
    // Shape: `IndexAccess { collection: List.tail(fields), index: 1 }`
    // → `IndexAccess { collection: fields, index: 2 }`.
    let direct_tail = PseudoExpr::BuiltinCall {
        name: "List.tail".to_string().into(),
        args: vec![PseudoExpr::var("fields")].into(),
    };
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(direct_tail),
        index: 1,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    match folded {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 2);
            assert!(matches!(*collection, PseudoExpr::Var { ref name, .. } if name == "fields"));
        }
        other => panic!("expected IndexAccess, got {:?}", other),
    }
}

#[test]
fn p5_3_collapses_apply_form_list_tail_with_index() {
    let apply_tail = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: "List.tail".to_string().into(),
            args: vec![].into(),
        }),
        args: vec![PseudoExpr::var("fields")].into(),
    };
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(apply_tail),
        index: 3,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    match folded {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 4);
            assert!(matches!(*collection, PseudoExpr::Var { ref name, .. } if name == "fields"));
        }
        other => panic!("expected IndexAccess, got {:?}", other),
    }
}

#[test]
fn p5_3_collapses_direct_form_chain_depth_two() {
    // `List.tail(List.tail(fields))[1]` → `fields[3]` (depth 2 + index 1).
    let inner = PseudoExpr::BuiltinCall {
        name: "List.tail".to_string().into(),
        args: vec![PseudoExpr::var("fields")].into(),
    };
    let outer = PseudoExpr::BuiltinCall {
        name: "List.tail".to_string().into(),
        args: vec![inner].into(),
    };
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(outer),
        index: 1,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    match folded {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 3);
            assert!(matches!(*collection, PseudoExpr::Var { ref name, .. } if name == "fields"));
        }
        other => panic!("expected IndexAccess, got {:?}", other),
    }
}

#[test]
fn p5_3_folds_unsafe_base_in_place() {
    // The IN-PLACE fold `X[k..][n]` → `X[k+n]` is sound for ANY base X,
    // including a destructor-like `BuiltinCall`
    // (`Data.un_list(x)[1..][1]` → `Data.un_list(x)[2]`): X stays in
    // exactly one textual place, both forms lower to the identical
    // `head_list(tail_list^(k+n)(X))`, and the fail set is identical at
    // every list length. `is_safe_base` guards only the base-DUPLICATING
    // alias-inlining path (`make_list_tail_chain`), not this fold.
    let unsafe_base = PseudoExpr::BuiltinCall {
        name: "Data.un_list".to_string().into(),
        args: vec![PseudoExpr::var("x")].into(),
    };
    let direct_tail = PseudoExpr::BuiltinCall {
        name: "List.tail".to_string().into(),
        args: vec![unsafe_base].into(),
    };
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(direct_tail),
        index: 1,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    // `List.tail(Data.un_list(x))[1]` folds in place to `Data.un_list(x)[2]`.
    match folded {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 2);
            assert!(
                matches!(*collection, PseudoExpr::BuiltinCall { ref name, .. } if name == "Data.un_list")
            );
        }
        other => panic!("expected folded Data.un_list(x)[2], got {:?}", other),
    }
}

/// `expect!(Not(Let X = v in Bool body), then, non_string_else)`:
///   1. D2 lifts the inner Let out: `Let X = v in expect!(Not(body),
///      then, non_string_else)`.
///   2. D3 converts the remaining 3-arg expect! — `Not(body)` is
///      structurally Bool — to `If`.
///      Final shape: `Let { X, v, If { Not(body), then, else } }`.
///
/// Pins the ordering invariant: D2 must run before D3, since D3
/// alone refuses `Not(Let)`.
#[test]
fn d3_composed_with_d2_lifts_let_then_rewrites_to_if() {
    use crate::pseudo::ast::UnaryOp;
    let let_value_id = VarId::fresh_binding();
    let let_body_id = VarId::fresh_binding();
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "expect!".to_string(),
            id: None,
        }),
        args: vec![
            // args[0]: Not(Let X = v in Bool body)
            PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand: PBox::new(PseudoExpr::Let {
                    name: "x".to_string(),
                    id: Some(let_value_id),
                    value: PBox::new(PseudoExpr::Bool(true)),
                    body: PBox::new(PseudoExpr::BinOp {
                        op: BinaryOp::Eq,
                        left: PBox::new(PseudoExpr::Var {
                            name: "x".to_string(),
                            id: Some(let_value_id),
                        }),
                        right: PBox::new(PseudoExpr::Bool(false)),
                    }),
                }),
            },
            // args[1]: then
            PseudoExpr::Var {
                name: "then_branch".to_string(),
                id: Some(let_body_id),
            },
            // args[2]: non-String else
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: "else_fn".to_string(),
                    id: Some(VarId::fresh_binding()),
                }),
                args: vec![].into(),
            },
        ]
        .into(),
    };

    let out = prepare_for_render(&input, &RenderCtx::default());

    // No `decompiled` binder, so `promote_validator_entry_first`
    // rebuilds the let chain as-is; the outer Let is D2's lift.
    let outer_let = match out {
        PseudoExpr::Let {
            name, value, body, ..
        } if name == "x" => (value, body),
        other => panic!("expected outer Let lifted by D2, got {:?}", other),
    };
    // The outer Let must bind the lifted value.
    assert!(matches!(*outer_let.0, PseudoExpr::Bool(true)));
    // The body must be the D3-rewritten If.
    match outer_let.1.into_inner() {
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            // Condition is Not(BinOp::Eq(..)) — D2 lifted the Let
            // out, leaving a structurally Bool operand.
            assert!(matches!(
                *condition,
                PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    ..
                }
            ));
            assert!(matches!(
                *then_branch,
                PseudoExpr::Var { ref name, .. } if name == "then_branch"
            ));
            assert!(matches!(*else_branch, PseudoExpr::Apply { .. }));
        }
        other => panic!("expected D3 If after composition, got {other:?}"),
    }
}

#[test]
fn p5_3_collapses_through_field_access_record_base() {
    // `x_29.fields[1..][1]`:
    // `IndexAccess { collection: List.tail(FieldAccess(x_29, fields)), index: 1 }`
    // → `IndexAccess { collection: FieldAccess(x_29, fields), index: 2 }`.
    use crate::pseudo::field_selector::FieldSelector;
    let field_access = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::var("x_29")),
        selector: FieldSelector::NamedField("fields".to_string()),
    };
    let direct_tail = PseudoExpr::BuiltinCall {
        name: "List.tail".to_string().into(),
        args: vec![field_access.clone()].into(),
    };
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(direct_tail),
        index: 1,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    match folded {
        PseudoExpr::IndexAccess { collection, index } => {
            assert_eq!(index, 2);
            assert!(matches!(*collection, PseudoExpr::FieldAccess { .. }));
        }
        other => panic!("expected IndexAccess, got {:?}", other),
    }
}

/// `[a, b, c, d][2]` on a literal List folds to `c` when every
/// skipped element (0..2) is pure.
#[test]
fn p5_3_ext_folds_literal_list_index_when_skipped_are_pure() {
    let elements = vec![
        PseudoExpr::Int(10.into()),
        PseudoExpr::Int(20.into()),
        PseudoExpr::Int(30.into()),
        PseudoExpr::Int(40.into()),
    ];
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::List {
            elements: elements.into(),
            tail: None,
        }),
        index: 2,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    match folded {
        PseudoExpr::Int(n) => assert_eq!(n.to_string(), "30"),
        other => panic!("expected literal Int(30), got {:?}", other),
    }
}

/// `List.tail([a, b, c, d])[1]` folds through the slice chain to
/// `c` (slice depth 1 + index 1 = offset 2 into the literal).
#[test]
fn p5_3_ext_folds_literal_list_through_slice_chain() {
    let elements = vec![
        PseudoExpr::Int(10.into()),
        PseudoExpr::Int(20.into()),
        PseudoExpr::Int(30.into()),
        PseudoExpr::Int(40.into()),
    ];
    let list_lit = PseudoExpr::List {
        elements: elements.into(),
        tail: None,
    };
    let sliced = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: "List.tail".to_string().into(),
            args: vec![].into(),
        }),
        args: vec![list_lit].into(),
    };
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(sliced),
        index: 1,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    match folded {
        PseudoExpr::Int(n) => assert_eq!(n.to_string(), "30"),
        other => panic!("expected literal Int(30), got {:?}", other),
    }
}

/// Index out of bounds — leave the IndexAccess alone, let
/// the runtime fail.
#[test]
fn p5_3_ext_refuses_when_index_out_of_bounds() {
    let elements = vec![PseudoExpr::Int(10.into()), PseudoExpr::Int(20.into())];
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::List {
            elements: elements.into(),
            tail: None,
        }),
        index: 5, // out of range
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    assert!(matches!(folded, PseudoExpr::IndexAccess { .. }));
}

/// Impure skipped element (Apply, BuiltinCall, etc.):
/// discarding it would skip observable evaluation.
#[test]
fn p5_3_ext_refuses_when_skipped_element_is_impure() {
    let elements = vec![
        // Impure: a function call that could trace or fail.
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("compute_first")),
            args: vec![].into(),
        },
        PseudoExpr::Int(20.into()),
    ];
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::List {
            elements: elements.into(),
            tail: None,
        }),
        index: 1,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    // Must NOT fold — the skipped Apply is not pure.
    assert!(matches!(folded, PseudoExpr::IndexAccess { .. }));
}

/// `purity::is_pure_value` treats the `Var{name:"expect!",
/// id:None}` sentinel as impure: otherwise `[expect!, b][1]` would
/// fold to `b` and silently drop the abort.
#[test]
fn p5_3_ext_refuses_when_skipped_element_is_expect_sentinel() {
    let elements = vec![
        PseudoExpr::Var {
            name: "expect!".to_string(),
            id: None,
        },
        PseudoExpr::Int(20.into()),
    ];
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::List {
            elements: elements.into(),
            tail: None,
        }),
        index: 1,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    assert!(
        matches!(folded, PseudoExpr::IndexAccess { .. }),
        "must refuse when the skipped element is the abort sentinel — got {folded:?}"
    );
}

/// A list with a tail (`[a, b, ..rest]`) never folds: slicing past
/// the literal elements could fall through to the tail.
#[test]
fn p5_3_ext_refuses_when_list_has_tail() {
    let elements = vec![PseudoExpr::Int(10.into()), PseudoExpr::Int(20.into())];
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::List {
            elements: elements.into(),
            tail: Some(PBox::new(PseudoExpr::var("rest"))),
        }),
        index: 0,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    assert!(matches!(folded, PseudoExpr::IndexAccess { .. }));
}

/// Index 0 always folds: nothing is skipped, so purity is moot.
#[test]
fn p5_3_ext_folds_at_index_zero_regardless_of_purity() {
    let elements = vec![
        PseudoExpr::Int(10.into()),
        // Even if a later element is impure, index 0 doesn't skip it.
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("compute_second")),
            args: vec![].into(),
        },
    ];
    let expr = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::List {
            elements: elements.into(),
            tail: None,
        }),
        index: 0,
    };
    let folded = debug_inline_slice_chain_aliases(expr);
    match folded {
        PseudoExpr::Int(n) => assert_eq!(n.to_string(), "10"),
        other => panic!("expected Int(10), got {:?}", other),
    }
}
