use super::{
    fix_bool_option_confusion, hoist_let_from_expect, normalize_data_constr_calls,
    recover_free_validator_carriers, rename_option_like_patterns, repair_forward_let_dependencies,
    rewrite_boolish_data_ifs, run_display_polish_layer, run_structural_final_cleanup,
};
use crate::decompile::DecompileOptions;
use crate::decompile::pipeline_passes::PipelinePassId;
use crate::decompile::pipeline_runtime::PipelineExecutor;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

fn boolish_data_if_fixture() -> PseudoExpr {
    PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("c")),
        then_branch: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var("lhs")),
            right: PBox::new(PseudoExpr::int(1)),
        }),
        else_branch: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var("rhs")),
            right: PBox::new(PseudoExpr::int(7)),
        }),
    }
}

fn stale_hoistable_helper_expr() -> PseudoExpr {
    let outer_id = VarId::new(9311);
    let stale_ref_id = VarId::new(9312);
    let helper_id = VarId::new(9313);
    let helper_param_id = VarId::new(9314);

    PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![
                PseudoExpr::Let {
                    name: "helper".to_string(),
                    id: Some(helper_id),
                    value: PBox::new(PseudoExpr::Lambda {
                        params: vec![Binder::new("y", helper_param_id)],
                        body: PBox::new(PseudoExpr::var_with_id("y", helper_param_id)),
                    }),
                    body: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
                },
                PseudoExpr::var_with_id("x", stale_ref_id),
            ]
            .into(),
        }),
    }
}

fn display_rewrite_apply_hoist_expr() -> PseudoExpr {
    let outer_x_id = VarId::new(9451);
    let inner_x_id = VarId::new(9452);

    PseudoExpr::let_bind_with_id(
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
    )
}

#[test]
fn structural_final_cleanup_retargets_even_when_optimize_is_disabled() {
    let outer_id = VarId::new(9301);
    let inner_id = VarId::new(9302);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(PseudoExpr::var_with_id("x", outer_id)),
        }),
    };
    let options = DecompileOptions {
        simplify_passes: crate::decompile::SimplifyPasses::all_off(),
        safe_mode: true,
        ..Default::default()
    };

    let cleaned =
        run_structural_final_cleanup(expr, None, &options, &std::collections::HashMap::new());

    match cleaned {
        PseudoExpr::Let { body, .. } => match body.into_inner() {
            PseudoExpr::Let { body, .. } => {
                assert!(
                    matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "x" && *id == Some(inner_id)),
                    "final cleanup must retarget stale same-name refs even when optimize=false"
                );
            }
            other => panic!("expected inner let, got {other:?}"),
        },
        other => panic!("expected outer let, got {other:?}"),
    }
}

#[test]
fn display_polish_repairs_ref_ids_before_helper_hoist() {
    let expr = stale_hoistable_helper_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let mut passes = Vec::new();
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.emit(PipelinePassId::UniquifyFinal, &expr);

    let options = DecompileOptions::default();
    let result = run_display_polish_layer(expr, &options, &mut executor);

    let retarget_position = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("display polish should retarget stale refs before id-aware hoist");
    let hoist_position = passes
        .iter()
        .position(|pass| *pass == "hoist_local_helpers")
        .expect("fixture should trigger helper hoist");
    assert!(
        retarget_position < hoist_position,
        "expected retarget before helper hoist, got passes: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn display_polish_repairs_ref_ids_after_display_rewrite_apply_hoist() {
    let expr = display_rewrite_apply_hoist_expr();
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr),
        "fixture should enter display rewrite with clean refs"
    );

    let mut passes = Vec::new();
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.emit(PipelinePassId::UniquifyFinal, &expr);

    let options = DecompileOptions::default();
    let result = run_display_polish_layer(expr, &options, &mut executor);

    let display_position = passes
        .iter()
        .position(|pass| *pass == "normalize_display_rewrites")
        .expect("fixture should trigger display rewrite");
    let retarget_position = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("display polish should repair refs after display rewrite");
    assert!(
        display_position < retarget_position,
        "expected retarget after display rewrite, got passes: {passes:?}"
    );
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "display polish must emit clean refs after display rewrite repair, got: {result:?}"
    );
}

#[test]
fn display_polish_post_late_naming_preserves_clean_same_name_shadow_refs() {
    let fn_id = VarId::new(9441);
    let outer_result_id = VarId::new(9442);
    let inner_result_id = VarId::new(9443);
    let xs_id = VarId::new(9444);
    let needle_id = VarId::new(9445);
    let item_id = VarId::new(9446);

    let expr = PseudoExpr::Let {
        name: "fn_3".to_string(),
        id: Some(fn_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("xs", xs_id), Binder::new("needle", needle_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("any_2")),
                args: vec![
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_list"),
                        args: vec![PseudoExpr::var_with_id("xs", xs_id)].into(),
                    },
                    PseudoExpr::Lambda {
                        params: vec![Binder::new("item", item_id)],
                        body: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::var_with_id("item", item_id)),
                            right: PBox::new(PseudoExpr::var_with_id("needle", needle_id)),
                        }),
                    },
                ]
                .into(),
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "fn_3_result".to_string(),
            id: Some(outer_result_id),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("fn_3", fn_id)),
                args: vec![PseudoExpr::var("inputs"), PseudoExpr::var("target")].into(),
            }),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("fn_3_result", outer_result_id),
                    PseudoExpr::Let {
                        name: "fn_3_result".to_string(),
                        id: Some(inner_result_id),
                        value: PBox::new(PseudoExpr::int(1)),
                        body: PBox::new(PseudoExpr::var_with_id("fn_3_result", inner_result_id)),
                    },
                ]
                .into(),
            )),
        }),
    };
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr),
        "fixture must start with clean same-name shadow refs"
    );

    let mut passes = Vec::new();
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.emit(PipelinePassId::UniquifyFinal, &expr);

    let options = DecompileOptions::default();
    let result = run_display_polish_layer(expr, &options, &mut executor);

    assert!(
        passes.contains(&"improve_variable_names_post_late"),
        "fixture should exercise post-late naming, got passes: {passes:?}"
    );
    assert!(
        passes.iter().all(|pass| *pass != "retarget_refs_by_scope"),
        "clean input should not need retargeting in display polish, got passes: {passes:?}"
    );
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "post-late naming should preserve clean refs, got: {result:?}"
    );

    let PseudoExpr::Let { name, id, body, .. } = result else {
        panic!("expected renamed function let");
    };
    assert_eq!(name, "contains");
    assert_eq!(id, Some(fn_id));

    let PseudoExpr::Let { name, id, body, .. } = body.as_ref() else {
        panic!("expected renamed result let, got: {body:?}");
    };
    assert_eq!(name, "contains_result");
    assert_eq!(*id, Some(outer_result_id));
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Tuple(items)
                if matches!(
                    items.as_slice(),
                    [
                        PseudoExpr::Var { name, id, .. },
                        PseudoExpr::Let {
                            name: inner_name,
                            id: Some(inner_id),
                            body: inner_body,
                            ..
                        },
                    ] if name == "contains_result"
                        && *id == Some(outer_result_id)
                        && inner_name == "fn_3_result"
                        && *inner_id == inner_result_id
                        && matches!(
                            inner_body.as_ref(),
                            PseudoExpr::Var { name, id, .. }
                                if name == "fn_3_result" && *id == Some(inner_result_id)
                        )
                )
        ),
        "expected only the outer same-name result let to be renamed, got: {body:?}"
    );
}

#[test]
fn structural_final_cleanup_skips_semantic_round_in_safe_mode() {
    let safe_options = DecompileOptions {
        simplify_passes: crate::decompile::SimplifyPasses::all_on(),
        safe_mode: true,
        ..Default::default()
    };
    let unsafe_options = DecompileOptions {
        simplify_passes: crate::decompile::SimplifyPasses::all_on(),
        safe_mode: false,
        ..Default::default()
    };

    let safe = run_structural_final_cleanup(
        boolish_data_if_fixture(),
        None,
        &safe_options,
        &std::collections::HashMap::new(),
    );
    let unsafe_output = run_structural_final_cleanup(
        boolish_data_if_fixture(),
        None,
        &unsafe_options,
        &std::collections::HashMap::new(),
    );

    assert!(
        matches!(safe, PseudoExpr::If { .. }),
        "safe_mode must skip the late semantic fixpoint"
    );
    assert!(
        matches!(unsafe_output, PseudoExpr::When { .. }),
        "non-safe optimized cleanup should run the late semantic round"
    );
}

#[test]
fn test_hoist_let_from_expect_moves_function_let_out_of_condition() {
    let helper_id = VarId::new(9501);
    let param_id = VarId::new(9502);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::Let {
                name: "check".to_string(),
                id: Some(helper_id),
                value: PBox::new(PseudoExpr::Lambda {
                    params: vec![Binder::new("x", param_id)],
                    body: PBox::new(PseudoExpr::Bool(true)),
                }),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("check", helper_id)),
                    args: vec![PseudoExpr::var("datum")].into(),
                }),
            },
            PseudoExpr::var("body"),
        ]
        .into(),
    };

    let rewritten = hoist_let_from_expect(expr);
    let PseudoExpr::Let {
        name,
        id,
        value,
        body,
    } = rewritten
    else {
        panic!("expected helper let to move outside expect!, got: {rewritten:?}");
    };
    assert_eq!(name, "check");
    assert_eq!(id, Some(helper_id));
    assert!(matches!(value.as_ref(), PseudoExpr::Lambda { .. }));

    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        panic!("expected expect! body after hoist, got: {body:?}");
    };
    assert!(matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "expect!"));
    assert_eq!(args.len(), 2);
    assert!(matches!(
        &args[0],
        PseudoExpr::Apply { function, .. }
            if matches!(
                function.as_ref(),
                PseudoExpr::Var { name, id, .. } if name == "check" && *id == Some(helper_id)
            )
    ));
    assert!(matches!(&args[1], PseudoExpr::Var { name, .. } if name == "body"));
}

#[test]
fn test_hoist_let_from_expect_keeps_non_function_let_in_condition() {
    let temp_id = VarId::new(9511);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![PseudoExpr::Let {
            name: "check".to_string(),
            id: Some(temp_id),
            value: PBox::new(PseudoExpr::Bool(true)),
            body: PBox::new(PseudoExpr::var_with_id("check", temp_id)),
        }]
        .into(),
    };

    let rewritten = hoist_let_from_expect(expr);
    let PseudoExpr::Apply { function, args } = rewritten else {
        panic!("non-function let should remain inside expect!, got: {rewritten:?}");
    };
    assert!(matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "expect!"));
    assert!(matches!(
        args.as_slice(),
        [PseudoExpr::Let { name, id, .. }] if name == "check" && *id == Some(temp_id)
    ));
}

#[test]
fn test_normalize_data_constr_calls_normalizes_data_constr_builtin() {
    let expr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::Int(2.into()),
            PseudoExpr::List {
                elements: vec![PseudoExpr::var("a"), PseudoExpr::var("b")].into(),
                tail: None,
            },
        ]
        .into(),
    };

    let normalized = normalize_data_constr_calls(expr);
    assert!(matches!(
        normalized,
        PseudoExpr::Constr { tag: 2, fields, .. } if fields.len() == 2
    ));
}

#[test]
fn test_rewrite_boolish_data_ifs_converts_typed_data_condition_to_when() {
    let expr = boolish_data_if_fixture();

    let rewritten = rewrite_boolish_data_ifs(expr, None);
    match rewritten {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(
                matches!(subject.as_ref(), PseudoExpr::Var { name, .. } if name == "c"),
                "expected when subject to stay on c, got: {subject:?}"
            );
            assert_eq!(clauses.len(), 2, "expected constructor + wildcard clauses");
            assert!(matches!(
                &clauses[0].pattern,
                WhenPattern::Constructor { tag: 1, fields, .. } if fields.is_empty()
            ));
            assert!(matches!(&clauses[1].pattern, WhenPattern::Wildcard));
        }
        other => panic!("expected typed data if to become when, got: {other:?}"),
    }
}

#[test]
fn test_rewrite_boolish_data_ifs_ignores_same_name_different_id_field_accesses() {
    let condition_id = VarId::new(9330);
    let other_id = VarId::new(9331);
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var_with_id("subject", condition_id)),
        then_branch: PBox::new(PseudoExpr::var_with_id("subject", condition_id)),
        else_branch: PBox::new(PseudoExpr::Let {
            name: "subject".to_string(),
            id: Some(other_id),
            value: PBox::new(PseudoExpr::int(0)),
            body: PBox::new(PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("subject", other_id),
                    "fields".to_string(),
                )),
                index: 0,
            }),
        }),
    };

    let rewritten = rewrite_boolish_data_ifs(expr, None);

    assert!(
        matches!(rewritten, PseudoExpr::If { .. }),
        "same-name / different-id field accesses must not make the condition look data-field accessed"
    );
}

#[test]
fn test_rewrite_boolish_data_ifs_accepts_compat_field_access_for_authoritative_condition() {
    let condition_id = VarId::new(9332);
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var_with_id("subject", condition_id)),
        then_branch: PBox::new(PseudoExpr::var_with_id("subject", condition_id)),
        else_branch: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::field_access(
                PseudoExpr::compat_var("subject"),
                "fields".to_string(),
            )),
            index: 0,
        }),
    };

    let rewritten = rewrite_boolish_data_ifs(expr, None);

    assert!(
        matches!(rewritten, PseudoExpr::When { .. }),
        "compat field access should still count as accessing authoritative condition fields"
    );
}

#[test]
fn test_rewrite_boolish_data_ifs_ignores_shadowed_compat_condition_field_accesses() {
    let other_id = VarId::new(9333);
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::compat_var("subject")),
        then_branch: PBox::new(PseudoExpr::compat_var("subject")),
        else_branch: PBox::new(PseudoExpr::Let {
            name: "subject".to_string(),
            id: Some(other_id),
            value: PBox::new(PseudoExpr::int(0)),
            body: PBox::new(PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("subject", other_id),
                    "fields".to_string(),
                )),
                index: 0,
            }),
        }),
    };

    let rewritten = rewrite_boolish_data_ifs(expr, None);

    assert!(
        matches!(rewritten, PseudoExpr::If { .. }),
        "shadowed same-name field accesses must not satisfy compat condition fallback"
    );
}

#[test]
fn test_repair_forward_let_dependencies_swaps_adjacent_dependency_chain() {
    let fields_list_id = VarId::fresh_compat_placeholder();
    let fields_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "fields_0_list".to_string(),
        id: Some(fields_list_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_list"),
            args: vec![PseudoExpr::var_with_id(
                "fields_0",
                VarId::fresh_compat_placeholder(),
            )]
            .into(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "fields_0".to_string(),
            id: Some(fields_id),
            value: PBox::new(PseudoExpr::var("source")),
            body: PBox::new(PseudoExpr::var_with_id("fields_0_list", fields_list_id)),
        }),
    };
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr),
        "forward reference is not stale until the dependency binder is hoisted over it"
    );

    let rewritten = repair_forward_let_dependencies(expr);
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&rewritten),
        "repair should retarget the forward ref after expanding the dependency binder scope"
    );
    let PseudoExpr::Let { name, body, .. } = rewritten else {
        panic!("expected let after repair");
    };
    assert_eq!(
        name, "fields_0",
        "expected dependency binder to be hoisted first"
    );
    let PseudoExpr::Let { name, value, .. } = body.as_ref() else {
        panic!("expected nested let after repair");
    };
    assert_eq!(name, "fields_0_list");
    let PseudoExpr::BuiltinCall { args, .. } = value.as_ref() else {
        panic!("expected un_list call after repair");
    };
    assert!(
        matches!(&args[0], PseudoExpr::Var { name, id } if name == "fields_0" && *id == Some(fields_id))
    );
}

#[test]
fn test_repair_forward_let_dependencies_ignores_same_name_foreign_id() {
    let outer_id = VarId::new(9350);
    let inner_id = VarId::new(9351);
    let foreign_inner_ref_id = VarId::new(9352);
    let expr = PseudoExpr::Let {
        name: "fields_0_list".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_list"),
            args: vec![PseudoExpr::var_with_id("fields_0", foreign_inner_ref_id)].into(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "fields_0".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::var("source")),
            body: PBox::new(PseudoExpr::var_with_id("fields_0_list", outer_id)),
        }),
    };

    let rewritten = repair_forward_let_dependencies(expr);

    assert!(
        matches!(
            &rewritten,
            PseudoExpr::Let { name, id, value, body }
                if name == "fields_0_list"
                    && *id == Some(outer_id)
                    && matches!(value.as_ref(), PseudoExpr::BuiltinCall { args, .. }
                        if matches!(&args[0], PseudoExpr::Var { name, id }
                            if name == "fields_0" && *id == Some(foreign_inner_ref_id)))
                    && matches!(body.as_ref(), PseudoExpr::Let { name, id, .. }
                        if name == "fields_0" && *id == Some(inner_id))
        ),
        "same-name different-id forward references must not reorder lets, got: {rewritten:?}"
    );
}

#[test]
fn test_fix_bool_option_confusion_converts_false_none_lookup_shape() {
    let expr = PseudoExpr::RecFn {
        name: Binder::new(
            "rec_fn_9",
            crate::pseudo::var_id::VarId::fresh_compat_placeholder(),
        ),
        params: vec![
            Binder::new(
                "pairs",
                crate::pseudo::var_id::VarId::fresh_compat_placeholder(),
            ),
            Binder::new(
                "needle",
                crate::pseudo::var_id::VarId::fresh_compat_placeholder(),
            ),
        ],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("pairs")),
            subject_name: Some(Binder::synthetic("pairs")),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::bool(false),
                ),
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![Binder::synthetic("entry")],
                        tail: Some(Binder::synthetic("tail")),
                    },
                    PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "fst".to_string(),
                            )),
                            right: PBox::new(PseudoExpr::var("needle")),
                        }),
                        then_branch: PBox::new(PseudoExpr::constr(
                            ConstructorShape::unknown_data(0, 1),
                            vec![PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "snd".to_string(),
                            )],
                        )),
                        else_branch: PBox::new(PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::BinOp {
                                op: BinaryOp::Lt,
                                left: PBox::new(PseudoExpr::var("needle")),
                                right: PBox::new(PseudoExpr::field_access(
                                    PseudoExpr::var("entry"),
                                    "fst".to_string(),
                                )),
                            }),
                            then_branch: PBox::new(PseudoExpr::bool(false)),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("rec_fn_9")),
                                args: vec![PseudoExpr::var("tail"), PseudoExpr::var("needle")]
                                    .into(),
                            }),
                        }),
                    },
                ),
            ],
        }),
    };

    let fixed = fix_bool_option_confusion(expr);
    let fixed_debug = format!("{fixed:?}");
    assert!(
        fixed_debug.contains("shape: Known(None)"),
        "expected false empty case to convert to None, got: {fixed_debug}"
    );
    assert!(
        fixed_debug.contains("shape: Known(Some)"),
        "expected payload branch to convert to Some, got: {fixed_debug}"
    );
    assert!(
        !fixed_debug.contains("Bool(false)"),
        "expected false-none option shape to disappear, got: {fixed_debug}"
    );
}

#[test]
fn test_rename_option_like_patterns_marks_helper_result_patterns_as_some_none() {
    let expr = PseudoExpr::Let {
        name: "lookup_result".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("lookup")),
            args: vec![PseudoExpr::var("pairs"), PseudoExpr::var("needle")].into(),
        }),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("lookup_result")),
            subject_name: Some(Binder::synthetic("lookup_result")),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    PseudoExpr::bool(false),
                ),
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::bool(true),
                ),
            ],
        }),
    };
    let expr = PseudoExpr::Let {
        name: "lookup".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(fix_bool_option_confusion(PseudoExpr::RecFn {
            name: Binder::new(
                "lookup",
                crate::pseudo::var_id::VarId::fresh_compat_placeholder(),
            ),
            params: vec![
                Binder::new(
                    "pairs",
                    crate::pseudo::var_id::VarId::fresh_compat_placeholder(),
                ),
                Binder::new(
                    "needle",
                    crate::pseudo::var_id::VarId::fresh_compat_placeholder(),
                ),
            ],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("pairs")),
                subject_name: Some(Binder::synthetic("pairs")),
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec![],
                            tail: None,
                        },
                        PseudoExpr::bool(false),
                    ),
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec![Binder::synthetic("entry")],
                            tail: Some(Binder::synthetic("tail")),
                        },
                        PseudoExpr::constr(
                            ConstructorShape::unknown_data(0, 1),
                            vec![PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "snd".to_string(),
                            )],
                        ),
                    ),
                ],
            }),
        })),
        body: PBox::new(expr),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let renamed_debug = format!("{renamed:?}");
    assert!(
        renamed_debug.contains("shape: Known(None)"),
        "expected option-like helper results to render None-patterns, got: {renamed_debug}"
    );
    assert!(
        renamed_debug.contains("shape: Known(Some)"),
        "expected option-like helper results to render Some-patterns, got: {renamed_debug}"
    );
    assert!(
        !renamed_debug.contains("Bool(false)"),
        "expected None-pattern branches on option-like subjects to stop leaking False bodies, got: {renamed_debug}"
    );
}

#[test]
fn test_fix_bool_option_confusion_converts_false_some_if_binding() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::bool(false)),
        else_branch: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 1),
            vec![PseudoExpr::var("payload")],
        )),
    };

    let fixed = fix_bool_option_confusion(expr);
    let fixed_debug = format!("{fixed:?}");
    assert!(
        fixed_debug.contains("shape: Known(None)"),
        "expected false/some if binding to become None, got: {fixed_debug}"
    );
    assert!(
        fixed_debug.contains("shape: Known(Some)"),
        "expected false/some if binding to become Some, got: {fixed_debug}"
    );
}

#[test]
fn test_rename_option_like_patterns_fills_none_for_wildcard_on_option_subject() {
    let expr = PseudoExpr::Let {
        name: "opt".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond")),
            then_branch: PBox::new(PseudoExpr::constr_known(KnownConstructor::None, vec![])),
            else_branch: PBox::new(PseudoExpr::constr_known(
                KnownConstructor::Some,
                vec![PseudoExpr::var("payload")],
            )),
        }),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("opt")),
            subject_name: Some(Binder::synthetic("opt")),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::var("payload"),
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::var("fallback")),
            ],
        }),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let renamed_debug = format!("{renamed:?}");
    assert!(
        renamed_debug.contains("Known(None)"),
        "expected wildcard branch on option-like subject to become None, got: {renamed_debug}"
    );
    assert!(
        !renamed_debug.contains("pattern: Wildcard"),
        "expected option-like wildcard branch to be specialized, got: {renamed_debug}"
    );
}

#[test]
fn test_rename_option_like_patterns_recovers_missing_some_payload_binder() {
    let expr = PseudoExpr::Let {
        name: "get_at_result".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::var("payload")],
        )),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("get_at_result")),
            subject_name: Some(Binder::synthetic("get_at_result")),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::var("y2_2"),
                ),
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                    PseudoExpr::error(),
                ),
            ],
        }),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let PseudoExpr::Let { body, .. } = renamed else {
        panic!("expected let wrapper after rename");
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected when body after rename");
    };
    let WhenClause { pattern, body, .. } = &clauses[0];
    let WhenPattern::Constructor { shape, fields, .. } = pattern else {
        panic!("expected Some pattern after rename");
    };
    assert!(
        matches!(shape, ConstructorShape::Known(KnownConstructor::Some)),
        "expected Known(Some) shape, got {shape:?}"
    );
    assert_eq!(
        fields.len(),
        1,
        "expected payload binder to be recovered, got pattern: {pattern:?}"
    );
    assert_eq!(fields[0].name, "y2_2");
    let PseudoExpr::Var { name, id, .. } = body else {
        panic!("expected body to keep payload reference");
    };
    assert_eq!(name, "y2_2");
    assert_eq!(*id, Some(fields[0].id));
}

#[test]
fn test_rename_option_like_patterns_recovers_missing_some_payload_preserves_authoritative_id() {
    let payload_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "get_at_result".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::var("payload")],
        )),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("get_at_result")),
            subject_name: Some(Binder::synthetic("get_at_result")),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::var_with_id("payload", payload_id),
                ),
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                    PseudoExpr::error(),
                ),
            ],
        }),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let PseudoExpr::Let { body, .. } = renamed else {
        panic!("expected let wrapper after rename");
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected when body after rename");
    };
    let WhenClause { pattern, body, .. } = &clauses[0];
    let WhenPattern::Constructor { fields, .. } = pattern else {
        panic!("expected Some pattern after rename");
    };
    assert_eq!(
        fields.len(),
        1,
        "expected payload binder to be recovered, got pattern: {pattern:?}"
    );
    assert_eq!(
        fields[0].id, payload_id,
        "expected recovered payload binder to preserve authoritative free-ref id"
    );
    assert!(matches!(
        body,
        PseudoExpr::Var { name, id, .. } if name == "payload" && *id == Some(payload_id)
    ));
}

#[test]
fn test_rename_option_like_patterns_prefers_root_payload_name_among_multiple_generated_refs() {
    let expr = PseudoExpr::Let {
        name: "find_result".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::var("payload")],
        )),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("find_result")),
            subject_name: Some(Binder::synthetic("find_result")),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::Tuple(
                        (vec![PseudoExpr::var("fields"), PseudoExpr::var("field_0")]).into(),
                    ),
                ),
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                    PseudoExpr::error(),
                ),
            ],
        }),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let PseudoExpr::Let { body, .. } = renamed else {
        panic!("expected let wrapper after rename");
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected when body after rename");
    };
    let WhenPattern::Constructor { shape, fields, .. } = &clauses[0].pattern else {
        panic!("expected Some pattern after rename");
    };
    assert!(
        matches!(shape, ConstructorShape::Known(KnownConstructor::Some)),
        "expected Known(Some) shape, got {shape:?}"
    );
    assert_eq!(fields.len(), 1, "expected a recovered payload binder");
    assert_eq!(
        fields[0].name, "fields",
        "expected the root payload name to win over derived generated names"
    );
}

#[test]
fn test_rename_option_like_patterns_does_not_merge_ambiguous_same_name_different_id_payload_refs() {
    let left_id = VarId::fresh_binding();
    let right_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "find_result".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::var("payload")],
        )),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("find_result")),
            subject_name: Some(Binder::synthetic("find_result")),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::Tuple(
                        vec![
                            PseudoExpr::var_with_id("fields", left_id),
                            PseudoExpr::var_with_id("fields", right_id),
                        ]
                        .into(),
                    ),
                ),
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                    PseudoExpr::error(),
                ),
            ],
        }),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let PseudoExpr::Let { body, .. } = renamed else {
        panic!("expected let wrapper after rename");
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected when body after rename");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected Some-pattern candidate after rename");
    };
    assert!(
        fields.is_empty(),
        "expected ambiguous same-name / different-id payload refs to block binder recovery"
    );
    let PseudoExpr::Tuple(items) = &clauses[0].body else {
        panic!("expected body tuple after rename");
    };
    assert!(matches!(
        &items[0],
        PseudoExpr::Var { name, id, .. } if name == "fields" && *id == Some(left_id)
    ));
    assert!(matches!(
        &items[1],
        PseudoExpr::Var { name, id, .. } if name == "fields" && *id == Some(right_id)
    ));
}

#[test]
fn test_recover_free_validator_carriers_recovers_constructor_fields_from_direct_subject_accesses() {
    let subject = Binder::synthetic("item_0");
    let field0_access = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var_with_id(subject.name.clone(), subject.id),
            "fields".to_string(),
        )),
        index: 0,
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
        subject_name: Some(subject.clone()),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
            PseudoExpr::Tuple(
                vec![
                    PseudoExpr::Let {
                        name: "bytes".to_string(),
                        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                        value: PBox::new(PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
                            args: vec![field0_access].into(),
                        }),
                        body: PBox::new(PseudoExpr::var("bytes")),
                    },
                    PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var("i2_1"),
                            "fields".to_string(),
                        )),
                        index: 4,
                    },
                ]
                .into(),
            ),
        )],
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected when after recovery");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern after recovery");
    };
    assert_eq!(
        fields.len(),
        5,
        "expected recovered field_0 plus sparse field padding through index 4"
    );
    assert_eq!(fields[1].name, "_");
    assert_eq!(fields[2].name, "_");
    assert_eq!(fields[3].name, "_");
    assert_eq!(fields[4].name, "fields_4");

    let payload = &fields[0];
    let PseudoExpr::Tuple(elements) = &clauses[0].body else {
        panic!("expected tuple body after recovery");
    };
    let PseudoExpr::Let { value, .. } = &elements[0] else {
        panic!("expected let body after recovery");
    };
    let PseudoExpr::BuiltinCall { args, .. } = value.as_ref() else {
        panic!("expected Data.un_bytearray call after recovery");
    };
    assert!(matches!(
        &args[0],
        PseudoExpr::Var { name, id, .. } if name == &payload.name && *id == Some(payload.id)
    ));
    assert!(matches!(
        &elements[1],
        PseudoExpr::Var { name, id, .. } if name == "fields_4" && *id == Some(fields[4].id)
    ));
}

#[test]
fn test_recover_free_validator_carriers_infers_env_through_leading_root_let() {
    let redeemer = Binder::synthetic("redeemer");
    let script_context = Binder::synthetic("script_context");
    let expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![redeemer, script_context.clone()],
            body: PBox::new(PseudoExpr::var("inputs")),
        }),
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);

    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!("expected leading root let after recovery");
    };
    let PseudoExpr::Lambda { body, .. } = body.as_ref() else {
        panic!("expected validator lambda under leading root let");
    };
    let PseudoExpr::FieldAccess {
        record, selector, ..
    } = body.as_ref()
    else {
        panic!("expected inputs to rewrite to script_context.tx_info.inputs");
    };
    assert_eq!(selector.as_pretty_name(), "inputs");
    let PseudoExpr::FieldAccess {
        record: tx_info_record,
        selector: tx_info_selector,
        ..
    } = record.as_ref()
    else {
        panic!("expected inputs record to be script_context.tx_info");
    };
    assert_eq!(tx_info_selector.as_pretty_name(), "tx_info");
    assert!(matches!(
        tx_info_record.as_ref(),
        PseudoExpr::Var { name, id } if name == "script_context" && *id == Some(script_context.id)
    ));
}

#[test]
fn test_recover_free_validator_carriers_three_param_env_rewrites_redeemer_fields() {
    let datum = Binder::synthetic("datum");
    let redeemer = Binder::synthetic("redeemer");
    let script_context = Binder::synthetic("script_context");
    let expr = PseudoExpr::Lambda {
        params: vec![datum, redeemer.clone(), script_context],
        body: PBox::new(PseudoExpr::var("redeemer_fields_0")),
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);

    let PseudoExpr::Lambda { body, .. } = rewritten else {
        panic!("expected validator lambda after recovery");
    };
    let PseudoExpr::IndexAccess { collection, index } = body.as_ref() else {
        panic!("expected redeemer_fields_0 to rewrite to redeemer.fields[0]");
    };
    assert_eq!(*index, 0);
    let PseudoExpr::FieldAccess {
        record, selector, ..
    } = collection.as_ref()
    else {
        panic!("expected redeemer field access as index collection");
    };
    assert_eq!(selector.as_pretty_name(), "fields");
    assert!(matches!(
        record.as_ref(),
        PseudoExpr::Var { name, id } if name == "redeemer" && *id == Some(redeemer.id)
    ));
}

#[test]
fn test_recover_free_validator_carriers_does_not_infer_env_for_other_root_arities() {
    let one_param = PseudoExpr::Lambda {
        params: vec![Binder::synthetic("script_context")],
        body: PBox::new(PseudoExpr::var("inputs")),
    };
    let four_param = PseudoExpr::Lambda {
        params: vec![
            Binder::synthetic("datum"),
            Binder::synthetic("redeemer"),
            Binder::synthetic("script_context"),
            Binder::synthetic("extra"),
        ],
        body: PBox::new(PseudoExpr::var("redeemer_fields_0")),
    };

    let rewritten_one =
        recover_free_validator_carriers(one_param, &std::collections::HashMap::new(), false);
    let rewritten_four =
        recover_free_validator_carriers(four_param, &std::collections::HashMap::new(), false);

    assert!(
        matches!(
            rewritten_one,
            PseudoExpr::Lambda { body, .. }
                if matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "inputs")
        ),
        "1-param root lambda must not infer script_context"
    );
    assert!(
        matches!(
            rewritten_four,
            PseudoExpr::Lambda { body, .. }
                if matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "redeemer_fields_0")
        ),
        "4-param root lambda must not infer redeemer/script_context"
    );
}

#[test]
fn test_recover_free_validator_carriers_recovered_constructor_field_blocks_script_context_rewrite()
{
    let redeemer = Binder::synthetic("redeemer");
    let script_context = Binder::synthetic("script_context");
    let subject = Binder::synthetic("item_0");
    let data_id = VarId::fresh_binding();
    let expr = PseudoExpr::Lambda {
        params: vec![redeemer, script_context],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
            subject_name: Some(subject.clone()),
            clauses: vec![WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::Let {
                    name: "data".to_string(),
                    id: Some(data_id),
                    value: PBox::new(PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(subject.name.clone(), subject.id),
                            "fields".to_string(),
                        )),
                        index: 0,
                    }),
                    body: PBox::new(PseudoExpr::var_with_id("data", data_id)),
                },
            )],
        }),
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::Lambda { body, .. } = rewritten else {
        panic!("expected root validator lambda after recovery");
    };
    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected when body after recovery");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected recovered constructor pattern");
    };
    assert!(
        matches!(
            fields.as_slice(),
            [Binder { name, id, .. }] if name == "data" && *id == data_id
        ),
        "expected recovered field0 binder to reuse data id, got: {fields:?}"
    );
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::Var { name, id, .. } if name == "data" && *id == Some(data_id)
        ),
        "recovered field binder must block script_context.tx_info.data rewrite, got: {:?}",
        clauses[0].body
    );
}

#[test]
fn test_recover_free_validator_carriers_ignores_direct_subject_field_accesses_on_same_name_different_id()
 {
    let subject = Binder::synthetic("item_0");
    let outer_subject_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: subject.name.clone(),
        id: Some(outer_subject_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
            subject_name: Some(subject.clone()),
            clauses: vec![WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var_with_id(subject.name.clone(), outer_subject_id),
                                "fields".to_string(),
                            )),
                            index: 0,
                        },
                        PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var_with_id(subject.name.clone(), outer_subject_id),
                                "fields".to_string(),
                            )),
                            index: 2,
                        },
                    ]
                    .into(),
                ),
            )],
        }),
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!("expected outer let after recovery");
    };
    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected when after recovery");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern after recovery");
    };
    assert!(
        fields.is_empty(),
        "expected direct field access recovery to ignore outer same-name / different-id record accesses"
    );
    let PseudoExpr::Tuple(items) = &clauses[0].body else {
        panic!("expected tuple body after recovery");
    };
    assert!(matches!(
        &items[0],
        PseudoExpr::IndexAccess { collection, index: 0 }
            if matches!(
                collection.as_ref(),
                PseudoExpr::FieldAccess { record, selector, .. }
                    if selector.as_pretty_name() == "fields"
                        && matches!(
                            record.as_ref(),
                            PseudoExpr::Var { name, id, .. }
                                if name == &subject.name && *id == Some(outer_subject_id)
                        )
            )
    ));
    assert!(matches!(
        &items[1],
        PseudoExpr::IndexAccess { collection, index: 2 }
            if matches!(
                collection.as_ref(),
                PseudoExpr::FieldAccess { record, selector, .. }
                    if selector.as_pretty_name() == "fields"
                        && matches!(
                            record.as_ref(),
                            PseudoExpr::Var { name, id, .. }
                                if name == &subject.name && *id == Some(outer_subject_id)
                        )
            )
    ));
}

#[test]
fn test_recover_free_validator_carriers_keeps_same_name_different_id_field_access_after_recovery() {
    let subject = Binder::synthetic("item_0");
    let other_subject_id = VarId::fresh_binding();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
        subject_name: Some(subject.clone()),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
            PseudoExpr::Tuple(
                vec![
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_bytearray"),
                        args: vec![PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var_with_id(subject.name.clone(), subject.id),
                                "fields".to_string(),
                            )),
                            index: 0,
                        }]
                        .into(),
                    },
                    PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(subject.name.clone(), subject.id),
                            "fields".to_string(),
                        )),
                        index: 1,
                    },
                    PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(subject.name.clone(), other_subject_id),
                            "fields".to_string(),
                        )),
                        index: 1,
                    },
                ]
                .into(),
            ),
        )],
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected when after recovery");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern after recovery");
    };
    assert_eq!(
        fields.len(),
        2,
        "expected subject fields 0 and 1 to recover"
    );
    assert!(matches!(
        &clauses[0].body,
        PseudoExpr::Tuple(items)
            if matches!(
                &items[0],
                PseudoExpr::BuiltinCall { args, .. }
                    if matches!(
                        &args[0],
                        PseudoExpr::Var { name, id, .. }
                            if name == "field_0" && *id == Some(fields[0].id)
                    )
            )
            && matches!(
                &items[1],
                PseudoExpr::Var { name, id, .. }
                    if name == "fields_1" && *id == Some(fields[1].id)
            )
            && matches!(
                &items[2],
                PseudoExpr::IndexAccess { collection, index: 1 }
                    if matches!(
                        collection.as_ref(),
                        PseudoExpr::FieldAccess { record, selector, .. }
                            if selector.as_pretty_name() == "fields"
                                && matches!(
                                    record.as_ref(),
                                    PseudoExpr::Var { name, id, .. }
                                        if name == &subject.name && *id == Some(other_subject_id)
                                )
                    )
            )
    ));
}

#[test]
fn test_recover_free_validator_carriers_keeps_same_name_different_id_constructor_field_access() {
    let subject = Binder::synthetic("payload");
    let other_subject_id = VarId::fresh_binding();
    let field0 = Binder::synthetic("field_0");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
        subject_name: Some(subject.clone()),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(1, 1), vec![field0.clone()]),
            PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id(subject.name.clone(), other_subject_id),
                    "fields".to_string(),
                )),
                index: 0,
            },
        )],
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected when after recovery");
    };
    assert!(matches!(
        &clauses[0].body,
        PseudoExpr::IndexAccess { collection, index: 0 }
            if matches!(
                collection.as_ref(),
                PseudoExpr::FieldAccess { record, selector, .. }
                    if selector.as_pretty_name() == "fields"
                        && matches!(
                            record.as_ref(),
                            PseudoExpr::Var { name, id, .. }
                                if name == &subject.name && *id == Some(other_subject_id)
                        )
            )
    ));
}

#[test]
fn test_recover_free_validator_carriers_extracts_subject_field0_binder_from_buried_leading_let() {
    let subject = Binder::synthetic("item_0");
    let field0 = Binder::synthetic("fields_0");
    let fields_0_list_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
        subject_name: Some(subject.clone()),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
            PseudoExpr::Let {
                name: "fields_0_list".to_string(),
                id: Some(fields_0_list_id),
                value: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.un_list"),
                    args: vec![PseudoExpr::var_with_id(field0.name.clone(), field0.id)].into(),
                }),
                body: PBox::new(PseudoExpr::Let {
                    name: field0.name.clone(),
                    id: Some(field0.id),
                    value: PBox::new(PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(subject.name.clone(), subject.id),
                            "fields".to_string(),
                        )),
                        index: 0,
                    }),
                    body: PBox::new(PseudoExpr::var_with_id("fields_0_list", fields_0_list_id)),
                }),
            },
        )],
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected when after recovery");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern after recovery");
    };
    assert_eq!(
        fields.len(),
        1,
        "expected recovered field_0 binder, got: {fields:?}"
    );
    assert_eq!(fields[0].name, field0.name);
    assert_eq!(fields[0].id, field0.id);

    let PseudoExpr::Let { value, body, .. } = &clauses[0].body else {
        panic!("expected leading let after recovery");
    };
    let PseudoExpr::BuiltinCall { args, .. } = value.as_ref() else {
        panic!("expected Data.un_list call after recovery");
    };
    assert!(matches!(
        &args[0],
        PseudoExpr::Var { name, id, .. } if name == &field0.name && *id == Some(field0.id)
    ));
    assert!(
        matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "fields_0_list"),
        "expected buried field_0 let to be removed after recovery"
    );
}

#[test]
fn test_recover_free_validator_carriers_rewrites_generated_constructor_field_aliases_to_pattern_binders()
 {
    let subject = Binder::synthetic("item_0");
    let bytes = Binder::synthetic("bytes_3");
    let payload = Binder::synthetic("payload_3");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
        subject_name: Some(subject.clone()),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(
                ConstructorShape::unknown_data(1, 2),
                vec![bytes.clone(), payload.clone()],
            ),
            PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var("fields_0_3"),
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_bytearray"),
                        args: vec![PseudoExpr::var("field_1")].into(),
                    },
                ]
                .into(),
            ),
        )],
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected when after recovery");
    };
    let PseudoExpr::Tuple(elements) = &clauses[0].body else {
        panic!("expected tuple body after recovery");
    };
    assert!(matches!(
        &elements[0],
        PseudoExpr::Var { name, id, .. } if name == &bytes.name && *id == Some(bytes.id)
    ));
    let PseudoExpr::BuiltinCall { args, .. } = &elements[1] else {
        panic!("expected bytearray call after recovery");
    };
    assert!(matches!(
        &args[0],
        PseudoExpr::Var { name, id, .. } if name == &payload.name && *id == Some(payload.id)
    ));
}

#[test]
fn test_recover_free_validator_carriers_recovers_generated_field_under_same_name_different_id_outer_binding()
 {
    let subject = Binder::synthetic("item_0");
    let outer_shadow_id = VarId::fresh_binding();
    let field0 = Binder::synthetic("field_0");
    let recoverable_fields1_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "fields_1".to_string(),
        id: Some(outer_shadow_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
            subject_name: Some(subject.clone()),
            clauses: vec![WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::Let {
                    name: field0.name.clone(),
                    id: Some(field0.id),
                    value: PBox::new(PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(subject.name.clone(), subject.id),
                            "fields".to_string(),
                        )),
                        index: 0,
                    }),
                    body: PBox::new(PseudoExpr::Tuple(
                        vec![
                            PseudoExpr::var_with_id("fields_1", recoverable_fields1_id),
                            PseudoExpr::var_with_id("fields_1", outer_shadow_id),
                        ]
                        .into(),
                    )),
                },
            )],
        }),
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!("expected outer let after recovery");
    };
    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected when body after recovery");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern after recovery");
    };
    assert_eq!(
        fields.len(),
        2,
        "expected generated fields_1 to recover even with a same-name outer binder in scope"
    );
    assert_eq!(fields[0].id, field0.id);
    assert_eq!(fields[1].name, "fields_1");
    assert_eq!(
        fields[1].id, recoverable_fields1_id,
        "expected recovered field binder to preserve the authoritative generated-ref id"
    );
    assert_ne!(
        fields[1].id, outer_shadow_id,
        "expected recovered field binder to stay distinct from the unrelated outer same-name binder"
    );
    let PseudoExpr::Tuple(items) = &clauses[0].body else {
        panic!("expected stripped tuple body after recovery");
    };
    assert!(matches!(
        &items[0],
        PseudoExpr::Var { name, id, .. } if name == "fields_1" && *id == Some(fields[1].id)
    ));
    assert!(matches!(
        &items[1],
        PseudoExpr::Var { name, id, .. } if name == "fields_1" && *id == Some(outer_shadow_id)
    ));
}

#[test]
fn test_recover_free_validator_carriers_does_not_convert_if_when_condition_only_matches_field0_name()
 {
    let subject = Binder::synthetic("item_0");
    let outer_field0_id = VarId::fresh_binding();
    let recovered_field0 = Binder::synthetic("field_0");
    let then_generated_id = VarId::fresh_compat_placeholder();
    let else_generated_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "field_0".to_string(),
        id: Some(outer_field0_id),
        value: PBox::new(PseudoExpr::bool(true)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
            subject_name: Some(subject.clone()),
            clauses: vec![WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::Let {
                    name: recovered_field0.name.clone(),
                    id: Some(recovered_field0.id),
                    value: PBox::new(PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(subject.name.clone(), subject.id),
                            "fields".to_string(),
                        )),
                        index: 0,
                    }),
                    body: PBox::new(PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::var_with_id("field_0", outer_field0_id)),
                        then_branch: PBox::new(PseudoExpr::var_with_id(
                            "fields_1",
                            then_generated_id,
                        )),
                        else_branch: PBox::new(PseudoExpr::var_with_id(
                            "fields_2",
                            else_generated_id,
                        )),
                    }),
                },
            )],
        }),
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!("expected outer let after recovery");
    };
    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected when after recovery");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected recovered constructor pattern");
    };
    assert_eq!(
        fields.len(),
        3,
        "expected generated fields_1 and fields_2 to still recover into pattern slots"
    );
    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = &clauses[0].body
    else {
        panic!("expected condition to stay as if when only the field_0 name matches");
    };
    assert!(matches!(
        condition.as_ref(),
        PseudoExpr::Var { name, id, .. } if name == "field_0" && *id == Some(outer_field0_id)
    ));
    assert!(matches!(
        then_branch.as_ref(),
        PseudoExpr::Var { name, id, .. } if name == "fields_1" && *id == Some(fields[1].id)
    ));
    assert!(matches!(
        else_branch.as_ref(),
        PseudoExpr::Var { name, id, .. } if name == "fields_2" && *id == Some(fields[2].id)
    ));
}

#[test]
fn test_recover_free_validator_carriers_rewrites_direct_constructor_field_accesses_to_pattern_binders()
 {
    let subject = Binder::synthetic("item_0");
    let bytes = Binder::synthetic("bytes_3");
    let payload = Binder::synthetic("payload_3");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
        subject_name: Some(subject.clone()),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(
                ConstructorShape::unknown_data(1, 2),
                vec![bytes.clone(), payload.clone()],
            ),
            PseudoExpr::Tuple(
                vec![
                    PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(subject.name.clone(), subject.id),
                            "fields".to_string(),
                        )),
                        index: 0,
                    },
                    PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(subject.name.clone(), subject.id),
                            "fields".to_string(),
                        )),
                        index: 1,
                    },
                ]
                .into(),
            ),
        )],
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected when after recovery");
    };
    let PseudoExpr::Tuple(elements) = &clauses[0].body else {
        panic!("expected tuple body after recovery");
    };
    assert!(matches!(
        &elements[0],
        PseudoExpr::Var { name, id, .. } if name == &bytes.name && *id == Some(bytes.id)
    ));
    assert!(matches!(
        &elements[1],
        PseudoExpr::Var { name, id, .. } if name == &payload.name && *id == Some(payload.id)
    ));
}

#[test]
fn test_recover_free_validator_carriers_rewrites_generated_constructor_field_aliases_to_subject_accesses()
 {
    let subject = Binder::synthetic("fields_0");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
        subject_name: Some(subject.clone()),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
            PseudoExpr::Tuple(
                vec![PseudoExpr::var("fields_6"), PseudoExpr::var("fields_8")].into(),
            ),
        )],
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected when after recovery");
    };
    let PseudoExpr::Tuple(elements) = &clauses[0].body else {
        panic!("expected tuple body after recovery");
    };
    assert!(matches!(
        &elements[0],
        PseudoExpr::IndexAccess { collection, index: 6 }
            if matches!(
                collection.as_ref(),
                PseudoExpr::FieldAccess { record, selector, .. }
                    if selector.as_pretty_name() == "fields"
                        && matches!(
                            record.as_ref(),
                            PseudoExpr::Var { name, id, .. }
                                if name == &subject.name && *id == Some(subject.id)
                        )
            )
    ));
    assert!(matches!(
        &elements[1],
        PseudoExpr::IndexAccess { collection, index: 8 }
            if matches!(
                collection.as_ref(),
                PseudoExpr::FieldAccess { record, selector, .. }
                    if selector.as_pretty_name() == "fields"
                        && matches!(
                            record.as_ref(),
                            PseudoExpr::Var { name, id, .. }
                                if name == &subject.name && *id == Some(subject.id)
                        )
            )
    ));
}

#[test]
fn test_recover_free_validator_carriers_handles_option_subjects_without_tipo() {
    // Without a `TypeEnvironment` an Option subject is Unknown, like Data,
    // so field projection may apply; this only checks the rewrite survives.
    let subject = Binder::synthetic("opt");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
        subject_name: Some(subject.clone()),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
            PseudoExpr::var("fields_0"),
        )],
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    assert!(matches!(rewritten, PseudoExpr::When { .. }));
}

#[test]
fn test_recover_free_validator_carriers_rebinds_free_generated_subject_aliases() {
    let subject = Binder::synthetic("field_1");
    let field0 = Binder::synthetic("w");
    let item_alias = Binder::synthetic("item_1_1_1_1_1_1_1_1_1_1");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
        subject_name: Some(subject.clone()),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
            PseudoExpr::Let {
                name: field0.name.clone(),
                id: Some(field0.id),
                value: PBox::new(PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id(item_alias.name.clone(), item_alias.id),
                        "fields".to_string(),
                    )),
                    index: 0,
                }),
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var("fields_0"),
                        PseudoExpr::var("fields_2"),
                        PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var_with_id(item_alias.name.clone(), item_alias.id),
                                "fields".to_string(),
                            )),
                            index: 0,
                        },
                    ]
                    .into(),
                )),
            },
        )],
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected when after recovery");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern after recovery");
    };
    assert_eq!(fields.len(), 3, "expected sparse field slots to be padded");
    assert_eq!(fields[0].name, field0.name);
    assert_eq!(fields[1].name, "_");
    assert_eq!(fields[2].name, "fields_2");

    let PseudoExpr::Tuple(elements) = &clauses[0].body else {
        panic!("expected tuple body after recovery");
    };
    assert!(matches!(
        &elements[0],
        PseudoExpr::Var { name, id, .. } if name == &field0.name && *id == Some(field0.id)
    ));
    assert!(matches!(
        &elements[1],
        PseudoExpr::Var { name, .. } if name == "fields_2"
    ));
    assert!(matches!(
        &elements[2],
        PseudoExpr::Var { name, id, .. } if name == &field0.name && *id == Some(field0.id)
    ));
}

#[test]
fn test_recover_free_validator_carriers_expect_payload_prefers_condition_subject_id_over_same_name_scope_binder()
 {
    let scoped_subject = Binder::synthetic("payload");
    let expect_subject_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: scoped_subject.name.clone(),
        id: Some(scoped_subject.id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("expect!")),
            args: vec![
                PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::builtin_id(
                            crate::BuiltinId::ConstrUnpack,
                            vec![PseudoExpr::var_with_id(
                                scoped_subject.name.clone(),
                                expect_subject_id,
                            )],
                        ),
                        "fst".to_string(),
                    )),
                    right: PBox::new(PseudoExpr::int(0)),
                },
                PseudoExpr::var("fields_1"),
            ]
            .into(),
        }),
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::Let { body, .. } = rewritten else {
        panic!("expected let after recovery");
    };
    let PseudoExpr::Apply { args, .. } = body.as_ref() else {
        panic!("expected expect apply after recovery");
    };
    let PseudoExpr::IndexAccess {
        collection,
        index: 1,
    } = &args[1]
    else {
        panic!("expected free fields_1 to become subject field access");
    };
    let PseudoExpr::FieldAccess {
        record, selector, ..
    } = collection.as_ref()
    else {
        panic!("expected rewritten field projection");
    };
    assert_eq!(selector.as_pretty_name(), "fields");
    let PseudoExpr::Var { name, id, .. } = record.as_ref() else {
        panic!("expected rewritten field access to stay on subject var");
    };
    assert_eq!(name, &scoped_subject.name);
    assert_eq!(
        *id,
        Some(expect_subject_id),
        "expected expect payload rewrite to follow the condition subject id instead of the same-name scope binder"
    );
    assert_ne!(
        *id,
        Some(scoped_subject.id),
        "expected test to guard against falling back to the unrelated same-name scope binder"
    );
}

#[test]
fn test_recover_free_validator_carriers_expect_payload_preserves_free_compat_subject_id() {
    let subject_id = VarId::fresh_compat_placeholder();
    let subject_name = "payload".to_string();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::builtin_id(
                        crate::BuiltinId::ConstrUnpack,
                        vec![PseudoExpr::var_with_id(subject_name.clone(), subject_id)],
                    ),
                    "fst".to_string(),
                )),
                right: PBox::new(PseudoExpr::int(0)),
            },
            PseudoExpr::var("fields_1"),
        ]
        .into(),
    };

    let rewritten = recover_free_validator_carriers(expr, &std::collections::HashMap::new(), false);
    let PseudoExpr::Apply { args, .. } = rewritten else {
        panic!("expected expect apply after recovery");
    };
    let PseudoExpr::IndexAccess {
        collection,
        index: 1,
    } = &args[1]
    else {
        panic!("expected free fields_1 to become subject field access");
    };
    let PseudoExpr::FieldAccess {
        record, selector, ..
    } = collection.as_ref()
    else {
        panic!("expected rewritten field projection");
    };
    assert_eq!(selector.as_pretty_name(), "fields");
    let PseudoExpr::Var { name, id, .. } = record.as_ref() else {
        panic!("expected rewritten field access to stay on subject var");
    };
    assert_eq!(name, &subject_name);
    assert_eq!(
        *id,
        Some(subject_id),
        "expected free compat expect subject id to be preserved instead of minting a fresh authoritative binder"
    );
    assert!(
        id.expect("expected Some(id) in this test")
            .is_compat_placeholder(),
        "expected free expect subject to stay in compat space when no scope binder exists"
    );
}

#[test]
fn test_rewrite_constructor_subject_field_accesses_to_pattern_binders_after_expect_conversion() {
    let subject = Binder::synthetic("item");
    let variant = Binder::synthetic("variant");
    let map = Binder::synthetic("map");
    let value = Binder::synthetic("value");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id(subject.name.clone(), subject.id)),
        subject_name: Some(subject.clone()),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(
                ConstructorShape::unknown_data(2, 3),
                vec![variant, map.clone(), value],
            ),
            PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.un_map"),
                args: vec![PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id(subject.name.clone(), subject.id),
                        "fields".to_string(),
                    )),
                    index: 1,
                }]
                .into(),
            },
        )],
    };

    let rewritten = super::rewrite_constructor_subject_field_accesses_to_pattern_binders(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!("expected when after rewrite");
    };
    let PseudoExpr::BuiltinCall { args, .. } = &clauses[0].body else {
        panic!("expected builtin call after rewrite");
    };
    assert!(matches!(
        &args[0],
        PseudoExpr::Var { name, id, .. } if name == &map.name && *id == Some(map.id)
    ));
}

#[test]
fn test_rename_option_like_patterns_rewrites_subject_payload_field_accesses() {
    let opt = Binder::synthetic("opt");
    let expr = PseudoExpr::Let {
        name: opt.name.clone(),
        id: Some(opt.id),
        value: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::var("payload")],
        )),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(opt.name.clone(), opt.id)),
            subject_name: Some(opt.clone()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(opt.name.clone(), opt.id),
                            "fields".to_string(),
                        )),
                        index: 0,
                    },
                ),
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                    PseudoExpr::error(),
                ),
            ],
        }),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let PseudoExpr::Let { body, .. } = renamed else {
        panic!("expected let wrapper after rename");
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected when body after rename");
    };
    let WhenClause { pattern, body, .. } = &clauses[0];
    let WhenPattern::Constructor { shape, fields, .. } = pattern else {
        panic!("expected Some pattern after rename");
    };
    assert!(
        matches!(shape, ConstructorShape::Known(KnownConstructor::Some)),
        "expected Known(Some) shape, got {shape:?}"
    );
    assert_eq!(fields.len(), 1, "expected payload binder to be introduced");
    let PseudoExpr::Var { name, id, .. } = body else {
        panic!("expected subject payload access to collapse to binder var");
    };
    assert_eq!(name, &fields[0].name);
    assert_eq!(*id, Some(fields[0].id));
}

#[test]
fn test_rename_option_like_patterns_rewrites_subject_payload_field_projections() {
    let opt = Binder::synthetic("opt");
    let expr = PseudoExpr::Let {
        name: opt.name.clone(),
        id: Some(opt.id),
        value: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::var("payload")],
        )),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(opt.name.clone(), opt.id)),
            subject_name: Some(opt.clone()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(opt.name.clone(), opt.id),
                            "fields".to_string(),
                        )),
                        index: 1,
                    },
                ),
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                    PseudoExpr::error(),
                ),
            ],
        }),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let PseudoExpr::Let { body, .. } = renamed else {
        panic!("expected let wrapper after rename");
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected when body after rename");
    };
    let WhenClause { pattern, body, .. } = &clauses[0];
    let WhenPattern::Constructor { shape, fields, .. } = pattern else {
        panic!("expected Some pattern after rename");
    };
    assert!(
        matches!(shape, ConstructorShape::Known(KnownConstructor::Some)),
        "expected Known(Some) shape, got {shape:?}"
    );
    assert_eq!(fields.len(), 1, "expected payload binder to be introduced");
    let PseudoExpr::IndexAccess { collection, index } = body else {
        panic!("expected subject payload projection to remain an index access");
    };
    assert_eq!(*index, 1);
    let PseudoExpr::Var { name, id, .. } = collection.as_ref() else {
        panic!("expected projection collection to collapse to payload binder");
    };
    assert_eq!(name, &fields[0].name);
    assert_eq!(*id, Some(fields[0].id));
}

#[test]
fn test_rename_option_like_patterns_rewrites_expect_body_subject_payload_projections() {
    let opt = Binder::synthetic("opt");
    let fields = Binder::synthetic("fields");
    let expr = PseudoExpr::Let {
        name: opt.name.clone(),
        id: Some(opt.id),
        value: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::var("payload")],
        )),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("expect!")),
            args: vec![
                PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var_with_id(opt.name.clone(), opt.id)),
                    subject_name: Some(opt.clone()),
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::constructor_known(
                                KnownConstructor::Some,
                                vec![fields.clone()],
                            ),
                            PseudoExpr::Bool(true),
                        ),
                        WhenClause::new(
                            WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                            PseudoExpr::error(),
                        ),
                    ],
                },
                PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id(opt.name.clone(), opt.id),
                        "fields".to_string(),
                    )),
                    index: 1,
                },
            ]
            .into(),
        }),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let PseudoExpr::Let { body, .. } = renamed else {
        panic!("expected let wrapper after rename");
    };
    let PseudoExpr::Apply { args, .. } = body.into_inner() else {
        panic!("expected expect! apply after rename");
    };
    let PseudoExpr::When { clauses, .. } = &args[0] else {
        panic!("expected expect condition when after rename");
    };
    let WhenPattern::Constructor { shape, fields, .. } = &clauses[0].pattern else {
        panic!("expected Some pattern after rename");
    };
    assert!(
        matches!(shape, ConstructorShape::Known(KnownConstructor::Some)),
        "expected Some shape after rename, got {:?}",
        shape
    );
    assert_eq!(
        fields.len(),
        1,
        "expected payload binder to survive in the pattern"
    );
    let PseudoExpr::IndexAccess { collection, index } = &args[1] else {
        panic!("expected expect body projection to remain an index access");
    };
    assert_eq!(*index, 1);
    let PseudoExpr::Var { name, id, .. } = collection.as_ref() else {
        panic!("expected expect body projection to use payload binder");
    };
    assert_eq!(name, &fields[0].name);
    assert_eq!(*id, Some(fields[0].id));
}

#[test]
fn test_rename_option_like_patterns_rewrites_existing_some_binder_projections_in_body() {
    let opt = Binder::synthetic("opt");
    let fields = Binder::synthetic("fields");
    let expr = PseudoExpr::Let {
        name: opt.name.clone(),
        id: Some(opt.id),
        value: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![PseudoExpr::var("payload")],
        )),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(opt.name.clone(), opt.id)),
            subject_name: Some(opt.clone()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::Some, vec![fields.clone()]),
                    PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(opt.name.clone(), opt.id),
                            "fields".to_string(),
                        )),
                        index: 1,
                    },
                ),
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                    PseudoExpr::error(),
                ),
            ],
        }),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let PseudoExpr::Let { body, .. } = renamed else {
        panic!("expected let wrapper after rename");
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected when body after rename");
    };
    let PseudoExpr::IndexAccess { collection, index } = &clauses[0].body else {
        panic!("expected body projection to remain an index access");
    };
    assert_eq!(*index, 1);
    let PseudoExpr::Var { name, id, .. } = collection.as_ref() else {
        panic!("expected body projection to use existing payload binder");
    };
    assert_eq!(name, &fields.name);
    assert_eq!(*id, Some(fields.id));
}

#[test]
fn test_rename_option_like_patterns_specializes_none_plus_wildcard_to_some() {
    let opt = Binder::synthetic("opt");
    let expr = PseudoExpr::Let {
        name: opt.name.clone(),
        id: Some(opt.id),
        value: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond")),
            then_branch: PBox::new(PseudoExpr::constr_known(KnownConstructor::None, vec![])),
            else_branch: PBox::new(PseudoExpr::constr_known(
                KnownConstructor::Some,
                vec![PseudoExpr::var("payload")],
            )),
        }),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id(opt.name.clone(), opt.id)),
            subject_name: Some(opt.clone()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                    PseudoExpr::int(0),
                ),
                WhenClause::new(
                    WhenPattern::Wildcard,
                    PseudoExpr::IndexAccess {
                        collection: PBox::new(PseudoExpr::field_access(
                            PseudoExpr::var_with_id(opt.name.clone(), opt.id),
                            "fields".to_string(),
                        )),
                        index: 0,
                    },
                ),
            ],
        }),
    };

    let renamed = rename_option_like_patterns(
        expr,
        &crate::decompile::DecompileOptions::default(),
        &std::collections::HashMap::new(),
    );
    let renamed_debug = format!("{renamed:?}");
    assert!(
        renamed_debug.contains("shape: Known(Some)"),
        "expected wildcard branch to specialize to Some on option-like subject, got: {renamed_debug}"
    );
    assert!(
        !renamed_debug.contains("pattern: Wildcard"),
        "expected wildcard branch to disappear after Some specialization, got: {renamed_debug}"
    );
}
