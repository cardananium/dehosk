use super::*;
use crate::pseudo::ast::PVec;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;
use std::cell::RefCell;
use std::collections::HashSet;

struct LetNameCollector {
    names: Vec<String>,
}

impl ExprVisitor for LetNameCollector {
    fn visit_let(
        &mut self,
        name: &str,
        _id: &Option<VarId>,
        _value: &PseudoExpr,
        _body: &PseudoExpr,
    ) {
        self.names.push(name.to_string());
    }
}

fn assert_unique_let_names(expr: &PseudoExpr) {
    let mut collector = LetNameCollector { names: Vec::new() };
    collector.walk(expr);
    let mut seen = HashSet::new();
    for name in collector.names {
        assert!(seen.insert(name.clone()), "duplicate let name: {name}");
    }
}

fn shadowing_immediate_application_expr() -> PseudoExpr {
    let outer_x_id = VarId::fresh_binding();
    let lambda_x_id = VarId::fresh_binding();
    let y_id = VarId::fresh_binding();

    PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_x_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("x", lambda_x_id), Binder::new("y", y_id)],
                body: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::var_with_id("y", y_id)),
                    right: PBox::new(PseudoExpr::int(0)),
                }),
            }),
            args: vec![PseudoExpr::int(1), PseudoExpr::var_with_id("x", outer_x_id)].into(),
        }),
    }
}

fn stale_flattenable_let_chain_expr() -> PseudoExpr {
    let outer_id = VarId::new(9301);
    let inner_id = VarId::new(9302);
    let stale_outer_id = VarId::new(9303);

    PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::int(1)),
            body: PBox::new(PseudoExpr::var_with_id("y", inner_id)),
        }),
        body: PBox::new(PseudoExpr::var_with_id("x", stale_outer_id)),
    }
}

fn stale_cancel_force_delay_expr() -> PseudoExpr {
    let y_id = VarId::new(9311);
    let x_id = VarId::new(9312);
    let stale_x_id = VarId::new(9313);

    PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(y_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(x_id),
            value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
                "y", y_id,
            )))),
            body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id(
                "x", stale_x_id,
            )))),
        }),
    }
}

fn stale_destructurable_when_fields_expr() -> PseudoExpr {
    let redeemer_id = VarId::new(9321);
    let stale_redeemer_id = VarId::new(9322);
    let stale_redeemer_var = || PseudoExpr::var_with_id("redeemer", stale_redeemer_id);

    PseudoExpr::Let {
        name: "redeemer".to_string(),
        id: Some(redeemer_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(stale_redeemer_var()),
            subject_name: None,
            clauses: vec![WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
                PseudoExpr::field_access(
                    PseudoExpr::field_access(
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Constr.unpack"),
                            args: vec![stale_redeemer_var()].into(),
                        },
                        "snd".to_string(),
                    ),
                    "head".to_string(),
                ),
            )],
        }),
    }
}

fn stale_unpack_tag_when_subject_expr() -> PseudoExpr {
    let redeemer_id = VarId::new(9331);
    let stale_redeemer_id = VarId::new(9332);
    let stale_redeemer_var = || PseudoExpr::var_with_id("redeemer", stale_redeemer_id);

    PseudoExpr::Let {
        name: "redeemer".to_string(),
        id: Some(redeemer_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::field_access(
                PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Constr.unpack"),
                    args: vec![stale_redeemer_var()].into(),
                },
                "fst".to_string(),
            )),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::Literal(PseudoExpr::int(2)),
                    PseudoExpr::field_access(
                        PseudoExpr::field_access(
                            PseudoExpr::BuiltinCall {
                                name: crate::BuiltinId::expect_known("Constr.unpack"),
                                args: vec![stale_redeemer_var()].into(),
                            },
                            "snd".to_string(),
                        ),
                        "head".to_string(),
                    ),
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
    }
}

fn stale_data_case_expr() -> PseudoExpr {
    let data_id = VarId::new(9341);
    let stale_data_id = VarId::new(9342);
    let payload_id = VarId::new(9343);
    let stale_payload_id = VarId::new(9344);
    let fallback = PseudoExpr::Constr {
        type_hint: None,
        tag: 2,
        fields: PVec::new(),
        shape: ConstructorShape::unknown_data(2, 0),
    };

    PseudoExpr::Let {
        name: "data".to_string(),
        id: Some(data_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.case"),
            args: vec![
                PseudoExpr::var_with_id("data", stale_data_id),
                PseudoExpr::Lambda {
                    params: vec![Binder::new("payload", payload_id)],
                    body: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("payload", stale_payload_id),
                        "fields".to_string(),
                    )),
                },
                fallback.clone(),
                fallback.clone(),
                fallback.clone(),
                fallback,
            ]
            .into(),
        }),
    }
}

fn stale_scott_constructor_lambda_expr() -> PseudoExpr {
    let field_id = VarId::new(9345);
    let some_id = VarId::new(9346);
    let none_id = VarId::new(9347);
    let stale_some_id = VarId::new(9348);

    PseudoExpr::Let {
        name: "field".to_string(),
        id: Some(field_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("some", some_id), Binder::new("none", none_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("some", stale_some_id)),
                args: vec![PseudoExpr::var_with_id("field", field_id)].into(),
            }),
        }),
    }
}

fn stale_expect_fn_call_tag_expr() -> PseudoExpr {
    let x_id = VarId::new(9349);
    let stale_x_id = VarId::new(9350);

    PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::Constr {
            type_hint: None,
            tag: 0,
            fields: PVec::new(),
            shape: ConstructorShape::unknown_data(0, 0),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::expect_helper()),
            args: vec![
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::compat_var("fn_call")),
                    args: vec![
                        PseudoExpr::var_with_id("x", stale_x_id),
                        PseudoExpr::field_access(
                            PseudoExpr::var_with_id("x", x_id),
                            "tag".to_string(),
                        ),
                    ]
                    .into(),
                },
                PseudoExpr::Bool(true),
            ]
            .into(),
        }),
    }
}

fn stale_identity_lambda_expr() -> PseudoExpr {
    let param_id = VarId::new(9353);
    let stale_param_id = VarId::new(9354);

    PseudoExpr::Lambda {
        params: vec![Binder::new("x_17", param_id)],
        body: PBox::new(PseudoExpr::var_with_id("x_17", stale_param_id)),
    }
}

fn stale_live_let_expr() -> PseudoExpr {
    let live_id = VarId::new(9351);
    let stale_live_id = VarId::new(9352);

    PseudoExpr::Let {
        name: "live".to_string(),
        id: Some(live_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::var_with_id("live", stale_live_id)),
    }
}

fn stale_raw_fields_disambiguation_expr() -> PseudoExpr {
    let subject_id = VarId::new(9361);
    let stale_subject_id = VarId::new(9362);

    PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(subject_id),
        value: PBox::new(PseudoExpr::Constr {
            type_hint: None,
            tag: 0,
            fields: PVec::new(),
            shape: ConstructorShape::unknown_data(0, 0),
        }),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("x", subject_id)),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::field_access(
                        PseudoExpr::var_with_id("x", stale_subject_id),
                        "fields".to_string(),
                    ),
                ),
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    PseudoExpr::int(1),
                ),
            ],
        }),
    }
}

fn stale_eta_pair_selector_expr() -> PseudoExpr {
    let pair_src_id = VarId::new(9371);
    let selector_id = VarId::new(9372);
    let rest_id = VarId::new(9373);
    let stale_selector_id = VarId::new(9374);
    let stale_rest_id = VarId::new(9375);
    let left_id = VarId::new(9376);
    let right_id = VarId::new(9377);

    PseudoExpr::Let {
        name: "pair_src".to_string(),
        id: Some(pair_src_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::Lambda {
                params: vec![
                    Binder::new("sel", selector_id),
                    Binder::new("rest", rest_id),
                ],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("sel", stale_selector_id)),
                    args: vec![
                        PseudoExpr::var_with_id("pair_src", pair_src_id),
                        PseudoExpr::var_with_id("rest", stale_rest_id),
                    ]
                    .into(),
                }),
            }),
            subject_name: None,
            clauses: vec![WhenClause::new(
                WhenPattern::Pair(Binder::new("left", left_id), Binder::new("right", right_id)),
                PseudoExpr::var_with_id("left", left_id),
            )],
        }),
    }
}

fn stale_recursive_inner_recfn_expr() -> PseudoExpr {
    let inner_id = VarId::new(9381);
    let stale_inner_id = VarId::new(9382);

    PseudoExpr::RecFn {
        name: Binder::new("outer", VarId::new(9383)),
        params: Vec::new(),
        body: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("inner", inner_id),
            params: Vec::new(),
            body: PBox::new(PseudoExpr::var_with_id("inner", stale_inner_id)),
        }),
    }
}

fn stale_z_combinator_step_expr() -> PseudoExpr {
    let captured_id = VarId::new(9391);
    let rec_id = VarId::new(9392);
    let acc_id = VarId::new(9393);
    let next_id = VarId::new(9394);
    let stale_acc_id = VarId::new(9395);
    let stale_next_id = VarId::new(9396);
    let stale_captured_id = VarId::new(9397);

    PseudoExpr::Let {
        name: "captured".to_string(),
        id: Some(captured_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("self", rec_id),
            params: vec![Binder::new("acc", acc_id)],
            body: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("next", next_id)],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("acc", stale_acc_id)),
                    args: vec![
                        PseudoExpr::var_with_id("captured", stale_captured_id),
                        PseudoExpr::var_with_id("next", stale_next_id),
                    ]
                    .into(),
                }),
            }),
        }),
    }
}

fn stale_immediate_lambda_application_expr() -> PseudoExpr {
    let param_id = VarId::new(9401);
    let stale_param_id = VarId::new(9402);

    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", param_id)],
            body: PBox::new(PseudoExpr::var_with_id("x", stale_param_id)),
        }),
        args: vec![PseudoExpr::int(1)].into(),
    }
}

fn duplicate_named_complex_when_subject_expr() -> PseudoExpr {
    let outer_x_id = VarId::new(9405);
    let subject_x_id = VarId::new(9406);
    let tmp_id = VarId::new(9407);

    PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_x_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Lambda {
                    params: vec![Binder::new("tmp", tmp_id)],
                    body: PBox::new(PseudoExpr::Tuple(
                        vec![
                            PseudoExpr::var_with_id("tmp", tmp_id),
                            PseudoExpr::Bool(true),
                        ]
                        .into(),
                    )),
                }),
                args: vec![PseudoExpr::var_with_id("x", outer_x_id)].into(),
            }),
            subject_name: Some(Binder::new("x", subject_x_id)),
            clauses: vec![WhenClause::new(
                WhenPattern::Wildcard,
                PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("x", subject_x_id),
                        PseudoExpr::var_with_id("x", outer_x_id),
                    ]
                    .into(),
                ),
            )],
        }),
    }
}

#[test]
fn type_refinement_skips_dedup_invalidating_pass_for_unique_binding_ids() {
    let binding_id = VarId::new(9411);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    assert!(!has_duplicate_binding_ids(&expr));
    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let mut blueprint_registry = BlueprintHintRegistry::new();
    let mut final_types = None;
    let mut kind_annotations = std::collections::HashMap::new();

    let type_passes = crate::decompile::TypePasses::all_on();
    let _result = run_type_refinement_stage(
        expr,
        None,
        None,
        TypeRefinementPasses {
            deduplicate: PipelinePassId::DeduplicateVarIdsForTypeRefinement,
            solve: PipelinePassId::SolveTypeConstraints,
            propagate: PipelinePassId::PropagateTypes,
            resolve_cardano_fields: PipelinePassId::ResolveCardanoFieldNames,
        },
        &type_passes,
        &mut kind_annotations,
        &mut blueprint_registry,
        &mut final_types,
        &mut executor,
    );

    assert_eq!(passes.into_inner(), vec!["solve_type_constraints"]);
    assert!(final_types.is_some());
}

#[test]
fn type_refinement_repairs_ref_ids_after_actual_dedup_before_solve() {
    let duplicate_id = VarId::new(9412);
    let expr = PseudoExpr::Let {
        name: "outer".to_string(),
        id: Some(duplicate_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "inner".to_string(),
            id: Some(duplicate_id),
            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(PseudoExpr::var_with_id("outer", duplicate_id)),
        }),
    };
    assert!(has_duplicate_binding_ids(&expr));
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr),
        "duplicate-id fixture should start scope-consistent: {expr:?}"
    );

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let mut blueprint_registry = BlueprintHintRegistry::new();
    let mut final_types = None;
    let mut kind_annotations = std::collections::HashMap::new();

    let type_passes = crate::decompile::TypePasses::all_on();
    let result = run_type_refinement_stage(
        expr,
        None,
        None,
        TypeRefinementPasses {
            deduplicate: PipelinePassId::DeduplicateVarIdsForTypeRefinement,
            solve: PipelinePassId::SolveTypeConstraints,
            propagate: PipelinePassId::PropagateTypes,
            resolve_cardano_fields: PipelinePassId::ResolveCardanoFieldNames,
        },
        &type_passes,
        &mut kind_annotations,
        &mut blueprint_registry,
        &mut final_types,
        &mut executor,
    );
    let passes = passes.into_inner();

    assert_eq!(
        passes,
        vec![
            "deduplicate_var_ids_for_type_refinement",
            "retarget_refs_by_scope",
            "solve_type_constraints"
        ]
    );
    assert!(final_types.is_some());
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn final_dangling_alias_stage_repairs_ref_ids_before_inline_aliases() {
    let duplicate_id = VarId::new(9421);
    let expr = PseudoExpr::Let {
        name: "outer".to_string(),
        id: Some(duplicate_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "inner".to_string(),
            id: Some(duplicate_id),
            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(PseudoExpr::var_with_id("outer", duplicate_id)),
        }),
    };
    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let mut options = DecompileOptions::default();
    options.script_version = Some(ScriptVersion::PlutusV3);
    let mut blueprint_registry = BlueprintHintRegistry::new();
    let mut final_types = None;
    let mut kind_annotations = std::collections::HashMap::new();
    let expr = crate::decompile::simplify::rename_validator_params(expr, options.script_version);
    executor.emit(PipelinePassId::RenameValidatorParams, &expr);

    let result = run_structural_final_cleanup_stage(
        expr,
        None,
        &options,
        &mut kind_annotations,
        &mut blueprint_registry,
        &mut final_types,
        &mut executor,
    );
    let passes = passes.into_inner();

    let field_pos = passes
        .iter()
        .position(|pass| *pass == "resolve_cardano_field_names_final")
        .expect("expected final field-name resolution");
    let retarget_pos = passes
        .iter()
        .skip(field_pos + 1)
        .position(|pass| *pass == "retarget_refs_by_scope")
        .map(|pos| field_pos + 1 + pos)
        .expect("expected ref retarget before dangling alias inline");
    let inline_pos = passes
        .iter()
        .position(|pass| *pass == "inline_dangling_field_aliases")
        .expect("expected inline_dangling_field_aliases");
    assert!(
        field_pos < retarget_pos && retarget_pos < inline_pos,
        "expected final field names -> retarget -> inline aliases, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn final_type_refinement_skips_dedup_invalidating_pass_for_unique_binding_ids() {
    let binding_id = VarId::new(9425);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    assert!(!has_duplicate_binding_ids(&expr));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();
    let mut final_types = None;
    let mut kind_annotations = std::collections::HashMap::new();

    let result = run_structural_final_cleanup_stage(
        expr,
        None,
        &options,
        &mut kind_annotations,
        &mut blueprint_registry,
        &mut final_types,
        &mut executor,
    );
    let passes = passes.into_inner();

    assert!(
        !passes.contains(&"deduplicate_var_ids_final"),
        "unique binding ids should skip final dedup invalidator, got: {passes:?}"
    );
    assert!(
        passes.contains(&"solve_type_constraints_final"),
        "final solve should still run, got: {passes:?}"
    );
    assert!(final_types.is_some());
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn initial_postprocess_repairs_validator_param_rename_collision_before_tail_collapse() {
    let outer_id = VarId::new(9431);
    let inner_id = VarId::new(9432);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("__context__", outer_id)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("script_context", inner_id)],
            body: PBox::new(PseudoExpr::var_with_id("__context__", outer_id)),
        }),
    };
    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let mut options = DecompileOptions::default();
    options.script_version = Some(ScriptVersion::PlutusV3);

    let mut kind_annotations = std::collections::HashMap::new();
    let result =
        run_initial_postprocess_stage(expr, &options, &mut kind_annotations, &mut executor);
    let passes = passes.into_inner();

    assert_eq!(
        passes,
        vec![
            "rename_validator_params",
            "uniquify_final",
            "collapse_tail_chains"
        ]
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
    assert!(matches!(
        kind_annotations.get(&outer_id),
        Some(crate::pseudo::nameless::VarKind::CardanoContext { context_type })
            if context_type == "script_context"
    ));
    assert!(
        !kind_annotations.contains_key(&inner_id),
        "shadowed inner script_context name should not inherit the entrypoint metadata"
    );
}

#[test]
fn pre_type_immediate_applications_normalizes_shadowing_output() {
    let expr = shadowing_immediate_application_expr();
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();

    let result = run_pre_type_structural_recovery_cluster(
        expr,
        &options,
        None,
        &mut blueprint_registry,
        &mut executor,
    );
    let passes = passes.into_inner();

    assert!(
        passes.contains(&"resolve_immediate_applications"),
        "expected base immediate-application pass to run, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
    assert_unique_let_names(&result);
}

#[test]
fn late_immediate_applications_normalizes_shadowing_output() {
    let expr = shadowing_immediate_application_expr();
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);

    let options = DecompileOptions::default();
    let result = run_late_pattern_recovery_cluster(expr, &options, None, &mut executor);

    assert_eq!(
        passes.into_inner(),
        vec!["resolve_immediate_applications_late"]
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
    assert_unique_let_names(&result);
}

#[test]
fn cleanup_normalization_repairs_ref_ids_before_strip_cosmetic_delays() {
    let expr = stale_cancel_force_delay_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);

    let polish = crate::decompile::DisplayPolishPasses::all_on();
    let result = run_cleanup_normalization_cluster(expr, &polish, &mut executor);

    assert_eq!(
        passes.into_inner(),
        vec![
            "retarget_refs_by_scope",
            "strip_cosmetic_delays",
            "cancel_force_delay_vars",
            "normalize_list_cons_literals",
        ]
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn pre_type_structural_repairs_ref_ids_before_when_field_destructure() {
    let expr = stale_destructurable_when_fields_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();

    let result = run_pre_type_structural_recovery_cluster(
        expr,
        &options,
        None,
        &mut blueprint_registry,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-destructure ref retarget");
    let destructure_pos = passes
        .iter()
        .position(|pass| *pass == "destructure_when_fields")
        .expect("expected destructure_when_fields to run");
    assert!(
        retarget_pos < destructure_pos,
        "expected retarget before destructure, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn pre_type_structural_repairs_ref_ids_before_unpack_tag_lift() {
    let expr = stale_unpack_tag_when_subject_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();

    let result = run_pre_type_structural_recovery_cluster(
        expr,
        &options,
        None,
        &mut blueprint_registry,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-lift ref retarget");
    let lift_pos = passes
        .iter()
        .position(|pass| *pass == "lift_unpack_tag_when_subjects")
        .expect("expected lift_unpack_tag_when_subjects to run");
    assert!(
        retarget_pos < lift_pos,
        "expected retarget before unpack/tag lift, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn pre_type_structural_repairs_ref_ids_before_data_case_resolution() {
    let expr = stale_data_case_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();

    let result = run_pre_type_structural_recovery_cluster(
        expr,
        &options,
        None,
        &mut blueprint_registry,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-Data.case ref retarget");
    let data_case_pos = passes
        .iter()
        .position(|pass| *pass == "resolve_data_case")
        .expect("expected resolve_data_case to run");
    assert!(
        retarget_pos < data_case_pos,
        "expected retarget before Data.case resolution, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn pre_type_structural_repairs_ref_ids_before_scott_constructor_resolution() {
    let expr = stale_scott_constructor_lambda_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();

    let result = run_pre_type_structural_recovery_cluster(
        expr,
        &options,
        None,
        &mut blueprint_registry,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-Scott ref retarget");
    let scott_pos = passes
        .iter()
        .position(|pass| *pass == "resolve_scott_constructor_lambdas")
        .expect("expected resolve_scott_constructor_lambdas to run");
    assert!(
        retarget_pos < scott_pos,
        "expected retarget before Scott constructor resolution, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));

    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected outer field let");
    };
    let PseudoExpr::Constr {
        tag, fields, shape, ..
    } = body.as_ref()
    else {
        panic!("expected Scott lambda to resolve to constructor, got: {body:?}");
    };
    assert_eq!(*tag, 0);
    assert_eq!(fields.len(), 1);
    assert!(matches!(
        shape,
        ConstructorShape::Unknown {
            tag: 0,
            arity: 1,
            ..
        }
    ));
    assert!(matches!(
        &fields[0],
        PseudoExpr::Var { name, .. } if name == "field"
    ));
}

#[test]
fn safe_mode_recovery_repairs_ref_ids_before_expect_tag_conversion() {
    let expr = stale_expect_fn_call_tag_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);

    let structural = crate::decompile::StructuralRecoveryPasses::all_on();
    let result = run_safe_mode_post_simplify_recovery_stage(expr, &structural, &mut executor);
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-expect-tag ref retarget");
    let convert_pos = passes
        .iter()
        .position(|pass| *pass == "convert_expect_tag")
        .expect("expected convert_expect_tag to run");
    assert!(
        retarget_pos < convert_pos,
        "expected retarget before expect-tag conversion, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));

    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected outer x let");
    };
    let PseudoExpr::When {
        subject, clauses, ..
    } = body.as_ref()
    else {
        panic!("expected expect-tag conversion to produce when, got: {body:?}");
    };
    assert!(matches!(
        subject.as_ref(),
        PseudoExpr::Var { name, id } if name == "x" && *id == Some(VarId::new(9349))
    ));
    assert!(matches!(
        clauses.first().map(|clause| &clause.pattern),
        Some(WhenPattern::Constructor { tag: 0, fields, .. }) if fields.is_empty()
    ));
}

#[test]
fn context_field_resolution_repairs_ref_ids_before_resolve_field_accesses() {
    let expr = stale_live_let_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let artifacts = SimplifyContextArtifacts::default();

    let result = run_context_field_resolution_stage(
        expr,
        Some(ScriptVersion::PlutusV3),
        &artifacts,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-field-resolution ref retarget");
    let resolve_pos = passes
        .iter()
        .position(|pass| *pass == "resolve_field_accesses")
        .expect("expected resolve_field_accesses to run");
    assert!(
        retarget_pos < resolve_pos,
        "expected retarget before field resolution, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

fn assert_normalized_identity_lambda(result: &PseudoExpr) {
    let PseudoExpr::Lambda { params, body } = result else {
        panic!("expected normalized identity lambda, got: {result:?}");
    };
    let [param] = params.as_slice() else {
        panic!("expected one lambda parameter, got: {params:?}");
    };
    assert_eq!(param.as_str(), "x");
    assert_eq!(param.id, VarId::new(9353));
    assert!(matches!(
        body.as_ref(),
        PseudoExpr::Var { name, id } if name == "x" && *id == Some(VarId::new(9353))
    ));
}

#[test]
fn base_readability_repairs_ref_ids_before_boolean_identity_simplification() {
    let expr = stale_identity_lambda_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);

    let options = DecompileOptions::default();
    let result = run_base_readability_cleanup(expr, &options, None, &mut executor);
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-boolean ref retarget");
    let boolean_pos = passes
        .iter()
        .position(|pass| *pass == "simplify_boolean_and_identity")
        .expect("expected simplify_boolean_and_identity to run");
    assert!(
        retarget_pos < boolean_pos,
        "expected retarget before boolean cleanup, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
    assert_normalized_identity_lambda(&result);
}

#[test]
fn post_readability_repairs_ref_ids_before_boolean_identity_simplification() {
    let expr = stale_identity_lambda_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);

    let options = DecompileOptions::default();
    let result = run_post_readability_cleanup_cluster(
        expr,
        PostReadabilityPasses {
            cps: PipelinePassId::EliminateCpsSelectorsPostReadability,
            boolean: PipelinePassId::SimplifyBooleanAndIdentityPostReadability,
            eta: PipelinePassId::CollapseEtaPairSelectorWhenSubjectsPostReadability,
            flatten: PipelinePassId::FlattenLetChainsPostReadability,
        },
        &options,
        None,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected post-readability pre-boolean ref retarget");
    let boolean_pos = passes
        .iter()
        .position(|pass| *pass == "simplify_boolean_and_identity_post_readability")
        .expect("expected post-readability boolean cleanup to run");
    assert!(
        retarget_pos < boolean_pos,
        "expected retarget before post-readability boolean cleanup, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
    assert_normalized_identity_lambda(&result);
}

#[test]
fn post_readability_simplify_records_late_call_result_annotation() {
    let trigger_id = VarId::new(9_871);
    let fn_id = VarId::new(9_872);
    let arg_id = VarId::new(9_873);
    let tmp_id = VarId::new(9_874);
    let preserved_id = VarId::new(9_875);
    let expr = PseudoExpr::Let {
        name: "trigger".to_string(),
        id: Some(trigger_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "tmp_17".to_string(),
            id: Some(tmp_id),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("fn_3", fn_id)),
                args: vec![PseudoExpr::var_with_id("arg", arg_id)].into(),
            }),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("trigger", trigger_id),
                    PseudoExpr::var_with_id("tmp_17", tmp_id),
                    PseudoExpr::var_with_id("tmp_17", tmp_id),
                ]
                .into(),
            )),
        }),
    };

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let expr = executor.ensure_consistent_ref_ids(expr);
    let mut simplify_state = simplify::SimplifyState::default();
    simplify_state.var_kinds.kind_annotations.insert(
        preserved_id,
        crate::pseudo::nameless::VarKind::DataLiteralHoist,
    );
    let preserved = HashSet::new();

    let options = DecompileOptions::default();
    let result = run_post_inline_simplify_if_changed(
        &expr,
        &options,
        &preserved,
        None,
        &mut simplify_state,
        false,
        &mut executor,
    )
    .expect("single-use trigger should force the late simplify path");

    assert!(
        matches!(
            simplify_state.var_kinds.kind_annotations.get(&tmp_id),
            Some(crate::pseudo::nameless::VarKind::CallResult { callee }) if *callee == fn_id
        ),
        "late simplify must record CallResult annotation in persistent state, got: {:?}",
        simplify_state.var_kinds.kind_annotations.get(&tmp_id)
    );
    assert!(
        matches!(
            simplify_state.var_kinds.kind_annotations.get(&preserved_id),
            Some(crate::pseudo::nameless::VarKind::DataLiteralHoist)
        ),
        "late simplify must extend, not replace, existing annotations"
    );
    assert!(
        passes.into_inner().contains(&"simplify_post_readability"),
        "expected late simplify pass to run"
    );
    assert!(
        matches!(
            result,
            PseudoExpr::Let { ref name, id, .. } if name == "fn_3_result" && id == Some(tmp_id)
        ),
        "expected late simplify to keep the annotated call-result let, got: {result:?}"
    );
}

#[test]
fn post_readability_simplify_records_late_field_index_alias_annotation() {
    let trigger_id = VarId::new(9_876);
    let parent_id = VarId::new(9_877);
    let fields_id = VarId::new(9_878);
    let expr = PseudoExpr::Let {
        name: "trigger".to_string(),
        id: Some(trigger_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "parent".to_string(),
            id: Some(parent_id),
            value: PBox::new(PseudoExpr::raw("parent", "test parent")),
            body: PBox::new(PseudoExpr::Let {
                name: "fields_0".to_string(),
                id: Some(fields_id),
                value: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("parent", parent_id),
                    "fields".to_string(),
                )),
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("trigger", trigger_id),
                        PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::var_with_id("fields_0", fields_id)),
                            index: 0,
                        },
                    ]
                    .into(),
                )),
            }),
        }),
    };

    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let expr = executor.ensure_consistent_ref_ids(expr);
    let mut simplify_state = simplify::SimplifyState::default();
    let preserved = HashSet::from([parent_id, fields_id]);

    let options = DecompileOptions::default();
    let _result = run_post_inline_simplify_if_changed(
        &expr,
        &options,
        &preserved,
        None,
        &mut simplify_state,
        false,
        &mut executor,
    )
    .expect("single-use trigger should force the late simplify path");

    assert!(
        simplify_state
            .var_kinds
            .kind_annotations
            .values()
            .any(|kind| {
                matches!(
                    kind,
                    crate::pseudo::nameless::VarKind::FieldIndexAlias { parent, index }
                        if *parent == parent_id && *index == 0
                )
            }),
        "late simplify must record FieldIndexAlias in persistent state, got: {:?}",
        simplify_state.var_kinds.kind_annotations
    );
}

#[test]
fn readability_repairs_ref_ids_before_dead_let_elimination() {
    let expr = stale_live_let_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let mut options = DecompileOptions::default();
    options.safe_mode = true;
    options.type_passes = crate::decompile::TypePasses::all_off();
    let preserved = HashSet::new();
    let type_env = crate::decompile::mid::type_env::TypeEnvironment::new();
    let mut blueprint_registry = BlueprintHintRegistry::new();
    let mut final_types = None;
    let mut simplify_state = simplify::SimplifyState::default();

    let result = run_readability_pipeline_stage(
        expr,
        &options,
        &mut simplify_state,
        &preserved,
        &type_env,
        &mut blueprint_registry,
        &mut final_types,
        &mut executor,
    );

    assert_eq!(
        passes.into_inner(),
        vec!["retarget_refs_by_scope", "eliminate_dead_lets"]
    );
    assert!(
        matches!(
            result,
            PseudoExpr::Let { ref name, ref body, .. }
                if name == "live"
                    && matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "live")
        ),
        "DCE must keep the live let after ref-id repair"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn pre_type_structural_repairs_ref_ids_before_constructor_disambiguation() {
    let expr = stale_raw_fields_disambiguation_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();

    let result = run_pre_type_structural_recovery_cluster(
        expr,
        &options,
        None,
        &mut blueprint_registry,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-disambiguation ref retarget");
    let disambiguate_pos = passes
        .iter()
        .position(|pass| *pass == "disambiguate_constructors")
        .expect("expected disambiguate_constructors to run");
    assert!(
        retarget_pos < disambiguate_pos,
        "expected retarget before constructor disambiguation, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));

    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected outer let");
    };
    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected when body");
    };
    for clause in clauses {
        let WhenPattern::Constructor { shape, .. } = &clause.pattern else {
            panic!("expected constructor pattern, got: {:?}", clause.pattern);
        };
        assert!(
            matches!(shape, ConstructorShape::Unknown { .. }),
            "raw `.fields` access should suppress Bool/Option fallback disambiguation"
        );
    }
}

#[test]
fn base_readability_repairs_ref_ids_before_eta_pair_selector_collapse() {
    let expr = stale_eta_pair_selector_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);

    let options = DecompileOptions::default();
    let result = run_base_readability_cleanup(expr, &options, None, &mut executor);
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-eta-collapse ref retarget");
    let collapse_pos = passes
        .iter()
        .position(|pass| *pass == "collapse_eta_pair_selector_when_subjects")
        .expect("expected eta pair selector collapse to run");
    assert!(
        retarget_pos < collapse_pos,
        "expected retarget before eta pair selector collapse, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn post_readability_repairs_ref_ids_before_eta_pair_selector_collapse() {
    let expr = stale_eta_pair_selector_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);

    let options = DecompileOptions::default();
    let result = run_post_readability_cleanup_cluster(
        expr,
        PostReadabilityPasses {
            cps: PipelinePassId::EliminateCpsSelectorsPostReadability,
            boolean: PipelinePassId::SimplifyBooleanAndIdentityPostReadability,
            eta: PipelinePassId::CollapseEtaPairSelectorWhenSubjectsPostReadability,
            flatten: PipelinePassId::FlattenLetChainsPostReadability,
        },
        &options,
        None,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected post-readability ref retarget");
    let collapse_pos = passes
        .iter()
        .position(|pass| *pass == "collapse_eta_pair_selector_when_subjects_post_readability")
        .expect("expected post-readability eta collapse to run");
    assert!(
        retarget_pos < collapse_pos,
        "expected retarget before post-readability eta collapse, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn pre_type_structural_repairs_ref_ids_before_double_rec_simplification() {
    let expr = stale_recursive_inner_recfn_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();

    let result = run_pre_type_structural_recovery_cluster(
        expr,
        &options,
        None,
        &mut blueprint_registry,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-double-rec ref retarget");
    let simplify_pos = passes
        .iter()
        .position(|pass| *pass == "simplify_double_rec_fn")
        .expect("expected simplify_double_rec_fn to run");
    assert!(
        retarget_pos < simplify_pos,
        "expected retarget before double-rec simplification, got: {passes:?}"
    );
    assert!(
        matches!(
            result,
            PseudoExpr::RecFn { ref body, .. }
                if matches!(body.as_ref(), PseudoExpr::RecFn { .. })
        ),
        "inner recursive function must not be converted to a lambda after ref-id repair"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn pre_type_structural_repairs_ref_ids_before_z_combinator_simplification() {
    let expr = stale_z_combinator_step_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();

    let result = run_pre_type_structural_recovery_cluster(
        expr,
        &options,
        None,
        &mut blueprint_registry,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-Z ref retarget");
    let simplify_pos = passes
        .iter()
        .position(|pass| *pass == "simplify_z_combinator")
        .expect("expected simplify_z_combinator to run");
    assert!(
        retarget_pos < simplify_pos,
        "expected retarget before Z-combinator simplification, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));

    let PseudoExpr::Let { body, .. } = result else {
        panic!("expected captured let wrapper");
    };
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        panic!("expected Z-combinator step to resolve to fix application, got: {body:?}");
    };
    assert!(matches!(
        function.as_ref(),
        PseudoExpr::HelperSymbol(crate::pseudo::ast::HelperIntrinsic::Fix)
    ));
    assert!(matches!(
        args.as_slice(),
        [PseudoExpr::Var { name, id }] if name == "captured" && *id == Some(VarId::new(9391))
    ));
}

#[test]
fn pre_type_structural_repairs_ref_ids_before_immediate_application_resolution() {
    let expr = stale_immediate_lambda_application_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();

    let result = run_pre_type_structural_recovery_cluster(
        expr,
        &options,
        None,
        &mut blueprint_registry,
        &mut executor,
    );
    let passes = passes.into_inner();

    let retarget_pos = passes
        .iter()
        .position(|pass| *pass == "retarget_refs_by_scope")
        .expect("expected pre-immediate-application ref retarget");
    let immediate_pos = passes
        .iter()
        .position(|pass| *pass == "resolve_immediate_applications")
        .expect("expected resolve_immediate_applications to run");
    assert!(
        retarget_pos < immediate_pos,
        "expected retarget before immediate application resolution, got: {passes:?}"
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
    assert!(matches!(
        result,
        PseudoExpr::Let {
            ref name,
            id,
            ref body,
            ..
        } if name == "x"
            && id == Some(VarId::new(9401))
            && matches!(
                body.as_ref(),
                PseudoExpr::Var { name, id } if name == "x" && *id == Some(VarId::new(9401))
            )
    ));
}

#[test]
fn pre_type_structural_extract_complex_when_subjects_emits_normalized_output() {
    let expr = duplicate_named_complex_when_subject_expr();
    assert!(contains_complex_when_subjects(&expr));

    let passes = RefCell::new(Vec::new());
    let extracted = RefCell::new(None);
    let mut on_pass = |pass: &'static str, expr: &PseudoExpr| {
        passes.borrow_mut().push(pass);
        if pass == "extract_complex_when_subjects" {
            *extracted.borrow_mut() = Some(expr.clone());
        }
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    let options = DecompileOptions::default();
    let mut blueprint_registry = BlueprintHintRegistry::new();

    let result = run_pre_type_structural_recovery_cluster(
        expr,
        &options,
        None,
        &mut blueprint_registry,
        &mut executor,
    );
    let passes = passes.into_inner();

    assert!(
        passes.contains(&"extract_complex_when_subjects"),
        "expected complex when-subject extraction to run, got: {passes:?}"
    );
    let extracted = extracted
        .into_inner()
        .expect("expected emitted extract_complex_when_subjects snapshot");
    assert_unique_let_names(&extracted);
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&extracted));
    assert_unique_let_names(&result);
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}

#[test]
fn post_readability_flatten_repairs_ref_ids_before_id_aware_flatten() {
    let expr = stale_flattenable_let_chain_expr();
    assert!(crate::decompile::ref_retarget::refs_need_retarget_by_scope(
        &expr
    ));

    let passes = RefCell::new(Vec::new());
    let mut on_pass = |pass: &'static str, _: &PseudoExpr| {
        passes.borrow_mut().push(pass);
    };
    let mut executor = PipelineExecutor::new(&mut on_pass, false);

    let options = DecompileOptions::default();
    let result = run_post_readability_cleanup_cluster(
        expr,
        PostReadabilityPasses {
            cps: PipelinePassId::EliminateCpsSelectorsPostReadability,
            boolean: PipelinePassId::SimplifyBooleanAndIdentityPostReadability,
            eta: PipelinePassId::CollapseEtaPairSelectorWhenSubjectsPostReadability,
            flatten: PipelinePassId::FlattenLetChainsPostReadability,
        },
        &options,
        None,
        &mut executor,
    );

    assert_eq!(
        passes.into_inner(),
        vec![
            "retarget_refs_by_scope",
            "flatten_let_chains_post_readability"
        ]
    );
    assert!(!crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result));
}
