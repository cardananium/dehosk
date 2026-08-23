use super::*;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;
use std::collections::HashMap;

fn binder(name: &str) -> Binder {
    Binder::synthetic(name)
}

fn assert_cardano_context(
    annotations: &HashMap<VarId, VarKind>,
    id: VarId,
    expected_context_type: &str,
) {
    match annotations.get(&id) {
        Some(VarKind::CardanoContext { context_type }) => {
            assert_eq!(context_type, expected_context_type);
        }
        other => panic!("expected CardanoContext annotation for {id:?}, got {other:?}"),
    }
}

#[test]
fn v3_records_script_context_kind_annotation_for_entry_param() {
    let context_id = VarId::new(901);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("__context__", context_id)],
        body: PBox::new(PseudoExpr::var_with_id("__context__", context_id)),
    };
    let mut annotations = HashMap::new();

    let renamed = rename_validator_params_with_var_kinds(
        lambda,
        Some(ScriptVersion::PlutusV3),
        &mut annotations,
        None,
        None,
    );

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "script_context");
            assert_eq!(params[0].var_id(), context_id);
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
    assert_cardano_context(&annotations, context_id, "script_context");
}

#[test]
fn v2_records_role_kind_annotations_for_validator_params() {
    let datum_id = VarId::new(902);
    let redeemer_id = VarId::new(903);
    let context_id = VarId::new(904);
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("a", datum_id),
            Binder::new("b", redeemer_id),
            Binder::new("c", context_id),
        ],
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut annotations = HashMap::new();

    // Early rename: datum/redeemer get NON-authoritative
    // ValidatorEntryParam markers, script_context gets CardanoContext.
    let renamed = rename_validator_params_with_var_kinds(
        lambda,
        Some(ScriptVersion::PlutusV2),
        &mut annotations,
        None,
        None,
    );

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params[0].as_str(), "datum");
            assert_eq!(params[1].as_str(), "redeemer");
            assert_eq!(params[2].as_str(), "script_context");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
    assert_eq!(
        annotations.get(&datum_id),
        Some(&VarKind::ValidatorEntryParam {
            param_name: "datum".to_string(),
            authoritative: false,
        })
    );
    assert_eq!(
        annotations.get(&redeemer_id),
        Some(&VarKind::ValidatorEntryParam {
            param_name: "redeemer".to_string(),
            authoritative: false,
        })
    );
    assert_cardano_context(&annotations, context_id, "script_context");
    assert_eq!(annotations.len(), 3);
}

#[test]
fn v2_authoritative_rename_stamps_authoritative_role_markers() {
    let datum_id = VarId::new(912);
    let redeemer_id = VarId::new(913);
    let context_id = VarId::new(914);
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("a", datum_id),
            Binder::new("b", redeemer_id),
            Binder::new("c", context_id),
        ],
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut annotations = HashMap::new();

    // The authoritative (late) rename: datum/redeemer get AUTHORITATIVE
    // markers so assign_names lets them claim the bare role name.
    let _ = rename_validator_params_with_var_kinds_authoritative(
        lambda,
        Some(ScriptVersion::PlutusV2),
        &mut annotations,
        None,
        None,
    );

    assert_eq!(
        annotations.get(&datum_id),
        Some(&VarKind::ValidatorEntryParam {
            param_name: "datum".to_string(),
            authoritative: true,
        })
    );
    assert_eq!(
        annotations.get(&redeemer_id),
        Some(&VarKind::ValidatorEntryParam {
            param_name: "redeemer".to_string(),
            authoritative: true,
        })
    );
    assert_cardano_context(&annotations, context_id, "script_context");
}

#[test]
fn no_script_version_records_no_kind_annotation() {
    let context_id = VarId::new(905);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("__context__", context_id)],
        body: PBox::new(PseudoExpr::var_with_id("__context__", context_id)),
    };
    let mut annotations = HashMap::new();

    let renamed =
        rename_validator_params_with_var_kinds(lambda, None, &mut annotations, None, None);

    assert!(annotations.is_empty());
    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "__context__");
            assert_eq!(params[0].var_id(), context_id);
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v3_renames_single_context_param_with_no_prologue() {
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("__context__")],
        body: PBox::new(PseudoExpr::var("body_result")),
    };

    let renamed = rename_validator_params(lambda, Some(ScriptVersion::PlutusV3));

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "script_context");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

/// A V3 validator with one user-level parameter deployed via
/// `applyParamsToScript` lowers to `Let p = Const in Lambda [p,
/// __context__] body`. The entry arity is 2, so a strict V3-arity-1
/// match bails out and leaves the real context param un-renamed.
#[test]
fn v3_renames_last_param_of_multi_arg_entry_under_let_prologue() {
    let applied_param_id = VarId::new(101);
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("_"), binder("__5")],
        body: PBox::new(PseudoExpr::var("body_result")),
    };
    let expr = PseudoExpr::Let {
        name: "x_4".to_string(),
        id: Some(applied_param_id),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(lambda),
    };

    let renamed = rename_validator_params(expr, Some(ScriptVersion::PlutusV3));

    let PseudoExpr::Let { body, .. } = renamed else {
        panic!("expected outer Let prologue to be preserved");
    };
    match body.into_inner() {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 2);
            assert_eq!(
                params[0].as_str(),
                "_",
                "leading user-level param should stay untouched"
            );
            assert_eq!(
                params[1].as_str(),
                "script_context",
                "last param must be renamed to script_context"
            );
        }
        other => panic!("expected inner Lambda under Let, got: {other:?}"),
    }
}

#[test]
fn v3_renames_last_param_of_three_arg_entry() {
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("__2"), binder("__3"), binder("__5")],
        body: PBox::new(PseudoExpr::var("body_result")),
    };

    let renamed = rename_validator_params(lambda, Some(ScriptVersion::PlutusV3));

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 3);
            assert_eq!(params[0].as_str(), "__2");
            assert_eq!(params[1].as_str(), "__3");
            assert_eq!(params[2].as_str(), "script_context");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v1_v2_with_standard_arity_still_renames_all_entries() {
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("a"), binder("b"), binder("c")],
        body: PBox::new(PseudoExpr::var("body_result")),
    };

    let renamed = rename_validator_params(lambda, Some(ScriptVersion::PlutusV2));

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params[0].as_str(), "datum");
            assert_eq!(params[1].as_str(), "redeemer");
            assert_eq!(params[2].as_str(), "script_context");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v1_v2_arity_above_spend_is_ambiguous_and_not_renamed() {
    // V1/V2 can't disambiguate "spend + N user params" from "mint +
    // (N+1) user params" at arity > 3, so no param is renamed rather
    // than risk mis-labelling a user arg as `datum` or `redeemer`.
    let lambda = PseudoExpr::Lambda {
        params: vec![
            binder("user_a"),
            binder("user_b"),
            binder("x_1"),
            binder("x_2"),
            binder("x_3"),
        ],
        body: PBox::new(PseudoExpr::var("body_result")),
    };

    let renamed = rename_validator_params(lambda.clone(), Some(ScriptVersion::PlutusV2));

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            let names: Vec<&str> = params.iter().map(Binder::as_str).collect();
            assert_eq!(names, vec!["user_a", "user_b", "x_1", "x_2", "x_3"]);
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v3_renames_entry_param_without_touching_shadowed_same_name_binding() {
    let outer_id = VarId::new(201);
    let inner_id = VarId::new(202);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("__5", outer_id)],
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Var {
                    name: "__5".to_string(),
                    id: Some(outer_id),
                },
                PseudoExpr::Lambda {
                    params: vec![Binder::new("__5", inner_id)],
                    body: PBox::new(PseudoExpr::Var {
                        name: "__5".to_string(),
                        id: Some(inner_id),
                    }),
                },
            ]
            .into(),
        )),
    };

    let renamed = rename_validator_params(lambda, Some(ScriptVersion::PlutusV3));

    match renamed {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "script_context");
            assert_eq!(params[0].var_id(), outer_id);

            match body.into_inner() {
                PseudoExpr::Tuple(items) => {
                    assert_eq!(items.len(), 2);
                    assert!(
                        matches!(
                            &items[0],
                            PseudoExpr::Var { name, id, .. }
                                if name == "script_context" && *id == Some(outer_id)
                        ),
                        "expected outer ref to be renamed by id, got: {:?}",
                        items[0]
                    );
                    assert!(
                        matches!(
                            &items[1],
                            PseudoExpr::Lambda { params, body }
                                if params.len() == 1
                                    && params[0].as_str() == "__5"
                                    && params[0].var_id() == inner_id
                                    && matches!(
                                        body.as_ref(),
                                        PseudoExpr::Var { name, id, .. }
                                            if name == "__5" && *id == Some(inner_id)
                                    )
                        ),
                        "expected shadowed inner binding to stay untouched, got: {:?}",
                        items[1]
                    );
                }
                other => panic!("expected tuple body after rename, got: {other:?}"),
            }
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v3_target_name_collision_can_invalidate_consistent_ref_ids_until_uniquify() {
    let outer_id = VarId::new(203);
    let inner_id = VarId::new(204);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("__context__", outer_id)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("script_context", inner_id)],
            body: PBox::new(PseudoExpr::Var {
                name: "__context__".to_string(),
                id: Some(outer_id),
            }),
        }),
    };

    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&lambda),
        "fixture must start with consistent refs"
    );

    let renamed = rename_validator_params(lambda, Some(ScriptVersion::PlutusV3));

    assert!(
        crate::decompile::ref_retarget::refs_need_retarget_by_scope(&renamed),
        "renaming to script_context can collide with an inner target-name binder"
    );

    let uniquified = crate::decompile::uniquify_let_names(renamed);
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&uniquified),
        "the following uniquify boundary restores name/id consistency"
    );
}

#[test]
fn no_script_version_is_still_noop() {
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("__context__")],
        body: PBox::new(PseudoExpr::var("body_result")),
    };
    let before = lambda.clone();
    let after = rename_validator_params(lambda, None);
    assert_eq!(format!("{before:?}"), format!("{after:?}"));
}

/// V3 parameterized validator with one user param.
/// Blueprint hint `["amount"]` renames the leading slot to `amount`
/// while `script_context` still occupies the trailing slot.
#[test]
fn v3_parameterized_validator_uses_blueprint_param_name() {
    let amount_id = VarId::new(701);
    let ctx_id = VarId::new(702);
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("__1", amount_id),
            Binder::new("__context__", ctx_id),
        ],
        body: PBox::new(PseudoExpr::var_with_id("__1", amount_id)),
    };
    let names = vec!["amount".to_string()];

    let renamed =
        rename_validator_params_with_blueprint(lambda, Some(ScriptVersion::PlutusV3), Some(&names));

    match renamed {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].as_str(), "amount");
            assert_eq!(params[0].var_id(), amount_id);
            assert_eq!(params[1].as_str(), "script_context");
            assert_eq!(params[1].var_id(), ctx_id);
            assert!(
                matches!(
                    *body,
                    PseudoExpr::Var { ref name, id, .. }
                        if name == "amount" && id == Some(amount_id)
                ),
                "expected body ref renamed to amount, got: {body:?}"
            );
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

/// V1/V2 arity-4 is otherwise ambiguous and falls through
/// unrenamed. A blueprint hint of length 1 fixes the trailing
/// layout as spend (datum, redeemer, script_context).
#[test]
fn v1v2_arity_four_disambiguated_by_blueprint_hint_length() {
    let lambda = PseudoExpr::Lambda {
        params: vec![
            binder("user_a"),
            binder("__d"),
            binder("__r"),
            binder("__sc"),
        ],
        body: PBox::new(PseudoExpr::var("body_result")),
    };
    let names = vec!["user_a".to_string()];

    let renamed =
        rename_validator_params_with_blueprint(lambda, Some(ScriptVersion::PlutusV2), Some(&names));

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 4);
            assert_eq!(params[0].as_str(), "user_a");
            assert_eq!(params[1].as_str(), "datum");
            assert_eq!(params[2].as_str(), "redeemer");
            assert_eq!(params[3].as_str(), "script_context");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

/// Edge case: blueprint param name "_" stays anonymous
/// (the leading slot is left untouched rather than renamed to "_").
#[test]
fn blueprint_param_underscore_leaves_slot_untouched() {
    let amount_id = VarId::new(703);
    let ctx_id = VarId::new(704);
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("__1", amount_id),
            Binder::new("__context__", ctx_id),
        ],
        body: PBox::new(PseudoExpr::var_with_id("__1", amount_id)),
    };
    let names = vec!["_".to_string()];

    let renamed =
        rename_validator_params_with_blueprint(lambda, Some(ScriptVersion::PlutusV3), Some(&names));

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 2);
            // Leading slot stays at the simplifier-chosen name when
            // the blueprint hint is "_".
            assert_eq!(params[0].as_str(), "__1");
            assert_eq!(params[0].var_id(), amount_id);
            assert_eq!(params[1].as_str(), "script_context");
            assert_eq!(params[1].var_id(), ctx_id);
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

// ──────────────────────────────────────────────────────────────────
// Curried-Lambda uncurry tests.
//
// PlutusTx sometimes emit the validator entry as a curried
// `Lambda(p1) { ... Lambda(p2) { body } }` chain instead of a single
// multi-arg Lambda. The rename pass uncurries to the nearest
// validator arity before applying the trailing-param rename plan.
// ──────────────────────────────────────────────────────────────────

#[test]
fn v2_uncurry_curried_2_lambda_renames_redeemer_and_script_context() {
    // λy. λx. x  →  λ(y, x). x  ; rename trailing 2 to (redeemer, script_context).
    let y_id = VarId::new(1001);
    let x_id = VarId::new(1002);
    let inner = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    let outer = PseudoExpr::Lambda {
        params: vec![Binder::new("y", y_id)],
        body: PBox::new(inner),
    };
    let renamed = rename_validator_params(outer, Some(ScriptVersion::PlutusV2));

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].as_str(), "redeemer");
            assert_eq!(params[0].var_id(), y_id);
            assert_eq!(params[1].as_str(), "script_context");
            assert_eq!(params[1].var_id(), x_id);
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v2_uncurry_curried_3_lambda_renames_datum_redeemer_script_context() {
    // λa. λb. λc. c  →  λ(a, b, c). c  ; rename trailing 3.
    let a_id = VarId::new(1010);
    let b_id = VarId::new(1011);
    let c_id = VarId::new(1012);
    let innermost = PseudoExpr::Lambda {
        params: vec![Binder::new("c", c_id)],
        body: PBox::new(PseudoExpr::var_with_id("c", c_id)),
    };
    let middle = PseudoExpr::Lambda {
        params: vec![Binder::new("b", b_id)],
        body: PBox::new(innermost),
    };
    let outer = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id)],
        body: PBox::new(middle),
    };
    let renamed = rename_validator_params(outer, Some(ScriptVersion::PlutusV2));

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 3);
            assert_eq!(params[0].as_str(), "datum");
            assert_eq!(params[1].as_str(), "redeemer");
            assert_eq!(params[2].as_str(), "script_context");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v2_uncurry_preserves_let_chain_between_lambdas() {
    // λy. let a = y in λx. a  →  λ(y, x). let a = y in a
    let y_id = VarId::new(1020);
    let x_id = VarId::new(1021);
    let a_id = VarId::new(1022);
    let inner = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("a", a_id)),
    };
    let let_a = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(a_id),
        value: PBox::new(PseudoExpr::var_with_id("y", y_id)),
        body: PBox::new(inner),
    };
    let outer = PseudoExpr::Lambda {
        params: vec![Binder::new("y", y_id)],
        body: PBox::new(let_a),
    };
    let renamed = rename_validator_params(outer, Some(ScriptVersion::PlutusV2));

    // Expected shape: λ(redeemer, script_context). let a = redeemer in a
    match renamed {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].as_str(), "redeemer");
            assert_eq!(params[0].var_id(), y_id);
            assert_eq!(params[1].as_str(), "script_context");
            assert_eq!(params[1].var_id(), x_id);
            match body.into_inner() {
                PseudoExpr::Let {
                    name,
                    body: inner_body,
                    value,
                    ..
                } => {
                    assert_eq!(name, "a");
                    // The let's VALUE now references redeemer.
                    match value.into_inner() {
                        PseudoExpr::Var { name, .. } => assert_eq!(name, "redeemer"),
                        other => panic!("expected Var in let value, got: {other:?}"),
                    }
                    // The let body still references `a` (unchanged).
                    match inner_body.into_inner() {
                        PseudoExpr::Var { name, .. } => assert_eq!(name, "a"),
                        other => panic!("expected Var in let body, got: {other:?}"),
                    }
                }
                other => panic!("expected Let inside fused Lambda, got: {other:?}"),
            }
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v2_uncurry_fails_when_inner_is_not_lambda() {
    // λy. y  (arity 1, no inner Lambda) — V2 wants 2/3, not 1.
    // Direct rename fails, uncurry fails (no further lambdas),
    // so the Lambda is returned unchanged.
    let y_id = VarId::new(1030);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("y", y_id)],
        body: PBox::new(PseudoExpr::var_with_id("y", y_id)),
    };
    let renamed = rename_validator_params(lambda, Some(ScriptVersion::PlutusV2));

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 1);
            // Untouched.
            assert_eq!(params[0].as_str(), "y");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v3_direct_arity_1_preempts_uncurry() {
    // V3 accepts any arity ≥ 1 (last slot = script_context, leading
    // slots are user params). For λy. λx. x, direct arity 1 already
    // matches V3's "arity ≥ 1 → script_context" rule, so the outer y
    // becomes script_context and the inner λx stays part of the body.
    //
    // V1/V2 differ: they require exactly arity 2 or 3, so uncurry IS
    // needed when direct arity is 1. V3's permissive rule cannot
    // distinguish a single-arg entry from a curried multi-arg one, so
    // direct arity wins here.
    let y_id = VarId::new(1040);
    let x_id = VarId::new(1041);
    let inner = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    let outer = PseudoExpr::Lambda {
        params: vec![Binder::new("y", y_id)],
        body: PBox::new(inner),
    };
    let renamed = rename_validator_params(outer, Some(ScriptVersion::PlutusV3));

    match renamed {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "script_context");
            assert_eq!(params[0].var_id(), y_id);
            // Body remains the inner Lambda — uncurry did not fire.
            assert!(matches!(*body, PseudoExpr::Lambda { .. }));
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v2_uncurry_rejects_when_let_binder_shadowed_by_inner_lambda_param() {
    // λy. let x = y in λx. x  — the inner λx originally shadows
    // the let-x. Fusion to `λ(y, x). let x = y in x` would
    // reverse shadowing (let-x now shadows the param-x), changing
    // semantics. Hygiene guard rejects; lambda stays untouched.
    let y_id = VarId::new(1060);
    let x_let_id = VarId::new(1061);
    let x_param_id = VarId::new(1062);
    let inner = PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_param_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_param_id)),
    };
    let let_x = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_let_id),
        value: PBox::new(PseudoExpr::var_with_id("y", y_id)),
        body: PBox::new(inner),
    };
    let outer = PseudoExpr::Lambda {
        params: vec![Binder::new("y", y_id)],
        body: PBox::new(let_x),
    };
    let renamed = rename_validator_params(outer, Some(ScriptVersion::PlutusV2));

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            // Untouched — uncurry rejected, no rename applied.
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "y");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v2_uncurry_rejects_when_extra_lambda_remains_after_target_arity() {
    // λu. λd. λr. λsc. sc  — 4-deep curried. V1/V2 candidate
    // arities are [3, 2]. Uncurry-to-3 would peel u,d,r and
    // leave λsc in the body — that classifies arity 4 as arity
    // 3, dropping the actual script_context param. The truncation
    // guard rejects.
    //
    // Direct arity 1 also doesn't match V1/V2 (needs 2/3 or
    // blueprint-disambiguated > 3). So overall no rename fires.
    let u_id = VarId::new(1070);
    let d_id = VarId::new(1071);
    let r_id = VarId::new(1072);
    let sc_id = VarId::new(1073);
    let innermost = PseudoExpr::Lambda {
        params: vec![Binder::new("sc", sc_id)],
        body: PBox::new(PseudoExpr::var_with_id("sc", sc_id)),
    };
    let l3 = PseudoExpr::Lambda {
        params: vec![Binder::new("r", r_id)],
        body: PBox::new(innermost),
    };
    let l2 = PseudoExpr::Lambda {
        params: vec![Binder::new("d", d_id)],
        body: PBox::new(l3),
    };
    let l1 = PseudoExpr::Lambda {
        params: vec![Binder::new("u", u_id)],
        body: PBox::new(l2),
    };
    let renamed = rename_validator_params(l1, Some(ScriptVersion::PlutusV2));

    match renamed {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "u");
            // Body must still be the inner lambda chain unchanged.
            assert!(matches!(*body, PseudoExpr::Lambda { .. }));
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn v2_uncurry_keeps_binder_silent_when_direct_arity_already_matches() {
    // λ(a, b). b already matches V2's arity 2, so the direct rename
    // fires without uncurry: trailing 2 become redeemer,
    // script_context.
    let a_id = VarId::new(1050);
    let b_id = VarId::new(1051);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
        body: PBox::new(PseudoExpr::var_with_id("b", b_id)),
    };
    let renamed = rename_validator_params(lambda, Some(ScriptVersion::PlutusV2));

    match renamed {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].as_str(), "redeemer");
            assert_eq!(params[1].as_str(), "script_context");
            // Body should still be the single Var (no uncurry-induced Let).
            assert!(matches!(*body, PseudoExpr::Var { .. }));
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

// ──────────────────────────────────────────────────────────────────
// has_script_context_evidence tests.
// ──────────────────────────────────────────────────────────────────

use crate::pseudo::field_selector::FieldSelector;

#[test]
fn sc_evidence_signal_tagged_param() {
    let p_id = VarId::new(2000);
    let params = vec![Binder::new("__1", p_id)];
    let body = PseudoExpr::Unit;
    let mut kinds = HashMap::new();
    kinds.insert(
        p_id,
        VarKind::CardanoContext {
            context_type: "script_context".to_string(),
        },
    );
    assert!(has_script_context_evidence(&params, &body, Some(&kinds)));
}

#[test]
fn sc_evidence_signal_named_param() {
    let p_id = VarId::new(2001);
    let params = vec![Binder::new("script_context", p_id)];
    let body = PseudoExpr::Unit;
    assert!(has_script_context_evidence(&params, &body, None));
}

#[test]
fn sc_evidence_signal_context_field_projection() {
    let p_id = VarId::new(2002);
    let params = vec![Binder::new("__1", p_id)];
    let body = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::var_with_id("__1", p_id)),
        selector: FieldSelector::ContextField("tx_info".to_string()),
    };
    assert!(has_script_context_evidence(&params, &body, None));
}

#[test]
fn sc_evidence_signal_named_field_projection() {
    let p_id = VarId::new(2003);
    let params = vec![Binder::new("__1", p_id)];
    let body = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::var_with_id("__1", p_id)),
        selector: FieldSelector::NamedField("purpose".to_string()),
    };
    assert!(has_script_context_evidence(&params, &body, None));
}

#[test]
fn sc_evidence_signal_index_access_projection() {
    let p_id = VarId::new(2004);
    let params = vec![Binder::new("__1", p_id)];
    let body = PseudoExpr::IndexAccess {
        collection: PBox::new(PseudoExpr::var_with_id("__1", p_id)),
        index: 0,
    };
    assert!(has_script_context_evidence(&params, &body, None));
}

#[test]
fn sc_evidence_no_signal_returns_false() {
    let p_id = VarId::new(2005);
    let params = vec![Binder::new("__1", p_id)];
    let body = PseudoExpr::var_with_id("__1", p_id);
    assert!(!has_script_context_evidence(&params, &body, None));
}

#[test]
fn sc_evidence_projection_on_non_param_var_is_not_signal() {
    let p_id = VarId::new(2006);
    let other_id = VarId::new(2007);
    let params = vec![Binder::new("__1", p_id)];
    let body = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::var_with_id("other", other_id)),
        selector: FieldSelector::ContextField("tx_info".to_string()),
    };
    assert!(!has_script_context_evidence(&params, &body, None));
}

#[test]
fn sc_evidence_nested_projection_inside_let() {
    let p_id = VarId::new(2008);
    let let_id = VarId::new(2009);
    let params = vec![Binder::new("__1", p_id)];
    let body = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(let_id),
        value: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("__1", p_id)),
            selector: FieldSelector::NamedField("purpose".to_string()),
        }),
        body: PBox::new(PseudoExpr::var_with_id("x", let_id)),
    };
    assert!(has_script_context_evidence(&params, &body, None));
}

#[test]
fn sc_evidence_nested_projection_inside_when_clause_body() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    let p_id = VarId::new(2010);
    let params = vec![Binder::new("__1", p_id)];
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("__1", p_id)),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![],
                shape: ConstructorShape::unknown_data(0, 0),
            },
            PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::var_with_id("__1", p_id)),
                selector: FieldSelector::ContextField("tx_info".to_string()),
            },
        )],
    };
    assert!(has_script_context_evidence(&params, &body, None));
}

// ──────────────────────────────────────────────────────────────────
// scored_picker_* tests.
//
// These exercise the hoisted-helpers shape with a non-Lambda tail
// where the prefix stack holds several let-bound Lambdas.
// SC-evidence scoring is not wired in, so the reverse-walk picks
// the last arity-matching prefix.
// ──────────────────────────────────────────────────────────────────

#[test]
fn scored_picker_bails_when_multiple_sc_candidates_falls_back_to_last() {
    // Both lets have SC evidence, so scoring cannot disambiguate;
    // the fallback reverse-walk picks the LAST one.
    let a_id = VarId::new(3200);
    let b_id = VarId::new(3201);
    let c_id = VarId::new(3202);
    let d_id = VarId::new(3203);

    let first_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
        body: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("b", b_id)),
            selector: FieldSelector::ContextField("tx_info".to_string()),
        }),
    };
    let second_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("c", c_id), Binder::new("d", d_id)],
        body: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("d", d_id)),
            selector: FieldSelector::ContextField("tx_info".to_string()),
        }),
    };
    let inner = PseudoExpr::Let {
        name: "second".to_string(),
        id: Some(VarId::new(3300)),
        value: PBox::new(second_lambda),
        body: PBox::new(PseudoExpr::Unit),
    };
    let outer = PseudoExpr::Let {
        name: "first".to_string(),
        id: Some(VarId::new(3301)),
        value: PBox::new(first_lambda),
        body: PBox::new(inner),
    };

    let renamed = rename_validator_params(outer, Some(ScriptVersion::PlutusV2));

    // Two SC candidates → bail → fallback renames the LAST (second).
    let PseudoExpr::Let {
        body: outer_body,
        value: first_value,
        ..
    } = renamed
    else {
        panic!("expected outer Let")
    };
    let PseudoExpr::Lambda {
        params: first_params,
        ..
    } = first_value.into_inner()
    else {
        panic!("expected first Lambda value")
    };
    // First's params stay at their original names (a, b).
    assert_eq!(first_params[0].as_str(), "a");
    assert_eq!(first_params[1].as_str(), "b");

    let PseudoExpr::Let {
        value: second_value,
        ..
    } = outer_body.into_inner()
    else {
        panic!("expected inner Let")
    };
    let PseudoExpr::Lambda {
        params: second_params,
        ..
    } = second_value.into_inner()
    else {
        panic!("expected second Lambda value")
    };
    // Fallback reverse-walk renamed the last one (second).
    assert_eq!(second_params[0].as_str(), "redeemer");
    assert_eq!(second_params[1].as_str(), "script_context");
}

#[test]
fn scored_picker_helper_with_sc_then_entry_without() {
    // Shape:
    //   let helper = fn(a, sc) { sc.tx_info }     // arity 2, SC projection
    //   let entry  = fn(r, sc) { helper(sc) }     // arity 2, NO SC projection
    //   Unit
    //
    // The reverse-walk picks `entry` (last arity-match), which is
    // correct. A naive "promote the unique SC candidate" rule would
    // promote `helper` instead — this test guards against wiring one in.
    let helper_a_id = VarId::new(3600);
    let helper_sc_id = VarId::new(3601);
    let entry_r_id = VarId::new(3602);
    let entry_sc_id = VarId::new(3603);

    let helper_lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("a", helper_a_id),
            Binder::new("sc", helper_sc_id),
        ],
        body: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("sc", helper_sc_id)),
            selector: FieldSelector::ContextField("tx_info".to_string()),
        }),
    };
    // Entry calls helper(sc) — no direct sc.tx_info projection on
    // entry's own params.
    let entry_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("r", entry_r_id), Binder::new("sc", entry_sc_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("helper", VarId::new(3700))),
            args: vec![PseudoExpr::var_with_id("sc", entry_sc_id)].into(),
        }),
    };
    let inner = PseudoExpr::Let {
        name: "entry".to_string(),
        id: Some(VarId::new(3700)),
        value: PBox::new(entry_lambda),
        body: PBox::new(PseudoExpr::Unit),
    };
    let outer = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(3701)),
        value: PBox::new(helper_lambda),
        body: PBox::new(inner),
    };

    let renamed = rename_validator_params(outer, Some(ScriptVersion::PlutusV2));

    let PseudoExpr::Let {
        name: outer_name,
        value: helper_value,
        body: outer_body,
        ..
    } = renamed
    else {
        panic!("expected outer Let")
    };
    assert_eq!(outer_name, "helper");
    let PseudoExpr::Lambda {
        params: helper_params,
        ..
    } = helper_value.into_inner()
    else {
        panic!("expected helper Lambda value")
    };
    // Helper params must NOT be renamed to (redeemer, script_context).
    assert_eq!(
        helper_params[0].as_str(),
        "a",
        "helper's first param must NOT be renamed (regression guard)"
    );
    assert_eq!(
        helper_params[1].as_str(),
        "sc",
        "helper's second param must NOT be renamed (regression guard)"
    );

    let PseudoExpr::Let {
        name: inner_name,
        value: entry_value,
        ..
    } = outer_body.into_inner()
    else {
        panic!("expected inner Let")
    };
    assert_eq!(inner_name, "entry");
    let PseudoExpr::Lambda {
        params: entry_params,
        ..
    } = entry_value.into_inner()
    else {
        panic!("expected entry Lambda value")
    };
    // Entry's params SHOULD be renamed (it's the last arity-matching let).
    assert_eq!(entry_params[0].as_str(), "redeemer");
    assert_eq!(entry_params[1].as_str(), "script_context");
}

#[test]
fn scored_picker_no_sc_evidence_falls_back_to_last() {
    // Neither let has SC evidence; reverse-walk renames the last.
    let a_id = VarId::new(3400);
    let b_id = VarId::new(3401);
    let c_id = VarId::new(3402);
    let d_id = VarId::new(3403);

    let first_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
        body: PBox::new(PseudoExpr::var_with_id("a", a_id)),
    };
    let second_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("c", c_id), Binder::new("d", d_id)],
        body: PBox::new(PseudoExpr::var_with_id("c", c_id)),
    };
    let inner = PseudoExpr::Let {
        name: "second".to_string(),
        id: Some(VarId::new(3500)),
        value: PBox::new(second_lambda),
        body: PBox::new(PseudoExpr::Unit),
    };
    let outer = PseudoExpr::Let {
        name: "first".to_string(),
        id: Some(VarId::new(3501)),
        value: PBox::new(first_lambda),
        body: PBox::new(inner),
    };

    let renamed = rename_validator_params(outer, Some(ScriptVersion::PlutusV2));

    let PseudoExpr::Let {
        body: outer_body,
        value: first_value,
        ..
    } = renamed
    else {
        panic!("expected outer Let")
    };
    let PseudoExpr::Lambda {
        params: first_params,
        ..
    } = first_value.into_inner()
    else {
        panic!("expected first Lambda value")
    };
    // First's params unchanged.
    assert_eq!(first_params[0].as_str(), "a");
    assert_eq!(first_params[1].as_str(), "b");

    let PseudoExpr::Let {
        value: second_value,
        ..
    } = outer_body.into_inner()
    else {
        panic!("expected inner Let")
    };
    let PseudoExpr::Lambda {
        params: second_params,
        ..
    } = second_value.into_inner()
    else {
        panic!("expected second Lambda value")
    };
    // Fallback picks the last.
    assert_eq!(second_params[0].as_str(), "redeemer");
    assert_eq!(second_params[1].as_str(), "script_context");
}

// ──────────────────────────────────────────────────────────────────
// Explicit-purpose disambiguation tests.
//
// An explicit `--purpose` outranks the legacy exact-2/exact-3
// arity arms: `--purpose mint` at arity 3 takes the mint layout,
// not spend. These pin the priority order:
// blueprint > purpose > legacy.
//

use crate::decompile::validator_meta::ValidatorPurpose;

#[test]
fn purpose_mint_arity_three_treats_leading_as_user_param() {
    // V1/V2 arity-3 is ambiguous (could be spend OR mint+1-user). With
    // `--purpose mint`, the user has declared the runtime layout, so
    // the leading slot must stay as a user param (left untouched),
    // not be renamed to `datum`.
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("__user"), binder("__r"), binder("__sc")],
        body: PBox::new(PseudoExpr::var("body")),
    };
    let mut annotations = HashMap::new();

    let renamed = rename_validator_params_with_var_kinds(
        lambda,
        Some(ScriptVersion::PlutusV2),
        &mut annotations,
        None,
        Some(ValidatorPurpose::Mint),
    );

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 3);
            // Leading slot stays at simplifier-chosen name (no rename).
            assert_eq!(params[0].as_str(), "__user");
            assert_eq!(params[1].as_str(), "redeemer");
            assert_eq!(params[2].as_str(), "script_context");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn purpose_spend_arity_two_is_rejected() {
    // V1/V2 arity-2 with `--purpose spend` cannot be a spend
    // validator (spend needs 3 runtime params). The renamer must
    // reject (return unchanged), not silently apply the mint layout.
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("__a"), binder("__b")],
        body: PBox::new(PseudoExpr::var("body")),
    };
    let mut annotations = HashMap::new();

    let renamed = rename_validator_params_with_var_kinds(
        lambda,
        Some(ScriptVersion::PlutusV2),
        &mut annotations,
        None,
        Some(ValidatorPurpose::Spend),
    );

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 2);
            // Both slots stay untouched — no spurious rename.
            assert_eq!(params[0].as_str(), "__a");
            assert_eq!(params[1].as_str(), "__b");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn purpose_mint_arity_four_renames_trailing_runtime_params() {
    // Arity 4 with mint purpose: trailing 2 become `redeemer,
    // script_context`; leading 2 stay as user/compile-time params.
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("__1"), binder("__2"), binder("__3"), binder("__4")],
        body: PBox::new(PseudoExpr::var("body")),
    };
    let mut annotations = HashMap::new();

    let renamed = rename_validator_params_with_var_kinds(
        lambda,
        Some(ScriptVersion::PlutusV2),
        &mut annotations,
        None,
        Some(ValidatorPurpose::Mint),
    );

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 4);
            assert_eq!(params[0].as_str(), "__1");
            assert_eq!(params[1].as_str(), "__2");
            assert_eq!(params[2].as_str(), "redeemer");
            assert_eq!(params[3].as_str(), "script_context");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn purpose_mint_curried_three_deep_uncurries_and_renames_trailing() {
    // A curried V1/V2 chain `λa.λr.λsc.body` (arity 3 once uncurried)
    // with explicit `--purpose mint` is a mint validator with one user
    // param: the purpose widens the candidate arities past the standard
    // `[3, 2]` and sends the arity-3 plan to mint, not spend.
    let a_id = VarId::new(2010);
    let r_id = VarId::new(2011);
    let sc_id = VarId::new(2012);
    let innermost = PseudoExpr::Lambda {
        params: vec![Binder::new("__sc", sc_id)],
        body: PBox::new(PseudoExpr::var_with_id("__sc", sc_id)),
    };
    let mid = PseudoExpr::Lambda {
        params: vec![Binder::new("__r", r_id)],
        body: PBox::new(innermost),
    };
    let outer = PseudoExpr::Lambda {
        params: vec![Binder::new("__a", a_id)],
        body: PBox::new(mid),
    };

    let mut annotations = HashMap::new();
    let renamed = rename_validator_params_with_var_kinds(
        outer,
        Some(ScriptVersion::PlutusV2),
        &mut annotations,
        None,
        Some(ValidatorPurpose::Mint),
    );

    // Uncurried to flat arity-3 Lambda; leading user slot kept,
    // trailing 2 renamed to mint runtime layout.
    match renamed {
        PseudoExpr::Lambda { params, body: _ } => {
            assert_eq!(params.len(), 3);
            assert_eq!(params[0].as_str(), "__a");
            assert_eq!(params[0].var_id(), a_id);
            assert_eq!(params[1].as_str(), "redeemer");
            assert_eq!(params[1].var_id(), r_id);
            assert_eq!(params[2].as_str(), "script_context");
            assert_eq!(params[2].var_id(), sc_id);
        }
        other => panic!("expected uncurried Lambda, got: {other:?}"),
    }
}

#[test]
fn purpose_mint_let_prefix_curried_entry_uncurries_via_selector() {
    // Let-prefix paths (`rename_lambda_inside_matching_let_prefix`)
    // must not call `rename_callable_params` directly, which bypasses
    // the purpose-gated uncurry in `select_validator_callable`. Routed
    // through the selector, a `let entry = λa.λr.λsc.body in entry` shape
    // with `--purpose mint` uncurries inside the let value and
    // gets the trailing mint layout.
    let a_id = VarId::new(3001);
    let r_id = VarId::new(3002);
    let sc_id = VarId::new(3003);
    let entry_id = VarId::new(3004);
    let innermost = PseudoExpr::Lambda {
        params: vec![Binder::new("__sc", sc_id)],
        body: PBox::new(PseudoExpr::var_with_id("__sc", sc_id)),
    };
    let mid = PseudoExpr::Lambda {
        params: vec![Binder::new("__r", r_id)],
        body: PBox::new(innermost),
    };
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("__a", a_id)],
        body: PBox::new(mid),
    };
    let let_expr = PseudoExpr::Let {
        name: "entry".into(),
        id: Some(entry_id),
        value: PBox::new(outer_lambda),
        body: PBox::new(PseudoExpr::var_with_id("entry", entry_id)),
    };

    let mut annotations = HashMap::new();
    let renamed = rename_validator_params_with_var_kinds(
        let_expr,
        Some(ScriptVersion::PlutusV2),
        &mut annotations,
        None,
        Some(ValidatorPurpose::Mint),
    );

    let PseudoExpr::Let {
        value: let_value, ..
    } = renamed
    else {
        panic!("expected outer Let")
    };
    // The value is the (now uncurried + renamed) entry lambda.
    match let_value.into_inner() {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 3);
            assert_eq!(params[0].as_str(), "__a");
            assert_eq!(params[1].as_str(), "redeemer");
            assert_eq!(params[2].as_str(), "script_context");
        }
        other => panic!("expected uncurried Lambda in let value, got: {other:?}"),
    }
}

#[test]
fn purpose_mint_unit_tail_prefix_curried_entry_uncurries_via_selector() {
    // The Unit-tail reverse-prefix path
    // (`rename_lambda_in_last_matching_prefix`) also routes
    // through `select_validator_callable`. Pattern:
    // `let entry = λa.λr.λsc.body in Unit`.
    let a_id = VarId::new(3010);
    let r_id = VarId::new(3011);
    let sc_id = VarId::new(3012);
    let entry_id = VarId::new(3013);
    let innermost = PseudoExpr::Lambda {
        params: vec![Binder::new("__sc", sc_id)],
        body: PBox::new(PseudoExpr::var_with_id("__sc", sc_id)),
    };
    let mid = PseudoExpr::Lambda {
        params: vec![Binder::new("__r", r_id)],
        body: PBox::new(innermost),
    };
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("__a", a_id)],
        body: PBox::new(mid),
    };
    let let_expr = PseudoExpr::Let {
        name: "entry".into(),
        id: Some(entry_id),
        value: PBox::new(outer_lambda),
        body: PBox::new(PseudoExpr::Unit),
    };

    let mut annotations = HashMap::new();
    let renamed = rename_validator_params_with_var_kinds(
        let_expr,
        Some(ScriptVersion::PlutusV2),
        &mut annotations,
        None,
        Some(ValidatorPurpose::Mint),
    );

    let PseudoExpr::Let {
        value: let_value,
        body,
        ..
    } = renamed
    else {
        panic!("expected outer Let")
    };
    assert!(matches!(*body, PseudoExpr::Unit), "tail must remain Unit");
    match let_value.into_inner() {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 3);
            assert_eq!(params[0].as_str(), "__a");
            assert_eq!(params[1].as_str(), "redeemer");
            assert_eq!(params[2].as_str(), "script_context");
        }
        other => panic!("expected uncurried Lambda in let value, got: {other:?}"),
    }
}

#[test]
fn blueprint_wins_when_purpose_conflicts_documenting_current_behavior() {
    // When BOTH blueprint hints (length 1) AND `--purpose mint`
    // are given on an arity-4 V2 entry, blueprint's `hint_len + 3
    // == arity` rule wins: `(user_a, datum, redeemer,
    // script_context)`. `--purpose mint` alone would give
    // `(user_a, user_b, redeemer, script_context)`, but no
    // diagnostic plumbing exists at this layer; this test pins
    // the blueprint-wins behavior.
    let lambda = PseudoExpr::Lambda {
        params: vec![
            binder("user_a"),
            binder("__d"),
            binder("__r"),
            binder("__sc"),
        ],
        body: PBox::new(PseudoExpr::var("body")),
    };
    let names = vec!["user_a".to_string()];
    let mut annotations = HashMap::new();

    let renamed = rename_validator_params_with_var_kinds(
        lambda,
        Some(ScriptVersion::PlutusV2),
        &mut annotations,
        Some(&names),
        Some(ValidatorPurpose::Mint),
    );

    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 4);
            // Blueprint wins: spend layout selected.
            assert_eq!(params[0].as_str(), "user_a");
            assert_eq!(params[1].as_str(), "datum");
            assert_eq!(params[2].as_str(), "redeemer");
            assert_eq!(params[3].as_str(), "script_context");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn purpose_none_preserves_legacy_exact_two_three_behavior() {
    // Without `--purpose`, the legacy heuristic applies:
    // arity 2 → mint layout, arity 3 → spend layout.
    let lambda_three = PseudoExpr::Lambda {
        params: vec![binder("__d"), binder("__r"), binder("__sc")],
        body: PBox::new(PseudoExpr::var("body")),
    };
    let mut annotations = HashMap::new();
    let renamed = rename_validator_params_with_var_kinds(
        lambda_three,
        Some(ScriptVersion::PlutusV2),
        &mut annotations,
        None,
        None,
    );
    match renamed {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params[0].as_str(), "datum");
            assert_eq!(params[1].as_str(), "redeemer");
            assert_eq!(params[2].as_str(), "script_context");
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}
