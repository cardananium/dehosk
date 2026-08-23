use super::*;

fn list_tail(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![].into(),
        }),
        args: vec![arg].into(),
    }
}

#[test]
fn sync_late_slice_tail_kind_annotations_records_final_tail_lets() {
    let source_id = VarId::new(46_001);
    let tail_id = VarId::new(46_002);
    let expr = PseudoExpr::Let {
        name: "tail".to_string(),
        id: Some(tail_id),
        value: PBox::new(list_tail(PseudoExpr::var_with_id("items", source_id))),
        body: PBox::new(PseudoExpr::var_with_id("tail", tail_id)),
    };
    let mut annotations = HashMap::new();

    sync_late_slice_tail_kind_annotations(&expr, &mut annotations);

    assert!(
        matches!(
            annotations.get(&tail_id),
            Some(VarKind::SliceTailAlias { parent, depth })
                if *parent == source_id && *depth == 1
        ),
        "expected late SliceTailAlias annotation, got: {annotations:?}"
    );
}

#[test]
fn sync_late_slice_tail_kind_annotations_propagates_final_alias_lets() {
    let source_id = VarId::new(46_011);
    let tail_id = VarId::new(46_012);
    let alias_id = VarId::new(46_013);
    let expr = PseudoExpr::Let {
        name: "tail".to_string(),
        id: Some(tail_id),
        value: PBox::new(list_tail(PseudoExpr::var_with_id("items", source_id))),
        body: PBox::new(PseudoExpr::Let {
            name: "tail_alias".to_string(),
            id: Some(alias_id),
            value: PBox::new(PseudoExpr::var_with_id("tail", tail_id)),
            body: PBox::new(PseudoExpr::var_with_id("tail_alias", alias_id)),
        }),
    };
    let mut annotations = HashMap::new();

    sync_late_slice_tail_kind_annotations(&expr, &mut annotations);

    assert!(
        matches!(
            annotations.get(&alias_id),
            Some(VarKind::SliceTailAlias { parent, depth })
                if *parent == source_id && *depth == 1
        ),
        "expected propagated SliceTailAlias annotation, got: {annotations:?}"
    );
}

#[test]
fn sync_late_slice_tail_kind_annotations_accumulates_existing_alias_depth() {
    let source_id = VarId::new(46_021);
    let alias_id = VarId::new(46_022);
    let next_id = VarId::new(46_023);
    let expr = PseudoExpr::Let {
        name: "next_tail".to_string(),
        id: Some(next_id),
        value: PBox::new(list_tail(PseudoExpr::var_with_id("tail_alias", alias_id))),
        body: PBox::new(PseudoExpr::var_with_id("next_tail", next_id)),
    };
    let mut annotations = HashMap::from([(
        alias_id,
        VarKind::SliceTailAlias {
            parent: source_id,
            depth: 2,
        },
    )]);

    sync_late_slice_tail_kind_annotations(&expr, &mut annotations);

    assert!(
        matches!(
            annotations.get(&next_id),
            Some(VarKind::SliceTailAlias { parent, depth })
                if *parent == source_id && *depth == 3
        ),
        "expected accumulated SliceTailAlias annotation, got: {annotations:?}"
    );
}

#[test]
fn sync_late_slice_tail_kind_annotations_preserves_existing_annotations() {
    let source_id = VarId::new(46_031);
    let tail_id = VarId::new(46_032);
    let expr = PseudoExpr::Let {
        name: "tail".to_string(),
        id: Some(tail_id),
        value: PBox::new(list_tail(PseudoExpr::var_with_id("items", source_id))),
        body: PBox::new(PseudoExpr::var_with_id("tail", tail_id)),
    };
    let mut annotations = HashMap::from([(tail_id, VarKind::DataLiteralHoist)]);

    sync_late_slice_tail_kind_annotations(&expr, &mut annotations);

    assert!(
        matches!(annotations.get(&tail_id), Some(VarKind::DataLiteralHoist)),
        "late sync must not replace existing mint-site annotations: {annotations:?}"
    );
}

#[test]
fn sync_late_call_result_kind_annotations_records_final_result_lets() {
    let result_id = VarId::new(47_001);
    let callee_id = VarId::new(47_002);
    let arg_id = VarId::new(47_003);
    let expr = PseudoExpr::Let {
        name: "contains_result".to_string(),
        id: Some(result_id),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("contains", callee_id)),
            args: vec![PseudoExpr::var_with_id("input", arg_id)].into(),
        }),
        body: PBox::new(PseudoExpr::var_with_id("contains_result", result_id)),
    };
    let mut annotations = HashMap::new();

    sync_late_call_result_kind_annotations(&expr, &mut annotations);

    assert!(
        matches!(
            annotations.get(&result_id),
            Some(VarKind::CallResult { callee }) if *callee == callee_id
        ),
        "expected late CallResult annotation, got: {annotations:?}"
    );
}

#[test]
fn sync_late_call_result_kind_annotations_preserves_existing_annotations() {
    let result_id = VarId::new(47_011);
    let callee_id = VarId::new(47_012);
    let arg_id = VarId::new(47_013);
    let expr = PseudoExpr::Let {
        name: "contains_result".to_string(),
        id: Some(result_id),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("contains", callee_id)),
            args: vec![PseudoExpr::var_with_id("input", arg_id)].into(),
        }),
        body: PBox::new(PseudoExpr::var_with_id("contains_result", result_id)),
    };
    let mut annotations = HashMap::from([(result_id, VarKind::DataLiteralHoist)]);

    sync_late_call_result_kind_annotations(&expr, &mut annotations);

    assert!(
        matches!(annotations.get(&result_id), Some(VarKind::DataLiteralHoist)),
        "late sync must not replace existing mint-site annotations: {annotations:?}"
    );
}

#[test]
fn sync_late_constr_payload_kind_annotations_records_constructor_pattern_binders() {
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let subject_id = VarId::new(48_001);
    let payload_id = VarId::new(48_002);
    let other_id = VarId::new(48_003);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(
                ConstructorShape::unknown_data(0, 2),
                vec![
                    Binder::new("payload", payload_id),
                    Binder::new("other", other_id),
                ],
            ),
            PseudoExpr::var_with_id("payload", payload_id),
        )],
    };
    let mut annotations = HashMap::new();

    sync_late_constr_payload_kind_annotations(&expr, &mut annotations);

    assert!(
        matches!(
            annotations.get(&payload_id),
            Some(VarKind::ConstrPayload { index: 0, .. })
        ),
        "expected ConstrPayload at index 0 for first field binder, got: {annotations:?}"
    );
    assert!(
        matches!(
            annotations.get(&other_id),
            Some(VarKind::ConstrPayload { index: 1, .. })
        ),
        "expected ConstrPayload at index 1 for second field binder, got: {annotations:?}"
    );
}

#[test]
fn sync_late_constr_payload_kind_annotations_preserves_existing_annotations() {
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let subject_id = VarId::new(48_011);
    let payload_id = VarId::new(48_012);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(
                ConstructorShape::unknown_data(0, 1),
                vec![Binder::new("payload", payload_id)],
            ),
            PseudoExpr::var_with_id("payload", payload_id),
        )],
    };
    let mut annotations = HashMap::from([(
        payload_id,
        VarKind::CardanoContext {
            context_type: "redeemer".to_string(),
        },
    )]);

    sync_late_constr_payload_kind_annotations(&expr, &mut annotations);

    assert!(
        matches!(
            annotations.get(&payload_id),
            Some(VarKind::CardanoContext { context_type }) if context_type == "redeemer"
        ),
        "late sync must not overwrite existing mint-site annotations (e.g., CardanoContext): {annotations:?}"
    );
}

// ---- promote_let_bound_entry ----
//
// The fallback wrap-validator-entry path descends the top-level Let
// chain through `Let.body` only: a `script_context` param nested in
// `Let.value`, `Lambda.body`, or `RecFn.body` belongs to a helper,
// not to the validator entry.

fn entry_shaped_lambda_with_context_param() -> (VarId, PseudoExpr) {
    let sc_id = VarId::new(70_001);
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("redeemer", VarId::new(70_002)),
            Binder::new("script_context", sc_id),
        ],
        body: PBox::new(PseudoExpr::Unit),
    };
    (sc_id, lambda)
}

#[test]
fn promote_let_bound_entry_finds_top_level_let_chain_entry() {
    let helper_id = VarId::new(70_100);
    let entry_let_id = VarId::new(70_101);
    let (_sc_id, entry_lambda) = entry_shaped_lambda_with_context_param();

    // let helper_fn = (some Lambda without script_context) in
    //   let _entry_helper_name = entry_lambda in
    //     Unit
    let helper_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", VarId::new(70_102))],
        body: PBox::new(PseudoExpr::var("x")),
    };
    let inner = PseudoExpr::Let {
        name: "entry_helper_name".to_string(),
        id: Some(entry_let_id),
        value: PBox::new(entry_lambda),
        body: PBox::new(PseudoExpr::Unit),
    };
    let outer = PseudoExpr::Let {
        name: "helper_fn".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(inner),
    };

    let mut kinds: HashMap<VarId, VarKind> = HashMap::new();
    let result = super::wrap_validator_entry_for_render(outer, &mut kinds);

    // The top-level let chain's second binder was promoted to
    // `decompiled` and tagged ValidatorEntry.
    let PseudoExpr::Let {
        name: outer_name,
        body,
        ..
    } = result
    else {
        panic!("expected outer Let")
    };
    assert_eq!(outer_name, "helper_fn");
    let PseudoExpr::Let {
        name: inner_name,
        id: inner_id,
        ..
    } = body.into_inner()
    else {
        panic!("expected inner Let")
    };
    assert_eq!(inner_name, "decompiled");
    let inner_id = inner_id.expect("inner let must keep an id");
    assert!(
        matches!(kinds.get(&inner_id), Some(VarKind::ValidatorEntry)),
        "kinds: {kinds:?}"
    );
}

#[test]
fn promote_let_bound_entry_does_not_recurse_into_lambda_body() {
    // let h = Lambda(_, Lambda(redeemer, script_context, _)) in Unit
    // The nested Lambda's `script_context` param lives inside a
    // helper's body, not in its own params. Must NOT be promoted.
    let h_id = VarId::new(70_200);
    let outer_param_id = VarId::new(70_201);
    let red_id = VarId::new(70_202);
    let sc_id = VarId::new(70_203);
    let inner_lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("redeemer", red_id),
            Binder::new("script_context", sc_id),
        ],
        body: PBox::new(PseudoExpr::Unit),
    };
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", outer_param_id)],
        body: PBox::new(inner_lambda),
    };
    let expr = PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(h_id),
        value: PBox::new(outer_lambda),
        body: PBox::new(PseudoExpr::Unit),
    };

    let mut kinds: HashMap<VarId, VarKind> = HashMap::new();
    let result = super::wrap_validator_entry_for_render(expr, &mut kinds);

    let PseudoExpr::Let { name, .. } = result else {
        panic!("expected Let")
    };
    // Binder stays as "h" (untouched), no ValidatorEntry tag minted.
    assert_eq!(name, "h");
    assert!(kinds.is_empty(), "kinds: {kinds:?}");
}

#[test]
fn promote_let_bound_entry_does_not_recurse_into_let_value() {
    // let h = (let inner = Lambda(redeemer, script_context, _) in inner)
    // The Lambda is INSIDE another let's value. Must NOT be promoted.
    let h_id = VarId::new(70_300);
    let inner_id = VarId::new(70_301);
    let (_sc_id, entry_lambda) = entry_shaped_lambda_with_context_param();
    let inner_let = PseudoExpr::Let {
        name: "inner".to_string(),
        id: Some(inner_id),
        value: PBox::new(entry_lambda),
        body: PBox::new(PseudoExpr::var_with_id("inner", inner_id)),
    };
    let expr = PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(h_id),
        value: PBox::new(inner_let),
        body: PBox::new(PseudoExpr::Unit),
    };

    let mut kinds: HashMap<VarId, VarKind> = HashMap::new();
    let result = super::wrap_validator_entry_for_render(expr, &mut kinds);

    let PseudoExpr::Let { name, .. } = result else {
        panic!("expected Let")
    };
    assert_eq!(name, "h", "must not promote let inside another let's value");
    assert!(kinds.is_empty(), "kinds: {kinds:?}");
}

#[test]
fn promote_let_bound_entry_does_not_recurse_into_recfn_body() {
    // rec fn r(x) { let inner = Lambda(redeemer, script_context, _) in
    //                 inner }
    // RecFn body contains an entry-shaped let. Must NOT be promoted.
    let r_id = VarId::new(70_400);
    let x_id = VarId::new(70_401);
    let inner_let_id = VarId::new(70_402);
    let (_sc_id, entry_lambda) = entry_shaped_lambda_with_context_param();
    let inner_let = PseudoExpr::Let {
        name: "inner".to_string(),
        id: Some(inner_let_id),
        value: PBox::new(entry_lambda),
        body: PBox::new(PseudoExpr::var_with_id("inner", inner_let_id)),
    };
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("r", r_id),
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(inner_let),
    };

    let mut kinds: HashMap<VarId, VarKind> = HashMap::new();
    let result = super::wrap_validator_entry_for_render(rec_fn, &mut kinds);

    // Result is a RecFn (not a Let), so no promotion happened.
    assert!(matches!(result, PseudoExpr::RecFn { .. }));
    assert!(kinds.is_empty(), "kinds: {kinds:?}");
}

#[test]
fn test_catch_internal_stage_panic_converts_string_panic_to_internal_error() {
    let err = catch_internal_stage_panic("synthetic_stage", || -> PseudoExpr {
        panic!("boom from stage");
    })
    .expect_err("expected panic to convert into an internal error");

    assert!(matches!(
        err,
        DecompileError::Internal(message)
            if message.contains("synthetic_stage") && message.contains("boom from stage")
    ));
}
