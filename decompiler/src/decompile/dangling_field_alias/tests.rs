use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

fn binder(name: &str) -> Binder {
    Binder::new(name, VarId::fresh_binding())
}

fn var(name: &str) -> PseudoExpr {
    PseudoExpr::Var {
        name: name.to_string(),
        id: VarId::fresh_compat_placeholder().into(),
    }
}

#[test]
fn inline_dangling_field_aliases_does_not_produce_consistent_ref_ids_from_stale_input() {
    let binding_id = VarId::fresh_binding();
    let stale_ref_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", stale_ref_id)),
    };
    assert!(
        crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr),
        "fixture must start with a stale same-name ref"
    );

    let result = inline_dangling_field_aliases(
        expr,
        ScriptVersion::PlutusV3,
        &std::collections::HashMap::new(),
        false,
    );

    assert!(
        crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "dangling alias repair is not a general ref-id producer"
    );
}

#[test]
fn rewrites_free_field_n_under_script_context() {
    // fn(script_context) { field_2 }
    // expected: fn(script_context) { script_context.tx_info.outputs }
    let body = var("field_2");
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context")],
        body: PBox::new(body),
    };

    let result = inline_dangling_field_aliases(
        expr,
        ScriptVersion::PlutusV3,
        &std::collections::HashMap::new(),
        false,
    );

    let inner = match result {
        PseudoExpr::Lambda { body, .. } => body.into_inner(),
        _ => panic!("expected lambda"),
    };
    match inner {
        PseudoExpr::FieldAccess { record, selector } => {
            assert_eq!(selector.as_pretty_name(), "outputs");
            match record.into_inner() {
                PseudoExpr::FieldAccess {
                    record: anchor,
                    selector: tx_info_sel,
                } => {
                    assert_eq!(tx_info_sel.as_pretty_name(), "tx_info");
                    match anchor.into_inner() {
                        PseudoExpr::Var { name, .. } => assert_eq!(name, "script_context"),
                        other => panic!("expected script_context Var, got {:?}", other),
                    }
                }
                other => panic!("expected nested FieldAccess, got {:?}", other),
            }
        }
        other => panic!("expected FieldAccess, got {:?}", other),
    }
}

#[test]
fn rewrites_free_named_field_under_tx_info_anchor() {
    // fn(tx_info) { inputs }
    // expected: fn(tx_info) { tx_info.inputs }
    let body = var("inputs");
    let expr = PseudoExpr::Lambda {
        params: vec![binder("tx_info")],
        body: PBox::new(body),
    };

    let result = inline_dangling_field_aliases(
        expr,
        ScriptVersion::PlutusV3,
        &std::collections::HashMap::new(),
        false,
    );

    let inner = match result {
        PseudoExpr::Lambda { body, .. } => body.into_inner(),
        _ => panic!("expected lambda"),
    };
    match inner {
        PseudoExpr::FieldAccess { record, selector } => {
            assert_eq!(selector.as_pretty_name(), "inputs");
            match record.into_inner() {
                PseudoExpr::Var { name, .. } => assert_eq!(name, "tx_info"),
                other => panic!("expected tx_info Var, got {:?}", other),
            }
        }
        other => panic!("expected FieldAccess, got {:?}", other),
    }
}

#[test]
fn rewrites_free_named_field_under_compat_tx_info_anchor_preserves_anchor_id() {
    let tx_info_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "tx_info".to_string(),
        id: Some(tx_info_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(var("inputs")),
    };

    let result = inline_dangling_field_aliases(
        expr,
        ScriptVersion::PlutusV3,
        &std::collections::HashMap::new(),
        false,
    );

    let body = match result {
        PseudoExpr::Let { body, .. } => body.into_inner(),
        other => panic!("expected tx_info let, got {:?}", other),
    };
    match body {
        PseudoExpr::FieldAccess { record, selector } => {
            assert_eq!(selector.as_pretty_name(), "inputs");
            match record.into_inner() {
                PseudoExpr::Var { name, id } => {
                    assert_eq!(name, "tx_info");
                    assert_eq!(id, Some(tx_info_id));
                }
                other => panic!("expected tx_info Var, got {:?}", other),
            }
        }
        other => panic!("expected FieldAccess, got {:?}", other),
    }
}

#[test]
fn when_subject_name_anchor_uses_subject_binder_id() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};

    let tx_info = binder("tx_info");
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Unit),
        subject_name: Some(tx_info.clone()),
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: var("inputs"),
        }],
    };

    let result = inline_dangling_field_aliases(
        expr,
        ScriptVersion::PlutusV3,
        &std::collections::HashMap::new(),
        false,
    );

    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "resolver should keep the synthesized anchor ref scope-consistent, got: {result:?}"
    );

    let clause_body = match result {
        PseudoExpr::When { mut clauses, .. } => clauses.remove(0).body,
        other => panic!("expected When, got {:?}", other),
    };
    match clause_body {
        PseudoExpr::FieldAccess { record, selector } => {
            assert_eq!(selector.as_pretty_name(), "inputs");
            match record.into_inner() {
                PseudoExpr::Var { name, id } => {
                    assert_eq!(name, "tx_info");
                    assert_eq!(id, Some(tx_info.var_id()));
                }
                other => panic!("expected tx_info Var, got {:?}", other),
            }
        }
        other => panic!("expected FieldAccess(tx_info, inputs), got {:?}", other),
    }
}

#[test]
fn does_not_rewrite_when_name_is_bound_locally() {
    // fn(script_context) { let outputs = 1 in outputs }
    let body = PseudoExpr::Let {
        name: "outputs".to_string(),
        id: VarId::fresh_binding().into(),
        value: PBox::new(PseudoExpr::Int(1.into())),
        body: PBox::new(var("outputs")),
    };
    let expr = PseudoExpr::Lambda {
        params: vec![binder("script_context")],
        body: PBox::new(body),
    };

    let result = inline_dangling_field_aliases(
        expr,
        ScriptVersion::PlutusV3,
        &std::collections::HashMap::new(),
        false,
    );

    let inner = match result {
        PseudoExpr::Lambda { body, .. } => body.into_inner(),
        _ => panic!("expected lambda"),
    };
    match inner {
        PseudoExpr::Let { body, .. } => match body.into_inner() {
            PseudoExpr::Var { name, .. } => assert_eq!(name, "outputs"),
            other => panic!("expected Var, got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn no_rewrite_without_anchor() {
    // fn(other) { inputs } — no script_context / tx_info anchor in scope.
    let body = var("inputs");
    let expr = PseudoExpr::Lambda {
        params: vec![binder("other")],
        body: PBox::new(body),
    };

    let result = inline_dangling_field_aliases(
        expr,
        ScriptVersion::PlutusV3,
        &std::collections::HashMap::new(),
        false,
    );

    let inner = match result {
        PseudoExpr::Lambda { body, .. } => body.into_inner(),
        _ => panic!("expected lambda"),
    };
    match inner {
        PseudoExpr::Var { name, .. } => assert_eq!(name, "inputs"),
        other => panic!("expected Var, got {:?}", other),
    }
}

/// Constr clause whose pattern was renamed by Cardano-naming
/// (`item_0` → `credential`) while the body still references
/// `item_0`; the repair substitutes the pattern's binder name.
#[test]
fn substitutes_orphan_item_to_renamed_constr_binder() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let credential = binder("credential");
    let pattern = WhenPattern::Constructor {
        type_hint: None,
        tag: 2,
        fields: vec![credential.clone()],
        shape: ConstructorShape::unknown_data(2, 1),
    };
    let body = var("item_0");

    let when_expr = PseudoExpr::When {
        subject: PBox::new(var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern,
            guard: None,
            body,
        }],
    };

    let result =
        repair_dangling_constr_payload_binders(when_expr, &std::collections::HashMap::new(), false);

    let clause_body = match result {
        PseudoExpr::When { mut clauses, .. } => clauses.remove(0).body,
        _ => panic!("expected When"),
    };
    match clause_body {
        PseudoExpr::Var { name, .. } => assert_eq!(name, "credential"),
        other => panic!("expected Var(credential), got {:?}", other),
    }
}

#[test]
fn recovers_orphan_under_same_name_different_id_outer_binding() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let outer_item0_id = VarId::fresh_binding();
    let orphan_item0_id = VarId::fresh_compat_placeholder();
    let credential = binder("credential");

    let when_expr = PseudoExpr::When {
        subject: PBox::new(var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 2,
                fields: vec![credential.clone()],
                shape: ConstructorShape::unknown_data(2, 1),
            },
            guard: None,
            body: PseudoExpr::Var {
                name: "item_0".to_string(),
                id: Some(orphan_item0_id),
            },
        }],
    };
    let expr = PseudoExpr::Let {
        name: "item_0".to_string(),
        id: Some(outer_item0_id),
        value: PBox::new(PseudoExpr::Int(0.into())),
        body: PBox::new(when_expr),
    };

    let result =
        repair_dangling_constr_payload_binders(expr, &std::collections::HashMap::new(), false);

    let clause_body = match result {
        PseudoExpr::Let { body, .. } => match body.into_inner() {
            PseudoExpr::When { mut clauses, .. } => clauses.remove(0).body,
            other => panic!("expected when under outer let, got {:?}", other),
        },
        other => panic!("expected outer let, got {:?}", other),
    };
    assert!(
        matches!(
            clause_body,
            PseudoExpr::Var { name, id }
                if name == "credential" && id == Some(credential.var_id())
        ),
        "expected repair to follow the orphan ref id instead of the outer same-name binding"
    );
}

#[test]
fn single_orphan_rewrite_preserves_existing_same_name_outer_ref_id() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let outer_credential_id = VarId::fresh_binding();
    let credential = binder("credential");

    let when_expr = PseudoExpr::When {
        subject: PBox::new(var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 2,
                fields: vec![credential.clone()],
                shape: ConstructorShape::unknown_data(2, 1),
            },
            guard: None,
            body: PseudoExpr::Tuple(
                vec![
                    var("item_0"),
                    PseudoExpr::Var {
                        name: "credential".to_string(),
                        id: Some(outer_credential_id),
                    },
                ]
                .into(),
            ),
        }],
    };
    let expr = PseudoExpr::Let {
        name: "credential".to_string(),
        id: Some(outer_credential_id),
        value: PBox::new(PseudoExpr::Int(0.into())),
        body: PBox::new(when_expr),
    };

    let result =
        repair_dangling_constr_payload_binders(expr, &std::collections::HashMap::new(), false);

    let clause_body = match result {
        PseudoExpr::Let { body, .. } => match body.into_inner() {
            PseudoExpr::When { mut clauses, .. } => clauses.remove(0).body,
            other => panic!("expected when under outer let, got {:?}", other),
        },
        other => panic!("expected outer let, got {:?}", other),
    };
    match clause_body {
        PseudoExpr::Tuple(items) => {
            assert!(
                matches!(
                    &items[0],
                    PseudoExpr::Var { name, id }
                        if name == "credential" && *id == Some(credential.var_id())
                ),
                "expected orphan rewrite to adopt the pattern binder identity"
            );
            assert!(
                matches!(
                    &items[1],
                    PseudoExpr::Var { name, id }
                        if name == "credential" && *id == Some(outer_credential_id)
                ),
                "expected pre-existing outer credential ref to keep its original id"
            );
        }
        other => panic!("expected tuple body, got {:?}", other),
    }
}

#[test]
fn orphan_rewrite_avoids_capture_under_same_name_lambda_param() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let orphan_id = VarId::fresh_compat_placeholder();
    let credential = binder("credential");
    let inner_credential = binder("credential");

    let when_expr = PseudoExpr::When {
        subject: PBox::new(var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 2,
                fields: vec![credential],
                shape: ConstructorShape::unknown_data(2, 1),
            },
            guard: None,
            body: PseudoExpr::Lambda {
                params: vec![inner_credential.clone()],
                body: PBox::new(PseudoExpr::Var {
                    name: "item_0".to_string(),
                    id: Some(orphan_id),
                }),
            },
        }],
    };

    let result =
        repair_dangling_constr_payload_binders(when_expr, &std::collections::HashMap::new(), false);

    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "repair should not rewrite an orphan under a same-name capture scope, got: {result:?}"
    );

    let clause_body = match result {
        PseudoExpr::When { mut clauses, .. } => clauses.remove(0).body,
        other => panic!("expected When, got {:?}", other),
    };
    let PseudoExpr::Lambda { params, body } = clause_body else {
        panic!("expected lambda body, got {:?}", clause_body);
    };
    assert_eq!(params[0].var_id(), inner_credential.var_id());
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Var { name, id } if name == "item_0" && *id == Some(orphan_id)
        ),
        "expected orphan ref to stay untouched inside capture scope, got: {body:?}"
    );
}

#[test]
fn does_not_merge_ambiguous_same_name_different_id_orphan_refs() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let left_id = VarId::fresh_compat_placeholder();
    let right_id = VarId::fresh_compat_placeholder();
    let credential = binder("credential");

    let when_expr = PseudoExpr::When {
        subject: PBox::new(var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 2,
                fields: vec![credential],
                shape: ConstructorShape::unknown_data(2, 1),
            },
            guard: None,
            body: PseudoExpr::Tuple(
                vec![
                    PseudoExpr::Var {
                        name: "item_0".to_string(),
                        id: Some(left_id),
                    },
                    PseudoExpr::Var {
                        name: "item_0".to_string(),
                        id: Some(right_id),
                    },
                ]
                .into(),
            ),
        }],
    };

    let result =
        repair_dangling_constr_payload_binders(when_expr, &std::collections::HashMap::new(), false);

    let clause_body = match result {
        PseudoExpr::When { mut clauses, .. } => clauses.remove(0).body,
        other => panic!("expected When, got {:?}", other),
    };
    match clause_body {
        PseudoExpr::Tuple(items) => {
            assert!(
                matches!(
                    &items[0],
                    PseudoExpr::Var { name, id } if name == "item_0" && *id == Some(left_id)
                ),
                "expected ambiguous left orphan ref to stay untouched"
            );
            assert!(
                matches!(
                    &items[1],
                    PseudoExpr::Var { name, id } if name == "item_0" && *id == Some(right_id)
                ),
                "expected ambiguous right orphan ref to stay untouched"
            );
        }
        other => panic!("expected tuple body, got {:?}", other),
    }
}

#[test]
fn multi_orphan_constructor_rewrite_uses_pattern_binder_ids() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let first = binder("credential");
    let second = binder("datum");
    let pattern = WhenPattern::Constructor {
        type_hint: None,
        tag: 2,
        fields: vec![first.clone(), second.clone()],
        shape: ConstructorShape::unknown_data(2, 2),
    };
    let body = PseudoExpr::Tuple((vec![var("item_0"), var("field_1")]).into());

    let when_expr = PseudoExpr::When {
        subject: PBox::new(var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern,
            guard: None,
            body,
        }],
    };

    let result =
        repair_dangling_constr_payload_binders(when_expr, &std::collections::HashMap::new(), false);

    let clause_body = match result {
        PseudoExpr::When { mut clauses, .. } => clauses.remove(0).body,
        other => panic!("expected When, got {:?}", other),
    };
    match clause_body {
        PseudoExpr::Tuple(items) => {
            assert!(
                matches!(
                    &items[0],
                    PseudoExpr::Var { name, id }
                        if name == "credential" && *id == Some(first.var_id())
                ),
                "expected item_0 rewrite to adopt the first pattern binder id"
            );
            assert!(
                matches!(
                    &items[1],
                    PseudoExpr::Var { name, id }
                        if name == "datum" && *id == Some(second.var_id())
                ),
                "expected field_1 rewrite to adopt the second pattern binder id"
            );
        }
        other => panic!("expected tuple body, got {:?}", other),
    }
}

/// Bare `Constr<N>` with no payload binder but a body reference
/// to a free `t1_1`; the repair re-introduces `t1_1` as the binder.
#[test]
fn introduces_binder_from_orphan_when_pattern_is_bare() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let pattern = WhenPattern::Constructor {
        type_hint: None,
        tag: 1,
        fields: vec![],
        shape: ConstructorShape::unknown_data(1, 0),
    };
    let body = var("t1_1");

    let when_expr = PseudoExpr::When {
        subject: PBox::new(var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern,
            guard: None,
            body,
        }],
    };

    let result =
        repair_dangling_constr_payload_binders(when_expr, &std::collections::HashMap::new(), false);

    let clause = match result {
        PseudoExpr::When { mut clauses, .. } => clauses.remove(0),
        _ => panic!("expected When"),
    };
    match clause.pattern {
        WhenPattern::Constructor { fields, .. } => {
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].as_str(), "t1_1");
        }
        other => panic!("expected Constructor, got {:?}", other),
    }
}

#[test]
fn list_pattern_rewrite_uses_target_binder_id() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};

    let head = binder("head");
    let when_expr = PseudoExpr::When {
        subject: PBox::new(var("subject")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::List {
                elements: vec![head.clone()],
                tail: None,
            },
            guard: None,
            body: var("item_0"),
        }],
    };

    let result =
        repair_dangling_constr_payload_binders(when_expr, &std::collections::HashMap::new(), false);

    let clause_body = match result {
        PseudoExpr::When { mut clauses, .. } => clauses.remove(0).body,
        other => panic!("expected When, got {:?}", other),
    };
    match clause_body {
        PseudoExpr::Var { name, id } => {
            assert_eq!(name, "head");
            assert_eq!(id, Some(head.var_id()));
        }
        other => panic!("expected Var(head), got {:?}", other),
    }
}

/// A synthetic `field_N` used as a `when` subject must resolve
/// against the SCRIPT_CONTEXT schema, not unconditionally tx_info.
/// Otherwise a free `field_1` (= redeemer in V3) maps to
/// `tx_info.fields[1]` (= reference_inputs), producing the invalid
/// field chain `script_context.tx_info.reference_inputs`.
#[test]
fn field_alias_used_as_when_subject_resolves_to_script_context() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    // fn(script_context) {
    //   when field_1 is { Constr<2>(_) -> Unit; _ -> fail }
    // }
    let when_expr = PseudoExpr::When {
        subject: PBox::new(var("field_1")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 2,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(2, 0),
                },
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
        ],
    };
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("script_context")],
        body: PBox::new(when_expr),
    };

    let result = inline_dangling_field_aliases(
        lambda,
        ScriptVersion::PlutusV3,
        &std::collections::HashMap::new(),
        false,
    );

    let when_in_lambda = match result {
        PseudoExpr::Lambda { body, .. } => body.into_inner(),
        _ => panic!("expected lambda"),
    };
    let subject = match when_in_lambda {
        PseudoExpr::When { subject, .. } => subject.into_inner(),
        _ => panic!("expected when"),
    };
    // Expected: `script_context.redeemer` — NOT
    // `script_context.tx_info.reference_inputs`.
    match subject {
        PseudoExpr::FieldAccess { record, selector } => {
            assert_eq!(selector.as_pretty_name(), "redeemer");
            match record.into_inner() {
                PseudoExpr::Var { name, .. } => assert_eq!(name, "script_context"),
                other => panic!("expected Var(script_context), got {:?}", other),
            }
        }
        other => panic!(
            "expected FieldAccess(script_context, redeemer), got {:?}",
            other
        ),
    }
}

/// A synthetic `field_N` outside When-subject position (here a
/// `Data.un_map(field_4)` argument) resolves against the TX_INFO
/// schema instead.
#[test]
fn field_alias_used_as_extractor_arg_still_resolves_to_tx_info() {
    // fn(script_context) { Data.un_map(field_4) }
    let body = PseudoExpr::BuiltinCall {
        name: "Data.un_map".to_string().into(),
        args: vec![var("field_4")].into(),
    };
    let lambda = PseudoExpr::Lambda {
        params: vec![binder("script_context")],
        body: PBox::new(body),
    };

    let result = inline_dangling_field_aliases(
        lambda,
        ScriptVersion::PlutusV3,
        &std::collections::HashMap::new(),
        false,
    );

    let body_after = match result {
        PseudoExpr::Lambda { body, .. } => body.into_inner(),
        _ => panic!("expected lambda"),
    };
    let arg = match body_after {
        PseudoExpr::BuiltinCall { mut args, .. } => args.remove(0),
        other => panic!("expected BuiltinCall, got {:?}", other),
    };
    // Expected: script_context.tx_info.mint
    match arg {
        PseudoExpr::FieldAccess { record, selector } => {
            assert_eq!(selector.as_pretty_name(), "mint");
            match record.into_inner() {
                PseudoExpr::FieldAccess {
                    record: anchor,
                    selector: tx_info_sel,
                } => {
                    assert_eq!(tx_info_sel.as_pretty_name(), "tx_info");
                    match anchor.into_inner() {
                        PseudoExpr::Var { name, .. } => assert_eq!(name, "script_context"),
                        other => panic!("expected script_context Var, got {:?}", other),
                    }
                }
                other => panic!("expected nested FieldAccess, got {:?}", other),
            }
        }
        other => panic!("expected FieldAccess, got {:?}", other),
    }
}
