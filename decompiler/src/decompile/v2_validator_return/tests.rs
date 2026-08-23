use super::*;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;

/// Build (Let-wrapped validator entry, kind_annotations) pair where the
/// outer Let's binder is tagged with `VarKind::ValidatorEntry`. Mirrors
/// what `wrap_validator_entry_for_render` produces.
fn make_validator_let(body: PseudoExpr) -> (PseudoExpr, HashMap<VarId, VarKind>) {
    let validator_id = VarId::fresh_binding();
    let mut kinds = HashMap::new();
    kinds.insert(validator_id, VarKind::ValidatorEntry);
    // Name is irrelevant; `VarKind::ValidatorEntry` marks the entry.
    let expr = PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(validator_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["script_context".into()],
            body: PBox::new(body),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };
    (expr, kinds)
}

#[test]
fn v2_rewrites_top_level_tail_unit_to_true() {
    let (expr, kinds) = make_validator_let(PseudoExpr::Unit);
    let result = lower_v2_tail_unit_to_true(expr, Some(ScriptVersion::PlutusV2), &kinds);
    match result {
        PseudoExpr::Let { value, .. } => match value.into_inner() {
            PseudoExpr::Lambda { body, .. } => {
                assert_eq!(*body, PseudoExpr::Bool(true));
            }
            _ => panic!("expected Lambda in value"),
        },
        _ => panic!("expected Let"),
    }
}

#[test]
fn v2_rewrites_if_then_unit_to_true() {
    // V2 spend body: `if cond { Void } else { expect rest }` → `if cond { True } else { ... }`.
    let body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::Unit),
        else_branch: PBox::new(PseudoExpr::var("rest")),
    };
    let (expr, kinds) = make_validator_let(body);
    let result = lower_v2_tail_unit_to_true(expr, Some(ScriptVersion::PlutusV2), &kinds);
    let lambda_body = match result {
        PseudoExpr::Let { value, .. } => match value.into_inner() {
            PseudoExpr::Lambda { body, .. } => body.into_inner(),
            _ => panic!(),
        },
        _ => panic!(),
    };
    match lambda_body {
        PseudoExpr::If {
            then_branch,
            else_branch,
            ..
        } => {
            assert_eq!(*then_branch, PseudoExpr::Bool(true));
            assert_eq!(*else_branch, PseudoExpr::var("rest"));
        }
        other => panic!("expected If, got {other:?}"),
    }
}

#[test]
fn v2_rewrites_when_clause_body_unit_to_true() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Literal(PseudoExpr::int(0)),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Bool(false),
            },
        ],
    };
    let (expr, kinds) = make_validator_let(body);
    let result = lower_v2_tail_unit_to_true(expr, Some(ScriptVersion::PlutusV2), &kinds);
    let lambda_body = match result {
        PseudoExpr::Let { value, .. } => match value.into_inner() {
            PseudoExpr::Lambda { body, .. } => body.into_inner(),
            _ => panic!(),
        },
        _ => panic!(),
    };
    match lambda_body {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses[0].body, PseudoExpr::Bool(true));
            assert_eq!(clauses[1].body, PseudoExpr::Bool(false));
        }
        other => panic!("expected When, got {other:?}"),
    }
}

#[test]
fn v3_leaves_tail_unit_alone() {
    // V3 spend body intentionally returns Unit/Void.
    let (expr, kinds) = make_validator_let(PseudoExpr::Unit);
    let result = lower_v2_tail_unit_to_true(expr.clone(), Some(ScriptVersion::PlutusV3), &kinds);
    assert_eq!(result, expr, "V3 must not rewrite Void to True");
}

#[test]
fn none_script_version_leaves_alone() {
    let (expr, kinds) = make_validator_let(PseudoExpr::Unit);
    let result = lower_v2_tail_unit_to_true(expr.clone(), None, &kinds);
    assert_eq!(result, expr);
}

#[test]
fn v2_does_not_touch_argument_position_unit() {
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![PseudoExpr::Unit].into(),
    };
    let (expr, kinds) = make_validator_let(body);
    let result = lower_v2_tail_unit_to_true(expr.clone(), Some(ScriptVersion::PlutusV2), &kinds);
    assert_eq!(result, expr, "argument-position Unit must be preserved");
}

#[test]
fn v2_does_not_touch_nested_lambda_body_unit() {
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("each")),
        args: vec![PseudoExpr::Lambda {
            params: vec!["x".into()],
            body: PBox::new(PseudoExpr::Unit),
        }]
        .into(),
    };
    let (expr, kinds) = make_validator_let(body);
    let result = lower_v2_tail_unit_to_true(expr.clone(), Some(ScriptVersion::PlutusV2), &kinds);
    assert_eq!(result, expr, "nested lambda's body Unit must be preserved");
}

#[test]
fn v2_rewrites_unit_through_let_chain_in_body() {
    let body = PseudoExpr::let_bind(
        "x",
        PseudoExpr::var("e1"),
        PseudoExpr::let_bind("y", PseudoExpr::var("e2"), PseudoExpr::Unit),
    );
    let (expr, kinds) = make_validator_let(body);
    let result = lower_v2_tail_unit_to_true(expr, Some(ScriptVersion::PlutusV2), &kinds);
    let inner_body = match result {
        PseudoExpr::Let { value, .. } => match value.into_inner() {
            PseudoExpr::Lambda { body, .. } => body.into_inner(),
            _ => panic!(),
        },
        _ => panic!(),
    };
    match inner_body {
        PseudoExpr::Let { body: b1, .. } => match b1.into_inner() {
            PseudoExpr::Let { body: b2, .. } => {
                assert_eq!(*b2, PseudoExpr::Bool(true));
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
}

#[test]
fn v1_also_rewrites() {
    let (expr, kinds) = make_validator_let(PseudoExpr::Unit);
    let result = lower_v2_tail_unit_to_true(expr, Some(ScriptVersion::PlutusV1), &kinds);
    match result {
        PseudoExpr::Let { value, .. } => match value.into_inner() {
            PseudoExpr::Lambda { body, .. } => {
                assert_eq!(*body, PseudoExpr::Bool(true));
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
}

#[test]
fn missing_validator_marker_is_a_noop() {
    let expr = PseudoExpr::Unit;
    let result =
        lower_v2_tail_unit_to_true(expr.clone(), Some(ScriptVersion::PlutusV2), &HashMap::new());
    assert_eq!(result, expr);
}

#[test]
fn v2_rewrites_trace_value_in_tail() {
    // `trace msg val` returns `val`; Trace.value is in tail position.
    let body = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::string("debug")),
        value: PBox::new(PseudoExpr::Unit),
    };
    let (expr, kinds) = make_validator_let(body);
    let result = lower_v2_tail_unit_to_true(expr, Some(ScriptVersion::PlutusV2), &kinds);
    let lambda_body = match result {
        PseudoExpr::Let { value, .. } => match value.into_inner() {
            PseudoExpr::Lambda { body, .. } => body.into_inner(),
            _ => panic!(),
        },
        _ => panic!(),
    };
    match lambda_body {
        PseudoExpr::Trace { value, .. } => {
            assert_eq!(*value, PseudoExpr::Bool(true));
        }
        other => panic!("expected Trace, got {other:?}"),
    }
}

#[test]
fn other_top_level_let_without_validator_kind_is_untouched() {
    // A non-validator Let at the top level must not have its Lambda body rewritten.
    let mut kinds = HashMap::new();
    let helper_id = VarId::fresh_binding();
    kinds.insert(helper_id, VarKind::User);
    let expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".into()],
            body: PBox::new(PseudoExpr::Unit),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };
    let result = lower_v2_tail_unit_to_true(expr.clone(), Some(ScriptVersion::PlutusV2), &kinds);
    assert_eq!(result, expr, "non-validator Let must not be rewritten");
}

#[test]
fn v2_rewrites_trailing_identity_lambda_in_validator_tail() {
    // Validator-entry Lambda whose body's tail is `fn(x) { x }` —
    // the V1/V2 "junk return" pattern. Must rewrite to Bool(true).
    let validator_id = VarId::fresh_binding();
    let mut kinds = HashMap::new();
    kinds.insert(validator_id, VarKind::ValidatorEntry);
    let x_id = VarId::fresh_binding();
    let identity_lambda = PseudoExpr::Lambda {
        params: vec![crate::pseudo::ast::Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    let validator_body = PseudoExpr::Lambda {
        params: vec![crate::pseudo::ast::Binder::new(
            "datum",
            VarId::fresh_binding(),
        )],
        body: PBox::new(identity_lambda),
    };
    let expr = PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(validator_id),
        value: PBox::new(validator_body),
        body: PBox::new(PseudoExpr::Unit),
    };
    let result = lower_v2_tail_unit_to_true(expr, Some(ScriptVersion::PlutusV1), &kinds);
    let PseudoExpr::Let { value, .. } = result else {
        panic!()
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!()
    };
    assert!(
        matches!(*body, PseudoExpr::Bool(true)),
        "trailing identity Lambda must be rewritten to Bool(true), got {:?}",
        body
    );
}

#[test]
fn v2_walks_through_expect_bang_to_continuation() {
    // Validator body = `Apply { function: Var("expect!"), args:
    // [cond, fn(x) { x }] }` — walk_tail must rewrite the
    // identity Lambda in the continuation.
    let validator_id = VarId::fresh_binding();
    let mut kinds = HashMap::new();
    kinds.insert(validator_id, VarKind::ValidatorEntry);
    let x_id = VarId::fresh_binding();
    let identity = PseudoExpr::Lambda {
        params: vec![crate::pseudo::ast::Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    let expect_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "expect!".to_string(),
            id: None,
        }),
        args: vec![PseudoExpr::Bool(true), identity].into(),
    };
    let validator_body = PseudoExpr::Lambda {
        params: vec![crate::pseudo::ast::Binder::new(
            "datum",
            VarId::fresh_binding(),
        )],
        body: PBox::new(expect_call),
    };
    let expr = PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(validator_id),
        value: PBox::new(validator_body),
        body: PBox::new(PseudoExpr::Unit),
    };
    let result = lower_v2_tail_unit_to_true(expr, Some(ScriptVersion::PlutusV1), &kinds);
    let PseudoExpr::Let { value, .. } = result else {
        panic!()
    };
    let PseudoExpr::Lambda { body, .. } = value.into_inner() else {
        panic!()
    };
    let PseudoExpr::Apply { args, .. } = body.into_inner() else {
        panic!("expected outer Apply (expect! call)");
    };
    assert!(
        matches!(args[1], PseudoExpr::Bool(true)),
        "expect! continuation's identity Lambda must be rewritten to Bool(true), got {:?}",
        args[1]
    );
}

#[test]
fn v3_leaves_trailing_identity_lambda_alone() {
    // V3 expects Unit in tail position, so the identity Lambda
    // is not rewritten.
    let validator_id = VarId::fresh_binding();
    let mut kinds = HashMap::new();
    kinds.insert(validator_id, VarKind::ValidatorEntry);
    let x_id = VarId::fresh_binding();
    let identity = PseudoExpr::Lambda {
        params: vec![crate::pseudo::ast::Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", x_id)),
    };
    let validator_body = PseudoExpr::Lambda {
        params: vec![crate::pseudo::ast::Binder::new(
            "datum",
            VarId::fresh_binding(),
        )],
        body: PBox::new(identity),
    };
    let expr = PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(validator_id),
        value: PBox::new(validator_body),
        body: PBox::new(PseudoExpr::Unit),
    };
    let result = lower_v2_tail_unit_to_true(expr.clone(), Some(ScriptVersion::PlutusV3), &kinds);
    assert_eq!(result, expr, "V3 must leave identity Lambda alone");
}
