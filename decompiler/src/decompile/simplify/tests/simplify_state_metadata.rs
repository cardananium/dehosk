use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_simplify_state_carries_boolean_tracking_between_passes() {
    let and_fn_id = VarId::from_raw(29100);
    let a_id = VarId::from_raw(29101);
    let b_id = VarId::from_raw(29102);
    let learn_and = PseudoExpr::Let {
        name: "and_fn".to_string(),
        id: Some(and_fn_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(PseudoExpr::var_with_id("a", a_id)),
                right: PBox::new(PseudoExpr::var_with_id("b", b_id)),
            }),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };

    let mut state = SimplifyState::default();
    let _ = simplify_with_state(learn_and, None, false, None, &mut state);
    assert!(
        state.booleans.and_vars.contains(and_fn_id),
        "first pass should harvest and_fn boolean metadata"
    );

    let left_id = VarId::from_raw(29103);
    let right_id = VarId::from_raw(29104);
    let rewritten_and = simplify_with_state(
        PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("and_fn", and_fn_id)),
            args: vec![
                PseudoExpr::var_with_id("left", left_id),
                PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("right", right_id))),
            ]
            .into(),
        })),
        None,
        false,
        None,
        &mut state,
    )
    .expr;
    assert!(
        matches!(
            &rewritten_and,
            PseudoExpr::BinOp { op: BinaryOp::And, left, right }
                if matches!(left.as_ref(), PseudoExpr::Var { name, id } if name == "left" && *id == Some(left_id))
                    && matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "right" && *id == Some(right_id))
        ),
        "second pass should seed and_fn metadata and rewrite force(and_fn(...)), got: {rewritten_and:?}"
    );

    let or_fn_id = VarId::from_raw(29105);
    let learn_or = PseudoExpr::Let {
        name: "or_fn".to_string(),
        id: Some(or_fn_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Or,
                left: PBox::new(PseudoExpr::var_with_id("a", a_id)),
                right: PBox::new(PseudoExpr::var_with_id("b", b_id)),
            }),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };
    let mut state = SimplifyState::default();
    let _ = simplify_with_state(learn_or, None, false, None, &mut state);
    assert!(
        state.booleans.or_vars.contains(or_fn_id),
        "first pass should harvest or_fn boolean metadata"
    );

    let rewritten_or = simplify_with_state(
        PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("or_fn", or_fn_id)),
            args: vec![
                PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("left", left_id))),
                PseudoExpr::var_with_id("right", right_id),
            ]
            .into(),
        })),
        None,
        false,
        None,
        &mut state,
    )
    .expr;
    assert!(
        matches!(
            &rewritten_or,
            PseudoExpr::BinOp { op: BinaryOp::Or, left, right }
                if matches!(left.as_ref(), PseudoExpr::Var { name, id } if name == "left" && *id == Some(left_id))
                    && matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "right" && *id == Some(right_id))
        ),
        "second pass should seed or_fn metadata and rewrite force(or_fn(...)), got: {rewritten_or:?}"
    );
}

#[test]
fn test_simplify_state_carries_partial_if_then_values_between_passes() {
    let helper_id = VarId::from_raw(29110);
    let param_id = VarId::from_raw(29111);
    let learn_partial_if = PseudoExpr::Let {
        name: "or_prefix".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", param_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("if"),
                    args: vec![].into(),
                }),
                args: vec![
                    PseudoExpr::var_with_id("x", param_id),
                    PseudoExpr::Bool(true),
                ]
                .into(),
            }),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };

    let mut state = SimplifyState::default();
    let _ = simplify_with_state(learn_partial_if, None, false, None, &mut state);
    assert!(
        state.booleans.partial_if_then_vals.get(helper_id).is_some(),
        "first pass should harvest partial-if then-value metadata"
    );

    let cond_id = VarId::from_raw(29112);
    let fallback_id = VarId::from_raw(29113);
    let rewritten = simplify_with_state(
        PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("or_prefix", helper_id)),
            args: vec![
                PseudoExpr::var_with_id("cond", cond_id),
                PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("fallback", fallback_id))),
            ]
            .into(),
        })),
        None,
        false,
        None,
        &mut state,
    )
    .expr;

    assert!(
        matches!(
            &rewritten,
            PseudoExpr::BinOp { op: BinaryOp::Or, left, right }
                if matches!(left.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id))
                    && matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "fallback" && *id == Some(fallback_id))
        ),
        "second pass should seed partial-if metadata and rewrite to ||, got: {rewritten:?}"
    );
}

#[test]
fn test_simplify_state_carries_builtin_aliases_between_passes() {
    let alias_id = VarId::from_raw(29114);
    let learn_alias = PseudoExpr::Let {
        name: "head_alias".to_string(),
        id: Some(alias_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: BuiltinId::ListHead,
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Unit),
    };

    let mut state = SimplifyState::default();
    let _ = simplify_with_state(learn_alias, None, false, None, &mut state);
    assert_eq!(
        state.naming.builtin_aliases.get(alias_id),
        Some(&BuiltinId::ListHead),
        "first pass should harvest builtin alias metadata"
    );

    let rewritten = simplify_with_state(
        PseudoExpr::var_with_id("head_alias", alias_id),
        None,
        false,
        None,
        &mut state,
    )
    .expr;
    assert!(
        matches!(&rewritten, PseudoExpr::BuiltinCall { name, args } if *name == BuiltinId::ListHead && args.is_empty()),
        "second pass should seed builtin alias metadata and route the Var to a BuiltinCall, got: {rewritten:?}"
    );
    assert_eq!(
        state.naming.builtin_aliases.get(alias_id),
        Some(&BuiltinId::ListHead),
        "builtin alias metadata should survive the seed/harvest round trip"
    );
}
