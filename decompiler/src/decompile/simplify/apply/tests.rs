use super::*;
use crate::pseudo::ast::Binder;

fn cps_unit_continuation(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![Binder::new("_", VarId::fresh_binding())],
        body: PBox::new(body),
    }
}

fn let_id_from_continue_loop(action: ApplyAction) -> VarId {
    match action {
        ApplyAction::ContinueLoop {
            function: PseudoExpr::Let { id, .. },
            args,
            ..
        } => {
            assert!(
                args.is_empty(),
                "expected no residual apply args, got: {args:?}"
            );
            id.expect("expected let id to be Some")
        }
        ApplyAction::ContinueLoop { function, .. } => {
            panic!("expected let-chain continue function, got: {function:?}")
        }
        ApplyAction::Done(expr) | ApplyAction::Resimplify(expr) => {
            panic!("expected continue-loop lambda desugar, got: {expr:?}")
        }
    }
}

#[test]
fn immediate_lambda_application_fallback_keeps_param_id() {
    let param = Binder::new("x", VarId::fresh_binding());
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Lambda {
            params: vec![param.clone()],
            body: PBox::new(PseudoExpr::Unit),
        },
        vec![PseudoExpr::int(1)],
    );

    assert_eq!(let_id_from_continue_loop(action), param.id);
}

#[test]
fn over_application_fallback_keeps_bound_param_id() {
    let param = Binder::new("x", VarId::fresh_binding());
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Lambda {
            params: vec![param.clone()],
            body: PBox::new(PseudoExpr::var("next")),
        },
        vec![PseudoExpr::int(1), PseudoExpr::int(2)],
    );

    assert_eq!(let_id_from_continue_loop(action), param.id);
}

#[test]
fn over_application_iife_moves_args_and_preserves_ids() {
    let bound = Binder::new("config", VarId::from_raw(9920));
    let callee_id = VarId::from_raw(9921);
    let arg_id = VarId::from_raw(9922);
    let residual_id = VarId::from_raw(9923);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Lambda {
            params: vec![bound.clone()],
            body: PBox::new(PseudoExpr::var_with_id("next", callee_id)),
        },
        vec![
            PseudoExpr::var_with_id("chosen_config", arg_id),
            PseudoExpr::var_with_id("datum", residual_id),
        ],
    );

    let ApplyAction::ContinueLoop {
        function,
        args,
        delay_restore: None,
    } = action
    else {
        panic!("expected over-application to desugar into a let-chain");
    };
    assert!(
        args.is_empty(),
        "expected no residual apply args, got: {args:?}"
    );

    let (name, id, value, body) = match function {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => (name, id, value, body),
        other => panic!("expected outer let for bound param, got: {other:?}"),
    };
    assert_eq!(name, "config");
    assert_eq!(id, Some(bound.id));
    assert!(
        matches!(
            value.as_ref(),
            PseudoExpr::Var { name, id } if name == "chosen_config" && *id == Some(arg_id)
        ),
        "over-application should move the owned bound arg into the let value, got: {value:?}"
    );
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "next" && *id == Some(callee_id))
                    && matches!(args.as_slice(), [PseudoExpr::Var { name, id }] if name == "datum" && *id == Some(residual_id))
        ),
        "over-application should move residual args into the nested apply, got: {body:?}"
    );
}

#[test]
fn over_application_capture_fallback_preserves_original_force_lambda_shape() {
    let x = Binder::new("x", VarId::from_raw(9924));
    let foreign_x_id = VarId::from_raw(9925);
    let residual_id = VarId::from_raw(9926);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Force(PBox::new(PseudoExpr::Lambda {
            params: vec![x.clone()],
            body: PBox::new(PseudoExpr::var_with_id("next", VarId::from_raw(9927))),
        })),
        vec![
            PseudoExpr::var_with_id("x", foreign_x_id),
            PseudoExpr::var_with_id("datum", residual_id),
        ],
    );

    let ApplyAction::Done(PseudoExpr::Apply { function, args }) = action else {
        panic!("expected capture guard fallback to preserve original apply shape");
    };

    assert!(
        matches!(
            function.as_ref(),
            PseudoExpr::Force(inner)
                if matches!(
                    inner.as_ref(),
                    PseudoExpr::Lambda { params, .. }
                        if matches!(params.as_slice(), [first] if first.id == x.id)
                )
        ),
        "capture fallback must keep the original Force(Lambda) function, got: {function:?}"
    );
    assert!(
        matches!(
            args.as_slice(),
            [
                PseudoExpr::Var { name: first_name, id: first_id },
                PseudoExpr::Var { name: second_name, id: second_id },
            ] if first_name == "x"
                && *first_id == Some(foreign_x_id)
                && second_name == "datum"
                && *second_id == Some(residual_id)
        ),
        "capture fallback must preserve original arg ids, got: {args:?}"
    );
}

#[test]
fn under_application_fallback_keeps_bound_param_id() {
    let bound = Binder::new("x", VarId::fresh_binding());
    let remaining = Binder::new("y", VarId::fresh_binding());
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Lambda {
            params: vec![bound.clone(), remaining.clone()],
            body: PBox::new(PseudoExpr::var_with_id("y", remaining.id)),
        },
        vec![PseudoExpr::int(1)],
    );

    assert_eq!(let_id_from_continue_loop(action), bound.id);
}

#[test]
fn under_application_iife_moves_arg_and_preserves_ids() {
    let bound = Binder::new("config", VarId::from_raw(9910));
    let remaining = Binder::new("datum", VarId::from_raw(9911));
    let arg_id = VarId::from_raw(9912);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Lambda {
            params: vec![bound.clone(), remaining.clone()],
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("config", bound.id),
                    PseudoExpr::var_with_id("datum", remaining.id),
                ]
                .into(),
            )),
        },
        vec![PseudoExpr::var_with_id("chosen_config", arg_id)],
    );

    let ApplyAction::ContinueLoop {
        function,
        args,
        delay_restore: None,
    } = action
    else {
        panic!("expected under-application to desugar into a let-chain");
    };
    assert!(
        args.is_empty(),
        "expected no residual apply args, got: {args:?}"
    );

    let (name, id, value, body) = match function {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => (name, id, value, body),
        other => panic!("expected outer let for bound param, got: {other:?}"),
    };
    assert_eq!(name, "config");
    assert_eq!(id, Some(bound.id));
    assert!(
        matches!(
            value.as_ref(),
            PseudoExpr::Var { name, id } if name == "chosen_config" && *id == Some(arg_id)
        ),
        "under-application should move the owned arg into the let value, got: {value:?}"
    );
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Lambda { params, body }
                if matches!(params.as_slice(), [binder] if binder.as_str() == "datum" && binder.id == remaining.id)
                    && matches!(body.as_ref(), PseudoExpr::Tuple(items) if items.len() == 2)
        ),
        "under-application should preserve remaining lambda binder ids, got: {body:?}"
    );
}

#[test]
fn under_application_capture_fallback_preserves_original_force_lambda_shape() {
    let x = Binder::new("x", VarId::from_raw(9913));
    let y = Binder::new("y", VarId::from_raw(9914));
    let foreign_x_id = VarId::from_raw(9915);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Force(PBox::new(PseudoExpr::Lambda {
            params: vec![x.clone(), y.clone()],
            body: PBox::new(PseudoExpr::var_with_id("y", y.id)),
        })),
        vec![PseudoExpr::var_with_id("x", foreign_x_id)],
    );

    let ApplyAction::Done(PseudoExpr::Apply { function, args }) = action else {
        panic!("expected capture guard fallback to preserve original apply shape");
    };

    assert!(
        matches!(
            function.as_ref(),
            PseudoExpr::Force(inner)
                if matches!(
                    inner.as_ref(),
                    PseudoExpr::Lambda { params, .. }
                        if matches!(params.as_slice(), [first, second] if first.id == x.id && second.id == y.id)
                )
        ),
        "capture fallback must keep the original Force(Lambda) function, got: {function:?}"
    );
    assert!(
        matches!(
            args.as_slice(),
            [PseudoExpr::Var { name, id }] if name == "x" && *id == Some(foreign_x_id)
        ),
        "capture fallback must preserve the original arg id, got: {args:?}"
    );
}

#[test]
fn expect_tag_rewrite_moves_value_arg_and_preserves_id() {
    let subject_id = VarId::from_raw(9990);
    let value_id = VarId::from_raw(9991);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::expect_helper(),
        vec![
            PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("subject", subject_id),
                    "tag".to_string(),
                )),
                right: PBox::new(PseudoExpr::int(2)),
            },
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("value", value_id))),
        ],
    );

    let ApplyAction::Done(PseudoExpr::When {
        subject, clauses, ..
    }) = action
    else {
        panic!("expected expect-tag rewrite to produce When");
    };
    assert!(
        matches!(
            subject.as_ref(),
            PseudoExpr::Var { name, id } if name == "subject" && *id == Some(subject_id)
        ),
        "expect-tag rewrite should preserve subject id, got: {subject:?}"
    );
    assert!(
        matches!(
            &clauses[0].pattern,
            WhenPattern::Constructor {
                shape: ConstructorShape::Unknown {
                    tag: 2,
                    arity: 0,
                    ..
                },
                ..
            }
        ),
        "expected Constr<2> pattern, got: {:?}",
        clauses[0].pattern
    );
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::Var { name, id } if name == "value" && *id == Some(value_id)
        ),
        "expect-tag rewrite should move and unwrap value with id intact, got: {:?}",
        clauses[0].body
    );
}

#[test]
fn y_comb_direct_application_moves_extra_args_and_preserves_ids() {
    let self_id = VarId::from_raw(9960);
    let param_id = VarId::from_raw(9961);
    let arg_id = VarId::from_raw(9962);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::var("__y_comb_direct"),
        vec![
            PseudoExpr::Lambda {
                params: vec![Binder::new("self_fn", self_id), Binder::new("n", param_id)],
                body: PBox::new(PseudoExpr::var_with_id("n", param_id)),
            },
            PseudoExpr::var_with_id("seed", arg_id),
        ],
    );

    let ApplyAction::Done(PseudoExpr::Let {
        name,
        id,
        value,
        body,
    }) = action
    else {
        panic!("expected direct Y-combinator call to produce a let-bound RecFn");
    };
    assert_eq!(name, "self_fn");
    assert_eq!(id, Some(self_id));
    assert!(
        matches!(
            value.as_ref(),
            PseudoExpr::RecFn { name, params, .. }
                if name.as_str() == "self_fn"
                    && name.id == self_id
                    && matches!(params.as_slice(), [binder] if binder.as_str() == "n" && binder.id == param_id)
        ),
        "expected RecFn value to preserve self/param ids, got: {value:?}"
    );
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "self_fn" && *id == Some(self_id))
                    && matches!(args.as_slice(), [PseudoExpr::Var { name, id }] if name == "seed" && *id == Some(arg_id))
        ),
        "direct Y-combinator call should move trailing call args with ids intact, got: {body:?}"
    );
}

#[test]
fn and_or_helper_application_moves_args_and_preserves_ids() {
    let and_id = VarId::from_raw(9970);
    let left_id = VarId::from_raw(9971);
    let right_id = VarId::from_raw(9972);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier
        .booleans
        .and_vars
        .insert_binding("and_fn", Some(and_id));

    let action = simplifier.simplify_apply_match(
        PseudoExpr::var_with_id("and_fn", and_id),
        vec![
            PseudoExpr::var_with_id("left", left_id),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("right", right_id))),
        ],
    );

    let ApplyAction::Done(PseudoExpr::BinOp { op, left, right }) = action else {
        panic!("expected and_fn application to become BinOp");
    };
    assert_eq!(op, BinaryOp::And);
    assert!(
        matches!(left.as_ref(), PseudoExpr::Var { name, id } if name == "left" && *id == Some(left_id)),
        "and_fn should move lhs with id intact, got: {left:?}"
    );
    assert!(
        matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "right" && *id == Some(right_id)),
        "and_fn should move and unwrap rhs with id intact, got: {right:?}"
    );

    let or_id = VarId::from_raw(9973);
    let left_id = VarId::from_raw(9974);
    let right_id = VarId::from_raw(9975);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier
        .booleans
        .or_vars
        .insert_binding("or_fn", Some(or_id));

    let action = simplifier.simplify_apply_match(
        PseudoExpr::var_with_id("or_fn", or_id),
        vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("left", left_id))),
            PseudoExpr::var_with_id("right", right_id),
        ],
    );

    let ApplyAction::Done(PseudoExpr::BinOp { op, left, right }) = action else {
        panic!("expected or_fn application to become BinOp");
    };
    assert_eq!(op, BinaryOp::Or);
    assert!(
        matches!(left.as_ref(), PseudoExpr::Var { name, id } if name == "left" && *id == Some(left_id)),
        "or_fn should move and unwrap lhs with id intact, got: {left:?}"
    );
    assert!(
        matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "right" && *id == Some(right_id)),
        "or_fn should move rhs with id intact, got: {right:?}"
    );
}

#[test]
fn direct_f_if_moves_condition_and_delayed_branches() {
    let cond_id = VarId::from_raw(9977);
    let then_id = VarId::from_raw(9978);
    let else_id = VarId::from_raw(9979);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::var("f"),
        vec![
            PseudoExpr::var_with_id("cond", cond_id),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("then", then_id))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("else", else_id))),
        ],
    );

    let ApplyAction::Done(PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    }) = action
    else {
        panic!("expected direct f-if to become If");
    };
    assert!(
        matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "direct f-if should move condition id intact, got: {condition:?}"
    );
    assert!(
        matches!(then_branch.as_ref(), PseudoExpr::Var { name, id } if name == "then" && *id == Some(then_id)),
        "direct f-if should move then branch id intact, got: {then_branch:?}"
    );
    assert!(
        matches!(else_branch.as_ref(), PseudoExpr::Var { name, id } if name == "else" && *id == Some(else_id)),
        "direct f-if should move else branch id intact, got: {else_branch:?}"
    );
}

#[test]
fn direct_f_if_and_pattern_moves_then_branch() {
    let cond_id = VarId::from_raw(9980);
    let then_id = VarId::from_raw(9981);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::var("f"),
        vec![
            PseudoExpr::var_with_id("cond", cond_id),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("then", then_id))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::Bool(false))),
        ],
    );

    let ApplyAction::Done(PseudoExpr::BinOp { op, left, right }) = action else {
        panic!("expected direct f-if && pattern to become BinOp");
    };
    assert_eq!(op, BinaryOp::And);
    assert!(
        matches!(left.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "direct f-if && should move condition id intact, got: {left:?}"
    );
    assert!(
        matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "then" && *id == Some(then_id)),
        "direct f-if && should move then branch id intact, got: {right:?}"
    );
}

#[test]
fn constr_exposer_wrapper_moves_index_arg_and_preserves_id() {
    let subject_id = VarId::from_raw(9982);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::var("__constr_index_exposer"),
        vec![PseudoExpr::var_with_id("subject", subject_id)],
    );

    let ApplyAction::Done(PseudoExpr::BuiltinCall { name, args }) = action else {
        panic!("expected constr index exposer wrapper to become builtin call");
    };
    assert_eq!(name, crate::BuiltinId::DataConstrIndex);
    assert!(
        matches!(args.as_slice(), [PseudoExpr::Var { name, id }] if name == "subject" && *id == Some(subject_id)),
        "constr index exposer should move subject id intact, got: {args:?}"
    );
}

#[test]
fn constr_exposer_wrapper_moves_fields_arg_and_preserves_id() {
    let subject_id = VarId::from_raw(9983);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::var("__constr_fields_exposer"),
        vec![PseudoExpr::var_with_id("subject", subject_id)],
    );

    let ApplyAction::Done(PseudoExpr::BuiltinCall { name, args }) = action else {
        panic!("expected constr fields exposer wrapper to become builtin call");
    };
    assert_eq!(name, crate::BuiltinId::DataConstrFields);
    assert!(
        matches!(args.as_slice(), [PseudoExpr::Var { name, id }] if name == "subject" && *id == Some(subject_id)),
        "constr fields exposer should move subject id intact, got: {args:?}"
    );
}

#[test]
fn forced_partial_if_moves_builtin_and_apply_args() {
    let cond_id = VarId::from_raw(9988);
    let then_id = VarId::from_raw(9989);
    let else_id = VarId::from_raw(9990);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Force(PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![
                PseudoExpr::var_with_id("cond", cond_id),
                PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("then", then_id))),
            ]
            .into(),
        })),
        vec![PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
            "else", else_id,
        )))],
    );

    let ApplyAction::Done(PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    }) = action
    else {
        panic!("expected forced partial if to become If");
    };
    assert!(
        matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "forced partial if should move condition id intact, got: {condition:?}"
    );
    assert!(
        matches!(then_branch.as_ref(), PseudoExpr::Var { name, id } if name == "then" && *id == Some(then_id)),
        "forced partial if should move then branch id intact, got: {then_branch:?}"
    );
    assert!(
        matches!(else_branch.as_ref(), PseudoExpr::Var { name, id } if name == "else" && *id == Some(else_id)),
        "forced partial if should move else branch id intact, got: {else_branch:?}"
    );
}

#[test]
fn forced_partial_if_extra_args_moves_residual_args() {
    let cond_id = VarId::from_raw(9991);
    let then_id = VarId::from_raw(9992);
    let else_id = VarId::from_raw(9993);
    let residual_id = VarId::from_raw(9994);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Force(PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![
                PseudoExpr::var_with_id("cond", cond_id),
                PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("then", then_id))),
            ]
            .into(),
        })),
        vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("else", else_id))),
            PseudoExpr::var_with_id("residual", residual_id),
        ],
    );

    let ApplyAction::ContinueLoop {
        function,
        args,
        delay_restore: None,
    } = action
    else {
        panic!("expected forced partial if with extra args to continue");
    };
    assert!(
        matches!(
            &function,
            PseudoExpr::If { condition, then_branch, else_branch }
                if matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id))
                    && matches!(then_branch.as_ref(), PseudoExpr::Var { name, id } if name == "then" && *id == Some(then_id))
                    && matches!(else_branch.as_ref(), PseudoExpr::Var { name, id } if name == "else" && *id == Some(else_id))
        ),
        "forced partial if should move core args into If, got: {function:?}"
    );
    assert!(
        matches!(args.as_slice(), [PseudoExpr::Var { name, id }] if name == "residual" && *id == Some(residual_id)),
        "forced partial if should move residual args intact, got: {args:?}"
    );
}

#[test]
fn scott_application_reversal_moves_selected_arg_and_fields() {
    let selected_id = VarId::from_raw(9984);
    let skipped_id = VarId::from_raw(9985);
    let first_field_id = VarId::from_raw(9986);
    let second_field_id = VarId::from_raw(9987);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::constr(
            ConstructorShape::unknown_data(1, 2),
            vec![
                PseudoExpr::var_with_id("first_field", first_field_id),
                PseudoExpr::var_with_id("second_field", second_field_id),
            ],
        ),
        vec![
            PseudoExpr::var_with_id("skipped", skipped_id),
            PseudoExpr::var_with_id("selected", selected_id),
        ],
    );

    let ApplyAction::ContinueLoop {
        function,
        args,
        delay_restore: None,
    } = action
    else {
        panic!("expected Scott reversal to continue with selected continuation");
    };
    assert!(
        matches!(
            &function,
            PseudoExpr::Var { name, id } if name == "selected" && *id == Some(selected_id)
        ),
        "Scott reversal should move the selected continuation with id intact, got: {function:?}"
    );
    assert!(
        matches!(
            args.as_slice(),
            [
                PseudoExpr::Var { name: first_name, id: first_id },
                PseudoExpr::Var { name: second_name, id: second_id },
            ] if first_name == "first_field"
                && *first_id == Some(first_field_id)
                && second_name == "second_field"
                && *second_id == Some(second_field_id)
        ),
        "Scott reversal should move constructor fields into residual args, got: {args:?}"
    );
}

#[test]
fn scott_list_emptiness_moves_branch_values() {
    let subject_id = VarId::from_raw(9984);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::var_with_id("xs", subject_id),
        vec![
            PseudoExpr::Lambda {
                params: vec![Binder::from("_")],
                body: PBox::new(PseudoExpr::Bool(false)),
            },
            PseudoExpr::Bool(true),
        ],
    );

    let ApplyAction::Done(PseudoExpr::When {
        subject, clauses, ..
    }) = action
    else {
        panic!("expected Scott list emptiness rewrite to produce When");
    };
    assert!(
        matches!(
            subject.as_ref(),
            PseudoExpr::Var { name, id } if name == "xs" && *id == Some(subject_id)
        ),
        "Scott list emptiness should preserve subject id, got: {subject:?}"
    );
    assert!(matches!(clauses[0].body, PseudoExpr::Bool(false)));
    assert!(matches!(clauses[1].body, PseudoExpr::Bool(true)));
}

#[test]
fn partial_application_moves_arg_and_preserves_ids() {
    let callee_id = VarId::from_raw(9920);
    let arg_id = VarId::from_raw(9921);

    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.delays.partial_apps.insert_binding(
        "c",
        Some(callee_id),
        (BinaryOp::Sub, PseudoExpr::int(0), true),
    );
    let action = simplifier.simplify_apply_match(
        PseudoExpr::var_with_id("c", callee_id),
        vec![PseudoExpr::var_with_id("x", arg_id)],
    );

    let ApplyAction::Done(PseudoExpr::BinOp { op, left, right }) = action else {
        panic!("expected partial application to rewrite to BinOp");
    };
    assert_eq!(op, BinaryOp::Sub);
    assert!(matches!(left.as_ref(), PseudoExpr::Int(n) if *n == 0.into()));
    assert!(
        matches!(
            right.as_ref(),
            PseudoExpr::Var { name, id } if name == "x" && *id == Some(arg_id)
        ),
        "partial application should move the owned arg with id intact, got: {right:?}"
    );

    let callee_id = VarId::from_raw(9922);
    let arg_id = VarId::from_raw(9923);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.delays.partial_apps.insert_binding(
        "c",
        Some(callee_id),
        (BinaryOp::Eq, PseudoExpr::int(1), false),
    );
    let action = simplifier.simplify_apply_match(
        PseudoExpr::var_with_id("c", callee_id),
        vec![PseudoExpr::var_with_id("x", arg_id)],
    );

    let ApplyAction::Done(PseudoExpr::BinOp { op, left, right }) = action else {
        panic!("expected partial application to rewrite to BinOp");
    };
    assert_eq!(op, BinaryOp::Eq);
    assert!(
        matches!(
            left.as_ref(),
            PseudoExpr::Var { name, id } if name == "x" && *id == Some(arg_id)
        ),
        "partial application should move the owned arg with id intact, got: {left:?}"
    );
    assert!(matches!(right.as_ref(), PseudoExpr::Int(n) if *n == 1.into()));
}

#[test]
fn constr_pack_partial_application_moves_fields_and_preserves_ids() {
    let callee_id = VarId::from_raw(9930);
    let fields_id = VarId::from_raw(9931);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.constructors.constr_pack_tags.insert_binding(
        "pack",
        Some(callee_id),
        PseudoExpr::int(2),
    );

    let action = simplifier.simplify_apply_match(
        PseudoExpr::var_with_id("pack", callee_id),
        vec![PseudoExpr::var_with_id("fields", fields_id)],
    );

    let ApplyAction::Done(PseudoExpr::Constr { tag, fields, .. }) = action else {
        panic!("expected Constr.pack partial application to become Constr");
    };
    assert_eq!(tag, 2);
    assert!(
        matches!(fields.as_slice(), [PseudoExpr::Var { name, id }] if name == "fields" && *id == Some(fields_id)),
        "Constr.pack partial application should move the fields arg with id intact, got: {:?}",
        fields
    );
}

#[test]
fn constr_pack_partial_application_extra_args_moves_residual_args() {
    let callee_id = VarId::from_raw(9932);
    let fields_id = VarId::from_raw(9933);
    let residual_id = VarId::from_raw(9934);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier.constructors.constr_pack_tags.insert_binding(
        "pack",
        Some(callee_id),
        PseudoExpr::int(3),
    );

    let action = simplifier.simplify_apply_match(
        PseudoExpr::var_with_id("pack", callee_id),
        vec![
            PseudoExpr::var_with_id("fields", fields_id),
            PseudoExpr::var_with_id("residual", residual_id),
        ],
    );

    let ApplyAction::ContinueLoop { function, args, .. } = action else {
        panic!("expected Constr.pack partial application with extra args to continue");
    };
    assert!(
        matches!(
            &function,
            PseudoExpr::Constr { tag: 3, fields, .. }
                if matches!(fields.as_slice(), [PseudoExpr::Var { name, id }] if name == "fields" && *id == Some(fields_id))
        ),
        "expected fields arg to move into Constr function, got: {function:?}"
    );
    assert!(
        matches!(args.as_slice(), [PseudoExpr::Var { name, id }] if name == "residual" && *id == Some(residual_id)),
        "expected residual args to move into ContinueLoop, got: {args:?}"
    );
}

#[test]
fn constr_pack_direct_application_moves_tag_and_fields_and_preserves_ids() {
    let tag_id = VarId::from_raw(9935);
    let fields_id = VarId::from_raw(9936);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Constr.pack"),
            args: vec![PseudoExpr::var_with_id("tag", tag_id)].into(),
        },
        vec![PseudoExpr::var_with_id("fields", fields_id)],
    );

    let ApplyAction::Done(PseudoExpr::BuiltinCall { name, args }) = action else {
        panic!("expected direct Constr.pack application to become Data.Constr");
    };
    assert_eq!(name, crate::BuiltinId::DataConstr);
    assert!(
        matches!(
            args.as_slice(),
            [
                PseudoExpr::Var { name: tag_name, id: moved_tag_id },
                PseudoExpr::Var { name: fields_name, id: moved_fields_id },
            ] if tag_name == "tag"
                && *moved_tag_id == Some(tag_id)
                && fields_name == "fields"
                && *moved_fields_id == Some(fields_id)
        ),
        "direct Constr.pack application should move tag and fields args intact, got: {args:?}"
    );
}

#[test]
fn partial_apply_if_moves_builtin_and_apply_args_and_preserves_ids() {
    let cond_id = VarId::from_raw(9937);
    let then_id = VarId::from_raw(9938);
    let else_id = VarId::from_raw(9939);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![
                PseudoExpr::var_with_id("cond", cond_id),
                PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("then", then_id))),
            ]
            .into(),
        },
        vec![PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
            "else", else_id,
        )))],
    );

    let ApplyAction::Done(PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    }) = action
    else {
        panic!("expected partial Apply-form if to become If");
    };
    assert!(
        matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "partial Apply-form if should move condition id intact, got: {condition:?}"
    );
    assert!(
        matches!(then_branch.as_ref(), PseudoExpr::Var { name, id } if name == "then" && *id == Some(then_id)),
        "partial Apply-form if should move then branch id intact, got: {then_branch:?}"
    );
    assert!(
        matches!(else_branch.as_ref(), PseudoExpr::Var { name, id } if name == "else" && *id == Some(else_id)),
        "partial Apply-form if should move else branch id intact, got: {else_branch:?}"
    );
}

#[test]
fn partial_apply_if_cps_moves_continuation_bodies_and_preserves_ids() {
    let cond_id = VarId::from_raw(9940);
    let then_id = VarId::from_raw(9941);
    let else_id = VarId::from_raw(9942);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![PseudoExpr::var_with_id("cond", cond_id)].into(),
        },
        vec![
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::from_raw(9943))],
                body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
                    "then", then_id,
                )))),
            },
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::from_raw(9944))],
                body: PBox::new(PseudoExpr::var_with_id("else", else_id)),
            },
            PseudoExpr::var_with_id("trigger", VarId::from_raw(9945)),
        ],
    );

    let ApplyAction::Done(PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    }) = action
    else {
        panic!("expected partial CPS Apply-form if to become If");
    };
    assert!(
        matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "partial CPS Apply-form if should move condition id intact, got: {condition:?}"
    );
    assert!(
        matches!(then_branch.as_ref(), PseudoExpr::Var { name, id } if name == "then" && *id == Some(then_id)),
        "partial CPS Apply-form if should move then body id intact, got: {then_branch:?}"
    );
    assert!(
        matches!(else_branch.as_ref(), PseudoExpr::Var { name, id } if name == "else" && *id == Some(else_id)),
        "partial CPS Apply-form if should move else body id intact, got: {else_branch:?}"
    );
}

#[test]
fn partial_apply_if_cps_fallback_moves_functions_and_preserves_trigger_ids() {
    let cond_id = VarId::from_raw(9946);
    let then_fn_id = VarId::from_raw(9947);
    let else_fn_id = VarId::from_raw(9948);
    let trigger_id = VarId::from_raw(9949);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![PseudoExpr::var_with_id("cond", cond_id)].into(),
        },
        vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("then_fn", then_fn_id))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("else_fn", else_fn_id))),
            PseudoExpr::var_with_id("trigger", trigger_id),
        ],
    );

    let ApplyAction::Done(PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    }) = action
    else {
        panic!("expected partial CPS Apply-form if fallback to become If");
    };
    assert!(
        matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "partial CPS Apply-form fallback should move condition id intact, got: {condition:?}"
    );
    assert!(
        matches!(
            then_branch.as_ref(),
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "then_fn" && *id == Some(then_fn_id))
                    && matches!(args.as_slice(), [PseudoExpr::Var { name, id }] if name == "trigger" && *id == Some(trigger_id))
        ),
        "partial CPS Apply-form fallback should move then function and apply trigger, got: {then_branch:?}"
    );
    assert!(
        matches!(
            else_branch.as_ref(),
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "else_fn" && *id == Some(else_fn_id))
                    && matches!(args.as_slice(), [PseudoExpr::Var { name, id }] if name == "trigger" && *id == Some(trigger_id))
        ),
        "partial CPS Apply-form fallback should move else function and apply trigger, got: {else_branch:?}"
    );
}

#[test]
fn generic_if_over_application_moves_core_and_residual_args() {
    let cond_id = VarId::from_raw(9950);
    let then_id = VarId::from_raw(9951);
    let else_id = VarId::from_raw(9952);
    let first_residual_id = VarId::from_raw(9953);
    let second_residual_id = VarId::from_raw(9954);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![].into(),
        },
        vec![
            PseudoExpr::var_with_id("cond", cond_id),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("then", then_id))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("else", else_id))),
            PseudoExpr::var_with_id("first", first_residual_id),
            PseudoExpr::var_with_id("second", second_residual_id),
        ],
    );

    let ApplyAction::ContinueLoop {
        function,
        args,
        delay_restore: None,
    } = action
    else {
        panic!("expected over-applied if to continue with residual args");
    };
    assert!(
        matches!(
            &function,
            PseudoExpr::If { condition, then_branch, else_branch }
                if matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id))
                    && matches!(then_branch.as_ref(), PseudoExpr::Var { name, id } if name == "then" && *id == Some(then_id))
                    && matches!(else_branch.as_ref(), PseudoExpr::Var { name, id } if name == "else" && *id == Some(else_id))
        ),
        "generic over-applied if should move core args into If, got: {function:?}"
    );
    assert!(
        matches!(
            args.as_slice(),
            [
                PseudoExpr::Var { name: first_name, id: first_id },
                PseudoExpr::Var { name: second_name, id: second_id },
            ] if first_name == "first"
                && *first_id == Some(first_residual_id)
                && second_name == "second"
                && *second_id == Some(second_residual_id)
        ),
        "generic over-applied if should move residual args intact, got: {args:?}"
    );
}

#[test]
fn apply_if_cps_and_moves_cond_and_then_body_preserving_ids() {
    let cond_id = VarId::from_raw(9959);
    let then_id = VarId::from_raw(9960);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![].into(),
        },
        vec![
            PseudoExpr::var_with_id("cond", cond_id),
            cps_unit_continuation(PseudoExpr::var_with_id("then", then_id)),
            cps_unit_continuation(PseudoExpr::Bool(false)),
            PseudoExpr::Unit,
        ],
    );

    let ApplyAction::Done(PseudoExpr::BinOp { op, left, right }) = action else {
        panic!("expected 4-arg CPS-if && pattern to become BinOp");
    };
    assert_eq!(op, BinaryOp::And);
    assert!(
        matches!(left.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "4-arg CPS-if && should move condition id intact, got: {left:?}"
    );
    assert!(
        matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "then" && *id == Some(then_id)),
        "4-arg CPS-if && should move then body id intact, got: {right:?}"
    );
}

#[test]
fn apply_if_cps_or_moves_cond_and_else_body_preserving_ids() {
    let cond_id = VarId::from_raw(9961);
    let else_id = VarId::from_raw(9962);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![].into(),
        },
        vec![
            PseudoExpr::var_with_id("cond", cond_id),
            cps_unit_continuation(PseudoExpr::Bool(true)),
            cps_unit_continuation(PseudoExpr::var_with_id("else", else_id)),
            PseudoExpr::Unit,
        ],
    );

    let ApplyAction::Done(PseudoExpr::BinOp { op, left, right }) = action else {
        panic!("expected 4-arg CPS-if || pattern to become BinOp");
    };
    assert_eq!(op, BinaryOp::Or);
    assert!(
        matches!(left.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "4-arg CPS-if || should move condition id intact, got: {left:?}"
    );
    assert!(
        matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "else" && *id == Some(else_id)),
        "4-arg CPS-if || should move else body id intact, got: {right:?}"
    );
}

#[test]
fn apply_if_cps_expect_moves_cond_and_value_body_preserving_ids() {
    let cond_id = VarId::from_raw(9963);
    let value_id = VarId::from_raw(9964);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![].into(),
        },
        vec![
            PseudoExpr::var_with_id("cond", cond_id),
            cps_unit_continuation(PseudoExpr::var_with_id("value", value_id)),
            cps_unit_continuation(PseudoExpr::Error {
                message: Some("boom".to_string()),
            }),
            PseudoExpr::Unit,
        ],
    );

    let ApplyAction::Done(PseudoExpr::Apply { function, args }) = action else {
        panic!("expected 4-arg CPS-if expect pattern to become expect!");
    };
    assert!(
        matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "expect!"),
        "expected expect! helper, got: {function:?}"
    );
    assert!(
        matches!(
            args.as_slice(),
            [
                PseudoExpr::Var { name: cond_name, id: moved_cond_id },
                PseudoExpr::Var { name: value_name, id: moved_value_id },
                PseudoExpr::String(message),
            ] if cond_name == "cond"
                && *moved_cond_id == Some(cond_id)
                && value_name == "value"
                && *moved_value_id == Some(value_id)
                && message == "boom"
        ),
        "4-arg CPS-if expect should move condition/value args and preserve message, got: {args:?}"
    );
}

#[test]
fn apply_if_cps_inverted_expect_moves_else_body_preserving_ids() {
    let cond_id = VarId::from_raw(9965);
    let value_id = VarId::from_raw(9966);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![].into(),
        },
        vec![
            PseudoExpr::var_with_id("cond", cond_id),
            cps_unit_continuation(PseudoExpr::Error {
                message: Some("nope".to_string()),
            }),
            cps_unit_continuation(PseudoExpr::var_with_id("value", value_id)),
            PseudoExpr::Unit,
        ],
    );

    let ApplyAction::Done(PseudoExpr::Apply { function, args }) = action else {
        panic!("expected inverted 4-arg CPS-if expect pattern to become expect!");
    };
    assert!(
        matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "expect!"),
        "expected expect! helper, got: {function:?}"
    );
    assert!(
        matches!(
            args.as_slice(),
            [
                PseudoExpr::UnOp { op: UnaryOp::Not, operand },
                PseudoExpr::Var { name: value_name, id: moved_value_id },
                PseudoExpr::String(message),
            ] if matches!(operand.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id))
                && value_name == "value"
                && *moved_value_id == Some(value_id)
                && message == "nope"
        ),
        "inverted 4-arg CPS-if expect should move condition/value args and preserve message, got: {args:?}"
    );
}

#[test]
fn apply_if_cps_regular_if_moves_all_bodies_preserving_ids() {
    let cond_id = VarId::from_raw(9967);
    let then_id = VarId::from_raw(9968);
    let else_id = VarId::from_raw(9969);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![].into(),
        },
        vec![
            PseudoExpr::var_with_id("cond", cond_id),
            cps_unit_continuation(PseudoExpr::var_with_id("then", then_id)),
            cps_unit_continuation(PseudoExpr::var_with_id("else", else_id)),
            PseudoExpr::Unit,
        ],
    );

    let ApplyAction::Done(PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    }) = action
    else {
        panic!("expected regular 4-arg CPS-if to become If");
    };
    assert!(
        matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "regular 4-arg CPS-if should move condition id intact, got: {condition:?}"
    );
    assert!(
        matches!(then_branch.as_ref(), PseudoExpr::Var { name, id } if name == "then" && *id == Some(then_id)),
        "regular 4-arg CPS-if should move then body id intact, got: {then_branch:?}"
    );
    assert!(
        matches!(else_branch.as_ref(), PseudoExpr::Var { name, id } if name == "else" && *id == Some(else_id)),
        "regular 4-arg CPS-if should move else body id intact, got: {else_branch:?}"
    );
}

#[test]
fn selector_if_five_arg_moves_condition_and_branches() {
    let cond_id = VarId::from_raw(9970);
    let then_id = VarId::from_raw(9971);
    let else_id = VarId::from_raw(9972);
    let fst_param = Binder::new("fst", VarId::from_raw(9973));
    let snd_param = Binder::new("snd", VarId::from_raw(9974));
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![].into(),
        },
        vec![
            PseudoExpr::var_with_id("cond", cond_id),
            PseudoExpr::Lambda {
                params: vec![fst_param.clone(), Binder::new("_", VarId::from_raw(9975))],
                body: PBox::new(PseudoExpr::var_with_id("fst", fst_param.id)),
            },
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::from_raw(9976)), snd_param.clone()],
                body: PBox::new(PseudoExpr::var_with_id("snd", snd_param.id)),
            },
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("then", then_id))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("else", else_id))),
        ],
    );

    let ApplyAction::Done(PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    }) = action
    else {
        panic!("expected 5-arg selector if to become If");
    };
    assert!(
        matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "5-arg selector if should move condition id intact, got: {condition:?}"
    );
    assert!(
        matches!(then_branch.as_ref(), PseudoExpr::Var { name, id } if name == "then" && *id == Some(then_id)),
        "5-arg selector if should move then branch id intact, got: {then_branch:?}"
    );
    assert!(
        matches!(else_branch.as_ref(), PseudoExpr::Var { name, id } if name == "else" && *id == Some(else_id)),
        "5-arg selector if should move else branch id intact, got: {else_branch:?}"
    );
}

#[test]
fn apply_if_cps_fallback_moves_functions_and_preserves_trigger_ids() {
    let cond_id = VarId::from_raw(9966);
    let then_fn_id = VarId::from_raw(9967);
    let else_fn_id = VarId::from_raw(9968);
    let trigger_id = VarId::from_raw(9969);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("if"),
            args: vec![].into(),
        },
        vec![
            PseudoExpr::var_with_id("cond", cond_id),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("then_fn", then_fn_id))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id("else_fn", else_fn_id))),
            PseudoExpr::var_with_id("trigger", trigger_id),
        ],
    );

    let ApplyAction::Done(PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    }) = action
    else {
        panic!("expected 4-arg CPS-if fallback to become If");
    };
    assert!(
        matches!(condition.as_ref(), PseudoExpr::Var { name, id } if name == "cond" && *id == Some(cond_id)),
        "4-arg CPS-if fallback should move condition id intact, got: {condition:?}"
    );
    assert!(
        matches!(
            then_branch.as_ref(),
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "then_fn" && *id == Some(then_fn_id))
                    && matches!(args.as_slice(), [PseudoExpr::Var { name, id }] if name == "trigger" && *id == Some(trigger_id))
        ),
        "4-arg CPS-if fallback should move then function and apply trigger, got: {then_branch:?}"
    );
    assert!(
        matches!(
            else_branch.as_ref(),
            PseudoExpr::Apply { function, args }
                if matches!(function.as_ref(), PseudoExpr::Var { name, id } if name == "else_fn" && *id == Some(else_fn_id))
                    && matches!(args.as_slice(), [PseudoExpr::Var { name, id }] if name == "trigger" && *id == Some(trigger_id))
        ),
        "4-arg CPS-if fallback should move else function and apply trigger, got: {else_branch:?}"
    );
}

#[test]
fn double_delayed_scott_encoding_moves_lambda_branch_and_preserves_ids() {
    let subject_id = VarId::from_raw(9940);
    let field_id = VarId::from_raw(9941);
    let body_id = VarId::from_raw(9942);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(
            PseudoExpr::var_with_id("subject", subject_id),
        )))),
        vec![PseudoExpr::Lambda {
            params: vec![Binder::new("field", field_id)],
            body: PBox::new(PseudoExpr::var_with_id("payload", body_id)),
        }],
    );

    let ApplyAction::Done(PseudoExpr::When {
        subject, clauses, ..
    }) = action
    else {
        panic!("expected double-delayed Scott encoding to rewrite to When");
    };
    assert!(
        matches!(
            subject.as_ref(),
            PseudoExpr::Var { name, id } if name == "subject" && *id == Some(subject_id)
        ),
        "Scott rewrite should preserve the subject id, got: {subject:?}"
    );
    assert_eq!(clauses.len(), 1);
    assert!(
        matches!(
            &clauses[0].pattern,
            WhenPattern::Constructor { fields, .. }
                if matches!(fields.as_slice(), [binder] if binder.as_str() == "field" && binder.id == field_id)
        ),
        "Scott rewrite should move lambda params into constructor fields, got: {:?}",
        clauses[0].pattern
    );
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::Var { name, id } if name == "payload" && *id == Some(body_id)
        ),
        "Scott rewrite should move lambda body with id intact, got: {:?}",
        clauses[0].body
    );
}

#[test]
fn double_delayed_scott_encoding_moves_bare_branch_and_preserves_ids() {
    let first_id = VarId::from_raw(9943);
    let second_id = VarId::from_raw(9944);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var(
            "subject",
        ))))),
        vec![
            PseudoExpr::var_with_id("first", first_id),
            PseudoExpr::var_with_id("second", second_id),
        ],
    );

    let ApplyAction::Done(PseudoExpr::When { clauses, .. }) = action else {
        panic!("expected double-delayed Scott encoding to rewrite to When");
    };
    assert_eq!(clauses.len(), 2);
    for (index, clause) in clauses.iter().enumerate() {
        assert!(
            matches!(
                &clause.pattern,
                WhenPattern::Constructor { shape, fields, .. }
                    if matches!(shape, ConstructorShape::Unknown { tag, arity, .. } if *tag == index && *arity == 0)
                        && fields.is_empty()
            ),
            "bare Scott branch should become a 0-field constructor clause, got: {:?}",
            clause.pattern
        );
    }
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::Var { name, id } if name == "first" && *id == Some(first_id)
        ),
        "Scott rewrite should move first bare branch with id intact, got: {:?}",
        clauses[0].body
    );
    assert!(
        matches!(
            &clauses[1].body,
            PseudoExpr::Var { name, id } if name == "second" && *id == Some(second_id)
        ),
        "Scott rewrite should move second bare branch with id intact, got: {:?}",
        clauses[1].body
    );
}

#[test]
fn apply_form_binop_moves_mixed_builtin_and_apply_args_preserving_order() {
    let left_id = VarId::from_raw(9955);
    let right_id = VarId::from_raw(9956);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Int.sub"),
            args: vec![PseudoExpr::var_with_id("left", left_id)].into(),
        },
        vec![PseudoExpr::var_with_id("right", right_id)],
    );

    let ApplyAction::Done(PseudoExpr::BinOp { op, left, right }) = action else {
        panic!("expected Apply-form Int.sub to become BinOp");
    };
    assert_eq!(op, BinaryOp::Sub);
    assert!(
        matches!(left.as_ref(), PseudoExpr::Var { name, id } if name == "left" && *id == Some(left_id)),
        "Apply-form BinOp should preserve builtin arg as left operand, got: {left:?}"
    );
    assert!(
        matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "right" && *id == Some(right_id)),
        "Apply-form BinOp should preserve apply arg as right operand, got: {right:?}"
    );
}

#[test]
fn apply_form_binop_moves_nullary_apply_args_and_preserves_ids() {
    let left_id = VarId::from_raw(9957);
    let right_id = VarId::from_raw(9958);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Int.add"),
            args: vec![].into(),
        },
        vec![
            PseudoExpr::var_with_id("left", left_id),
            PseudoExpr::var_with_id("right", right_id),
        ],
    );

    let ApplyAction::Done(PseudoExpr::BinOp { op, left, right }) = action else {
        panic!("expected Apply-form Int.add to become BinOp");
    };
    assert_eq!(op, BinaryOp::Add);
    assert!(
        matches!(left.as_ref(), PseudoExpr::Var { name, id } if name == "left" && *id == Some(left_id)),
        "Apply-form BinOp should move left apply arg intact, got: {left:?}"
    );
    assert!(
        matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "right" && *id == Some(right_id)),
        "Apply-form BinOp should move right apply arg intact, got: {right:?}"
    );
}

#[test]
fn apply_form_list_head_tail_depth_moves_subject_and_preserves_ids() {
    let xs_id = VarId::from_raw(9950);
    let action = Simplifier::with_safe_mode(false).simplify_apply_match(
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.head"),
            args: vec![].into(),
        },
        vec![PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("List.tail"),
                args: vec![].into(),
            }),
            args: vec![PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("List.tail"),
                    args: vec![].into(),
                }),
                args: vec![PseudoExpr::var_with_id("xs", xs_id)].into(),
            }]
            .into(),
        }],
    );

    let ApplyAction::Done(PseudoExpr::IndexAccess { collection, index }) = action else {
        panic!("expected Apply-form List.head traversal to become IndexAccess");
    };
    assert_eq!(index, 2);
    assert!(
        matches!(
            collection.as_ref(),
            PseudoExpr::Var { name, id } if name == "xs" && *id == Some(xs_id)
        ),
        "List.head traversal should move the final subject with id intact, got: {collection:?}"
    );
}
