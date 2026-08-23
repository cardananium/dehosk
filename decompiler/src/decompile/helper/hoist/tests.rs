use super::*;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

fn assert_hoist_idempotent(expr: PseudoExpr) {
    let (once, first_outcome) = run_hoist_local_helpers_fixed_point(expr);
    assert!(
        matches!(first_outcome, HoistFixedPointOutcome::Converged { .. }),
        "expected helper hoist to converge on first run, got {first_outcome:?}"
    );

    let (twice, second_outcome) = run_hoist_local_helpers_fixed_point(once.clone());
    assert!(
        matches!(
            second_outcome,
            HoistFixedPointOutcome::Converged { rounds: 1 }
        ),
        "expected second helper-hoist run to stabilize immediately, got {second_outcome:?}"
    );
    assert!(
        twice.structural_eq(&once),
        "helper hoist should be idempotent after convergence:\nfirst: {once:#?}\nsecond: {twice:#?}"
    );
}

#[test]
fn test_var_is_referenced() {
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(PseudoExpr::var("x")),
        right: PBox::new(PseudoExpr::var("y")),
    };
    assert!(var_is_referenced(&expr, "x"));
    assert!(var_is_referenced(&expr, "y"));
    assert!(!var_is_referenced(&expr, "z"));
}

#[test]
fn test_var_is_referenced_id_aware_ignores_shadowed_same_name_binding() {
    let outer_id = VarId::new(1);
    let inner_id = VarId::new(2);
    let expr = PseudoExpr::Let {
        name: "value".to_string(),
        id: Some(inner_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::var_with_id("value", inner_id)),
    };

    assert!(!var_is_referenced_id_aware(&expr, outer_id, "value"));
    assert!(var_is_referenced_id_aware(&expr, inner_id, "value"));
}

#[test]
fn test_var_is_referenced_id_aware_matches_unshadowed_compat_name() {
    let target_id = VarId::new(1);
    let expr = PseudoExpr::var("value");

    assert!(var_is_referenced_id_aware(&expr, target_id, "value"));
}

#[test]
fn test_var_is_referenced_id_aware_ignores_compat_name_shadowed_by_lambda_or_when_pattern() {
    let outer_id = VarId::new(1);
    let lambda_shadow_id = VarId::new(2);
    let pattern_shadow_id = VarId::new(3);

    let lambda_shadow = PseudoExpr::Lambda {
        params: vec![Binder::new("value", lambda_shadow_id)],
        body: PBox::new(PseudoExpr::var("value")),
    };
    assert!(!var_is_referenced_id_aware(
        &lambda_shadow,
        outer_id,
        "value"
    ));

    let when_pattern_shadow = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("subject")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Var(Binder::new("value", pattern_shadow_id)),
            PseudoExpr::var("value"),
        )],
    };
    assert!(!var_is_referenced_id_aware(
        &when_pattern_shadow,
        outer_id,
        "value"
    ));
}

#[test]
fn test_hoist_local_helpers_hoists_inner_recfn_from_let_value() {
    let inner_helper = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "helper".to_string().into(),
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("helper")),
            args: vec![PseudoExpr::int(1)].into(),
        }),
    };

    let expr = PseudoExpr::Let {
        name: "result".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(inner_helper),
        body: PBox::new(PseudoExpr::var("result")),
    };

    let result = hoist_local_helpers(expr);

    if let PseudoExpr::Let {
        name, value, body, ..
    } = result
    {
        assert_eq!(name, "helper");
        assert!(matches!(value.as_ref(), PseudoExpr::RecFn { .. }));
        assert!(matches!(body.as_ref(), PseudoExpr::Let { .. }));
    } else {
        panic!("expected helper binding to be hoisted");
    }
}

#[test]
fn test_hoist_local_helpers_hoists_helper_chain_out_of_let_value() {
    let helper_id = VarId::fresh_compat_placeholder();
    let bool_id = VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "cond_ok".to_string(),
        id: Some(bool_id),
        value: PBox::new(PseudoExpr::Let {
            name: "decode".to_string(),
            id: Some(helper_id),
            value: PBox::new(PseudoExpr::RecFn {
                name: "decode".to_string().into(),
                params: vec!["xs".to_string().into()],
                body: PBox::new(PseudoExpr::var("xs")),
            }),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("decode")),
                    args: vec![PseudoExpr::list(vec![])].into(),
                }),
                right: PBox::new(PseudoExpr::list(vec![])),
            }),
        }),
        body: PBox::new(PseudoExpr::var("cond_ok")),
    };

    let result = hoist_local_helpers(expr);

    match result {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "decode");
            assert!(matches!(value.as_ref(), PseudoExpr::RecFn { .. }));
            assert!(matches!(
                body.as_ref(),
                PseudoExpr::Let {
                    name,
                    value,
                    body,
                    ..
                } if name == "cond_ok"
                    && matches!(value.as_ref(), PseudoExpr::BinOp { .. })
                    && matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "cond_ok")
            ));
        }
        other => panic!("expected helper chain to hoist out of let value, got: {other:?}"),
    }
}

#[test]
fn test_hoist_local_helpers_hoists_helper_from_binop_operand() {
    let expr = PseudoExpr::Lambda {
        params: vec!["redeemer".to_string().into()],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Or,
            left: PBox::new(PseudoExpr::Bool(false)),
            right: PBox::new(PseudoExpr::Let {
                name: "decode".to_string(),
                id: Some(VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::RecFn {
                    name: "decode".to_string().into(),
                    params: vec!["xs".to_string().into()],
                    body: PBox::new(PseudoExpr::var("xs")),
                }),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("decode")),
                    args: vec![PseudoExpr::var("redeemer")].into(),
                }),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    match result {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "decode");
            assert!(matches!(value.as_ref(), PseudoExpr::RecFn { .. }));
            assert!(matches!(
                body.as_ref(),
                PseudoExpr::Lambda { body, .. }
                    if matches!(
                        body.as_ref(),
                        PseudoExpr::BinOp {
                            op: BinaryOp::Or,
                            right,
                            ..
                        } if matches!(
                            right.as_ref(),
                            PseudoExpr::Apply { function, .. }
                                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "decode")
                        )
                    )
            ));
        }
        other => panic!("expected helper to hoist out of binop operand, got: {other:?}"),
    }
}

#[test]
fn test_hoist_local_helpers_preserves_capture_identity_across_helper_param_and_call_site() {
    let outer_id = VarId::new(950);
    let helper_param_id = VarId::new(951);

    let expr = PseudoExpr::Let {
        name: "seed".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "helper".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "helper".to_string().into(),
                params: vec![Binder::new("x", helper_param_id)],
                body: PBox::new(PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::Bool(false)),
                    then_branch: PBox::new(PseudoExpr::var_with_id("seed", outer_id)),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("helper")),
                        args: vec![PseudoExpr::var_with_id("x", helper_param_id)].into(),
                    }),
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("helper")),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    let PseudoExpr::Let {
        name: helper_name,
        value: helper_value,
        body: helper_outer_body,
        ..
    } = result
    else {
        panic!("expected helper binding to be hoisted");
    };
    assert_eq!(helper_name, "helper");

    let PseudoExpr::RecFn {
        params: helper_params,
        body: helper_body,
        ..
    } = helper_value.as_ref()
    else {
        panic!("expected hoisted helper recfn, got: {helper_value:?}");
    };
    let capture_param = helper_params
        .last()
        .expect("expected helper hoist to append captured seed param");
    assert_eq!(capture_param.as_str(), "seed");

    let PseudoExpr::If {
        then_branch,
        else_branch,
        ..
    } = helper_body.as_ref()
    else {
        panic!("expected helper body to stay conditional, got: {helper_body:?}");
    };
    assert!(
        matches!(
            then_branch.as_ref(),
            PseudoExpr::Var { name, id, .. }
                if name == "seed" && id.get() == Some(capture_param.id)
        ),
        "expected captured seed ref in helper body to retarget to helper param id, got: {then_branch:?}"
    );
    let PseudoExpr::Apply {
        args: helper_recursive_args,
        ..
    } = else_branch.as_ref()
    else {
        panic!("expected recursive helper call, got: {else_branch:?}");
    };
    assert!(
        matches!(
            helper_recursive_args.get(1),
            Some(PseudoExpr::Var { name, id, .. })
                if name == "seed" && id.get() == Some(capture_param.id)
        ),
        "expected recursive helper call to pass helper param id, got: {:?}",
        helper_recursive_args.get(1)
    );

    let PseudoExpr::Let {
        body: lifted_call_body,
        ..
    } = helper_outer_body.as_ref()
    else {
        panic!("expected lifted outer let after helper hoist, got: {helper_outer_body:?}");
    };
    let PseudoExpr::Apply {
        args: lifted_call_args,
        ..
    } = lifted_call_body.as_ref()
    else {
        panic!("expected helper call in lifted body, got: {lifted_call_body:?}");
    };
    assert!(
        matches!(
            lifted_call_args.get(1),
            Some(PseudoExpr::Var { name, id, .. })
                if name == "seed" && id.get() == Some(outer_id)
        ),
        "expected lifted helper call to preserve outer let VarId, got: {:?}",
        lifted_call_args.get(1)
    );
}

#[test]
fn test_hoist_local_helpers_retargets_compat_name_capture_to_capture_param() {
    let outer_id = VarId::new(954);
    let helper_param_id = VarId::new(955);

    let expr = PseudoExpr::Let {
        name: "seed".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "helper".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "helper".to_string().into(),
                params: vec![Binder::new("x", helper_param_id)],
                body: PBox::new(PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::Bool(false)),
                    then_branch: PBox::new(PseudoExpr::var("seed")),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("helper")),
                        args: vec![PseudoExpr::var_with_id("x", helper_param_id)].into(),
                    }),
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("helper")),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    let PseudoExpr::Let {
        value: helper_value,
        body: helper_outer_body,
        ..
    } = result
    else {
        panic!("expected helper binding to be hoisted");
    };

    let PseudoExpr::RecFn {
        params: helper_params,
        body: helper_body,
        ..
    } = helper_value.as_ref()
    else {
        panic!("expected hoisted helper recfn, got: {helper_value:?}");
    };
    let capture_param = helper_params
        .last()
        .expect("expected helper hoist to append captured seed param");
    assert_eq!(capture_param.as_str(), "seed");
    assert_ne!(
        capture_param.id, outer_id,
        "helper-local capture param must get a fresh id"
    );

    let PseudoExpr::If {
        then_branch,
        else_branch,
        ..
    } = helper_body.as_ref()
    else {
        panic!("expected helper body to stay conditional, got: {helper_body:?}");
    };
    assert!(
        matches!(
            then_branch.as_ref(),
            PseudoExpr::Var { name, id, .. }
                if name == "seed" && *id == Some(capture_param.id)
        ),
        "expected compat seed capture to retarget to helper param id, got: {then_branch:?}"
    );
    let PseudoExpr::Apply {
        args: helper_recursive_args,
        ..
    } = else_branch.as_ref()
    else {
        panic!("expected recursive helper call, got: {else_branch:?}");
    };
    assert!(
        matches!(
            helper_recursive_args.get(1),
            Some(PseudoExpr::Var { name, id, .. })
                if name == "seed" && *id == Some(capture_param.id)
        ),
        "expected recursive helper call to pass helper param id, got: {:?}",
        helper_recursive_args.get(1)
    );

    let PseudoExpr::Let {
        body: lifted_call_body,
        ..
    } = helper_outer_body.as_ref()
    else {
        panic!("expected lifted outer let after helper hoist, got: {helper_outer_body:?}");
    };
    let PseudoExpr::Apply {
        args: lifted_call_args,
        ..
    } = lifted_call_body.as_ref()
    else {
        panic!("expected helper call in lifted body, got: {lifted_call_body:?}");
    };
    assert!(
        matches!(
            lifted_call_args.get(1),
            Some(PseudoExpr::Var { name, id, .. }) if name == "seed" && *id == Some(outer_id)
        ),
        "expected lifted helper call to pass the original outer id, got: {:?}",
        lifted_call_args.get(1)
    );
}

#[test]
fn test_hoist_local_helpers_preserves_compat_outer_capture_id_at_lifted_call_site() {
    let outer_id = VarId::fresh_compat_placeholder();
    let helper_param_id = VarId::new(952);
    assert!(outer_id.is_compat_placeholder());

    let expr = PseudoExpr::Let {
        name: "seed".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "helper".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "helper".to_string().into(),
                params: vec![Binder::new("x", helper_param_id)],
                body: PBox::new(PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::Bool(false)),
                    then_branch: PBox::new(PseudoExpr::var_with_id("seed", outer_id)),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("helper")),
                        args: vec![PseudoExpr::var_with_id("x", helper_param_id)].into(),
                    }),
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("helper")),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    let PseudoExpr::Let {
        body: helper_outer_body,
        ..
    } = result
    else {
        panic!("expected helper binding to be hoisted");
    };
    let PseudoExpr::Let {
        id: Some(lifted_outer_id),
        body: lifted_call_body,
        ..
    } = helper_outer_body.as_ref()
    else {
        panic!("expected lifted outer let after helper hoist, got: {helper_outer_body:?}");
    };
    assert_eq!(
        *lifted_outer_id, outer_id,
        "expected helper hoist to preserve the existing compat outer let id"
    );
    let PseudoExpr::Apply {
        args: lifted_call_args,
        ..
    } = lifted_call_body.as_ref()
    else {
        panic!("expected helper call in lifted body, got: {lifted_call_body:?}");
    };
    assert!(
        matches!(
            lifted_call_args.get(1),
            Some(PseudoExpr::Var { name, id, .. }) if name == "seed" && *id == Some(outer_id)
        ),
        "expected lifted helper call to keep the original compat outer id, got: {:?}",
        lifted_call_args.get(1)
    );
}

#[test]
fn test_helper_is_direct_call_only_treats_authoritative_same_name_non_helper_as_unrelated() {
    let helper_id = VarId::fresh_binding();
    let foreign_id = VarId::fresh_binding();
    let foreign_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("helper", foreign_id)),
        args: vec![PseudoExpr::int(1)].into(),
    };

    assert!(helper_is_direct_call_only(
        &foreign_call,
        "helper",
        helper_id,
        1
    ));
    assert!(!helper_is_direct_call_only(
        &PseudoExpr::var_with_id("helper", helper_id),
        "helper",
        helper_id,
        1
    ));
}

#[test]
fn test_append_helper_call_args_ignores_authoritative_same_name_non_helper_call() {
    let helper_id = VarId::fresh_binding();
    let foreign_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("helper", foreign_id)),
        args: vec![PseudoExpr::int(1)].into(),
    };

    let rewritten = append_helper_call_args(&expr, "helper", helper_id, 1, &[PseudoExpr::int(2)]);

    let PseudoExpr::Apply { function, args } = rewritten else {
        panic!("expected apply after rewrite");
    };
    assert!(matches!(
        function.as_ref(),
        PseudoExpr::Var { name, id, .. } if name == "helper" && *id == Some(foreign_id)
    ));
    assert_eq!(
        args.len(),
        1,
        "expected foreign same-name call to keep its original arity"
    );
}

#[test]
fn test_append_helper_call_args_appends_capture_arg_to_compat_helper_call() {
    let helper_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("helper")),
        args: vec![PseudoExpr::int(1)].into(),
    };

    let rewritten = append_helper_call_args(&expr, "helper", helper_id, 1, &[PseudoExpr::int(2)]);

    let PseudoExpr::Apply { function, args } = rewritten else {
        panic!("expected apply after rewrite");
    };
    assert!(matches!(
        function.as_ref(),
        PseudoExpr::Var { name, id, .. } if name == "helper" && id.get().is_none()
    ));
    assert_eq!(
        args.len(),
        2,
        "expected compat helper call to receive the capture arg"
    );
    assert_eq!(args.get(1), Some(&PseudoExpr::int(2)));
}

#[test]
fn test_hoist_local_helpers_does_not_append_capture_arg_to_authoritative_same_name_non_helper_call()
{
    let seed_id = VarId::fresh_binding();
    let helper_id = VarId::fresh_binding();
    let helper_param_id = VarId::fresh_binding();
    let foreign_helper_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "seed".to_string(),
        id: Some(seed_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "helper".to_string(),
            id: Some(helper_id),
            value: PBox::new(PseudoExpr::RecFn {
                name: Binder::new("helper", helper_id),
                params: vec![Binder::new("x", helper_param_id)],
                body: PBox::new(PseudoExpr::var_with_id("seed", seed_id)),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("helper", foreign_helper_id)),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    let PseudoExpr::Let {
        name,
        id,
        value,
        body,
    } = result
    else {
        panic!("expected helper binding to be hoisted");
    };
    assert_eq!(name, "helper");
    assert_eq!(id, Some(helper_id));
    let PseudoExpr::RecFn { params, .. } = value.as_ref() else {
        panic!("expected hoisted helper recfn, got: {value:?}");
    };
    assert_eq!(
        params.len(),
        2,
        "expected helper hoist to append the captured seed parameter"
    );
    let PseudoExpr::Let {
        id: Some(lifted_seed_id),
        body: lifted_call_body,
        ..
    } = body.as_ref()
    else {
        panic!("expected lifted seed let after helper hoist, got: {body:?}");
    };
    assert_eq!(*lifted_seed_id, seed_id);
    let PseudoExpr::Apply {
        function,
        args: lifted_call_args,
    } = lifted_call_body.as_ref()
    else {
        panic!("expected foreign helper call in lifted body, got: {lifted_call_body:?}");
    };
    assert!(matches!(
        function.as_ref(),
        PseudoExpr::Var { name, id, .. } if name == "helper" && *id == Some(foreign_helper_id)
    ));
    assert_eq!(
        lifted_call_args.len(),
        1,
        "expected hoist to leave the foreign same-name call arity unchanged"
    );
}

#[test]
fn test_hoist_local_helpers_hoists_clause_local_recfn() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("pairs")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::Bool(false),
            ),
            WhenClause::new(
                WhenPattern::Wildcard,
                PseudoExpr::Let {
                    name: "lookup_2".to_string(),
                    id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                    value: PBox::new(PseudoExpr::RecFn {
                        name: "lookup_2".to_string().into(),
                        params: vec!["xs".to_string().into(), "needle".to_string().into()],
                        body: PBox::new(PseudoExpr::var("needle")),
                    }),
                    body: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("lookup_2")),
                        args: vec![PseudoExpr::var("pairs"), PseudoExpr::var("needle")].into(),
                    }),
                },
            ),
        ],
    };

    let result = hoist_local_helpers(expr);

    match result {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "lookup_2");
            assert!(matches!(body.as_ref(), PseudoExpr::When { .. }));
        }
        _ => panic!("expected clause helper to be hoisted before when"),
    }
}

#[test]
fn test_hoist_local_helpers_lambda_lifts_capture_across_outer_let() {
    let outer_capture_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let expr = PseudoExpr::Let {
        name: "captured".to_string(),
        id: Some(outer_capture_id),
        value: PBox::new(PseudoExpr::ByteArray(vec![0xaa; 28])),
        body: PBox::new(PseudoExpr::Let {
            name: "lookup".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "lookup".to_string().into(),
                params: vec!["xs".to_string().into()],
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("xs")),
                    subject_name: None,
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            PseudoExpr::Bool(false),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec!["head".into()],
                                tail: Some("tail".into()),
                            },
                            PseudoExpr::If {
                                condition: PBox::new(PseudoExpr::BinOp {
                                    op: BinaryOp::Eq,
                                    left: PBox::new(PseudoExpr::var("captured")),
                                    right: PBox::new(PseudoExpr::var("head")),
                                }),
                                then_branch: PBox::new(PseudoExpr::Bool(true)),
                                else_branch: PBox::new(PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("lookup")),
                                    args: vec![PseudoExpr::var("tail")].into(),
                                }),
                            },
                        ),
                    ],
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("lookup")),
                args: vec![PseudoExpr::var("items")].into(),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    match result {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "lookup");
            let helper_capture_id = match value.as_ref() {
                PseudoExpr::RecFn { params, body, .. } => {
                    let capture_param = params
                        .last()
                        .expect("expected hoisted helper to append captured binder");
                    assert_eq!(capture_param.as_str(), "captured");
                    assert!(matches!(
                        body.as_ref(),
                        PseudoExpr::When { clauses, .. }
                            if matches!(
                                &clauses[1].body,
                                PseudoExpr::If { else_branch, .. }
                                    if matches!(
                                        else_branch.as_ref(),
                                        PseudoExpr::Apply { function, args }
                                            if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "lookup")
                                                && matches!(
                                                    args.as_slice(),
                                                    [
                                                        PseudoExpr::Var { name: tail_name, .. },
                                                        PseudoExpr::Var { name: captured_name, id, .. },
                                                    ] if tail_name == "tail"
                                                        && captured_name == "captured"
                                                        && id.get() == Some(capture_param.id)
                                                )
                                    )
                            )
                    ));
                    capture_param.id
                }
                other => panic!("expected lifted recfn, got: {other:?}"),
            };
            match value.as_ref() {
                PseudoExpr::RecFn { params, .. } => assert_eq!(params, &["xs", "captured"]),
                other => panic!("expected lifted recfn, got: {other:?}"),
            }
            assert!(matches!(
                body.as_ref(),
                PseudoExpr::Let { name: captured_name, id, body, .. }
                    if captured_name == "captured"
                        && *id == Some(outer_capture_id)
                        && *id != Some(helper_capture_id)
                        && matches!(
                            body.as_ref(),
                            PseudoExpr::Apply { function, args }
                                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "lookup")
                                    && matches!(
                                        args.as_slice(),
                                        [
                                            PseudoExpr::Var { name: items_name, .. },
                                            PseudoExpr::Var { name: captured_arg, id: arg_id, .. },
                                        ] if items_name == "items"
                                            && captured_arg == "captured"
                                            && arg_id.get() == id.get()
                                    )
                        )
            ));
        }
        other => panic!("expected helper to lift above captured let, got: {other:?}"),
    }
}

#[test]
fn test_hoist_local_helpers_hoists_closed_helper_out_of_root_lambda() {
    let expr = PseudoExpr::Lambda {
        params: vec!["redeemer".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "lookup".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "lookup".to_string().into(),
                params: vec!["xs".to_string().into()],
                body: PBox::new(PseudoExpr::var("xs")),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("lookup")),
                args: vec![PseudoExpr::var("redeemer")].into(),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    match result {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "lookup");
            assert!(matches!(value.as_ref(), PseudoExpr::RecFn { .. }));
            assert!(matches!(
                body.as_ref(),
                PseudoExpr::Lambda { body, .. }
                    if matches!(
                        body.as_ref(),
                        PseudoExpr::Apply { function, .. }
                            if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "lookup")
                    )
            ));
        }
        other => panic!("expected root helper to lift outside lambda, got: {other:?}"),
    }
}

#[test]
fn test_hoist_local_helpers_hoists_closed_helper_out_of_recfn_value() {
    let expr = PseudoExpr::Let {
        name: "cond_ok".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "decode_credential_10".to_string().into(),
            params: vec!["xs".to_string().into()],
            body: PBox::new(PseudoExpr::Let {
                name: "decode_credential_14".to_string(),
                id: Some(VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::RecFn {
                    name: "decode_credential_14".to_string().into(),
                    params: vec!["ys".to_string().into()],
                    body: PBox::new(PseudoExpr::var("ys")),
                }),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("decode_credential_14")),
                    args: vec![PseudoExpr::var("xs")].into(),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::var("cond_ok")),
    };

    let result = hoist_local_helpers(expr);

    match result {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "decode_credential_14");
            assert!(matches!(value.as_ref(), PseudoExpr::RecFn { .. }));
            assert!(matches!(
                body.as_ref(),
                PseudoExpr::Let {
                    name,
                    value,
                    ..
                } if name == "cond_ok" && matches!(value.as_ref(), PseudoExpr::RecFn { .. })
            ));
        }
        other => panic!("expected helper to hoist out of recfn value, got: {other:?}"),
    }
}

#[test]
fn test_hoist_local_helpers_hoists_closed_helper_out_of_if_apply_arg_past_constant_let() {
    let expr = PseudoExpr::RecFn {
        name: "outer".to_string().into(),
        params: vec!["xs".to_string().into(), "acc".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("xs")),
            subject_name: Some("xs".to_string().into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::var("acc"),
                ),
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec!["head".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::let_bind(
                        "data_const",
                        PseudoExpr::int(1),
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("outer")),
                            args: vec![
                                PseudoExpr::var("tail"),
                                PseudoExpr::If {
                                    condition: PBox::new(PseudoExpr::Bool(true)),
                                    then_branch: PBox::new(PseudoExpr::let_bind(
                                        "helper",
                                        PseudoExpr::RecFn {
                                            name: "helper".to_string().into(),
                                            params: vec![
                                                "list".to_string().into(),
                                                "acc_2".to_string().into(),
                                            ],
                                            body: PBox::new(PseudoExpr::var("acc_2")),
                                        },
                                        PseudoExpr::Apply {
                                            function: PBox::new(PseudoExpr::var("helper")),
                                            args: vec![
                                                PseudoExpr::var("acc"),
                                                PseudoExpr::var("data_const"),
                                            ]
                                            .into(),
                                        },
                                    )),
                                    else_branch: PBox::new(PseudoExpr::var("acc")),
                                },
                            ]
                            .into(),
                        },
                    ),
                ),
            ],
        }),
    };

    let result = hoist_local_helpers(expr);
    let rendered = crate::decompile::render::PrettyPrinter::new().print(&result);
    assert!(
        rendered.contains("rec fn helper(")
            && rendered.contains("let data_const = 1")
            && !rendered.contains("if True {\n      rec fn helper("),
        "expected helper to hoist out of if/apply and past constant let, got:\n{rendered}"
    );
}

#[test]
fn test_hoist_local_helpers_freshens_hoisted_apply_arg_helper_shadowed_by_param() {
    let param_id = VarId::fresh_binding();
    let helper_id = VarId::fresh_binding();
    let helper_param_id = VarId::fresh_binding();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x", param_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![
                PseudoExpr::Let {
                    name: "x".to_string(),
                    id: Some(helper_id),
                    value: PBox::new(PseudoExpr::Lambda {
                        params: vec![Binder::new("y", helper_param_id)],
                        body: PBox::new(PseudoExpr::var_with_id("y", helper_param_id)),
                    }),
                    body: PBox::new(PseudoExpr::var_with_id("x", helper_id)),
                },
                PseudoExpr::var_with_id("x", param_id),
            ]
            .into(),
        }),
    };

    let result = hoist_local_helpers(expr.clone());
    assert_hoist_idempotent(expr);

    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "hoisting a helper let across apply siblings should freshen the hoisted helper display name"
    );
    let PseudoExpr::Let {
        name: helper_name,
        id,
        body,
        ..
    } = result
    else {
        panic!("expected helper hoist to move the helper let above the lambda");
    };
    assert_eq!(id, Some(helper_id));
    assert_ne!(
        helper_name, "x",
        "hoisted helper display name must not be shadowed by the lambda param"
    );

    let PseudoExpr::Lambda { body, .. } = body.as_ref() else {
        panic!("expected lambda under hoisted helper let, got: {body:?}");
    };
    let PseudoExpr::Apply { args, .. } = body.as_ref() else {
        panic!("expected apply body under lambda, got: {body:?}");
    };
    assert!(
        matches!(
            args.first(),
            Some(PseudoExpr::Var { name, id, .. })
                if name == &helper_name && *id == Some(helper_id)
        ),
        "expected helper use to keep helper VarId and adopt fresh display name, got: {:?}",
        args.first()
    );
    assert!(
        matches!(
            args.get(1),
            Some(PseudoExpr::Var { name, id, .. }) if name == "x" && *id == Some(param_id)
        ),
        "expected lambda param use to remain untouched, got: {:?}",
        args.get(1)
    );
}

#[test]
fn test_hoist_local_helpers_does_not_produce_consistent_ref_ids_from_stale_input() {
    let outer_id = VarId::fresh_binding();
    let stale_ref_id = VarId::fresh_binding();
    let helper_id = VarId::fresh_binding();
    let helper_param_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
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
    };
    assert!(
        crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr),
        "fixture must start with a stale same-name ref"
    );

    let result = hoist_local_helpers(expr.clone());

    assert!(
        !result.structural_eq(&expr),
        "fixture must exercise an actual helper-hoist rewrite"
    );
    assert!(
        crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "helper hoist moves helper lets but does not repair unrelated stale refs"
    );
}

#[test]
fn test_canonicalize_inverted_recfn_let_does_not_capture_authoritative_outer_same_name_call() {
    let outer_id = VarId::new(9510);
    let outer_param_id = VarId::new(9511);
    let inner_id = VarId::new(9512);
    let fn_id = VarId::new(9513);
    let fn_param_id = VarId::new(9514);

    let value = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("helper", outer_id)),
        args: vec![PseudoExpr::int(1)].into(),
    };
    let body = PseudoExpr::RecFn {
        name: Binder::new("helper", fn_id),
        params: vec![Binder::new("x", fn_param_id)],
        body: PBox::new(PseudoExpr::var_with_id("x", fn_param_id)),
    };
    let fixture = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("payload", outer_param_id)],
            body: PBox::new(PseudoExpr::var_with_id("payload", outer_param_id)),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "helper".to_string(),
            id: Some(inner_id),
            value: PBox::new(value.clone()),
            body: PBox::new(body.clone()),
        }),
    };
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&fixture),
        "fixture should start with an authoritative outer same-name call that is already scope-consistent"
    );

    let canonical =
        canonicalize_inverted_recfn_let("helper".to_string(), Some(inner_id), &value, &body);

    assert!(
        canonical.is_none(),
        "canonicalization must not rewrite an authoritative outer call to the inner helper let"
    );
}

#[test]
fn test_hoist_local_helpers_normalizes_and_hoists_inverted_recfn_helper_from_if_apply_arg() {
    let expr = PseudoExpr::RecFn {
        name: "outer".to_string().into(),
        params: vec!["xs".to_string().into(), "acc".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("xs")),
            subject_name: Some("xs".to_string().into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::var("acc"),
                ),
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec!["head".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::let_bind(
                        "data_const",
                        PseudoExpr::int(1),
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("outer")),
                            args: vec![
                                PseudoExpr::var("tail"),
                                PseudoExpr::If {
                                    condition: PBox::new(PseudoExpr::Bool(true)),
                                    then_branch: PBox::new(PseudoExpr::let_bind(
                                        "helper",
                                        PseudoExpr::Apply {
                                            function: PBox::new(PseudoExpr::var("helper")),
                                            args: vec![
                                                PseudoExpr::var("acc"),
                                                PseudoExpr::var("data_const"),
                                            ]
                                            .into(),
                                        },
                                        PseudoExpr::RecFn {
                                            name: "helper".to_string().into(),
                                            params: vec![
                                                "list".to_string().into(),
                                                "acc_2".to_string().into(),
                                            ],
                                            body: PBox::new(PseudoExpr::var("acc_2")),
                                        },
                                    )),
                                    else_branch: PBox::new(PseudoExpr::var("acc")),
                                },
                            ]
                            .into(),
                        },
                    ),
                ),
            ],
        }),
    };

    let result = hoist_local_helpers(expr);
    let rendered = crate::decompile::render::PrettyPrinter::new().print(&result);
    assert!(
        rendered.contains("rec fn helper(")
            && rendered.contains("let data_const = 1")
            && !rendered.contains("if True {\n      rec fn helper(")
            && !rendered.contains("let helper = helper("),
        "expected inverted helper let to normalize and hoist out of if/apply, got:\n{rendered}"
    );
}

#[test]
fn test_hoist_local_helpers_keeps_root_lambda_helper_that_captures_param() {
    let expr = PseudoExpr::Lambda {
        params: vec!["seed".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "lookup".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "lookup".to_string().into(),
                params: vec!["xs".to_string().into()],
                body: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::var("seed")),
                    right: PBox::new(PseudoExpr::var("xs")),
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("lookup")),
                args: vec![PseudoExpr::var("seed")].into(),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    assert!(matches!(
        result,
        PseudoExpr::Lambda { body, .. }
            if matches!(body.as_ref(), PseudoExpr::Let { name, .. } if name == "lookup")
    ));
}

#[test]
fn test_hoist_local_helpers_hoists_root_lambda_helper_chain_without_main_captures() {
    let expr = PseudoExpr::Lambda {
        params: vec!["redeemer".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "lookup".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "lookup".to_string().into(),
                params: vec!["pairs".to_string().into()],
                body: PBox::new(PseudoExpr::var("pairs")),
            }),
            body: PBox::new(PseudoExpr::Let {
                name: "decode".to_string(),
                id: Some(VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::RecFn {
                    name: "decode".to_string().into(),
                    params: vec!["pairs".to_string().into()],
                    body: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("lookup")),
                        args: vec![PseudoExpr::var("pairs")].into(),
                    }),
                }),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("decode")),
                    args: vec![PseudoExpr::var("redeemer")].into(),
                }),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    match result {
        PseudoExpr::Let {
            name: first_name,
            body: first_body,
            ..
        } => match first_body.as_ref() {
            PseudoExpr::Let {
                name: second_name,
                body: lambda_body,
                ..
            } => {
                let mut helper_names = vec![first_name.clone(), second_name.clone()];
                helper_names.sort();
                assert_eq!(
                    helper_names,
                    vec!["decode".to_string(), "lookup".to_string()]
                );
                assert!(matches!(
                    lambda_body.as_ref(),
                    PseudoExpr::Lambda { body, .. }
                        if matches!(
                            body.as_ref(),
                            PseudoExpr::Apply { function, .. }
                                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "decode")
                        )
                ));
            }
            other => {
                panic!("expected second helper to remain hoisted after first, got: {other:?}")
            }
        },
        other => panic!("expected helper chain to lift outside lambda, got: {other:?}"),
    }
}

#[test]
fn test_hoist_local_helpers_hoists_root_lambda_helpers_past_non_helper_lets() {
    let expr = PseudoExpr::Lambda {
        params: vec!["script_context".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "purpose".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("script_context"),
                "purpose".to_string(),
            )),
            body: PBox::new(PseudoExpr::Let {
                name: "lookup".to_string(),
                id: Some(VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::RecFn {
                    name: "lookup".to_string().into(),
                    params: vec!["pairs".to_string().into()],
                    body: PBox::new(PseudoExpr::var("pairs")),
                }),
                body: PBox::new(PseudoExpr::Let {
                    name: "get_at".to_string(),
                    id: Some(VarId::fresh_compat_placeholder()),
                    value: PBox::new(PseudoExpr::RecFn {
                        name: "get_at".to_string().into(),
                        params: vec!["list".to_string().into()],
                        body: PBox::new(PseudoExpr::var("list")),
                    }),
                    body: PBox::new(PseudoExpr::Tuple(
                        vec![
                            PseudoExpr::var("purpose"),
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("lookup")),
                                args: vec![PseudoExpr::var("purpose")].into(),
                            },
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("get_at")),
                                args: vec![PseudoExpr::var("purpose")].into(),
                            },
                        ]
                        .into(),
                    )),
                }),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    match result {
        PseudoExpr::Let {
            name,
            body: lookup_body,
            ..
        } => {
            assert_eq!(name, "lookup");
            match lookup_body.as_ref() {
                PseudoExpr::Let {
                    name,
                    body: lambda_body,
                    ..
                } => {
                    assert_eq!(name, "get_at");
                    assert!(matches!(
                        lambda_body.as_ref(),
                        PseudoExpr::Lambda { body, .. }
                            if matches!(
                                body.as_ref(),
                                PseudoExpr::Let { name, .. } if name == "purpose"
                            )
                    ));
                }
                other => panic!("expected get_at to hoist after lookup, got: {other:?}"),
            }
        }
        other => panic!("expected helper lets to hoist outside lambda, got: {other:?}"),
    }
}

#[test]
fn test_hoist_local_helpers_hoists_closed_helper_from_expect_argument_out_of_root_lambda() {
    let expr = PseudoExpr::Lambda {
        params: vec!["script_context".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "purpose".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("script_context"),
                "purpose".to_string(),
            )),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("expect!")),
                args: vec![PseudoExpr::Let {
                    name: "find_2".to_string(),
                    id: Some(VarId::fresh_compat_placeholder()),
                    value: PBox::new(PseudoExpr::RecFn {
                        name: "find_2".to_string().into(),
                        params: vec!["xs".to_string().into()],
                        body: PBox::new(PseudoExpr::var("xs")),
                    }),
                    body: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("find_2")),
                        args: vec![PseudoExpr::var("purpose")].into(),
                    }),
                }]
                .into(),
            }),
        }),
    };

    let result = hoist_local_helpers(expr);

    match result {
        PseudoExpr::Let {
            name,
            body: lambda_body,
            ..
        } => {
            assert_eq!(name, "find_2");
            assert!(matches!(
                lambda_body.as_ref(),
                PseudoExpr::Lambda { body, .. }
                    if matches!(
                        body.as_ref(),
                        PseudoExpr::Let { name, body, .. }
                            if name == "purpose"
                                && matches!(
                                    body.as_ref(),
                                    PseudoExpr::Apply { function, args }
                                        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "expect!")
                                            && matches!(
                                                args.as_slice(),
                                                [PseudoExpr::Apply { function, .. }]
                                                    if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "find_2")
                                            )
                                )
                    )
            ));
        }
        other => {
            panic!("expected helper from expect! argument to hoist outside lambda, got: {other:?}")
        }
    }
}

#[test]
fn test_hoist_local_helpers_fixed_point_converges_without_budget_on_root_lambda_chain() {
    let expr = PseudoExpr::Lambda {
        params: vec!["script_context".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "purpose".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::field_access(
                PseudoExpr::var("script_context"),
                "purpose".to_string(),
            )),
            body: PBox::new(PseudoExpr::Let {
                name: "lookup".to_string(),
                id: Some(VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::RecFn {
                    name: "lookup".to_string().into(),
                    params: vec!["pairs".to_string().into()],
                    body: PBox::new(PseudoExpr::var("pairs")),
                }),
                body: PBox::new(PseudoExpr::Let {
                    name: "get_at".to_string(),
                    id: Some(VarId::fresh_compat_placeholder()),
                    value: PBox::new(PseudoExpr::RecFn {
                        name: "get_at".to_string().into(),
                        params: vec!["list".to_string().into()],
                        body: PBox::new(PseudoExpr::var("list")),
                    }),
                    body: PBox::new(PseudoExpr::Tuple(
                        vec![
                            PseudoExpr::var("purpose"),
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("lookup")),
                                args: vec![PseudoExpr::var("purpose")].into(),
                            },
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("get_at")),
                                args: vec![PseudoExpr::var("purpose")].into(),
                            },
                        ]
                        .into(),
                    )),
                }),
            }),
        }),
    };

    let (result, outcome) = run_hoist_local_helpers_fixed_point(expr);
    assert!(
        matches!(outcome, HoistFixedPointOutcome::Converged { rounds } if rounds >= 2),
        "expected multi-round convergence without a fixed budget, got {outcome:?}"
    );
    assert!(matches!(result, PseudoExpr::Let { .. }));
}

#[test]
fn test_hoist_local_helpers_idempotent_after_nested_let_value_extraction() {
    let expr = PseudoExpr::Let {
        name: "cond_ok".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Let {
            name: "decode".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "decode".to_string().into(),
                params: vec!["xs".to_string().into()],
                body: PBox::new(PseudoExpr::var("xs")),
            }),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("decode")),
                    args: vec![PseudoExpr::list(vec![])].into(),
                }),
                right: PBox::new(PseudoExpr::list(vec![])),
            }),
        }),
        body: PBox::new(PseudoExpr::var("cond_ok")),
    };

    assert_hoist_idempotent(expr);
}

#[test]
fn test_hoist_local_helpers_idempotent_after_capture_lifting() {
    let expr = PseudoExpr::Let {
        name: "captured".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::ByteArray(vec![0xaa; 28])),
        body: PBox::new(PseudoExpr::Let {
            name: "lookup".to_string(),
            id: Some(VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::RecFn {
                name: "lookup".to_string().into(),
                params: vec!["xs".to_string().into()],
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("xs")),
                    subject_name: None,
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            PseudoExpr::Bool(false),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec!["head".into()],
                                tail: Some("tail".into()),
                            },
                            PseudoExpr::If {
                                condition: PBox::new(PseudoExpr::BinOp {
                                    op: BinaryOp::Eq,
                                    left: PBox::new(PseudoExpr::var("captured")),
                                    right: PBox::new(PseudoExpr::var("head")),
                                }),
                                then_branch: PBox::new(PseudoExpr::Bool(true)),
                                else_branch: PBox::new(PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("lookup")),
                                    args: vec![PseudoExpr::var("tail")].into(),
                                }),
                            },
                        ),
                    ],
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("lookup")),
                args: vec![PseudoExpr::var("items")].into(),
            }),
        }),
    };

    assert_hoist_idempotent(expr);
}

// === analyze_dependencies ===

#[test]
fn test_analyze_dependencies_empty_chain() {
    let deps = analyze_dependencies(&[]);
    assert_eq!(deps.len(), 0);
    assert!(deps.is_empty());
}

#[test]
fn test_analyze_dependencies_closed_single_binding() {
    let a_id = VarId::new(1);
    let chain = vec![LiftedLet {
        name: "a".to_string(),
        id: Some(a_id),
        value: PseudoExpr::int(1),
    }];
    let deps = analyze_dependencies(&chain);
    assert_eq!(deps.len(), 1);
    let b0 = &deps.bindings[0];
    assert!(b0.is_closed());
    assert!(b0.is_closed_over_chain());
    assert!(b0.captures_in_chain.is_empty());
    assert!(b0.external_free_ids.is_empty());
    assert!(b0.external_free_compat_names.is_empty());
    assert_eq!(b0.target.id, a_id);
    assert_eq!(b0.target.name, "a");
}

#[test]
fn test_analyze_dependencies_single_binding_captures_external_id() {
    let x_id = VarId::new(100);
    let a_id = VarId::new(1);
    let chain = vec![LiftedLet {
        name: "a".to_string(),
        id: Some(a_id),
        value: PseudoExpr::var_with_id("x", x_id),
    }];
    let deps = analyze_dependencies(&chain);
    let b0 = &deps.bindings[0];
    assert!(!b0.is_closed());
    assert!(!b0.is_closed_over_chain());
    assert!(b0.captures_in_chain.is_empty());
    assert!(b0.external_free_ids.contains(&x_id));
}

#[test]
fn test_analyze_dependencies_chain_capture_by_id() {
    let a_id = VarId::new(1);
    let b_id = VarId::new(2);
    // let a = 1;
    // let b = a + 1;
    let chain = vec![
        LiftedLet {
            name: "a".to_string(),
            id: Some(a_id),
            value: PseudoExpr::int(1),
        },
        LiftedLet {
            name: "b".to_string(),
            id: Some(b_id),
            value: PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("a", a_id)),
                right: PBox::new(PseudoExpr::int(1)),
            },
        },
    ];
    let deps = analyze_dependencies(&chain);
    assert_eq!(deps.len(), 2);
    assert!(deps.bindings[0].is_closed());
    assert_eq!(deps.bindings[1].captures_in_chain, vec![0]);
    assert!(deps.bindings[1].is_closed_over_chain());
    assert!(!deps.bindings[1].is_closed());
}

#[test]
fn test_analyze_dependencies_chain_capture_by_compat_name() {
    // Simulates a later pass's reference carrying a compat-placeholder
    // id — the match falls back to name equality against chain[0].
    let a_id = VarId::new(1);
    let compat_id = VarId::fresh_compat_placeholder();
    assert!(
        compat_id.is_compat_placeholder(),
        "fresh_synthetic must yield a compat-placeholder id"
    );
    let b_id = VarId::new(2);
    let chain = vec![
        LiftedLet {
            name: "a".to_string(),
            id: Some(a_id),
            value: PseudoExpr::int(1),
        },
        LiftedLet {
            name: "b".to_string(),
            id: Some(b_id),
            value: PseudoExpr::var_with_id("a", compat_id),
        },
    ];
    let deps = analyze_dependencies(&chain);
    assert_eq!(deps.bindings[1].captures_in_chain, vec![0]);
    assert!(deps.bindings[1].is_closed_over_chain());
}

#[test]
fn test_analyze_dependencies_skips_non_referenced_earlier_entries() {
    let a_id = VarId::new(1);
    let b_id = VarId::new(2);
    let c_id = VarId::new(3);
    // let a = 1; let b = 2; let c = a; // c references a only
    let chain = vec![
        LiftedLet {
            name: "a".to_string(),
            id: Some(a_id),
            value: PseudoExpr::int(1),
        },
        LiftedLet {
            name: "b".to_string(),
            id: Some(b_id),
            value: PseudoExpr::int(2),
        },
        LiftedLet {
            name: "c".to_string(),
            id: Some(c_id),
            value: PseudoExpr::var_with_id("a", a_id),
        },
    ];
    let deps = analyze_dependencies(&chain);
    assert!(deps.bindings[0].is_closed());
    assert!(deps.bindings[1].is_closed());
    assert_eq!(deps.bindings[2].captures_in_chain, vec![0]);
    assert!(deps.bindings[2].is_closed_over_chain());
}

#[test]
fn test_analyze_dependencies_mixed_chain_and_external_captures() {
    let x_id = VarId::new(100);
    let a_id = VarId::new(1);
    let b_id = VarId::new(2);
    // let a = 1; let b = a + x; // b captures chain[0] and external x
    let chain = vec![
        LiftedLet {
            name: "a".to_string(),
            id: Some(a_id),
            value: PseudoExpr::int(1),
        },
        LiftedLet {
            name: "b".to_string(),
            id: Some(b_id),
            value: PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("a", a_id)),
                right: PBox::new(PseudoExpr::var_with_id("x", x_id)),
            },
        },
    ];
    let deps = analyze_dependencies(&chain);
    assert_eq!(deps.bindings[1].captures_in_chain, vec![0]);
    assert!(deps.bindings[1].external_free_ids.contains(&x_id));
    assert!(!deps.bindings[1].is_closed_over_chain());
}

#[test]
fn test_analyze_dependencies_ignores_inner_shadowing() {
    let a_id = VarId::new(1);
    let b_id = VarId::new(2);
    let inner_a_id = VarId::new(3);
    // let a = 1; let b = (let a = 2 in a); // inner a shadows chain[0]
    let chain = vec![
        LiftedLet {
            name: "a".to_string(),
            id: Some(a_id),
            value: PseudoExpr::int(1),
        },
        LiftedLet {
            name: "b".to_string(),
            id: Some(b_id),
            value: PseudoExpr::Let {
                name: "a".to_string(),
                id: Some(inner_a_id),
                value: PBox::new(PseudoExpr::int(2)),
                body: PBox::new(PseudoExpr::var_with_id("a", inner_a_id)),
            },
        },
    ];
    let deps = analyze_dependencies(&chain);
    assert!(
        deps.bindings[1].captures_in_chain.is_empty(),
        "inner `let a` shadows chain[0]; b must not capture it"
    );
    assert!(deps.bindings[1].is_closed());
}

// === rollback_unsafe_lifts ===

fn target(name: &str, id: VarId) -> BindingTarget {
    BindingTarget {
        name: name.to_string(),
        id,
    }
}

fn names(chain: &[LiftedLet]) -> Vec<String> {
    chain.iter().map(|b| b.name.clone()).collect()
}

#[test]
fn test_rollback_empty_chain_is_noop() {
    let forbidden = vec![target("x", VarId::new(99))];
    let (safe, rolled) = rollback_unsafe_lifts(Vec::new(), &forbidden);
    assert!(safe.is_empty());
    assert!(rolled.is_empty());
}

#[test]
fn test_rollback_empty_forbidden_is_noop() {
    let chain = vec![LiftedLet {
        name: "a".to_string(),
        id: Some(VarId::new(1)),
        value: PseudoExpr::int(1),
    }];
    let (safe, rolled) = rollback_unsafe_lifts(chain, &[]);
    assert_eq!(names(&safe), vec!["a"]);
    assert!(rolled.is_empty());
}

#[test]
fn test_rollback_closed_chain_keeps_everything_safe() {
    let chain = vec![
        LiftedLet {
            name: "a".to_string(),
            id: Some(VarId::new(1)),
            value: PseudoExpr::int(1),
        },
        LiftedLet {
            name: "b".to_string(),
            id: Some(VarId::new(2)),
            value: PseudoExpr::int(2),
        },
    ];
    let forbidden = vec![target("x", VarId::new(99))];
    let (safe, rolled) = rollback_unsafe_lifts(chain, &forbidden);
    assert_eq!(names(&safe), vec!["a", "b"]);
    assert!(rolled.is_empty());
}

#[test]
fn test_rollback_direct_id_capture_is_rolled_back() {
    let param_id = VarId::new(50);
    let chain = vec![LiftedLet {
        name: "h".to_string(),
        id: Some(VarId::new(1)),
        value: PseudoExpr::Lambda {
            params: vec!["y".to_string().into()],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("x", param_id)),
                right: PBox::new(PseudoExpr::var("y")),
            }),
        },
    }];
    let forbidden = vec![target("x", param_id)];
    let (safe, rolled) = rollback_unsafe_lifts(chain, &forbidden);
    assert!(safe.is_empty(), "binding captures forbidden param x");
    assert_eq!(names(&rolled), vec!["h"]);
}

#[test]
fn test_rollback_compat_name_capture_is_rolled_back() {
    // The binding references param "p" with a compat-placeholder id,
    // so the analysis records a free compat-name, not a free id.
    let param_id = VarId::new(50);
    let compat_id = VarId::fresh_compat_placeholder();
    assert!(compat_id.is_compat_placeholder());
    let chain = vec![LiftedLet {
        name: "h".to_string(),
        id: Some(VarId::new(1)),
        value: PseudoExpr::Lambda {
            params: vec!["y".to_string().into()],
            body: PBox::new(PseudoExpr::var_with_id("p", compat_id)),
        },
    }];
    let forbidden = vec![target("p", param_id)];
    let (safe, rolled) = rollback_unsafe_lifts(chain, &forbidden);
    assert!(safe.is_empty(), "binding captures forbidden name 'p'");
    assert_eq!(names(&rolled), vec!["h"]);
}

#[test]
fn test_rollback_transitive_through_chain_capture() {
    // h0 captures forbidden param x → must roll back.
    // h1 captures h0 in chain → must roll back transitively, or
    // its reference to h0 dangles.
    let param_id = VarId::new(50);
    let h0_id = VarId::new(1);
    let h1_id = VarId::new(2);
    let chain = vec![
        LiftedLet {
            name: "h0".to_string(),
            id: Some(h0_id),
            value: PseudoExpr::Lambda {
                params: vec!["y".to_string().into()],
                body: PBox::new(PseudoExpr::var_with_id("x", param_id)),
            },
        },
        LiftedLet {
            name: "h1".to_string(),
            id: Some(h1_id),
            value: PseudoExpr::Lambda {
                params: vec!["z".to_string().into()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("h0", h0_id)),
                    args: vec![PseudoExpr::var("z")].into(),
                }),
            },
        },
    ];
    let forbidden = vec![target("x", param_id)];
    let (safe, rolled) = rollback_unsafe_lifts(chain, &forbidden);
    assert!(safe.is_empty(), "both bindings must roll back");
    assert_eq!(names(&rolled), vec!["h0", "h1"]);
}

#[test]
fn test_rollback_keeps_safe_earlier_when_only_later_captures() {
    // h0 is closed → stays lifted, its order preserved.
    // h1 captures a forbidden param → rolled back.
    let param_id = VarId::new(50);
    let h0_id = VarId::new(1);
    let h1_id = VarId::new(2);
    let chain = vec![
        LiftedLet {
            name: "h0".to_string(),
            id: Some(h0_id),
            value: PseudoExpr::Lambda {
                params: vec!["y".to_string().into()],
                body: PBox::new(PseudoExpr::var("y")),
            },
        },
        LiftedLet {
            name: "h1".to_string(),
            id: Some(h1_id),
            value: PseudoExpr::Lambda {
                params: vec!["z".to_string().into()],
                body: PBox::new(PseudoExpr::var_with_id("x", param_id)),
            },
        },
    ];
    let forbidden = vec![target("x", param_id)];
    let (safe, rolled) = rollback_unsafe_lifts(chain, &forbidden);
    assert_eq!(names(&safe), vec!["h0"]);
    assert_eq!(names(&rolled), vec!["h1"]);
}

#[test]
fn test_rollback_does_not_cascade_to_unrelated_safe_chain_capture() {
    // h0 closed → safe.
    // h1 captures h0 only → safe (h0 is lifted with it).
    // h2 captures a forbidden param → only h2 rolls back.
    let param_id = VarId::new(50);
    let h0_id = VarId::new(1);
    let h1_id = VarId::new(2);
    let h2_id = VarId::new(3);
    let chain = vec![
        LiftedLet {
            name: "h0".to_string(),
            id: Some(h0_id),
            value: PseudoExpr::Lambda {
                params: vec!["y".to_string().into()],
                body: PBox::new(PseudoExpr::var("y")),
            },
        },
        LiftedLet {
            name: "h1".to_string(),
            id: Some(h1_id),
            value: PseudoExpr::Lambda {
                params: vec!["z".to_string().into()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("h0", h0_id)),
                    args: vec![PseudoExpr::var("z")].into(),
                }),
            },
        },
        LiftedLet {
            name: "h2".to_string(),
            id: Some(h2_id),
            value: PseudoExpr::Lambda {
                params: vec!["w".to_string().into()],
                body: PBox::new(PseudoExpr::var_with_id("x", param_id)),
            },
        },
    ];
    let forbidden = vec![target("x", param_id)];
    let (safe, rolled) = rollback_unsafe_lifts(chain, &forbidden);
    assert_eq!(names(&safe), vec!["h0", "h1"]);
    assert_eq!(names(&rolled), vec!["h2"]);
}

// === co-location via `split_entry_lambda_helper_chain` ===

fn let_chain(bindings: Vec<LiftedLet>, terminal: PseudoExpr) -> PseudoExpr {
    wrap_lifted_lets(bindings, terminal)
}

#[test]
fn test_split_lifts_helper_not_referencing_forbidden_param() {
    let h_id = VarId::new(1);
    let chain = vec![LiftedLet {
        name: "h".to_string(),
        id: Some(h_id),
        value: PseudoExpr::Lambda {
            params: vec!["y".to_string().into()],
            body: PBox::new(PseudoExpr::var("y")),
        },
    }];
    let forbidden = vec![target("p", VarId::new(99))];
    let expr = let_chain(chain, PseudoExpr::var("h"));
    let (lifted, body) = split_entry_lambda_helper_chain(expr, &forbidden);
    assert_eq!(names(&lifted), vec!["h"]);
    assert!(matches!(body, PseudoExpr::Var { .. }));
}

#[test]
fn test_split_keeps_helper_referencing_forbidden_param_by_name() {
    // The helper's value references forbidden param name "z" through
    // a Var whose authoritative id doesn't match the param's, so
    // id-based matching alone would miss it; the name-based check
    // keeps the binding adjacent to its captor instead of lifting it
    // past the enclosing lambda.
    let h_id = VarId::new(1);
    let stale_var_id = VarId::new(42); // not compat, not matching param id
    let param_id = VarId::new(99);
    let chain = vec![LiftedLet {
        name: "h".to_string(),
        id: Some(h_id),
        value: PseudoExpr::Lambda {
            params: vec!["y".to_string().into()],
            body: PBox::new(PseudoExpr::var_with_id("z", stale_var_id)),
        },
    }];
    let forbidden = vec![target("z", param_id)];
    let expr = let_chain(chain, PseudoExpr::var("h"));
    let (lifted, body) = split_entry_lambda_helper_chain(expr, &forbidden);
    assert!(
        lifted.is_empty(),
        "binding references forbidden name 'z' via stale id"
    );
    // The kept binding is wrapped around the terminal.
    let PseudoExpr::Let { name, .. } = body else {
        panic!("expected kept let-binding");
    };
    assert_eq!(name, "h");
}

#[test]
fn test_split_preserves_source_order_when_mixing_lift_and_keep() {
    // Source order: h0 (lift-able), alias (non-helper, must stay), h1
    // (captures the param, must stay). h1 must be reinserted at its
    // original position, after alias rather than ahead of it.
    let h0_id = VarId::new(1);
    let alias_id = VarId::new(2);
    let h1_id = VarId::new(3);
    let param_id = VarId::new(99);
    let chain = vec![
        LiftedLet {
            name: "h0".to_string(),
            id: Some(h0_id),
            value: PseudoExpr::Lambda {
                params: vec!["y".to_string().into()],
                body: PBox::new(PseudoExpr::var("y")),
            },
        },
        LiftedLet {
            name: "alias".to_string(),
            id: Some(alias_id),
            value: PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("some_fn")),
                args: vec![PseudoExpr::int(1)].into(),
            },
        },
        LiftedLet {
            name: "h1".to_string(),
            id: Some(h1_id),
            value: PseudoExpr::Lambda {
                params: vec!["z".to_string().into()],
                body: PBox::new(PseudoExpr::var_with_id("p", param_id)),
            },
        },
    ];
    let forbidden = vec![target("p", param_id)];
    let expr = let_chain(chain, PseudoExpr::var("sentinel"));
    let (lifted, body) = split_entry_lambda_helper_chain(expr, &forbidden);
    assert_eq!(names(&lifted), vec!["h0"]);
    // Body should be Let(alias, Let(h1, Var(sentinel))).
    let PseudoExpr::Let {
        name: n0,
        body: body0,
        ..
    } = body
    else {
        panic!("expected kept alias let-binding");
    };
    assert_eq!(n0, "alias");
    let PseudoExpr::Let {
        name: n1,
        body: body1,
        ..
    } = body0.into_inner()
    else {
        panic!("expected kept h1 let-binding inside alias body");
    };
    assert_eq!(n1, "h1");
    assert!(matches!(*body1, PseudoExpr::Var { .. }));
}
