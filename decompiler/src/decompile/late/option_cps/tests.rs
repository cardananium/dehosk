use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr, PseudoType, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;
use std::rc::Rc;

#[test]
fn test_rewrite_option_cps_calls_skips_untyped_var_apply() {
    // A plain `Var` callee with no `RecFn` body cannot be shown to return Option,
    // so the CPS rewrite does not trigger.
    let rec_self_id = VarId::fresh_compat_placeholder();
    let list_id = VarId::fresh_compat_placeholder();
    let fn_id = VarId::fresh_compat_placeholder();
    let value_binder: Binder = "value".to_string().into();

    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: "acc_2".to_string(),
            id: Some(fn_id),
        }),
        args: vec![
            PseudoExpr::var_with_id("__y_comb_rec_fn", rec_self_id),
            PseudoExpr::Var {
                name: "xs".to_string(),
                id: Some(list_id),
            },
            PseudoExpr::Lambda {
                params: vec![value_binder.clone()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("handle")),
                    args: vec![PseudoExpr::var_with_id("value", value_binder.id)].into(),
                }),
            },
            PseudoExpr::error(),
        ]
        .into(),
    };

    let result = rewrite_option_cps_calls(expr, None);

    assert!(
        matches!(&result, PseudoExpr::Apply { .. }),
        "expected Apply to pass through when function type is unknown, got: {result:?}"
    );
}

#[test]
fn test_rewrite_option_cps_calls_rewrites_direct_recfn_option_cps_apply() {
    let rec_name: Binder = "acc_2".to_string().into();
    let self_binder: Binder = "loop".to_string().into();
    let list_binder: Binder = "xs".to_string().into();
    let tail_id = VarId::fresh_compat_placeholder();
    let value_binder: Binder = "value".to_string().into();

    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::RecFn {
            name: rec_name.clone(),
            params: vec![self_binder.clone(), list_binder.clone()],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::var("pred")),
                then_branch: PBox::new(PseudoExpr::some(PseudoExpr::var("payload"))),
                else_branch: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id(
                        self_binder.as_str(),
                        self_binder.id,
                    )),
                    args: vec![PseudoExpr::var_with_id("xs_t", tail_id)].into(),
                }),
            }),
        }),
        args: vec![
            PseudoExpr::var("__y_comb_rec_fn"),
            PseudoExpr::var_with_id(list_binder.as_str(), list_binder.id),
            PseudoExpr::Lambda {
                params: vec![value_binder.clone()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("handle")),
                    args: vec![PseudoExpr::var_with_id("value", value_binder.id)].into(),
                }),
            },
            PseudoExpr::error(),
        ]
        .into(),
    };

    let result = rewrite_option_cps_calls(expr, None);

    match result {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "acc_2");
            assert!(matches!(value.as_ref(), PseudoExpr::RecFn { .. }));
            assert!(matches!(
                body.as_ref(),
                PseudoExpr::When { subject, clauses, .. }
                    if matches!(
                        subject.as_ref(),
                        PseudoExpr::Apply { function, args }
                            if matches!(
                                function.as_ref(),
                                PseudoExpr::Var { name, id, .. }
                                    if name == "acc_2" && *id == Some(rec_name.id)
                            )
                            && matches!(
                                args.as_slice(),
                                [PseudoExpr::Var { name, id, .. }]
                                    if name == "xs" && *id == Some(list_binder.id)
                            )
                    )
                    && matches!(
                        clauses.as_slice(),
                        [
                            WhenClause {
                                pattern: WhenPattern::Constructor { shape: ConstructorShape::Known(KnownConstructor::Some), tag: 0, fields, .. },
                                ..
                            },
                            WhenClause {
                                pattern: WhenPattern::Constructor { shape: ConstructorShape::Known(KnownConstructor::None), tag: 1, fields: none_fields, .. },
                                body: PseudoExpr::Error { .. },
                                ..
                            }
                        ] if matches!(fields.as_slice(), [field] if field == &value_binder)
                            && none_fields.is_empty()
                    )
            ));
        }
        other => panic!("expected direct recfn cps call to become let+when, got: {other:?}"),
    }
}

#[test]
fn test_option_cps_self_arg_strip_keeps_matching_authoritative_self_id() {
    let rec_name = Binder::new("acc_2", VarId::new(9401));
    let self_binder = Binder::new("loop", VarId::new(9402));
    let list_binder = Binder::new("xs", VarId::new(9403));
    let value_binder = Binder::new("value", VarId::new(9404));

    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::RecFn {
            name: rec_name.clone(),
            params: vec![self_binder.clone(), list_binder.clone()],
            body: PBox::new(PseudoExpr::some(PseudoExpr::var_with_id(
                list_binder.as_str(),
                list_binder.id,
            ))),
        }),
        args: vec![
            PseudoExpr::var_with_id(rec_name.as_str(), rec_name.id),
            PseudoExpr::var_with_id(list_binder.as_str(), list_binder.id),
            PseudoExpr::Lambda {
                params: vec![value_binder.clone()],
                body: PBox::new(PseudoExpr::var_with_id(
                    value_binder.as_str(),
                    value_binder.id,
                )),
            },
            PseudoExpr::error(),
        ]
        .into(),
    };

    let result = rewrite_option_cps_calls(expr, None);

    assert!(
        matches!(
            &result,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::When { subject, .. }
                        if matches!(
                            subject.as_ref(),
                            PseudoExpr::Apply { args, .. }
                                if matches!(args.as_slice(), [PseudoExpr::Var { name, id, .. }]
                                    if name == "xs" && *id == Some(list_binder.id))
                        )
                )
        ),
        "matching authoritative self id should still strip recursive self arg, got: {result:?}"
    );
}

#[test]
fn test_option_cps_self_arg_strip_ignores_same_name_different_id() {
    let rec_name = Binder::new("acc_2", VarId::new(9411));
    let foreign_self_id = VarId::new(9412);
    let self_binder = Binder::new("loop", VarId::new(9413));
    let list_binder = Binder::new("xs", VarId::new(9414));
    let value_binder = Binder::new("value", VarId::new(9415));

    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::RecFn {
            name: rec_name.clone(),
            params: vec![self_binder.clone(), list_binder.clone()],
            body: PBox::new(PseudoExpr::some(PseudoExpr::var_with_id(
                list_binder.as_str(),
                list_binder.id,
            ))),
        }),
        args: vec![
            PseudoExpr::var_with_id(rec_name.as_str(), foreign_self_id),
            PseudoExpr::var_with_id(list_binder.as_str(), list_binder.id),
            PseudoExpr::Lambda {
                params: vec![value_binder.clone()],
                body: PBox::new(PseudoExpr::var_with_id(
                    value_binder.as_str(),
                    value_binder.id,
                )),
            },
            PseudoExpr::error(),
        ]
        .into(),
    };

    let result = rewrite_option_cps_calls(expr, None);

    assert!(
        matches!(
            &result,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::When { subject, .. }
                        if matches!(
                            subject.as_ref(),
                            PseudoExpr::Apply { args, .. }
                                if matches!(
                                    args.as_slice(),
                                    [
                                        PseudoExpr::Var { name: first_name, id: first_id, .. },
                                        PseudoExpr::Var { name: second_name, id: second_id, .. }
                                    ] if first_name == "acc_2"
                                        && *first_id == Some(foreign_self_id)
                                        && second_name == "xs"
                                        && *second_id == Some(list_binder.id)
                                )
                        )
                )
        ),
        "same-name different-id self arg must stay in subject args, got: {result:?}"
    );
}

#[test]
fn test_rewrite_option_cps_calls_freshens_direct_recfn_wrapper_let_name() {
    let outer_id = VarId::fresh_binding();
    let rec_name = Binder::new("acc_2", VarId::fresh_binding());
    let self_binder = Binder::new("loop", VarId::fresh_binding());
    let list_binder = Binder::new("xs", VarId::fresh_binding());
    let value_binder = Binder::new("value", VarId::fresh_binding());

    let expr = PseudoExpr::Let {
        name: "acc_2".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::RecFn {
                name: rec_name.clone(),
                params: vec![self_binder.clone(), list_binder.clone()],
                body: PBox::new(PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::var("pred")),
                    then_branch: PBox::new(PseudoExpr::some(PseudoExpr::var("payload"))),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var_with_id(
                            self_binder.as_str(),
                            self_binder.id,
                        )),
                        args: vec![PseudoExpr::var_with_id(
                            list_binder.as_str(),
                            list_binder.id,
                        )]
                        .into(),
                    }),
                }),
            }),
            args: vec![
                PseudoExpr::var("__y_comb_rec_fn"),
                PseudoExpr::var_with_id(list_binder.as_str(), list_binder.id),
                PseudoExpr::Lambda {
                    params: vec![value_binder.clone()],
                    body: PBox::new(PseudoExpr::var_with_id(
                        value_binder.as_str(),
                        value_binder.id,
                    )),
                },
                PseudoExpr::error(),
            ]
            .into(),
        }),
    };

    let result = rewrite_option_cps_calls(expr, None);

    let PseudoExpr::Let {
        name: outer_name,
        body,
        ..
    } = result
    else {
        panic!("expected outer let");
    };
    assert_eq!(outer_name, "acc_2");

    let PseudoExpr::Let {
        name: wrapper_name,
        id: Some(wrapper_id),
        body: wrapper_body,
        ..
    } = body.as_ref()
    else {
        panic!("expected freshened recfn wrapper let, got: {body:?}");
    };
    assert_ne!(
        wrapper_name, "acc_2",
        "generated wrapper let must not duplicate an existing let name"
    );
    assert_eq!(*wrapper_id, rec_name.id);

    let PseudoExpr::When { subject, .. } = wrapper_body.as_ref() else {
        panic!("expected when under wrapper let, got: {wrapper_body:?}");
    };
    assert!(
        matches!(
            subject.as_ref(),
            PseudoExpr::Apply { function, .. }
                if matches!(
                    function.as_ref(),
                    PseudoExpr::Var { name, id, .. }
                        if name == wrapper_name && *id == Some(rec_name.id)
                )
        ),
        "when subject must call the freshened wrapper name with the original recfn id"
    );
}

#[test]
fn test_rewrite_option_cps_calls_matches_lambda_self_by_name_when_var_id_drifted() {
    let self_binder: Binder = "x_19".to_string().into();
    let list_binder: Binder = "y_10".to_string().into();
    let helper_id = VarId::fresh_compat_placeholder();
    let stale_self_id = VarId::fresh_compat_placeholder();
    let value_binder: Binder = "value".to_string().into();

    let expr = PseudoExpr::Let {
        name: "acc_2".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![self_binder.clone(), list_binder.clone()],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var_with_id(
                    list_binder.as_str(),
                    list_binder.id,
                )),
                subject_name: None,
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec![],
                            tail: None,
                        },
                        PseudoExpr::none(),
                    ),
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec!["head".to_string().into()],
                            tail: Some("tail".to_string().into()),
                        },
                        PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::var("pred")),
                            then_branch: PBox::new(PseudoExpr::some(PseudoExpr::var("payload"))),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var_with_id(
                                    self_binder.as_str(),
                                    stale_self_id,
                                )),
                                args: vec![PseudoExpr::var("tail")].into(),
                            }),
                        },
                    ),
                ],
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("acc_2", helper_id)),
            args: vec![
                PseudoExpr::var("__y_comb_rec_fn"),
                PseudoExpr::var_with_id(list_binder.as_str(), list_binder.id),
                PseudoExpr::Lambda {
                    params: vec![value_binder.clone()],
                    body: PBox::new(PseudoExpr::var_with_id("value", value_binder.id)),
                },
                PseudoExpr::error(),
            ]
            .into(),
        }),
    };

    let result = rewrite_option_cps_calls(expr, None);

    assert!(matches!(
        result,
        PseudoExpr::Let { body, .. }
            if matches!(body.as_ref(), PseudoExpr::When { .. })
    ));
}

#[test]
fn test_rewrite_option_cps_calls_plumbs_env_refine_pre_pass() {
    // Plumbing smoke test: passing a `TypeEnvironment` must leave
    // the same structure as passing `None`.
    let vid = VarId::fresh_binding();
    let mut env = TypeEnvironment::new();
    env.bind_var(vid, Rc::new(PseudoType::Int));
    env.freeze();

    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(vid),
        value: PBox::new(PseudoExpr::int(7)),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(vid),
        }),
    };

    let refined = rewrite_option_cps_calls(expr.clone(), Some(&env));
    let PseudoExpr::Let { body, .. } = &refined else {
        panic!("expected let, got: {refined:?}");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Var { .. }),
        "expected var body, got: {body:?}"
    );

    let untouched = rewrite_option_cps_calls(expr, None);
    let PseudoExpr::Let { body, .. } = &untouched else {
        panic!("expected let, got: {untouched:?}");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Var { .. }),
        "expected var body, got: {body:?}"
    );
}
