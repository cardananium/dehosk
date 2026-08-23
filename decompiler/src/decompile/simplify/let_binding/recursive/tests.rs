use super::Simplifier;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::var_id::VarId;

#[test]
fn test_try_promote_lambda_rec_wrapper_preserves_extra_param_var_id() {
    let list_id = VarId::new(960);
    let acc_id = VarId::new(961);
    let inner_list_id = VarId::new(962);

    let lambda_params = vec![Binder::new("xs", list_id), Binder::new("acc", acc_id)];
    let lambda_body = PseudoExpr::let_bind(
        "inner",
        PseudoExpr::RecFn {
            name: "inner".to_string().into(),
            params: vec![Binder::new("xs", inner_list_id)],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::Bool(false)),
                then_branch: PBox::new(PseudoExpr::var_with_id("acc", acc_id)),
                else_branch: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("inner")),
                    args: vec![PseudoExpr::var_with_id("xs", inner_list_id)].into(),
                }),
            }),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("inner")),
            args: vec![PseudoExpr::var_with_id("xs", list_id)].into(),
        },
    );

    let simplifier = Simplifier::with_safe_mode(false);
    let promoted = simplifier
        .try_promote_lambda_rec_wrapper("wrapper", VarId::new(968), &lambda_params, &lambda_body)
        .expect("expected wrapper lambda to promote into a recfn");

    let PseudoExpr::RecFn { params, body, .. } = &promoted else {
        panic!("expected promoted recfn, got: {promoted:?}");
    };
    assert_eq!(params.len(), 2);
    assert_eq!(params[0].id, list_id);
    assert_eq!(params[1].id, acc_id);

    let PseudoExpr::If {
        then_branch,
        else_branch,
        ..
    } = body.as_ref()
    else {
        panic!("expected promoted recfn body to stay conditional, got: {body:?}");
    };
    assert!(
        matches!(
            then_branch.as_ref(),
            PseudoExpr::Var { name, id, .. }
                if name == "acc" && id.get() == Some(acc_id)
        ),
        "expected captured acc reference to preserve outer param VarId, got: {then_branch:?}"
    );
    let PseudoExpr::Apply { args, .. } = else_branch.as_ref() else {
        panic!("expected recursive self-call in promoted body, got: {else_branch:?}");
    };
    assert!(
        matches!(
            args.get(1),
            Some(PseudoExpr::Var { name, id, .. })
                if name == "acc" && id.get() == Some(acc_id)
        ),
        "expected promoted recursive call to append acc with preserved VarId, got: {:?}",
        args.get(1)
    );
}

#[test]
fn test_try_promote_lambda_rec_wrapper_rejects_same_name_foreign_free_capture() {
    let list_id = VarId::new(984);
    let acc_id = VarId::new(985);
    let foreign_acc_id = VarId::new(986);
    let inner_list_id = VarId::new(987);

    let lambda_params = vec![Binder::new("xs", list_id), Binder::new("acc", acc_id)];
    let lambda_body = PseudoExpr::let_bind(
        "inner",
        PseudoExpr::RecFn {
            name: "inner".to_string().into(),
            params: vec![Binder::new("xs", inner_list_id)],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::Bool(false)),
                then_branch: PBox::new(PseudoExpr::var_with_id("acc", foreign_acc_id)),
                else_branch: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("inner")),
                    args: vec![PseudoExpr::var_with_id("xs", inner_list_id)].into(),
                }),
            }),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("inner")),
            args: vec![PseudoExpr::var_with_id("xs", list_id)].into(),
        },
    );

    let simplifier = Simplifier::with_safe_mode(false);
    assert!(
        simplifier
            .try_promote_lambda_rec_wrapper(
                "wrapper",
                VarId::new(988),
                &lambda_params,
                &lambda_body
            )
            .is_none(),
        "foreign same-name free capture must not be authorized by an outer param name"
    );
}

#[test]
fn test_try_promote_lambda_rec_wrapper_allows_compat_free_capture_by_name() {
    let list_id = VarId::new(989);
    let acc_id = VarId::new(990);
    let inner_list_id = VarId::new(991);

    let lambda_params = vec![Binder::new("xs", list_id), Binder::new("acc", acc_id)];
    let lambda_body = PseudoExpr::let_bind(
        "inner",
        PseudoExpr::RecFn {
            name: "inner".to_string().into(),
            params: vec![Binder::new("xs", inner_list_id)],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::Bool(false)),
                then_branch: PBox::new(PseudoExpr::compat_var("acc")),
                else_branch: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("inner")),
                    args: vec![PseudoExpr::var_with_id("xs", inner_list_id)].into(),
                }),
            }),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("inner")),
            args: vec![PseudoExpr::var_with_id("xs", list_id)].into(),
        },
    );

    let simplifier = Simplifier::with_safe_mode(false);
    let promoted = simplifier
        .try_promote_lambda_rec_wrapper("wrapper", VarId::new(992), &lambda_params, &lambda_body)
        .expect("compat placeholder free capture should preserve existing name fallback");

    let PseudoExpr::RecFn { params, body, .. } = &promoted else {
        panic!("expected promoted recfn, got: {promoted:?}");
    };
    assert_eq!(params[1].id, acc_id);
    let PseudoExpr::If { then_branch, .. } = body.as_ref() else {
        panic!("expected promoted recfn body to stay conditional, got: {body:?}");
    };
    assert!(
        matches!(
            then_branch.as_ref(),
            PseudoExpr::Var { name, id, .. } if name == "acc" && id.get().is_none()
        ),
        "compat free capture should remain a compat ref for later retargeting, got: {then_branch:?}"
    );
}

#[test]
fn test_try_promote_lambda_rec_wrapper_rejects_authoritative_same_name_foreign_entry_call() {
    let list_id = VarId::new(963);
    let inner_let_id = VarId::new(964);
    let rec_id = VarId::new(965);
    let foreign_inner_id = VarId::new(966);
    let inner_list_id = VarId::new(967);

    let lambda_params = vec![Binder::new("xs", list_id)];
    let lambda_body = PseudoExpr::Let {
        name: "inner".to_string(),
        id: Some(inner_let_id),
        value: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("inner", rec_id),
            params: vec![Binder::new("xs", inner_list_id)],
            body: PBox::new(PseudoExpr::var_with_id("xs", inner_list_id)),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("inner", foreign_inner_id)),
            args: vec![PseudoExpr::var_with_id("xs", list_id)].into(),
        }),
    };

    let simplifier = Simplifier::with_safe_mode(false);
    assert!(
        simplifier
            .try_promote_lambda_rec_wrapper(
                "wrapper",
                VarId::new(969),
                &lambda_params,
                &lambda_body
            )
            .is_none(),
        "expected foreign same-name entry call to block lambda-rec promotion"
    );
}

#[test]
fn test_try_promote_lambda_rec_wrapper_rejects_authoritative_same_name_foreign_body_call() {
    let list_id = VarId::new(976);
    let acc_id = VarId::new(977);
    let inner_let_id = VarId::new(978);
    let rec_id = VarId::new(979);
    let foreign_inner_id = VarId::new(980);
    let inner_list_id = VarId::new(981);

    let lambda_params = vec![Binder::new("xs", list_id), Binder::new("acc", acc_id)];
    let lambda_body = PseudoExpr::Let {
        name: "inner".to_string(),
        id: Some(inner_let_id),
        value: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("inner", rec_id),
            params: vec![Binder::new("xs", inner_list_id)],
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var_with_id("inner", rec_id)),
                        args: vec![PseudoExpr::var_with_id("xs", inner_list_id)].into(),
                    },
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var_with_id("inner", foreign_inner_id)),
                        args: vec![PseudoExpr::var_with_id("xs", inner_list_id)].into(),
                    },
                    PseudoExpr::var_with_id("acc", acc_id),
                ]
                .into(),
            )),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("inner", inner_let_id)),
            args: vec![PseudoExpr::var_with_id("xs", list_id)].into(),
        }),
    };

    let simplifier = Simplifier::with_safe_mode(false);
    assert!(
        simplifier
            .try_promote_lambda_rec_wrapper(
                "wrapper",
                VarId::new(982),
                &lambda_params,
                &lambda_body,
            )
            .is_none(),
        "foreign same-name recursive calls should block wrapper promotion instead of being treated as owned captures"
    );
}

#[test]
fn test_try_promote_lambda_rec_wrapper_allows_bound_same_name_foreign_ref() {
    let wrapper_id = VarId::new(993);
    let list_id = VarId::new(994);
    let inner_let_id = VarId::new(995);
    let rec_id = VarId::new(996);
    let foreign_id = VarId::new(997);
    let inner_list_id = VarId::new(998);

    let lambda_params = vec![Binder::new("xs", list_id)];
    let lambda_body = PseudoExpr::Let {
        name: "inner".to_string(),
        id: Some(inner_let_id),
        value: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("inner", rec_id),
            params: vec![Binder::new("xs", inner_list_id)],
            body: PBox::new(PseudoExpr::Let {
                name: "shadow_owner".to_string(),
                id: Some(foreign_id),
                value: PBox::new(PseudoExpr::int(0)),
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("wrapper", foreign_id),
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var_with_id("inner", rec_id)),
                            args: vec![PseudoExpr::var_with_id("xs", inner_list_id)].into(),
                        },
                    ]
                    .into(),
                )),
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("inner", inner_let_id)),
            args: vec![PseudoExpr::var_with_id("xs", list_id)].into(),
        }),
    };

    let simplifier = Simplifier::with_safe_mode(false);
    let promoted = simplifier
        .try_promote_lambda_rec_wrapper("wrapper", wrapper_id, &lambda_params, &lambda_body)
        .expect("same-name refs with a foreign bound VarId must not block promotion");

    let PseudoExpr::RecFn { body, .. } = &promoted else {
        panic!("expected promoted RecFn, got: {promoted:?}");
    };
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Let { id, body, .. }
                if id.get() == Some(foreign_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Tuple(items)
                            if matches!(
                                items.first(),
                                Some(PseudoExpr::Var { name, id, .. })
                                    if name == "wrapper" && id.get() == Some(foreign_id)
                            )
                    )
        ),
        "foreign bound ref should remain untouched in promoted body, got: {body:?}"
    );
}

#[test]
fn test_try_promote_lambda_rec_wrapper_reorders_recursive_args_to_outer_param_order() {
    let a_id = VarId::new(970);
    let b_id = VarId::new(971);
    let c_id = VarId::new(972);
    let d_id = VarId::new(973);
    let inner_d_id = VarId::new(974);
    let tail_id = VarId::new(975);

    let lambda_params = vec![
        Binder::new("a", a_id),
        Binder::new("b", b_id),
        Binder::new("c", c_id),
        Binder::new("d", d_id),
    ];
    let lambda_body = PseudoExpr::let_bind(
        "inner",
        PseudoExpr::RecFn {
            name: "inner".to_string().into(),
            params: vec![Binder::new("d", inner_d_id)],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var_with_id("d", inner_d_id)),
                subject_name: None,
                clauses: vec![crate::pseudo::ast::WhenClause::new(
                    WhenPattern::List {
                        elements: vec!["y_h".to_string().into()],
                        tail: Some(Binder::new("y_t", tail_id)),
                    },
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("inner")),
                        args: vec![PseudoExpr::var_with_id("y_t", tail_id)].into(),
                    },
                )],
            }),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("inner")),
            args: vec![PseudoExpr::var_with_id("d", d_id)].into(),
        },
    );

    let simplifier = Simplifier::with_safe_mode(false);
    let promoted = simplifier
        .try_promote_lambda_rec_wrapper("wrapper", VarId::new(983), &lambda_params, &lambda_body)
        .expect("expected wrapper lambda to promote into a recfn");

    let PseudoExpr::RecFn { params, body, .. } = &promoted else {
        panic!("expected promoted recfn, got: {promoted:?}");
    };
    assert_eq!(
        params
            .iter()
            .map(|param| param.as_str())
            .collect::<Vec<_>>(),
        vec!["a", "b", "c", "d"]
    );

    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected promoted body to stay a when, got: {body:?}");
    };
    let PseudoExpr::Apply { args, .. } = &clauses[0].body else {
        panic!(
            "expected recursive self-call in promoted body, got: {:?}",
            clauses[0].body
        );
    };
    assert_eq!(args.len(), 4);
    assert!(
        matches!(args[0], PseudoExpr::Var { ref name, id, .. } if name == "a" && id.get() == Some(a_id))
    );
    assert!(
        matches!(args[1], PseudoExpr::Var { ref name, id, .. } if name == "b" && id.get() == Some(b_id))
    );
    assert!(
        matches!(args[2], PseudoExpr::Var { ref name, id, .. } if name == "c" && id.get() == Some(c_id))
    );
    assert!(
        matches!(args[3], PseudoExpr::Var { ref name, id, .. } if name == "y_t" && id.get() == Some(tail_id))
    );
}
