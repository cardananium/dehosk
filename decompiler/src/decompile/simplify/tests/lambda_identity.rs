use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_lambda_param_identity_stays_stable_across_repeated_simplify_passes() {
    // Hygienic input: the param binder and the body ref share one
    // VarId, so retarget's hygiene pass leaves the ref's id alone.
    let param_id = VarId::from_raw(42);
    let expr = PseudoExpr::Lambda {
        params: vec![crate::pseudo::ast::Binder::new("x", param_id)],
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(param_id),
        }),
    };

    let once = simplify(expr);
    let twice = simplify(once);

    match twice {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params, vec!["x".to_string()]);
            assert!(
                matches!(body.as_ref(), PseudoExpr::Var { name, id, .. } if name == "x" && id.get() == Some(param_id)),
                "repeated simplify should preserve the original binding identity: {body:?}"
            );
        }
        other => panic!("expected lambda after repeated simplify, got: {other:?}"),
    }
}

#[test]
fn test_lambda_param_mismatched_body_ref_id_is_rebound_before_unused_check() {
    let param_id = VarId::from_raw(100);
    let stale_ref_id = VarId::from_raw(200);
    let expr = PseudoExpr::Lambda {
        params: vec![crate::pseudo::ast::Binder::new("redeemer", param_id)],
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::Var {
                name: "redeemer".to_string(),
                id: Some(stale_ref_id),
            },
            "fields[0]".to_string(),
        )),
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params, vec!["redeemer".to_string()]);
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::FieldAccess { record, selector, .. }
                        if selector.as_pretty_name() == "fields[0]"
                            && matches!(
                                record.as_ref(),
                                PseudoExpr::Var { name, id, .. }
                                    if name == "redeemer"
                                        && (id.get() == Some(stale_ref_id)
                                            || id.get() == Some(param_id))
                            )
                ),
                "lambda param should keep a readable binding instead of being anonymised by a mismatched body ref id: {body:?}"
            );
        }
        other => panic!("expected lambda after simplify, got: {other:?}"),
    }
}

#[test]
fn test_lambda_force_alias_value_uses_param_var_id() {
    let param_id = VarId::from_raw(731);
    let force_param = || PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("d", param_id)));
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("d", param_id)],
        body: PBox::new(PseudoExpr::Tuple(
            vec![force_param(), force_param(), force_param()].into(),
        )),
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "d");
            assert_eq!(params[0].id, param_id);

            match body.as_ref() {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    assert_eq!(name, "d_forced");
                    assert!(
                        !id.is_none_or(|v| v.is_compat_placeholder()),
                        "force alias binder should use a real local id, got {id:?}"
                    );
                    assert!(
                        matches!(
                            value.as_ref(),
                            PseudoExpr::Force(inner)
                                if matches!(
                                    inner.as_ref(),
                                    PseudoExpr::Var { name, id, .. }
                                        if name == "d" && *id == Some(param_id)
                                )
                        ),
                        "inserted force alias value must reference the lambda param id, got: {value:?}"
                    );
                    assert!(
                        matches!(
                            body.as_ref(),
                            PseudoExpr::Tuple(items)
                                if items.iter().all(|item| matches!(
                                    item,
                                    PseudoExpr::Var { name, id: item_id, .. }
                                        if name == "d_forced" && item_id == id
                                ))
                        ),
                        "force alias body should reuse the inserted alias id, got: {body:?}"
                    );
                }
                other => panic!("expected force alias let in lambda body, got: {other:?}"),
            }
        }
        other => panic!("expected lambda after simplify, got: {other:?}"),
    }
}

#[test]
fn test_lambda_force_alias_noop_for_only_same_name_foreign_force_refs() {
    let outer_id = VarId::from_raw(736);
    let inner_id = VarId::from_raw(737);
    let force_inner = || PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", inner_id)));
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x", outer_id)],
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Lambda {
                    params: vec![Binder::new("x", inner_id)],
                    body: PBox::new(PseudoExpr::Tuple(
                        vec![force_inner(), force_inner(), force_inner()].into(),
                    )),
                },
                PseudoExpr::var_with_id("x", outer_id),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);

    assert!(
        matches!(
            simplified,
            PseudoExpr::Lambda { body, .. }
                if !matches!(body.as_ref(), PseudoExpr::Let { name, .. } if name == "x_forced")
        ),
        "foreign same-name force refs alone must not create an outer force alias"
    );
}

#[test]
fn test_lambda_force_alias_rewrites_outer_refs_under_same_name_inner_lambda() {
    let outer_id = VarId::from_raw(738);
    let inner_id = VarId::from_raw(739);
    let force_outer = || PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", outer_id)));
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x", outer_id)],
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Lambda {
                    params: vec![Binder::new("x", inner_id)],
                    body: PBox::new(PseudoExpr::Tuple(
                        vec![force_outer(), force_outer(), force_outer()].into(),
                    )),
                },
                PseudoExpr::var_with_id("x", outer_id),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Lambda { body, .. } => {
            let PseudoExpr::Let {
                name,
                id: Some(alias_id),
                value,
                body,
            } = body.as_ref()
            else {
                panic!("expected outer force alias let, got: {body:?}");
            };

            assert_eq!(name, "x_forced");
            assert!(
                matches!(
                    value.as_ref(),
                    PseudoExpr::Force(inner)
                        if matches!(
                            inner.as_ref(),
                            PseudoExpr::Var { name, id, .. }
                                if name == "x" && *id == Some(outer_id)
                        )
                ),
                "outer alias value must force the outer param id, got: {value:?}"
            );

            let PseudoExpr::Tuple(items) = body.as_ref() else {
                panic!("expected tuple after outer alias, got: {body:?}");
            };
            assert_eq!(items.len(), 2);

            let PseudoExpr::Lambda {
                params: inner_params,
                body: inner_body,
            } = &items[0]
            else {
                panic!("expected inner lambda, got: {:?}", items[0]);
            };
            assert_eq!(inner_params, &vec![Binder::new("x", inner_id)]);
            assert!(
                matches!(
                    inner_body.as_ref(),
                    PseudoExpr::Tuple(inner_items)
                        if inner_items.iter().all(|item| matches!(
                            item,
                            PseudoExpr::Var { name, id, .. }
                                if name == "x_forced" && *id == Some(*alias_id)
                        ))
                ),
                "outer force refs under same-name inner lambda should rewrite to the outer alias, got: {inner_body:?}"
            );
            assert!(
                matches!(
                    &items[1],
                    PseudoExpr::Var { name, id, .. } if name == "x" && *id == Some(outer_id)
                ),
                "outer param ref should keep the outer id, got: {:?}",
                items[1]
            );
        }
        other => panic!("expected lambda after simplify, got: {other:?}"),
    }
}
