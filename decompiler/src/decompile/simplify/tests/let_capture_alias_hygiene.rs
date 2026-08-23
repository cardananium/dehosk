use super::*;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;

#[test]
fn test_let_value_does_not_capture_own_binder_id_during_simplify() {
    let outer_id = VarId::from_raw(9810);
    let inner_id = VarId::from_raw(9811);

    let inner_ref = || PseudoExpr::Var {
        name: "x_1".to_string(),
        id: Some(inner_id),
    };

    let expr = PseudoExpr::Let {
        name: "x_1".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::ByteArray(vec![1])),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Let {
                    name: "x_1".to_string(),
                    id: Some(inner_id),
                    value: PBox::new(PseudoExpr::BuiltinCall {
                        name: BuiltinId::expect_known("Data.to_bytes"),
                        args: vec![PseudoExpr::Var {
                            name: "x_1".to_string(),
                            id: Some(VarId::fresh_compat_placeholder()),
                        }]
                        .into(),
                    }),
                    body: PBox::new(PseudoExpr::Tuple((vec![inner_ref(), inner_ref()]).into())),
                },
                PseudoExpr::Var {
                    name: "x_1".to_string(),
                    id: Some(outer_id),
                },
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);
    let report = audit_id_orphans(&simplified, &[]);

    assert_eq!(
        report.stranded,
        0,
        "a let value must not acquire its own binder id while simplifying; stranded: {:?}\n{}",
        report.stranded_by_name,
        simplified.to_pretty()
    );
}

#[test]
fn test_let_value_self_ref_without_outer_shadow_uses_compat_placeholder() {
    let binding_id = VarId::from_raw(9820);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: BuiltinId::expect_known("Data.to_bytes"),
            args: vec![PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(binding_id),
            }]
            .into(),
        }),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(binding_id),
        }),
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::BuiltinCall { args, .. } => {
            assert!(
                matches!(
                    args.as_slice(),
                    [PseudoExpr::Var { name, id }]
                        if name == "x"
                            && id.get().is_none()
                            && *id != Some(binding_id)
                            && id.is_some_and(|v| v.is_compat_placeholder())
                ),
                "value-side self ref should be restored to an explicit compat placeholder, got: {args:?}"
            );
        }
        other => panic!("expected inlined builtin call, got: {other:?}"),
    }
}

#[test]
fn test_alias_let_substitution_preserves_aliased_var_id() {
    let x_id = VarId::from_raw(9830);
    let y_id = VarId::from_raw(9831);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::var_with_id("y", y_id)),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("x", x_id),
                PseudoExpr::Int(0.into()),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::Tuple(items)
                if matches!(&items[0], PseudoExpr::Var { name, id, .. } if name == "y" && id.get() == Some(y_id))
        ),
        "alias-let collapse should retarget x refs to y's VarId, got: {simplified:?}"
    );

    let report = audit_id_orphans(&simplified, &[("y".to_string(), y_id)]);
    assert_eq!(
        report.stranded, 0,
        "alias-let collapse must not strand the dropped x binder id: {:?}\n{:?}",
        report.stranded_by_name, simplified
    );
}

#[test]
fn test_alias_let_substitution_skips_inner_new_name_binding() {
    let x_id = VarId::from_raw(9840);
    let outer_y_id = VarId::from_raw(9841);
    let inner_y_id = VarId::from_raw(9842);
    let record_id = VarId::from_raw(9843);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::var_with_id("y", outer_y_id)),
        body: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(inner_y_id),
            value: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::var_with_id("record", record_id)),
                selector: crate::pseudo::FieldSelector::from_display_name("tag"),
            }),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("x", x_id),
                    PseudoExpr::var_with_id("y", inner_y_id),
                    PseudoExpr::var_with_id("y", inner_y_id),
                ]
                .into(),
            )),
        }),
    };

    let simplified = simplify(expr);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } if name == "x"
                && id.get() == Some(x_id)
                && matches!(value.as_ref(), PseudoExpr::Var { name, id, .. } if name == "y" && id.get() == Some(outer_y_id))
                && matches!(
                    body.as_ref(),
                    PseudoExpr::Let { name, id, body, .. }
                        if name == "y"
                            && id.get() == Some(inner_y_id)
                            && matches!(
                                body.as_ref(),
                                PseudoExpr::Tuple(items)
                                    if matches!(&items[0], PseudoExpr::Var { name, id, .. } if name == "x" && id.get() == Some(x_id))
                                        && matches!(&items[1], PseudoExpr::Var { name, id, .. } if name == "y" && id.get() == Some(inner_y_id))
                                        && matches!(&items[2], PseudoExpr::Var { name, id, .. } if name == "y" && id.get() == Some(inner_y_id))
                            )
                )
        ),
        "alias-let collapse should not capture x refs under an inner y binder, got: {simplified:?}"
    );

    let report = audit_id_orphans(
        &simplified,
        &[
            ("y".to_string(), outer_y_id),
            ("record".to_string(), record_id),
        ],
    );
    assert_eq!(
        report.stranded, 0,
        "capture guard should preserve all binder ids: {:?}\n{:?}",
        report.stranded_by_name, simplified
    );
}
