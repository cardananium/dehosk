use super::delayed_rec_force_expansion::assert_no_duplicate_binder_var_ids;
use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_partial_comparison_application_preserves_lambda_param_id() {
    let target_id = VarId::new(9281);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Int.eq"),
            args: vec![].into(),
        }),
        args: vec![PseudoExpr::var_with_id("target", target_id)].into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Lambda { params, body } => {
            let [param] = params.as_slice() else {
                panic!("expected single lambda param, got: {params:?}");
            };
            assert_eq!(param.as_str(), "x");
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::BinOp { op: BinaryOp::Eq, left, right }
                        if matches!(left.as_ref(), PseudoExpr::Var { name, id, .. } if name == "x" && *id == Some(param.id))
                            && matches!(right.as_ref(), PseudoExpr::Var { name, id } if name == "target" && *id == Some(target_id))
                ),
                "expected partial Int.eq application to keep lambda binder id and move the target arg, got: {body:?}"
            );
        }
        other => {
            panic!("expected partial comparison application to produce lambda, got: {other:?}")
        }
    }
}

#[test]
fn test_direct_recfn_apply_with_ignored_non_thunk_arg_expands() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::RecFn {
            name: "b9".to_string().into(),
            params: vec!["_".to_string().into()],
            body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
                PseudoExpr::Lambda {
                    params: vec!["x".to_string().into()],
                    body: PBox::new(PseudoExpr::var("x")),
                },
            ))))),
        }),
        args: vec![PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec!["y".to_string().into()],
            body: PBox::new(PseudoExpr::var("y")),
        }))]
        .into(),
    };

    let simplified = simplify(expr);
    assert!(!matches!(simplified, PseudoExpr::Apply { .. }));
}

#[test]
fn test_direct_recfn_apply_with_ignored_effectful_arg_kept() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::RecFn {
            name: "b9".to_string().into(),
            params: vec!["_".to_string().into()],
            body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::int(1)))),
        }),
        args: vec![PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::string("m")),
            value: PBox::new(PseudoExpr::int(0)),
        }]
        .into(),
    };

    let simplified = simplify(expr);
    assert!(matches!(simplified, PseudoExpr::Apply { .. }));
}

#[test]
fn test_direct_recfn_apply_freshens_retained_recfn_value_binders() {
    fn find_let_value<'a>(
        expr: &'a PseudoExpr,
        target: &str,
    ) -> Option<(Option<VarId>, &'a PseudoExpr)> {
        if let PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } = expr
        {
            if name == target {
                return Some((*id, value.as_ref()));
            }
            return find_let_value(body, target);
        }
        None
    }

    let rec_id = VarId::new(9_860);
    let param_id = VarId::new(9_861);
    let seed_id = VarId::new(9_862);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("loop", rec_id),
            params: vec![Binder::new("n", param_id)],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::var_with_id("n", param_id)),
                    right: PBox::new(PseudoExpr::int(0)),
                }),
                then_branch: PBox::new(PseudoExpr::int(0)),
                else_branch: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("loop", rec_id)),
                    args: vec![PseudoExpr::BinOp {
                        op: BinaryOp::Sub,
                        left: PBox::new(PseudoExpr::var_with_id("n", param_id)),
                        right: PBox::new(PseudoExpr::int(1)),
                    }]
                    .into(),
                }),
            }),
        }),
        args: vec![PseudoExpr::var_with_id("seed", seed_id)].into(),
    };

    let simplified = simplify(expr);

    assert_no_duplicate_binder_var_ids(&simplified);
    let (call_site_rec_id, retained_value) =
        find_let_value(&simplified, "loop").expect("expected retained recursive let binding");
    let PseudoExpr::RecFn { name, params, body } = retained_value else {
        panic!("expected retained value to stay RecFn, got: {retained_value:?}");
    };
    assert_ne!(
        Some(name.id),
        call_site_rec_id,
        "retained RecFn self binder must not share the call-site let id"
    );
    assert_ne!(
        params.first().map(|param| param.id),
        Some(param_id),
        "retained RecFn param binder must not share the call-site param id"
    );
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::If { else_branch, .. }
                if matches!(
                    else_branch.as_ref(),
                    PseudoExpr::Apply { function, .. }
                        if matches!(
                            function.as_ref(),
                            PseudoExpr::Var { name: call_name, id }
                                if call_name == "loop" && *id == Some(name.id)
                        )
                )
        ),
        "freshened retained RecFn body refs should target its own self binder, got: {body:?}"
    );

    let report = audit_id_orphans(&simplified, &[("seed".to_string(), seed_id)]);
    assert_eq!(
        report.stranded + report.truly_free,
        0,
        "direct RecFn application should not strand ids, got {report:?}\n{}",
        simplified.to_pretty()
    );
}
