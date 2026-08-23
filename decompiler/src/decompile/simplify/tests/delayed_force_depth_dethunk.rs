use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_delay_depth_lowering_for_all_forced_uses() {
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
            PseudoExpr::field_access(PseudoExpr::var("q"), "tag".to_string()),
        ))))),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Force(PBox::new(PseudoExpr::var("k"))),
                PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var(
                    "k",
                ))))),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);
    assert_eq!(Simplifier::count_force_chain_uses(&simplified, "k", 2), 0);
}

#[test]
fn test_delay_force_known_delayed_alias_var_to_var() {
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }))),
        body: PBox::new(PseudoExpr::Let {
            name: "k".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::var("y")),
            body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Force(PBox::new(
                PseudoExpr::var("k"),
            ))))),
        }),
    };

    let simplified = simplify(expr);
    assert!(!matches!(
        simplified,
        PseudoExpr::Let { body, .. }
            if matches!(
                body.as_ref(),
                PseudoExpr::Let { body, .. }
                    if matches!(
                        body.as_ref(),
                        PseudoExpr::Delay(inner)
                            if matches!(
                                inner.as_ref(),
                                PseudoExpr::Force(force_inner)
                                    if matches!(force_inner.as_ref(), PseudoExpr::Var { name, .. } if name == "k")
                            )
                    )
            )
    ));
}

#[test]
fn test_delay_force_delay_chain_structural_cancellation() {
    let expr = PseudoExpr::Delay(PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Force(
        PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
            PseudoExpr::var("x"),
        ))))),
    )))));

    let simplified = simplify(expr);
    assert!(matches!(
        simplified,
        PseudoExpr::Delay(inner)
            if matches!(inner.as_ref(), PseudoExpr::Var { name, .. } if name == "x")
    ));
}

#[test]
fn test_delayed_value_depth_tracking_respects_lambda_shadowing() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
            PseudoExpr::Lambda {
                params: vec!["k".to_string().into()],
                body: PBox::new(PseudoExpr::var("k")),
            },
        ))))),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Force(PBox::new(
                PseudoExpr::Force(PBox::new(PseudoExpr::var("x"))),
            ))))),
        }),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Lambda { body, .. } => {
            assert!(matches!(
                body.as_ref(),
                PseudoExpr::Delay(inner)
                    if matches!(
                        inner.as_ref(),
                        PseudoExpr::Force(inner2)
                            if matches!(
                                inner2.as_ref(),
                                PseudoExpr::Force(inner3)
                                    if matches!(inner3.as_ref(), PseudoExpr::Var { name, .. } if name == "x")
                            )
                    )
            ));
        }
        _ => panic!("expected lambda body"),
    }
}

#[test]
fn test_let_force_dethunk_field_access_non_safe_mode() {
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("q"),
            "tag".to_string(),
        )))),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("k")))),
    };

    let simplified = simplify(expr);
    assert!(!matches!(simplified, PseudoExpr::Let { .. }));
    assert!(!matches!(
        simplified,
        PseudoExpr::Force(inner)
            if matches!(inner.as_ref(), PseudoExpr::Var { name, .. } if name == "k")
    ));
}

#[test]
fn test_let_force_single_use_closed_lambda_inlined() {
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }))),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("k")))),
    };

    let simplified = simplify(expr);
    assert!(matches!(simplified, PseudoExpr::Lambda { .. }));
}

#[test]
fn test_let_multi_force_lambda_dethunk_without_duplication() {
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }))),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Force(PBox::new(PseudoExpr::var("k"))),
                PseudoExpr::Force(PBox::new(PseudoExpr::var("k"))),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);
    assert_eq!(Simplifier::count_force_chain_uses(&simplified, "k", 1), 0);
}

#[test]
fn test_mixed_plain_and_force_use_does_not_trigger_lambda_dethunk() {
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }))),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Force(PBox::new(PseudoExpr::var("k"))),
                PseudoExpr::var("k"),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Let { body, .. } => {
            assert!(Simplifier::count_force_chain_uses(body.as_ref(), "k", 1) >= 1);
        }
        _ => panic!("expected let"),
    }
}

#[test]
fn test_let_multi_force_recfn_dethunk_without_duplication() {
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::RecFn {
            name: "loop".to_string().into(),
            params: vec!["n".to_string().into()],
            body: PBox::new(PseudoExpr::var("n")),
        }))),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::Force(PBox::new(PseudoExpr::var("k"))),
                PseudoExpr::Force(PBox::new(PseudoExpr::var("k"))),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);
    assert_eq!(Simplifier::count_force_chain_uses(&simplified, "k", 1), 0);
}

#[test]
fn test_single_delayed_selector_tracking_respects_shadowing() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec!["k".to_string().into()],
            body: PBox::new(PseudoExpr::Lambda {
                params: vec!["k".to_string().into()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("f")),
                    args: vec![PseudoExpr::Force(PBox::new(PseudoExpr::var("k")))].into(),
                }),
            }),
        }),
        args: vec![PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec!["_".to_string().into(), "err".to_string().into()],
            body: PBox::new(PseudoExpr::var("err")),
        }))]
        .into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Lambda { body, .. } => match body.as_ref() {
            PseudoExpr::Apply { args, .. } => {
                assert!(matches!(args.first(), Some(PseudoExpr::Force(_))));
            }
            _ => panic!("expected apply in inner lambda"),
        },
        _ => panic!("expected simplified inner lambda"),
    }
}
