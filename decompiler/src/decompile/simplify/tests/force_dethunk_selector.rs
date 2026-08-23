use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_let_single_force_dethunk_closed_value() {
    let delayed_id = PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
        params: vec!["x".to_string().into(), "_".to_string().into()],
        body: PBox::new(PseudoExpr::var("x")),
    }));
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(delayed_id),
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
fn test_let_single_double_force_dethunk_closed_value() {
    let delayed_delayed_id = PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
        PseudoExpr::Lambda {
            params: vec!["x".to_string().into(), "_".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        },
    ))));
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(delayed_delayed_id),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(
            PseudoExpr::var("k"),
        ))))),
    };

    let simplified = simplify(expr);
    assert!(!matches!(simplified, PseudoExpr::Let { .. }));
    assert!(!matches!(
        simplified,
        PseudoExpr::Force(inner)
            if matches!(inner.as_ref(), PseudoExpr::Force(_))
    ));
}

#[test]
fn test_delay_non_lambda_inlined() {
    // let k = delay(y) in fn(y) { force(k) } -> fn(_) { y }
    // Delay(Var) is NOT excluded from single-use inlining (only Delay(Lambda/RecFn) is).
    // The unused lambda param "y" is renamed to "_"; inlining k into force(k)
    // gives force(delay(y)) -> the outer y.
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("y")))),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["y".to_string().into()],
            body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("k")))),
        }),
    };

    let simplified = simplify(expr);
    // Delay(Var) is inlined, force/delay cancel -> fn(_) { y }
    match simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params, vec!["_"]);
            assert!(matches!(*body, PseudoExpr::Var { ref name, .. } if name == "y"));
        }
        _ => panic!("expected lambda after inlining, got: {:?}", simplified),
    }
}

#[test]
fn test_small_function_inlining_preserves_multi_param_selector_aliases() {
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into(), "_".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }),
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond")),
            then_branch: PBox::new(PseudoExpr::var("k")),
            else_branch: PBox::new(PseudoExpr::Lambda {
                params: vec!["_".to_string().into(), "y".to_string().into()],
                body: PBox::new(PseudoExpr::var("y")),
            }),
        }),
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "k");
            match body.into_inner() {
                PseudoExpr::If { then_branch, .. } => {
                    assert!(
                        matches!(then_branch.as_ref(), PseudoExpr::Var { name, .. } if name == "k"),
                        "selector alias should stay as var in the body, got: {:?}",
                        then_branch
                    );
                }
                other => {
                    panic!("expected if body after preserving selector alias, got: {other:?}")
                }
            }
        }
        other => panic!("selector alias should not be inlined back to lambda, got: {other:?}"),
    }
}

#[test]
fn test_tracked_selector_var_application_rewrites_to_field_access() {
    let expr = PseudoExpr::Let {
        name: "choose_fst".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into(), "_".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("pair_value")),
            args: vec![PseudoExpr::var("choose_fst")].into(),
        }),
    };

    let simplified = simplify(expr);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::FieldAccess { record, selector, .. }
                if selector.is_pair_fst()
                    && matches!(record.as_ref(), PseudoExpr::Var { name, .. } if name == "pair_value")
        ),
        "tracked selector var should rewrite unary Scott application to field access, got: {simplified:?}"
    );
}
