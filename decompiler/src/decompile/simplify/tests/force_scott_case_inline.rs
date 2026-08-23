use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_scott_case_analysis_both_delay() {
    // force(force(z)(delay(a), delay(b))) -> when z is { Constr<0> -> a; Constr<1> -> b }
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("z")))),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
        ]
        .into(),
    }));

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(matches!(*subject, PseudoExpr::Var { .. }));
            assert_eq!(clauses.len(), 2);
            assert!(matches!(
                &clauses[0].pattern,
                WhenPattern::Constructor {
                    tag: 0,
                    fields,
                    ..
                } if fields.is_empty()
            ));
            assert!(matches!(
                &clauses[1].pattern,
                WhenPattern::Constructor {
                    tag: 1,
                    fields,
                    ..
                } if fields.is_empty()
            ));
        }
        _ => panic!("expected when expression, got: {simplified:?}"),
    }
}

#[test]
fn test_scott_case_analysis_delay_and_lambda() {
    // force(force(z)(delay(nil), fn(h, t) { delay(h + t) }))
    // > when z is { Constr<0> -> nil; Constr<1>(h, t) -> h + t }
    let h_id = VarId::fresh_binding();
    let t_id = VarId::fresh_binding();
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("z")))),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("nil"))),
            PseudoExpr::Lambda {
                params: vec![Binder::new("h", h_id), Binder::new("t", t_id)],
                body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(PseudoExpr::var_with_id("h", h_id)),
                    right: PBox::new(PseudoExpr::var_with_id("t", t_id)),
                }))),
            },
        ]
        .into(),
    }));

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(matches!(*subject, PseudoExpr::Var { .. }));
            assert_eq!(clauses.len(), 2);
            assert!(matches!(
                &clauses[0].pattern,
                WhenPattern::Constructor {
                    tag: 0,
                    fields,
                    ..
                } if fields.is_empty()
            ));
            match &clauses[1].pattern {
                WhenPattern::Constructor { tag: 1, fields, .. } => {
                    assert_eq!(fields.len(), 2);
                    assert_eq!(fields[0].id, h_id);
                    assert_eq!(fields[1].id, t_id);
                }
                _ => panic!("expected constructor pattern with fields"),
            }
            assert!(
                matches!(
                    &clauses[1].body,
                    PseudoExpr::BinOp { left, right, .. }
                        if matches!(left.as_ref(), PseudoExpr::Var { name, id, .. } if name == "h" && *id == Some(h_id))
                            && matches!(right.as_ref(), PseudoExpr::Var { name, id, .. } if name == "t" && *id == Some(t_id))
                ),
                "expected scott branch body refs to preserve original binder ids, got: {:?}",
                clauses[1].body
            );
        }
        _ => panic!("expected when expression, got: {simplified:?}"),
    }
}

#[test]
fn test_scott_case_analysis_delay_and_vars() {
    // force(force(z)(delay(a), b, c))
    // > when z is { Constr<0> -> a; Constr<1> -> b; Constr<2> -> c }
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("z")))),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
            PseudoExpr::var("b"),
            PseudoExpr::var("c"),
        ]
        .into(),
    }));

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 3);
            assert!(matches!(
                &clauses[0].body,
                PseudoExpr::Var { name, .. } if name == "a"
            ));
            assert!(matches!(
                &clauses[1].body,
                PseudoExpr::Var { name, .. } if name == "b"
            ));
            assert!(matches!(
                &clauses[2].body,
                PseudoExpr::Var { name, .. } if name == "c"
            ));
        }
        _ => panic!("expected when expression, got: {simplified:?}"),
    }
}

#[test]
fn test_force_force_field_access_outer_force_collapses() {
    // force(force(x).#3(a, b))(c, d) -> force(x).#3(a, b, c, d)
    let x_id = VarId::from_raw(29200);
    let a_id = VarId::from_raw(29201);
    let b_id = VarId::from_raw(29202);
    let c_id = VarId::from_raw(29203);
    let d_id = VarId::from_raw(29204);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::field_access(
                PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id("x", x_id))),
                "#3".to_string(),
            )),
            args: vec![
                PseudoExpr::var_with_id("a", a_id),
                PseudoExpr::var_with_id("b", b_id),
            ]
            .into(),
        }))),
        args: vec![
            PseudoExpr::var_with_id("c", c_id),
            PseudoExpr::var_with_id("d", d_id),
        ]
        .into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Apply { function, args } => {
            assert_eq!(args.len(), 4);
            assert!(
                matches!(&args[0], PseudoExpr::Var { name, id } if name == "a" && *id == Some(a_id))
            );
            assert!(
                matches!(&args[1], PseudoExpr::Var { name, id } if name == "b" && *id == Some(b_id))
            );
            assert!(
                matches!(&args[2], PseudoExpr::Var { name, id } if name == "c" && *id == Some(c_id))
            );
            assert!(
                matches!(&args[3], PseudoExpr::Var { name, id } if name == "d" && *id == Some(d_id))
            );
            match function.as_ref() {
                PseudoExpr::FieldAccess {
                    record, selector, ..
                } => {
                    assert_eq!(selector.as_pretty_name(), "#3");
                    assert!(matches!(
                        record.as_ref(),
                        PseudoExpr::Force(inner)
                            if matches!(inner.as_ref(), PseudoExpr::Var { name, id } if name == "x" && *id == Some(x_id))
                    ));
                }
                _ => panic!("expected field access function, got: {function:?}"),
            }
        }
        _ => panic!("expected apply expression, got: {simplified:?}"),
    }
}

#[test]
fn test_force_force_field_access_without_outer_args_collapses() {
    // force(force(x).#3(a, b)) -> force(x).#3(a, b)
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::field_access(
            PseudoExpr::Force(PBox::new(PseudoExpr::var("x"))),
            "#3".to_string(),
        )),
        args: vec![PseudoExpr::var("a"), PseudoExpr::var("b")].into(),
    }));

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::Apply { function, args } => {
            assert_eq!(args.len(), 2);
            assert!(matches!(&args[0], PseudoExpr::Var { name, .. } if name == "a"));
            assert!(matches!(&args[1], PseudoExpr::Var { name, .. } if name == "b"));
            match function.as_ref() {
                PseudoExpr::FieldAccess {
                    record, selector, ..
                } => {
                    assert_eq!(selector.as_pretty_name(), "#3");
                    assert!(matches!(
                        record.as_ref(),
                        PseudoExpr::Force(inner)
                            if matches!(inner.as_ref(), PseudoExpr::Var { name, .. } if name == "x")
                    ));
                }
                _ => panic!("expected field access function, got: {function:?}"),
            }
        }
        _ => panic!("expected apply expression, got: {simplified:?}"),
    }
}

#[test]
fn test_single_use_inlining_keeps_force_apply_binding_when_force_used() {
    // Keep:
    // let v63 = force(u63)(k)
    // in force(v63).#1
    // so single-use inlining does not recreate force(force(u63)(k)).#1.
    let expr = PseudoExpr::Let {
        name: "v63".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("u63")))),
            args: vec![PseudoExpr::var("k")].into(),
        }),
        body: PBox::new(PseudoExpr::field_access(
            PseudoExpr::Force(PBox::new(PseudoExpr::var("v63"))),
            "#1".to_string(),
        )),
    };

    let simplified = simplify(expr);
    let output = simplified.to_pretty();
    assert!(
        !output.contains("force(force("),
        "expected no reintroduced force(force(...)) via inlining, got:\n{}",
        output
    );
}

#[test]
fn test_scott_case_not_triggered_in_safe_mode() {
    // In safe_mode, Scott-encoded case analysis should NOT be rewritten
    let expr = PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("z")))),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("a"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("b"))),
        ]
        .into(),
    }));

    let simplified = simplify_with_options(expr, true);
    assert!(matches!(simplified, PseudoExpr::Force(_)));
}

#[test]
fn test_let_single_delayed_fst_selector_tracked() {
    // let x = delay(fn(a, _) { a }) in force(x)
    // > force(x) should simplify to fn(ok, _) { ok }
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec!["a".to_string().into(), "_".to_string().into()],
            body: PBox::new(PseudoExpr::var("a")),
        }))),
        body: PBox::new(PseudoExpr::Tuple(
            vec![PseudoExpr::Force(PBox::new(PseudoExpr::var("x")))].into(),
        )),
    };

    let simplified = simplify(expr);
    // After simplification, the forced selector should become a lambda with
    // binder/ref identity preserved inside the synthesized tuple element.
    match simplified {
        PseudoExpr::Tuple(elements) => {
            let [PseudoExpr::Lambda { params, body }] = elements.as_slice() else {
                panic!("expected tuple with selector lambda, got: {elements:?}");
            };
            assert_eq!(params.len(), 2);
            let kept = &params[0];
            assert_eq!(kept.as_str(), "ok");
            assert!(
                matches!(body.as_ref(), PseudoExpr::Var { name, id, .. } if name == "ok" && *id == Some(kept.id)),
                "expected synthesized selector body to reuse binder id, got: {body:?}"
            );
        }
        other => panic!("expected tuple with selector lambda, got: {other:?}"),
    }
}
