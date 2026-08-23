use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_force_force_delayed_rec_var_unwraps() {
    let y_delayed = PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
        PseudoExpr::Lambda {
            params: vec!["b".to_string().into()],
            body: PBox::new(PseudoExpr::Let {
                name: "c".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::Lambda {
                    params: vec!["d".to_string().into(), "e".to_string().into()],
                    body: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("b")),
                        args: vec![
                            PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("d")),
                                args: vec![PseudoExpr::var("d")].into(),
                            },
                            PseudoExpr::var("e"),
                        ]
                        .into(),
                    }),
                }),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("c")),
                    args: vec![PseudoExpr::var("c")].into(),
                }),
            }),
        },
    ))));

    let expr = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(y_delayed),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(
                PseudoExpr::var("r"),
            ))))),
            args: vec![PseudoExpr::Lambda {
                params: vec!["self".to_string().into(), "n".to_string().into()],
                body: PBox::new(PseudoExpr::var("n")),
            }]
            .into(),
        }),
    };

    let simplified = simplify(expr);
    assert_eq!(Simplifier::count_force_chain_uses(&simplified, "r", 2), 0);
}

#[test]
fn test_force_apply_forced_selector_var_simplifies() {
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
            PseudoExpr::Lambda {
                params: vec!["x".to_string().into(), "_".to_string().into()],
                body: PBox::new(PseudoExpr::var("x")),
            },
        ))))),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("k")))),
            args: vec![
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(11))),
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(22))),
            ]
            .into(),
        }))),
    };

    let simplified = simplify(expr);
    assert!(matches!(simplified, PseudoExpr::Int(_)));
}

#[test]
fn test_single_force_scott_rewrite_preserves_branch_param_ids() {
    let subject_id = VarId::new(110);
    let left_id = VarId::new(111);
    let right_id = VarId::new(112);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var_with_id(
            "subject", subject_id,
        )))),
        args: vec![PseudoExpr::Lambda {
            params: vec![Binder::new("left", left_id), Binder::new("right", right_id)],
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("left", left_id),
                    PseudoExpr::var_with_id("right", right_id),
                ]
                .into(),
            )),
        }]
        .into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(
                matches!(
                    subject.as_ref(),
                    PseudoExpr::Var { name, id } if name == "subject" && *id == Some(subject_id)
                ),
                "expected Scott subject id to be moved intact, got: {subject:?}"
            );
            let [clause] = clauses.as_slice() else {
                panic!("expected one Scott branch, got: {clauses:?}");
            };
            let WhenPattern::Constructor { fields, .. } = &clause.pattern else {
                panic!("expected constructor pattern, got: {:?}", clause.pattern);
            };
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].as_str(), "left");
            assert_eq!(fields[0].id, left_id);
            assert_eq!(fields[1].as_str(), "right");
            assert_eq!(fields[1].id, right_id);
            assert!(
                matches!(
                    &clause.body,
                    PseudoExpr::Tuple(items)
                        if matches!(&items[0], PseudoExpr::Var { name, id, .. } if name == "left" && *id == Some(left_id))
                            && matches!(&items[1], PseudoExpr::Var { name, id, .. } if name == "right" && *id == Some(right_id))
                ),
                "expected Scott body to keep the original branch binder ids, got: {:?}",
                clause.body
            );
        }
        other => panic!("expected Scott rewrite to when, got: {other:?}"),
    }
}

#[test]
fn test_double_force_scott_rewrite_preserves_branch_param_ids() {
    let subject_id = VarId::new(120);
    let ok_id = VarId::new(121);
    let err_left_id = VarId::new(122);
    let err_right_id = VarId::new(123);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Force(PBox::new(
            PseudoExpr::var_with_id("subject", subject_id),
        ))))),
        args: vec![
            PseudoExpr::Lambda {
                params: vec![Binder::new("ok", ok_id)],
                body: PBox::new(PseudoExpr::var_with_id("ok", ok_id)),
            },
            PseudoExpr::Lambda {
                params: vec![
                    Binder::new("err_left", err_left_id),
                    Binder::new("err_right", err_right_id),
                ],
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("err_left", err_left_id),
                        PseudoExpr::var_with_id("err_right", err_right_id),
                    ]
                    .into(),
                )),
            },
        ]
        .into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(
                matches!(
                    subject.as_ref(),
                    PseudoExpr::Var { name, id } if name == "subject" && *id == Some(subject_id)
                ),
                "expected double-force Scott subject id to be moved intact, got: {subject:?}"
            );
            assert_eq!(clauses.len(), 2);
            let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
                panic!(
                    "expected constructor pattern in first branch, got: {:?}",
                    clauses[0].pattern
                );
            };
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].as_str(), "ok");
            assert_eq!(fields[0].id, ok_id);
            assert!(
                matches!(
                    &clauses[0].body,
                    PseudoExpr::Var { name, id, .. } if name == "ok" && *id == Some(ok_id)
                ),
                "expected first Scott branch body to keep ok binder id, got: {:?}",
                clauses[0].body
            );

            let WhenPattern::Constructor { fields, .. } = &clauses[1].pattern else {
                panic!(
                    "expected constructor pattern in second branch, got: {:?}",
                    clauses[1].pattern
                );
            };
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].as_str(), "err_left");
            assert_eq!(fields[0].id, err_left_id);
            assert_eq!(fields[1].as_str(), "err_right");
            assert_eq!(fields[1].id, err_right_id);
            assert!(
                matches!(
                    &clauses[1].body,
                    PseudoExpr::Tuple(items)
                        if matches!(&items[0], PseudoExpr::Var { name, id, .. } if name == "err_left" && *id == Some(err_left_id))
                            && matches!(&items[1], PseudoExpr::Var { name, id, .. } if name == "err_right" && *id == Some(err_right_id))
                ),
                "expected second Scott branch body to keep both binder ids, got: {:?}",
                clauses[1].body
            );
        }
        other => panic!("expected Scott rewrite to when, got: {other:?}"),
    }
}

#[test]
fn test_force_apply_forced_transitive_selector_var_simplifies() {
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Delay(PBox::new(
            PseudoExpr::Lambda {
                params: vec!["x".to_string().into(), "_".to_string().into()],
                body: PBox::new(PseudoExpr::var("x")),
            },
        ))))),
        body: PBox::new(PseudoExpr::Let {
            name: "k2".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::var("k")),
            body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::var("k2")))),
                args: vec![
                    PseudoExpr::Delay(PBox::new(PseudoExpr::int(11))),
                    PseudoExpr::Delay(PBox::new(PseudoExpr::int(22))),
                ]
                .into(),
            }))),
        }),
    };

    let simplified = simplify(expr);
    assert!(matches!(simplified, PseudoExpr::Int(_)));
}
