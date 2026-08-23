use super::*;
use crate::pseudo::var_id::VarId;
use std::collections::HashSet;

#[test]
fn test_expr_contains_var_checks_let_value_but_not_shadowed_body() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),

        value: PBox::new(PseudoExpr::var("x")),
        body: PBox::new(PseudoExpr::var("x")),
    };

    assert!(expr_contains_var(&expr, "x"));
}

#[test]
fn test_register_free_vars_respects_body_only_let_binding_scope() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),

        value: PBox::new(PseudoExpr::var("x")),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("x")),
            args: vec![PseudoExpr::var("y")].into(),
        }),
    };

    let mut global_names = HashSet::new();
    register_free_vars(&expr, &HashSet::new(), &mut global_names);

    assert!(global_names.contains("x"));
    assert!(global_names.contains("y"));
    assert_eq!(global_names.len(), 2);
}

#[test]
fn test_collect_all_var_names_visitor_covers_nested_shapes() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),

        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var("x")),
                    subject_name: None,
                    clauses: vec![WhenClause::new(
                        WhenPattern::Wildcard,
                        PseudoExpr::Trace {
                            message: PBox::new(PseudoExpr::var("msg")),
                            value: PBox::new(PseudoExpr::var("y")),
                        },
                    )],
                }]
                .into(),
            }),
        }),
        body: PBox::new(PseudoExpr::var("f")),
    };

    let mut names = HashSet::new();
    collect_all_var_names(&expr, &mut names);

    assert!(names.contains("f"));
    assert!(names.contains("x"));
    assert!(names.contains("msg"));
    assert!(names.contains("y"));
}

#[test]
fn test_uniquify_no_conflict() {
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

            value: PBox::new(PseudoExpr::var("a")),
            body: PBox::new(PseudoExpr::var("b")),
        }),
    };
    let result = uniquify_let_names(expr);
    let output = result.to_pretty();
    assert!(output.contains("let a ="));
    assert!(output.contains("let b ="));
}

#[test]
fn test_uniquify_shadowed_let() {
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "a".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(PseudoExpr::var("a")),
        }),
    };
    let result = uniquify_let_names(expr);
    if let PseudoExpr::Let { name: n1, body, .. } = result {
        assert_eq!(n1, "a");
        if let PseudoExpr::Let {
            name: n2,
            body: inner_body,
            ..
        } = body.into_inner()
        {
            assert_eq!(n2, "a_2");
            if let PseudoExpr::Var { name, .. } = inner_body.into_inner() {
                assert_eq!(name, "a_2");
            }
        }
    }
}

#[test]
fn test_uniquify_sibling_scopes() {
    let lam1 = PseudoExpr::Lambda {
        params: vec!["x".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "tail".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

            value: PBox::new(PseudoExpr::var("x")),
            body: PBox::new(PseudoExpr::var("tail")),
        }),
    };
    let lam2 = PseudoExpr::Lambda {
        params: vec!["y".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "tail".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

            value: PBox::new(PseudoExpr::var("y")),
            body: PBox::new(PseudoExpr::var("tail")),
        }),
    };
    let expr = PseudoExpr::Apply {
        function: PBox::new(lam1),
        args: vec![lam2].into(),
    };
    let result = uniquify_let_names(expr);
    let output = result.to_pretty();
    assert!(output.contains("tail_2"));
}

#[test]
fn collapse_tail_chains_does_not_count_lambda_shadow_by_name() {
    let tail_id = VarId::new(401);
    let shadow_tail_id = VarId::new(402);
    let xs_id = VarId::new(403);
    let expr = PseudoExpr::let_bind_with_id(
        "tail",
        tail_id,
        PseudoExpr::builtin("List.tail", vec![PseudoExpr::var_with_id("xs", xs_id)]),
        PseudoExpr::Lambda {
            params: vec![Binder::new("tail", shadow_tail_id)],
            body: PBox::new(PseudoExpr::var_with_id("tail", shadow_tail_id)),
        },
    );

    let out = collapse_tail_chains(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { name, id, body, .. }
                if name == "tail"
                    && *id == Some(tail_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Lambda { body, .. }
                            if matches!(
                                body.as_ref(),
                                PseudoExpr::Var { name, id } if name == "tail" && *id == Some(shadow_tail_id)
                            )
                    )
        ),
        "collapse_tail_chains must not drop a tail let because of a same-name lambda param, got: {out:?}"
    );
}

#[test]
fn collapse_tail_chains_does_not_substitute_when_pattern_shadow() {
    let tail_id = VarId::new(404);
    let pattern_tail_id = VarId::new(405);
    let xs_id = VarId::new(406);
    let subject_id = VarId::new(407);
    let expr = PseudoExpr::let_bind_with_id(
        "tail",
        tail_id,
        PseudoExpr::builtin("List.tail", vec![PseudoExpr::var_with_id("xs", xs_id)]),
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("ys", subject_id)),
            subject_name: None,
            clauses: vec![WhenClause::new(
                WhenPattern::Var(Binder::new("tail", pattern_tail_id)),
                PseudoExpr::var_with_id("tail", pattern_tail_id),
            )],
        },
    );

    let out = collapse_tail_chains(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Let { name, id, body, .. }
                if name == "tail"
                    && *id == Some(tail_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::When { clauses, .. }
                            if matches!(
                                clauses.as_slice(),
                                [WhenClause { body, .. }]
                                    if matches!(
                                        body,
                                        PseudoExpr::Var { name, id } if name == "tail" && *id == Some(pattern_tail_id)
                                    )
                            )
                    )
        ),
        "collapse_tail_chains must not substitute a same-name when pattern binder, got: {out:?}"
    );
}

#[test]
fn collapse_tail_chains_substitutes_exact_tail_binder_id() {
    let tail_id = VarId::new(408);
    let xs_id = VarId::new(409);
    let expr = PseudoExpr::let_bind_with_id(
        "tail",
        tail_id,
        PseudoExpr::builtin("List.tail", vec![PseudoExpr::var_with_id("xs", xs_id)]),
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::builtin("List.tail", vec![])),
            args: vec![PseudoExpr::var_with_id("tail", tail_id)].into(),
        },
    );

    let out = collapse_tail_chains(expr);

    assert!(
        matches!(
            &out,
            PseudoExpr::Apply { args, .. }
                if matches!(
                    args.as_slice(),
                    [PseudoExpr::BuiltinCall { name, args }]
                        if name == "List.tail"
                            && matches!(
                                args.as_slice(),
                                [PseudoExpr::Var { name, id }]
                                    if name == "xs" && *id == Some(xs_id)
                            )
                )
        ),
        "collapse_tail_chains should still inline the exact single-use tail binder, got: {out:?}"
    );
}

#[test]
fn test_uniquify_let_recfn_preserved() {
    // let f = rec fn f(x) { f(x) } in f(1)
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

        value: PBox::new(PseudoExpr::RecFn {
            name: "f".to_string().into(),
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![PseudoExpr::var("x")].into(),
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::int(1)].into(),
        }),
    };
    let result = uniquify_let_names(expr);
    if let PseudoExpr::Let { name, value, .. } = &result {
        if let PseudoExpr::RecFn { name: fn_name, .. } = value.as_ref() {
            assert_eq!(name, fn_name.as_str(), "Let name and RecFn name must match");
        }
    }
}

#[test]
fn test_uniquify_let_recfn_renamed() {
    // let f = rec fn f(x) { f(x) } in let f = rec fn f(y) { f(y) } in f(1)
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

        value: PBox::new(PseudoExpr::RecFn {
            name: "f".to_string().into(),
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![PseudoExpr::var("x")].into(),
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "f".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),

            value: PBox::new(PseudoExpr::RecFn {
                name: "f".to_string().into(),
                params: vec!["y".to_string().into()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("f")),
                    args: vec![PseudoExpr::var("y")].into(),
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };
    let result = uniquify_let_names(expr);
    // First f stays as "f", second gets renamed to "f_2"
    if let PseudoExpr::Let {
        name: n1,
        value: v1,
        body,
        ..
    } = &result
    {
        assert_eq!(n1, "f");
        if let PseudoExpr::RecFn { name: fn1, .. } = v1.as_ref() {
            assert_eq!(fn1, "f");
        }
        if let PseudoExpr::Let {
            name: n2,
            value: v2,
            body: inner_body,
            ..
        } = body.as_ref()
        {
            assert_eq!(n2, "f_2");
            if let PseudoExpr::RecFn {
                name: fn2,
                body: fn_body,
                ..
            } = v2.as_ref()
            {
                assert_eq!(fn2, "f_2");
                let output = fn_body.to_pretty();
                assert!(
                    output.contains("f_2("),
                    "Self-ref should be renamed: {}",
                    output
                );
            }
            // Body reference should use renamed name
            if let PseudoExpr::Apply { function, .. } = inner_body.as_ref() {
                if let PseudoExpr::Var { name, .. } = function.as_ref() {
                    assert_eq!(name, "f_2");
                }
            }
        }
    }
}

#[test]
fn test_uniquify_when_pair_pattern_binders_rename_clause_body_by_var_id() {
    let left_id = VarId::new(300);
    let right_id = VarId::new(301);

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("pair")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Pair(Binder::new("x", left_id), Binder::new("x", right_id)),
            PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("x", left_id),
                    PseudoExpr::var_with_id("x", right_id),
                ]
                .into(),
            ),
        )],
    };

    let result = uniquify_let_names(expr);
    let PseudoExpr::When { clauses, .. } = result else {
        panic!("expected when expression");
    };
    let Some(WhenClause { pattern, body, .. }) = clauses.first() else {
        panic!("expected one clause");
    };
    let WhenPattern::Pair(left, right) = pattern else {
        panic!("expected pair pattern");
    };
    assert_ne!(left.as_str(), right.as_str());
    let PseudoExpr::Tuple(items) = body else {
        panic!("expected tuple body");
    };
    assert!(
        matches!(items.first(), Some(PseudoExpr::Var { name, id, .. }) if name == left.as_str() && id.get() == Some(left.id)),
        "expected first tuple item to follow left binder id, got: {:?}",
        items.first()
    );
    assert!(
        matches!(items.get(1), Some(PseudoExpr::Var { name, id, .. }) if name == right.as_str() && id.get() == Some(right.id)),
        "expected second tuple item to follow right binder id, got: {:?}",
        items.get(1)
    );
}

#[test]
fn test_uniquify_when_subject_name_renames_clause_refs_by_var_id() {
    let subject_id = VarId::new(302);

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("payload")),
        subject_name: Some(Binder::new("payload", subject_id)),
        clauses: vec![WhenClause::new(
            WhenPattern::Wildcard,
            PseudoExpr::var_with_id("payload", subject_id),
        )],
    };

    let result = uniquify_let_names(expr);
    let PseudoExpr::When {
        subject_name,
        clauses,
        ..
    } = result
    else {
        panic!("expected when expression");
    };
    let subject_name = subject_name.expect("expected subject binder");
    let Some(WhenClause { body, .. }) = clauses.first() else {
        panic!("expected one clause");
    };
    assert!(
        matches!(body, PseudoExpr::Var { name, id, .. } if name == subject_name.as_str() && id.get() == Some(subject_name.id)),
        "expected clause body ref to follow uniquified subject binder id, got: {body:?}"
    );
}
