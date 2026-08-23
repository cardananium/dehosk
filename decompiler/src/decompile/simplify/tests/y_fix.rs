use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_direct_y_application_rewritten_to_rec() {
    let y = PseudoExpr::Lambda {
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
    };

    let expr = PseudoExpr::Apply {
        function: PBox::new(y),
        args: vec![
            PseudoExpr::Lambda {
                params: vec!["self".to_string().into(), "n".to_string().into()],
                body: PBox::new(PseudoExpr::var("n")),
            },
            PseudoExpr::int(7),
        ]
        .into(),
    };

    let simplified = simplify(expr);
    // The trivially small callback fn(self, n) { n } gets inlined,
    // collapsing the Y-combinator entirely to just the result value 7.
    assert!(
        matches!(simplified, PseudoExpr::Int(_)) || matches!(simplified, PseudoExpr::Let { .. }),
        "Expected Int or Let, got: {:?}",
        simplified
    );
}

#[test]
fn test_y_combinator_with_nontrivial_callback() {
    // Test that Y-combinator detection still works with callbacks too large to inline
    let y = PseudoExpr::Lambda {
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
    };

    // Larger callback that won't be inlined (body_size > 4)
    let expr = PseudoExpr::Apply {
        function: PBox::new(y),
        args: vec![
            PseudoExpr::Lambda {
                params: vec!["self_fn".to_string().into(), "n".to_string().into()],
                body: PBox::new(PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::BinOp {
                        op: crate::pseudo::ast::BinaryOp::Eq,
                        left: PBox::new(PseudoExpr::var("n")),
                        right: PBox::new(PseudoExpr::int(0)),
                    }),
                    then_branch: PBox::new(PseudoExpr::int(1)),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("self_fn")),
                        args: vec![PseudoExpr::BinOp {
                            op: crate::pseudo::ast::BinaryOp::Sub,
                            left: PBox::new(PseudoExpr::var("n")),
                            right: PBox::new(PseudoExpr::int(1)),
                        }]
                        .into(),
                    }),
                }),
            },
            PseudoExpr::int(5),
        ]
        .into(),
    };

    let simplified = simplify(expr);
    // Should produce a Let with RecFn value
    assert!(
        matches!(simplified, PseudoExpr::Let { .. }),
        "Expected Let with RecFn, got: {:?}",
        simplified
    );
}

#[test]
fn test_direct_y_combinator_helper_ignores_same_name_scope_binding() {
    let foreign_helper_id = VarId::new(9380);
    let mut simplifier = Simplifier::with_safe_mode(false);
    simplifier
        .naming
        .name_to_id
        .insert("__y_comb_direct".to_string(), foreign_helper_id);

    let y = PseudoExpr::Lambda {
        params: vec!["b".to_string().into()],
        body: PBox::new(PseudoExpr::Let {
            name: "c".to_string(),
            id: Some(VarId::new(9381)),
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
    };
    let callback = PseudoExpr::Lambda {
        params: vec![
            Binder::new("self_fn", VarId::new(9382)),
            Binder::new("n", VarId::new(9383)),
        ],
        body: PBox::new(PseudoExpr::var_with_id("n", VarId::new(9383))),
    };

    let action = simplifier.simplify_apply_match(y, vec![callback, PseudoExpr::int(5)]);
    match action {
        super::super::apply::ApplyAction::ContinueLoop { function, .. } => {
            assert!(
                matches!(
                    &function,
                    PseudoExpr::Var { name, id, .. }
                        if name == "__y_comb_direct"
                            && id.is_none()
                            && *id != Some(foreign_helper_id)
                ),
                "internal y-combinator helper must not borrow a same-name scope id, got: {:?}",
                function
            );
        }
        other => panic!(
            "expected direct y-combinator to re-enter through helper, got: {:?}",
            std::mem::discriminant(&other)
        ),
    }
}

#[test]
fn test_direct_self_wrapper_seeded_by_y_comb_promotes_to_recfn() {
    let expr = PseudoExpr::let_bind(
        "wrapper",
        PseudoExpr::Lambda {
            params: vec!["self".to_string().into(), "xs".to_string().into()],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::Bool(false)),
                then_branch: PBox::new(PseudoExpr::Unit),
                else_branch: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("self")),
                    args: vec![PseudoExpr::var("xs_t")].into(),
                }),
            }),
        },
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("wrapper")),
            args: vec![
                PseudoExpr::var("__y_comb_rec_fn"),
                PseudoExpr::var("seed_xs"),
            ]
            .into(),
        },
    );

    let simplified = simplify(expr);

    let PseudoExpr::Let { value, body, .. } = simplified else {
        panic!("expected let-bound recursive wrapper, got: {simplified:?}");
    };
    assert!(
        matches!(value.as_ref(), PseudoExpr::RecFn { .. }),
        "expected direct self wrapper to promote into rec fn, got: {value:?}"
    );
    assert!(
        !format!("{body:?}").contains("__y_comb_rec_fn"),
        "expected seeded entry call to drop __y_comb_rec_fn after promotion, got: {body:?}"
    );
}

#[test]
fn test_lambda_wrapped_fix_definition_stays_explicit() {
    // This Y-comb-definition shape is NOT replaced by bare `Var("fix")`
    // in lambda.rs: the surrounding context here is almost always a
    // `when`-subject position rather than a function call, so the bare
    // fix marker would orphan. The explicit Y-comb structure is left
    // intact — verbose but correct.
    let acc_id = VarId::new(9_880);
    let self_id = VarId::new(9_881);
    let acc2_id = VarId::new(9_882);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("acc", acc_id)],
        body: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("self_fn_2", self_id),
            params: vec![Binder::new("acc_2", acc2_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("acc", acc_id)),
                args: vec![
                    PseudoExpr::var_with_id("self_fn_2", self_id),
                    PseudoExpr::var_with_id("acc_2", acc2_id),
                ]
                .into(),
            }),
        }),
    };

    let simplified = simplify(expr);
    // The Lambda must stay intact — NO `Var("fix")` rewrite.
    assert!(
        !matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "fix"),
        "Y-comb-definition Lambda must NOT collapse to bare Var(fix), got: {simplified:?}"
    );
    // Outer Lambda preserved.
    assert!(
        matches!(simplified, PseudoExpr::Lambda { .. }),
        "expected outer Lambda preserved, got: {simplified:?}"
    );
}

#[test]
fn test_lambda_wrapped_fix_definition_rejects_same_name_foreign_ids() {
    let acc_id = VarId::new(9_883);
    let self_id = VarId::new(9_884);
    let acc2_id = VarId::new(9_885);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("acc", acc_id)],
        body: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("self_fn_2", self_id),
            params: vec![Binder::new("acc_2", acc2_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("acc", VarId::new(9_886))),
                args: vec![
                    PseudoExpr::var_with_id("self_fn_2", VarId::new(9_887)),
                    PseudoExpr::var_with_id("acc_2", VarId::new(9_888)),
                ]
                .into(),
            }),
        }),
    };

    let simplified = simplify(expr);
    assert!(
        !matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "fix"),
        "same-name foreign ids must not satisfy lambda-wrapped fix recognition, got: {simplified:?}"
    );
    assert!(
        matches!(simplified, PseudoExpr::Lambda { .. }),
        "expected rejected fix shape to remain lambda-like, got: {simplified:?}"
    );
}
