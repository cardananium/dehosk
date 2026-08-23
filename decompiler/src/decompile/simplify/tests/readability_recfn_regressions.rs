use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_builtin_name_uses_canonical_data_contract() {
    assert_eq!(Simplifier::nice_builtin_name("i_data"), "Data.Int");
    assert_eq!(
        Simplifier::nice_builtin_name("un_b_data"),
        "Data.un_bytearray"
    );
}

#[test]
fn test_readability_used_names_include_binders_before_allocating_fresh_names() {
    let condition_id = VarId::from_raw(9901);
    let lambda_id = VarId::from_raw(9902);
    let pattern_id = VarId::from_raw(9903);
    let expr = PseudoExpr::Let {
        name: "condition_ok".to_string(),
        id: Some(condition_id),
        value: PBox::new(PseudoExpr::Bool(true)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("expected_data", lambda_id)],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("subject")),
                subject_name: Some("subject_alias".into()),
                clauses: vec![WhenClause::new(
                    WhenPattern::Var(Binder::new("field_0", pattern_id)),
                    PseudoExpr::var_with_id("condition_ok", condition_id),
                )],
            }),
        }),
    };

    let mut used_names = std::collections::HashSet::new();
    Simplifier::collect_var_names(&expr, &mut used_names);

    assert!(used_names.contains("condition_ok"));
    assert!(used_names.contains("expected_data"));
    assert!(used_names.contains("subject_alias"));
    assert!(used_names.contains("field_0"));

    let simplifier = Simplifier::with_safe_mode(false);
    assert_eq!(
        simplifier.fresh_name_for_scope(&mut used_names, "condition_ok".to_string()),
        "condition_ok_1"
    );
}

#[test]
fn test_lambda_rec_wrapper_promotion_rejects_outer_let_captures() {
    let expr = PseudoExpr::let_bind(
        "bytes",
        PseudoExpr::var("outer_bytes"),
        PseudoExpr::let_bind(
            "wrapper",
            PseudoExpr::Lambda {
                params: vec!["acc".to_string().into(), "key".to_string().into()],
                body: PBox::new(PseudoExpr::let_bind(
                    "inner",
                    PseudoExpr::RecFn {
                        name: "inner".to_string().into(),
                        params: vec!["acc".to_string().into()],
                        body: PBox::new(PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::BinOp {
                                op: BinaryOp::Eq,
                                left: PBox::new(PseudoExpr::var("key")),
                                right: PBox::new(PseudoExpr::var("bytes")),
                            }),
                            then_branch: PBox::new(PseudoExpr::var("acc")),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("inner")),
                                args: vec![PseudoExpr::var("acc")].into(),
                            }),
                        }),
                    },
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("inner")),
                        args: vec![PseudoExpr::var("acc")].into(),
                    },
                )),
            },
            PseudoExpr::var("wrapper"),
        ),
    );

    let simplified = simplify(expr);

    assert!(
        matches!(simplified, PseudoExpr::Lambda { .. }),
        "wrapper should stay a lambda when the inner rec fn captures outer let-bound values, got: {simplified:?}"
    );
}

#[test]
fn test_ordered_lookup_recfn_keeps_explicit_key_binding() {
    let expr = PseudoExpr::RecFn {
        name: "rec_fn_4".to_string().into(),
        params: vec!["acc_4".to_string().into(), "z_2".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("acc_4")),
            subject_name: Some("acc_4".to_string().into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::constr(ConstructorShape::unknown_data(1, 0), vec![]),
                ),
                WhenClause::new(
                    WhenPattern::Wildcard,
                    PseudoExpr::Let {
                        name: "j2".to_string(),
                        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                        value: PBox::new(PseudoExpr::IndexAccess {
                            collection: PBox::new(PseudoExpr::var("acc_4")),
                            index: 0,
                        }),
                        body: PBox::new(PseudoExpr::Let {
                            name: "k2".to_string(),
                            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                            value: PBox::new(PseudoExpr::BuiltinCall {
                                name: crate::BuiltinId::expect_known("List.tail"),
                                args: vec![PseudoExpr::var("acc_4")].into(),
                            }),
                            body: PBox::new(PseudoExpr::Let {
                                name: "to_bytes_partial_8".to_string(),
                                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                                value: PBox::new(PseudoExpr::BuiltinCall {
                                    name: crate::BuiltinId::expect_known("Data.un_bytearray"),
                                    args: vec![PseudoExpr::field_access(
                                        PseudoExpr::var("j2"),
                                        "fst".to_string(),
                                    )]
                                    .into(),
                                }),
                                body: PBox::new(PseudoExpr::Let {
                                    name: "to_int_partial_13".to_string(),
                                    id: Some(
                                        crate::pseudo::var_id::VarId::fresh_compat_placeholder(),
                                    ),
                                    value: PBox::new(PseudoExpr::BuiltinCall {
                                        name: crate::BuiltinId::expect_known("Data.un_int"),
                                        args: vec![PseudoExpr::field_access(
                                            PseudoExpr::var("j2"),
                                            "snd".to_string(),
                                        )]
                                        .into(),
                                    }),
                                    body: PBox::new(PseudoExpr::If {
                                        condition: PBox::new(PseudoExpr::BinOp {
                                            op: BinaryOp::Lte,
                                            left: PBox::new(PseudoExpr::var("z_2")),
                                            right: PBox::new(PseudoExpr::var("to_bytes_partial_8")),
                                        }),
                                        then_branch: PBox::new(PseudoExpr::If {
                                            condition: PBox::new(PseudoExpr::BinOp {
                                                op: BinaryOp::Eq,
                                                left: PBox::new(PseudoExpr::var("z_2")),
                                                right: PBox::new(PseudoExpr::var(
                                                    "to_bytes_partial_8",
                                                )),
                                            }),
                                            then_branch: PBox::new(PseudoExpr::constr(
                                                ConstructorShape::unknown_data(0, 1),
                                                vec![PseudoExpr::var("to_int_partial_13")],
                                            )),
                                            else_branch: PBox::new(PseudoExpr::constr(
                                                ConstructorShape::unknown_data(1, 0),
                                                vec![],
                                            )),
                                        }),
                                        else_branch: PBox::new(PseudoExpr::Apply {
                                            function: PBox::new(PseudoExpr::var("rec_fn_4")),
                                            args: vec![
                                                PseudoExpr::var("k2"),
                                                PseudoExpr::var("z_2"),
                                            ]
                                            .into(),
                                        }),
                                    }),
                                }),
                            }),
                        }),
                    },
                ),
            ],
        }),
    };

    let simplified = simplify(expr);
    let pretty = simplified.to_pretty();
    assert!(
        pretty.contains("let bytes =") || pretty.contains("let fst ="),
        "ordered lookup helper should keep an explicit key binding instead of leaking a free temp: {pretty}"
    );
    assert!(
        !pretty.contains("if z_2 <= fst_"),
        "ordered lookup helper should not leak free fst_* temporaries: {pretty}"
    );
}
