use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_direct_rec_filter_matches_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "fn_5".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "fn_5".to_string().into(),
            params: vec![
                "xs_2".to_string().into(),
                "pred_3".to_string().into(),
                "seed_4".to_string().into(),
            ],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("xs_2")),
                subject_name: Some("xs_2".to_string().into()),
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec![],
                            tail: None,
                        },
                        PseudoExpr::var("seed_4"),
                    ),
                    WhenClause::new(
                        WhenPattern::List {
                            elements: vec!["head".into()],
                            tail: Some("tail".into()),
                        },
                        PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("pred_3")),
                                args: vec![PseudoExpr::var("head")].into(),
                            }),
                            then_branch: PBox::new(PseudoExpr::BuiltinCall {
                                name: crate::BuiltinId::expect_known("List.cons"),
                                args: vec![
                                    PseudoExpr::var("head"),
                                    PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var("fn_5")),
                                        args: vec![
                                            PseudoExpr::var_with_id("tail", outer_tail_id),
                                            PseudoExpr::var("pred_3"),
                                            PseudoExpr::var("seed_4"),
                                        ]
                                        .into(),
                                    },
                                ]
                                .into(),
                            }),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("fn_5")),
                                args: vec![
                                    PseudoExpr::var_with_id("tail", outer_tail_id),
                                    PseudoExpr::var("pred_3"),
                                    PseudoExpr::var("seed_4"),
                                ]
                                .into(),
                            }),
                        },
                    ),
                ],
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("fn_5")),
            args: vec![
                PseudoExpr::var("inputs"),
                PseudoExpr::var("predicate"),
                PseudoExpr::var("seed"),
            ]
            .into(),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "fn_5");
            let PseudoExpr::RecFn {
                name: rec_name,
                params,
                ..
            } = value.as_ref()
            else {
                panic!("expected let-bound recfn value, got: {value:?}");
            };
            assert_eq!(rec_name.as_str(), "fn_5");
            assert_eq!(params[0].as_str(), "xs_2");
            assert_eq!(params[1].as_str(), "pred_3");
            assert_eq!(params[2].as_str(), "seed_4");
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, .. }
                        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "fn_5")
                ),
                "expected false-positive filter_matches helper to stay unrenamed, got: {body:?}"
            );
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}
