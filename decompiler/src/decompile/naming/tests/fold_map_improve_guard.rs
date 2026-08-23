use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_fold_map_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "fn_5".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                "map_data".to_string().into(),
                "step".to_string().into(),
                "init".to_string().into(),
            ],
            body: PBox::new(PseudoExpr::Let {
                name: "rec_fn".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::RecFn {
                    name: "rec_fn".to_string().into(),
                    params: vec![
                        "list".to_string().into(),
                        "idx".to_string().into(),
                        "acc".to_string().into(),
                    ],
                    body: PBox::new(PseudoExpr::When {
                        subject: PBox::new(PseudoExpr::var("list")),
                        subject_name: Some("list".to_string().into()),
                        clauses: vec![
                            WhenClause::new(
                                WhenPattern::List {
                                    elements: vec![],
                                    tail: None,
                                },
                                PseudoExpr::var("acc"),
                            ),
                            WhenClause::new(
                                WhenPattern::List {
                                    elements: vec!["entry".into()],
                                    tail: Some("tail".into()),
                                },
                                PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("rec_fn")),
                                    args: vec![
                                        PseudoExpr::var_with_id("tail", outer_tail_id),
                                        PseudoExpr::var("idx"),
                                        PseudoExpr::Apply {
                                            function: PBox::new(PseudoExpr::var("idx")),
                                            args: vec![
                                                PseudoExpr::var("acc"),
                                                PseudoExpr::var("entry"),
                                            ]
                                            .into(),
                                        },
                                    ]
                                    .into(),
                                },
                            ),
                        ],
                    }),
                }),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("rec_fn")),
                    args: vec![
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("Data.un_map"),
                            args: vec![PseudoExpr::var("map_data")].into(),
                        },
                        PseudoExpr::var("step"),
                        PseudoExpr::var("init"),
                    ]
                    .into(),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("fn_5")),
            args: vec![
                PseudoExpr::var("map_arg"),
                PseudoExpr::var("step_arg"),
                PseudoExpr::var("init_arg"),
            ]
            .into(),
        }),
    };

    let improved = improve_variable_names(expr);

    let PseudoExpr::Let { name, body, .. } = improved else {
        panic!("expected outer let");
    };
    assert_eq!(name, "fn_5");
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Apply { function, .. }
                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "fn_5")
        ),
        "expected fold-map false positive to stay unrenamed, got: {body:?}"
    );
}
