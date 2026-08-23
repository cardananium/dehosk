use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_leaves_data_list_wrapper_to_nameless_owner() {
    let temp_id = VarId::fresh_binding();
    let value = PseudoExpr::Let {
        name: "rec_fn_10".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "rec_fn_10".to_string().into(),
            params: vec!["list".to_string().into(), "acc".to_string().into()],
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
                            elements: vec!["head".into()],
                            tail: Some("tail".into()),
                        },
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::expect_known("List.cons"),
                            args: vec![
                                PseudoExpr::var("head"),
                                PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var("rec_fn_10")),
                                    args: vec![PseudoExpr::var("tail"), PseudoExpr::var("acc")]
                                        .into(),
                                },
                            ]
                            .into(),
                        },
                    ),
                ],
            }),
        }),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.List"),
            args: vec![PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("rec_fn_10")),
                args: vec![
                    PseudoExpr::var("pairs"),
                    PseudoExpr::List {
                        elements: vec![].into(),
                        tail: None,
                    },
                ]
                .into(),
            }]
            .into(),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "to_data_partial".to_string(),
        id: Some(temp_id),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::var_with_id("to_data_partial", temp_id)),
    };

    let semantic = semantic_improve_variable_names(expr.clone());
    let render = render_improve_variable_names(expr.clone());
    for improved in [semantic, render] {
        let PseudoExpr::Let { name, body, .. } = improved else {
            panic!("expected data list wrapper let");
        };
        assert_eq!(name, "to_data_partial");
        assert!(
            matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "to_data_partial" && *id == Some(temp_id)),
            "expected data_list wrapper temp to stay with nameless owner, got: {body:?}"
        );
    }

    let hints = collect_data_list_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("data_list"));
}

#[test]
fn collect_data_list_temp_display_name_hints_avoids_existing_data_list_binding() {
    let existing_id = VarId::fresh_binding();
    let temp_id = VarId::fresh_binding();
    let rec_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "data_list".to_string(),
        id: Some(existing_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "to_data_partial".to_string(),
            id: Some(temp_id),
            value: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.List"),
                args: vec![PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("rec_fn_10", rec_id)),
                    args: vec![PseudoExpr::List {
                        elements: vec![].into(),
                        tail: None,
                    }]
                    .into(),
                }]
                .into(),
            }),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("data_list", existing_id),
                    PseudoExpr::var_with_id("to_data_partial", temp_id),
                ]
                .into(),
            )),
        }),
    };

    let hints = collect_data_list_temp_display_name_hints(&expr);
    assert_eq!(hints.get(&temp_id).map(String::as_str), Some("data_list_2"));
    assert!(!hints.contains_key(&existing_id));
}
