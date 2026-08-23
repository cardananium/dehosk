use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_if_empty_lookup_recursion() {
    let value = PseudoExpr::RecFn {
        name: "fn_2".to_string().into(),
        params: vec!["x_4".to_string().into(), "y_2".to_string().into()],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("List.is_empty")),
                args: vec![PseudoExpr::var("x_4")].into(),
            }),
            then_branch: PBox::new(PseudoExpr::constr_known(KnownConstructor::None, vec![])),
            else_branch: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::field_access(PseudoExpr::var("x_4"), "head".to_string()),
                        "fst".to_string(),
                    )),
                    right: PBox::new(PseudoExpr::var("y_2")),
                }),
                then_branch: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::field_access(PseudoExpr::var("x_4"), "head".to_string()),
                    "snd".to_string(),
                )),
                else_branch: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("fn_2")),
                    args: vec![
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("List.tail")),
                            args: vec![PseudoExpr::var("x_4")].into(),
                        },
                        PseudoExpr::var("y_2"),
                    ]
                    .into(),
                }),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_2", &value),
        Some("lookup".to_string())
    );
}

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_if_empty_lookup_tail_ref() {
    let wrong_list_id = VarId::fresh_binding();
    let value = PseudoExpr::RecFn {
        name: "fn_2".to_string().into(),
        params: vec!["x_4".to_string().into(), "y_2".to_string().into()],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("List.is_empty")),
                args: vec![PseudoExpr::var("x_4")].into(),
            }),
            then_branch: PBox::new(PseudoExpr::constr_known(KnownConstructor::None, vec![])),
            else_branch: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::field_access(
                            PseudoExpr::var_with_id("x_4", wrong_list_id),
                            "head".to_string(),
                        ),
                        "fst".to_string(),
                    )),
                    right: PBox::new(PseudoExpr::var("y_2")),
                }),
                then_branch: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::field_access(
                        PseudoExpr::var_with_id("x_4", wrong_list_id),
                        "head".to_string(),
                    ),
                    "snd".to_string(),
                )),
                else_branch: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("fn_2")),
                    args: vec![
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("List.tail")),
                            args: vec![PseudoExpr::var_with_id("x_4", wrong_list_id)].into(),
                        },
                        PseudoExpr::var("y_2"),
                    ]
                    .into(),
                }),
            }),
        }),
    };

    assert_eq!(analyze_function_binding("fn_2", &value), None);
}

#[test]
fn test_analyze_rec_function_param_hints_if_empty_fold_recursion() {
    let params = vec![
        Binder::synthetic("x_4"),
        Binder::synthetic("f_9"),
        Binder::synthetic("z_2"),
    ];
    let body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("List.is_empty")),
            args: vec![PseudoExpr::var("x_4")].into(),
        }),
        then_branch: PBox::new(PseudoExpr::var("z_2")),
        else_branch: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("rec_fn_5")),
            args: vec![
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("List.tail")),
                    args: vec![PseudoExpr::var("x_4")].into(),
                },
                PseudoExpr::var("f_9"),
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("f_9")),
                    args: vec![
                        PseudoExpr::var("z_2"),
                        PseudoExpr::field_access(PseudoExpr::var("x_4"), "head".to_string()),
                    ]
                    .into(),
                },
            ]
            .into(),
        }),
    };

    let hints =
        analyze_rec_function_param_hints("rec_fn_5", Some(VarId::fresh_binding()), &params, &body);
    let hint_names: Vec<(&str, &str)> = hints
        .into_iter()
        .map(|(binder, hint)| (binder.as_str(), hint))
        .collect();

    assert_eq!(
        hint_names,
        vec![("x_4", "list"), ("f_9", "predicate"), ("z_2", "acc")]
    );
}

#[test]
fn test_analyze_rec_function_param_hints_if_empty_fold_ignores_same_name_different_id_tail_ref() {
    let list_id = VarId::fresh_binding();
    let wrong_list_id = VarId::fresh_binding();
    let pred_id = VarId::fresh_binding();
    let acc_id = VarId::fresh_binding();
    let params = vec![
        Binder::new("x_4", list_id),
        Binder::new("f_9", pred_id),
        Binder::new("z_2", acc_id),
    ];
    let body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("List.is_empty")),
            args: vec![PseudoExpr::var_with_id("x_4", list_id)].into(),
        }),
        then_branch: PBox::new(PseudoExpr::var_with_id("z_2", acc_id)),
        else_branch: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("rec_fn_5")),
            args: vec![
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("List.tail")),
                    args: vec![PseudoExpr::var_with_id("x_4", wrong_list_id)].into(),
                },
                PseudoExpr::var_with_id("f_9", pred_id),
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("f_9", pred_id)),
                    args: vec![
                        PseudoExpr::var_with_id("z_2", acc_id),
                        PseudoExpr::field_access(
                            PseudoExpr::var_with_id("x_4", wrong_list_id),
                            "head".to_string(),
                        ),
                    ]
                    .into(),
                },
            ]
            .into(),
        }),
    };

    let hints =
        analyze_rec_function_param_hints("rec_fn_5", Some(VarId::fresh_binding()), &params, &body);

    assert!(
        hints.is_empty(),
        "expected same-name different-id tail/head refs to disable if_empty fold hints, got: {hints:?}"
    );
}
