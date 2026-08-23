use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_rec_function_param_hints_forwarded_wrapper_uses_name_fallback_only_for_compat_refs()
{
    let outer_list_id = VarId::fresh_binding();
    let outer_pred_id = VarId::fresh_binding();
    let outer_acc_id = VarId::fresh_binding();
    let helper_id = VarId::fresh_binding();
    let inner_list_id = VarId::fresh_binding();
    let inner_pred_id = VarId::fresh_binding();
    let inner_acc_id = VarId::fresh_binding();

    let params = vec![
        Binder::new("x_4", outer_list_id),
        Binder::new("f_9", outer_pred_id),
        Binder::new("z_2", outer_acc_id),
    ];
    let body = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("helper", helper_id),
            params: vec![
                Binder::new("x_4", inner_list_id),
                Binder::new("f_9", inner_pred_id),
                Binder::new("z_2", inner_acc_id),
            ],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("List.is_empty")),
                    args: vec![PseudoExpr::var_with_id("x_4", inner_list_id)].into(),
                }),
                then_branch: PBox::new(PseudoExpr::var_with_id("z_2", inner_acc_id)),
                else_branch: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("helper")),
                    args: vec![
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("List.tail")),
                            args: vec![PseudoExpr::var_with_id("x_4", inner_list_id)].into(),
                        },
                        PseudoExpr::var_with_id("f_9", inner_pred_id),
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var_with_id("f_9", inner_pred_id)),
                            args: vec![
                                PseudoExpr::var_with_id("z_2", inner_acc_id),
                                PseudoExpr::field_access(
                                    PseudoExpr::var_with_id("x_4", inner_list_id),
                                    "head".to_string(),
                                ),
                            ]
                            .into(),
                        },
                    ]
                    .into(),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("helper")),
            args: vec![
                PseudoExpr::var("x_4"),
                PseudoExpr::var_with_id("f_9", outer_pred_id),
                PseudoExpr::var_with_id("z_2", outer_acc_id),
            ]
            .into(),
        }),
    };

    let hints =
        analyze_rec_function_param_hints("wrapper", Some(VarId::fresh_binding()), &params, &body);
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
fn test_analyze_rec_function_param_hints_forwarded_wrapper_ignores_same_name_different_id_outer_ref()
 {
    let outer_list_id = VarId::fresh_binding();
    let outer_pred_id = VarId::fresh_binding();
    let outer_acc_id = VarId::fresh_binding();
    let wrong_list_id = VarId::fresh_binding();
    let helper_id = VarId::fresh_binding();
    let inner_list_id = VarId::fresh_binding();
    let inner_pred_id = VarId::fresh_binding();
    let inner_acc_id = VarId::fresh_binding();

    let params = vec![
        Binder::new("x_4", outer_list_id),
        Binder::new("f_9", outer_pred_id),
        Binder::new("z_2", outer_acc_id),
    ];
    let body = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("helper", helper_id),
            params: vec![
                Binder::new("x_4", inner_list_id),
                Binder::new("f_9", inner_pred_id),
                Binder::new("z_2", inner_acc_id),
            ],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("List.is_empty")),
                    args: vec![PseudoExpr::var_with_id("x_4", inner_list_id)].into(),
                }),
                then_branch: PBox::new(PseudoExpr::var_with_id("z_2", inner_acc_id)),
                else_branch: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("helper")),
                    args: vec![
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("List.tail")),
                            args: vec![PseudoExpr::var_with_id("x_4", inner_list_id)].into(),
                        },
                        PseudoExpr::var_with_id("f_9", inner_pred_id),
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var_with_id("f_9", inner_pred_id)),
                            args: vec![
                                PseudoExpr::var_with_id("z_2", inner_acc_id),
                                PseudoExpr::field_access(
                                    PseudoExpr::var_with_id("x_4", inner_list_id),
                                    "head".to_string(),
                                ),
                            ]
                            .into(),
                        },
                    ]
                    .into(),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("helper")),
            args: vec![
                PseudoExpr::var_with_id("x_4", wrong_list_id),
                PseudoExpr::var_with_id("f_9", outer_pred_id),
                PseudoExpr::var_with_id("z_2", outer_acc_id),
            ]
            .into(),
        }),
    };

    let hints =
        analyze_rec_function_param_hints("wrapper", Some(VarId::fresh_binding()), &params, &body);
    assert!(
        hints.is_empty(),
        "expected authoritative same-name different-id outer arg to disable forwarded wrapper hints, got: {hints:?}"
    );
}
