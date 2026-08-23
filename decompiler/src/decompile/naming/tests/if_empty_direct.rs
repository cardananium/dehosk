use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_names_if_empty_count_recursion() {
    let value = PseudoExpr::RecFn {
        name: "rec_fn_15".to_string().into(),
        params: vec!["v_365".to_string().into()],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("List.is_empty")),
                args: vec![PseudoExpr::var("v_365")].into(),
            }),
            then_branch: PBox::new(PseudoExpr::int(0)),
            else_branch: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("rec_fn_15")),
                    args: vec![PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("List.tail")),
                        args: vec![PseudoExpr::var("v_365")].into(),
                    }]
                    .into(),
                }),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_15", &value),
        Some("count".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_if_empty_count_recursion_direct_builtin_call() {
    let value = PseudoExpr::RecFn {
        name: "rec_fn_15".to_string().into(),
        params: vec!["v_365".to_string().into()],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::ListIsEmpty,
                args: vec![PseudoExpr::var("v_365")].into(),
            }),
            then_branch: PBox::new(PseudoExpr::int(0)),
            else_branch: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("rec_fn_15")),
                    args: vec![PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::ListTail,
                        args: vec![PseudoExpr::var("v_365")].into(),
                    }]
                    .into(),
                }),
                right: PBox::new(PseudoExpr::int(1)),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_15", &value),
        Some("count".to_string())
    );
}

#[test]
fn test_analyze_function_binding_names_if_empty_all_direct_builtin_call() {
    let value = PseudoExpr::RecFn {
        name: "rec_fn_39".to_string().into(),
        params: vec!["x_148".to_string().into(), "y_41".to_string().into()],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::ListIsEmpty,
                args: vec![PseudoExpr::var("x_148")].into(),
            }),
            then_branch: PBox::new(PseudoExpr::bool(true)),
            else_branch: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("y_41")),
                    args: vec![PseudoExpr::field_access(
                        PseudoExpr::var("x_148"),
                        "head".to_string(),
                    )]
                    .into(),
                }),
                right: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("rec_fn_39")),
                    args: vec![
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::ListTail,
                            args: vec![PseudoExpr::var("x_148")].into(),
                        },
                        PseudoExpr::var("y_41"),
                    ]
                    .into(),
                }),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("rec_fn_39", &value),
        Some("all".to_string())
    );
}

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_if_empty_all_tail_ref() {
    let wrong_list_id = VarId::fresh_binding();
    let value = PseudoExpr::RecFn {
        name: "rec_fn_39".to_string().into(),
        params: vec!["x_148".to_string().into(), "y_41".to_string().into()],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::ListIsEmpty,
                args: vec![PseudoExpr::var("x_148")].into(),
            }),
            then_branch: PBox::new(PseudoExpr::bool(true)),
            else_branch: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("y_41")),
                    args: vec![PseudoExpr::field_access(
                        PseudoExpr::var_with_id("x_148", wrong_list_id),
                        "head".to_string(),
                    )]
                    .into(),
                }),
                right: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("rec_fn_39")),
                    args: vec![
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::ListTail,
                            args: vec![PseudoExpr::var_with_id("x_148", wrong_list_id)].into(),
                        },
                        PseudoExpr::var("y_41"),
                    ]
                    .into(),
                }),
            }),
        }),
    };

    assert_eq!(analyze_function_binding("rec_fn_39", &value), None);
}

#[test]
fn test_analyze_function_binding_names_collapsed_any_direct_builtin_call() {
    let value = PseudoExpr::RecFn {
        name: "fn_3".to_string().into(),
        params: vec!["x_7".to_string().into(), "y_3".to_string().into()],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(PseudoExpr::UnOp {
                op: crate::pseudo::ast::UnaryOp::Not,
                operand: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::ListIsEmpty,
                    args: vec![PseudoExpr::var("x_7")].into(),
                }),
            }),
            right: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Or,
                left: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("y_3")),
                    args: vec![PseudoExpr::field_access(
                        PseudoExpr::var("x_7"),
                        "head".to_string(),
                    )]
                    .into(),
                }),
                right: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("fn_3")),
                    args: vec![
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::ListTail,
                            args: vec![PseudoExpr::var("x_7")].into(),
                        },
                        PseudoExpr::var("y_3"),
                    ]
                    .into(),
                }),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_3", &value),
        Some("any".to_string())
    );
}

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_collapsed_any_tail_ref() {
    let wrong_list_id = VarId::fresh_binding();
    let value = PseudoExpr::RecFn {
        name: "fn_3".to_string().into(),
        params: vec!["x_7".to_string().into(), "y_3".to_string().into()],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(PseudoExpr::UnOp {
                op: crate::pseudo::ast::UnaryOp::Not,
                operand: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::ListIsEmpty,
                    args: vec![PseudoExpr::var("x_7")].into(),
                }),
            }),
            right: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Or,
                left: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("y_3")),
                    args: vec![PseudoExpr::field_access(
                        PseudoExpr::var_with_id("x_7", wrong_list_id),
                        "head".to_string(),
                    )]
                    .into(),
                }),
                right: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("fn_3")),
                    args: vec![
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::ListTail,
                            args: vec![PseudoExpr::var_with_id("x_7", wrong_list_id)].into(),
                        },
                        PseudoExpr::var("y_3"),
                    ]
                    .into(),
                }),
            }),
        }),
    };

    assert_eq!(analyze_function_binding("fn_3", &value), None);
}

#[test]
fn test_analyze_function_binding_names_collapsed_all_direct_builtin_call() {
    let value = PseudoExpr::RecFn {
        name: "fn_39".to_string().into(),
        params: vec!["x_148".to_string().into(), "y_41".to_string().into()],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Or,
            left: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::ListIsEmpty,
                args: vec![PseudoExpr::var("x_148")].into(),
            }),
            right: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("y_41")),
                    args: vec![PseudoExpr::field_access(
                        PseudoExpr::var("x_148"),
                        "head".to_string(),
                    )]
                    .into(),
                }),
                right: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("fn_39")),
                    args: vec![
                        PseudoExpr::BuiltinCall {
                            name: crate::BuiltinId::ListTail,
                            args: vec![PseudoExpr::var("x_148")].into(),
                        },
                        PseudoExpr::var("y_41"),
                    ]
                    .into(),
                }),
            }),
        }),
    };

    assert_eq!(
        analyze_function_binding("fn_39", &value),
        Some("all".to_string())
    );
}
