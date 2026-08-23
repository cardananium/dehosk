//! Unit tests for simplification helpers:
//! `simplify_boolean_and_identity` (selector collapse)
//! `simplify_double_rec_fn` (inner rec conversion)
//! `simplify_z_combinator` (Y-combinator recognition)
//! `convert_expect_tag_to_constr_when` (expect-tag → when)

#![cfg(test)]

use crate::decompile::boolean_cleanup::simplify_boolean_and_identity;
use crate::decompile::fix_combinator::{simplify_double_rec_fn, simplify_z_combinator};
use crate::decompile::simplify;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

// simplify_boolean_and_identity

#[test]
fn test_simplify_boolean_and_identity_collapses_inline_selector_conditions() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".into(), "_".into()],
            body: PBox::new(PseudoExpr::var("x")),
        }),
        then_branch: PBox::new(PseudoExpr::var("then_branch")),
        else_branch: PBox::new(PseudoExpr::var("else_branch")),
    };

    let simplified = simplify_boolean_and_identity(expr, None);
    assert_eq!(simplified, PseudoExpr::var("then_branch"));

    let inverted = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Lambda {
            params: vec!["_".into(), "y".into()],
            body: PBox::new(PseudoExpr::var("y")),
        }),
        then_branch: PBox::new(PseudoExpr::var("then_branch")),
        else_branch: PBox::new(PseudoExpr::var("else_branch")),
    };

    let simplified = simplify_boolean_and_identity(inverted, None);
    assert_eq!(simplified, PseudoExpr::var("else_branch"));
}

#[test]
fn test_simplify_boolean_and_identity_collapses_bound_selector_aliases() {
    let expr = PseudoExpr::let_bind(
        "choose_fst",
        PseudoExpr::Lambda {
            params: vec!["x".into(), "_".into()],
            body: PBox::new(PseudoExpr::var("x")),
        },
        PseudoExpr::let_bind(
            "choose_snd",
            PseudoExpr::Lambda {
                params: vec!["_".into(), "y".into()],
                body: PBox::new(PseudoExpr::var("y")),
            },
            PseudoExpr::If {
                condition: PBox::new(PseudoExpr::var("cond")),
                then_branch: PBox::new(PseudoExpr::var("choose_fst")),
                else_branch: PBox::new(PseudoExpr::var("choose_snd")),
            },
        ),
    );

    let simplified = simplify_boolean_and_identity(expr, None);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::Let { body, .. }
                        if matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "cond")
                )
        ),
        "bound selector aliases should collapse to the condition, got: {simplified:?}"
    );
}

// simplify_double_rec_fn

#[test]
fn test_simplify_double_rec_fn_converts_non_recursive_inner_rec_to_lambda() {
    let expr = PseudoExpr::RecFn {
        name: "outer".into(),
        params: vec!["acc".into()],
        body: PBox::new(PseudoExpr::RecFn {
            name: "inner".into(),
            params: vec!["x".into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("acc")),
                args: vec![PseudoExpr::var("x")].into(),
            }),
        }),
    };

    let simplified = simplify_double_rec_fn(expr);

    match simplified {
        PseudoExpr::RecFn { body, .. } => match body.as_ref() {
            PseudoExpr::Lambda { params, body } => {
                assert_eq!(params, &vec!["x".to_string()]);
                assert!(
                    matches!(
                        body.as_ref(),
                        PseudoExpr::Apply { function, args }
                            if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "acc")
                                && matches!(args.as_slice(), [PseudoExpr::Var { name, .. }] if name == "x")
                    ),
                    "expected inner rec body to become lambda, got: {body:?}"
                );
            }
            other => panic!("expected inner recfn to become lambda, got: {other:?}"),
        },
        other => panic!("expected outer recfn to be preserved, got: {other:?}"),
    }
}

#[test]
fn test_simplify_double_rec_fn_preserves_recursive_inner_rec() {
    let expr = PseudoExpr::RecFn {
        name: "outer".into(),
        params: vec!["acc".into()],
        body: PBox::new(PseudoExpr::RecFn {
            name: "inner".into(),
            params: vec!["x".into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("inner")),
                args: vec![PseudoExpr::var("x")].into(),
            }),
        }),
    };

    let simplified = simplify_double_rec_fn(expr.clone());
    assert_eq!(simplified, expr);
}

#[test]
fn test_simplify_double_rec_fn_ignores_outer_same_name_binding() {
    let outer_inner_id = VarId::fresh_binding();
    let outer_param_id = VarId::fresh_binding();
    let inner_param_id = VarId::fresh_binding();

    let expr = PseudoExpr::Let {
        name: "inner".to_string(),
        id: Some(outer_inner_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("value", VarId::fresh_binding())],
            body: PBox::new(PseudoExpr::Bool(true)),
        }),
        body: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("outer", VarId::fresh_binding()),
            params: vec![Binder::new("acc", outer_param_id)],
            body: PBox::new(PseudoExpr::RecFn {
                name: Binder::new("inner", VarId::fresh_binding()),
                params: vec![Binder::new("x", inner_param_id)],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::Var {
                        name: "inner".to_string(),
                        id: Some(outer_inner_id),
                    }),
                    args: vec![PseudoExpr::Var {
                        name: "x".to_string(),
                        id: Some(inner_param_id),
                    }]
                    .into(),
                }),
            }),
        }),
    };

    let simplified = simplify_double_rec_fn(expr);

    match simplified {
        PseudoExpr::Let { body, .. } => match body.as_ref() {
            PseudoExpr::RecFn { body, .. } => {
                assert!(
                    matches!(body.as_ref(), PseudoExpr::Lambda { .. }),
                    "expected outer same-name binding not to block double-rec simplification, got: {body:?}"
                );
            }
            other => panic!("expected outer RecFn after let, got: {other:?}"),
        },
        other => panic!("expected outer let to stay intact, got: {other:?}"),
    }
}

// simplify_z_combinator

#[test]
fn test_simplify_z_combinator_basic() {
    let acc_33 = Binder::synthetic("acc_33");
    let acc_34 = Binder::synthetic("acc_34");
    let captured_id = VarId::fresh_binding();
    let expr = PseudoExpr::RecFn {
        name: "self_fn_33".into(),
        params: vec![acc_33.clone()],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![acc_34.clone()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("acc_33", acc_33.var_id())),
                args: vec![
                    PseudoExpr::var_with_id("rec_fn_16", captured_id),
                    PseudoExpr::var_with_id("acc_34", acc_34.var_id()),
                ]
                .into(),
            }),
        }),
    };
    let result = simplify_z_combinator(expr);
    match result {
        PseudoExpr::Apply { function, args } => {
            match function.into_inner() {
                PseudoExpr::HelperSymbol(crate::pseudo::ast::HelperIntrinsic::Fix) => {}
                other => panic!("Expected HelperSymbol(Fix), got: {:?}", other),
            }
            assert_eq!(args.len(), 1);
            match &args[0] {
                PseudoExpr::Var { name, id, .. } => {
                    assert_eq!(name, "rec_fn_16");
                    assert_eq!(*id, Some(captured_id));
                }
                other => panic!("Expected Var(rec_fn_16), got: {:?}", other),
            }
        }
        other => panic!("Expected Apply(fix, rec_fn_16), got: {:?}", other),
    }
}

#[test]
fn test_simplify_z_combinator_different_names() {
    let acc_11 = Binder::synthetic("acc_11");
    let acc_12 = Binder::synthetic("acc_12");
    let expr = PseudoExpr::RecFn {
        name: "self_fn_11".into(),
        params: vec![acc_11.clone()],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![acc_12.clone()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("acc_11", acc_11.var_id())),
                args: vec![
                    PseudoExpr::var("rec_fn_5"),
                    PseudoExpr::var_with_id("acc_12", acc_12.var_id()),
                ]
                .into(),
            }),
        }),
    };
    let result = simplify_z_combinator(expr);
    match result {
        PseudoExpr::Apply { function, args } => {
            match function.into_inner() {
                PseudoExpr::HelperSymbol(crate::pseudo::ast::HelperIntrinsic::Fix) => {}
                other => panic!("Expected HelperSymbol(Fix), got: {:?}", other),
            }
            assert_eq!(args.len(), 1);
            match &args[0] {
                PseudoExpr::Var { name, .. } => assert_eq!(name, "rec_fn_5"),
                other => panic!("Expected Var(rec_fn_5), got: {:?}", other),
            }
        }
        other => panic!("Expected Apply(fix, rec_fn_5), got: {:?}", other),
    }
}

#[test]
fn test_simplify_y_combinator_definition() {
    let acc = Binder::synthetic("acc");
    let self_fn_2 = Binder::synthetic("self_fn_2");
    let acc_2 = Binder::synthetic("acc_2");
    let expr = PseudoExpr::RecFn {
        name: "a".into(),
        params: vec![acc.clone()],
        body: PBox::new(PseudoExpr::RecFn {
            name: self_fn_2.clone(),
            params: vec![acc_2.clone()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("acc", acc.var_id())),
                args: vec![
                    PseudoExpr::var_with_id("self_fn_2", self_fn_2.var_id()),
                    PseudoExpr::var_with_id("acc_2", acc_2.var_id()),
                ]
                .into(),
            }),
        }),
    };
    let result = simplify_z_combinator(expr);
    match result {
        PseudoExpr::HelperSymbol(crate::pseudo::ast::HelperIntrinsic::Fix) => {}
        other => panic!("Expected HelperSymbol(Fix), got: {:?}", other),
    }
}

#[test]
fn test_simplify_z_combinator_preserves_non_z() {
    let expr = PseudoExpr::RecFn {
        name: "f".into(),
        params: vec!["x".into()],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::var("x")].into(),
        }),
    };
    let result = simplify_z_combinator(expr.clone());
    assert_eq!(result, expr);
}

#[test]
fn test_simplify_z_combinator_preserves_multi_param() {
    let expr = PseudoExpr::RecFn {
        name: "f".into(),
        params: vec!["a".into(), "b".into()],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["c".into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("a")),
                args: vec![PseudoExpr::var("captured"), PseudoExpr::var("c")].into(),
            }),
        }),
    };
    let result = simplify_z_combinator(expr.clone());
    assert_eq!(result, expr);
}

#[test]
fn test_simplify_z_combinator_in_let() {
    let acc_33 = Binder::synthetic("acc_33");
    let acc_34 = Binder::synthetic("acc_34");
    let expr = PseudoExpr::Let {
        name: "fold_0".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "self_fn_33".into(),
            params: vec![acc_33.clone()],
            body: PBox::new(PseudoExpr::Lambda {
                params: vec![acc_34.clone()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("acc_33", acc_33.var_id())),
                    args: vec![
                        PseudoExpr::var("rec_fn_16"),
                        PseudoExpr::var_with_id("acc_34", acc_34.var_id()),
                    ]
                    .into(),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::var("fold_0")),
    };
    let result = simplify_z_combinator(expr);
    match result {
        PseudoExpr::Let { value, .. } => match value.into_inner() {
            PseudoExpr::Apply { function, args } => {
                match function.into_inner() {
                    PseudoExpr::HelperSymbol(crate::pseudo::ast::HelperIntrinsic::Fix) => {}
                    other => panic!("Expected HelperSymbol(Fix), got: {:?}", other),
                }
                assert_eq!(args.len(), 1);
                match &args[0] {
                    PseudoExpr::Var { name, .. } => assert_eq!(name, "rec_fn_16"),
                    other => panic!("Expected Var(rec_fn_16), got: {:?}", other),
                }
            }
            other => panic!("Expected Apply in let value, got: {:?}", other),
        },
        other => panic!("Expected Let, got: {:?}", other),
    }
}

#[test]
fn test_simplify_z_combinator_let_wrapped_fix_definition() {
    let acc = Binder::synthetic("acc");
    let inner = Binder::synthetic("inner");
    let x = Binder::synthetic("x");
    let v = Binder::synthetic("v");
    let expr = PseudoExpr::RecFn {
        name: "a".into(),
        params: vec![acc.clone()],
        body: PBox::new(PseudoExpr::Let {
            name: "inner".to_string(),
            id: Some(inner.var_id()),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("acc", acc.var_id())),
                args: vec![PseudoExpr::var_with_id("inner", inner.var_id())].into(),
            }),
            body: PBox::new(PseudoExpr::RecFn {
                name: inner.clone(),
                params: vec![x.clone()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("acc", acc.var_id())),
                    args: vec![PseudoExpr::Lambda {
                        params: vec![v.clone()],
                        body: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var_with_id("x", x.var_id())),
                            args: vec![
                                PseudoExpr::var_with_id("x", x.var_id()),
                                PseudoExpr::var_with_id("v", v.var_id()),
                            ]
                            .into(),
                        }),
                    }]
                    .into(),
                }),
            }),
        }),
    };

    let result = simplify_z_combinator(expr);
    match result {
        PseudoExpr::HelperSymbol(crate::pseudo::ast::HelperIntrinsic::Fix) => {}
        other => panic!("Expected HelperSymbol(Fix), got: {:?}", other),
    }
}

#[test]
fn test_simplify_z_combinator_let_bound_recursive_step_definition() {
    let acc = Binder::synthetic("acc");
    let inner = Binder::synthetic("inner");
    let x = Binder::synthetic("x");
    let v = Binder::synthetic("v");
    let expr = PseudoExpr::RecFn {
        name: "a".into(),
        params: vec![acc.clone()],
        body: PBox::new(PseudoExpr::Let {
            name: "inner".to_string(),
            id: Some(inner.var_id()),
            value: PBox::new(PseudoExpr::RecFn {
                name: inner.clone(),
                params: vec![x.clone()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("acc", acc.var_id())),
                    args: vec![PseudoExpr::Lambda {
                        params: vec![v.clone()],
                        body: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var_with_id("x", x.var_id())),
                            args: vec![
                                PseudoExpr::var_with_id("x", x.var_id()),
                                PseudoExpr::var_with_id("v", v.var_id()),
                            ]
                            .into(),
                        }),
                    }]
                    .into(),
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("acc", acc.var_id())),
                args: vec![PseudoExpr::var_with_id("inner", inner.var_id())].into(),
            }),
        }),
    };

    let result = simplify_z_combinator(expr);
    match result {
        PseudoExpr::HelperSymbol(crate::pseudo::ast::HelperIntrinsic::Fix) => {}
        other => panic!("Expected HelperSymbol(Fix), got: {:?}", other),
    }
}

#[test]
fn test_simplify_z_combinator_ignores_outer_same_name_self_application() {
    let outer_x_id = VarId::fresh_binding();
    let arg_a_id = VarId::fresh_binding();
    let arg_b_id = VarId::fresh_binding();
    let acc = Binder::synthetic("acc");
    let inner = Binder::synthetic("inner");
    let x = Binder::synthetic("x");
    let v = Binder::synthetic("v");
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_x_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("a", arg_a_id), Binder::new("b", arg_b_id)],
            body: PBox::new(PseudoExpr::Bool(true)),
        }),
        body: PBox::new(PseudoExpr::RecFn {
            name: "a".into(),
            params: vec![acc.clone()],
            body: PBox::new(PseudoExpr::Let {
                name: "inner".to_string(),
                id: Some(inner.var_id()),
                value: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("acc", acc.var_id())),
                    args: vec![PseudoExpr::var_with_id("inner", inner.var_id())].into(),
                }),
                body: PBox::new(PseudoExpr::RecFn {
                    name: inner.clone(),
                    params: vec![x.clone()],
                    body: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var_with_id("acc", acc.var_id())),
                        args: vec![PseudoExpr::Lambda {
                            params: vec![v.clone()],
                            body: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::Var {
                                    name: "x".to_string(),
                                    id: Some(outer_x_id),
                                }),
                                args: vec![
                                    PseudoExpr::var_with_id("x", x.var_id()),
                                    PseudoExpr::var_with_id("v", v.var_id()),
                                ]
                                .into(),
                            }),
                        }]
                        .into(),
                    }),
                }),
            }),
        }),
    };

    let result = simplify_z_combinator(expr.clone());
    assert_eq!(result, expr);
}

// Simplify::convert_expect_tag_to_constr_when

#[test]
fn test_convert_expect_tag_handles_unpack_fst_assertion() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::BinOp {
                op: crate::pseudo::ast::BinaryOp::Eq,
                left: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Constr.unpack"),
                        args: vec![PseudoExpr::var("redeemer")].into(),
                    },
                    "fst".to_string(),
                )),
                right: PBox::new(PseudoExpr::int(2)),
            },
            PseudoExpr::var("body"),
        ]
        .into(),
    };

    let converted = simplify::convert_expect_tag_to_constr_when(expr);

    match converted {
        PseudoExpr::When {
            subject,
            subject_name: None,
            clauses,
        } => {
            assert!(
                matches!(subject.as_ref(), PseudoExpr::Var { name, .. } if name == "redeemer"),
                "expected redeemer subject, got: {subject:?}"
            );
            assert_eq!(clauses.len(), 2, "expected expect-style when: {clauses:?}");
            assert!(
                matches!(
                    &clauses[0].pattern,
                    crate::pseudo::ast::WhenPattern::Constructor {
                        tag: 2,
                        fields,
                        ..
                    } if fields.is_empty()
                ),
                "expected Constr<2> pattern, got: {:?}",
                clauses[0].pattern
            );
            assert!(
                matches!(&clauses[0].body, PseudoExpr::Var { name, .. } if name == "body"),
                "expected body payload, got: {:?}",
                clauses[0].body
            );
            assert!(
                matches!(&clauses[1].body, PseudoExpr::Error { .. }),
                "expected wildcard fail branch, got: {:?}",
                clauses[1].body
            );
        }
        other => panic!("expected When after expect-tag conversion, got: {other:?}"),
    }
}

#[test]
fn test_convert_expect_tag_ignores_outer_same_name_callee() {
    let outer_x_id = VarId::fresh_binding();
    let callee_arg_id = VarId::fresh_binding();
    let param_x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_x_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("tag_value", callee_arg_id)],
            body: PBox::new(PseudoExpr::Bool(true)),
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", param_x_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("expect!")),
                args: vec![
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::Var {
                            name: "x".to_string(),
                            id: Some(outer_x_id),
                        }),
                        args: vec![PseudoExpr::field_access(
                            PseudoExpr::Var {
                                name: "x".to_string(),
                                id: Some(param_x_id),
                            },
                            "tag".to_string(),
                        )]
                        .into(),
                    },
                    PseudoExpr::Var {
                        name: "x".to_string(),
                        id: Some(param_x_id),
                    },
                ]
                .into(),
            }),
        }),
    };

    let converted = simplify::convert_expect_tag_to_constr_when(expr.clone());
    assert_eq!(converted, expr);
}

#[test]
fn test_convert_expect_tag_ignores_outer_same_name_fn_call_subject() {
    let outer_x_id = VarId::fresh_binding();
    let param_x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_x_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", param_x_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("expect!")),
                args: vec![
                    PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("fn_call")),
                        args: vec![
                            PseudoExpr::Var {
                                name: "x".to_string(),
                                id: Some(outer_x_id),
                            },
                            PseudoExpr::field_access(
                                PseudoExpr::Var {
                                    name: "x".to_string(),
                                    id: Some(param_x_id),
                                },
                                "tag".to_string(),
                            ),
                        ]
                        .into(),
                    },
                    PseudoExpr::Var {
                        name: "x".to_string(),
                        id: Some(param_x_id),
                    },
                ]
                .into(),
            }),
        }),
    };

    let converted = simplify::convert_expect_tag_to_constr_when(expr.clone());
    assert_eq!(converted, expr);
}

#[test]
fn test_convert_expect_tag_ignores_mixed_id_compat_same_name_callee() {
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("x", x_id)),
                args: vec![PseudoExpr::field_access(PseudoExpr::compat_var("x"), "tag")].into(),
            },
            PseudoExpr::var("body"),
        ]
        .into(),
    };

    let converted = simplify::convert_expect_tag_to_constr_when(expr.clone());

    assert_eq!(converted, expr);
}

#[test]
fn test_convert_expect_tag_ignores_mixed_id_compat_same_name_fn_call_subject() {
    let x_id = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("fn_call")),
                args: vec![
                    PseudoExpr::var_with_id("x", x_id),
                    PseudoExpr::field_access(PseudoExpr::compat_var("x"), "tag"),
                ]
                .into(),
            },
            PseudoExpr::var("body"),
        ]
        .into(),
    };

    let converted = simplify::convert_expect_tag_to_constr_when(expr.clone());

    assert_eq!(converted, expr);
}

#[test]
fn test_convert_expect_tag_accepts_both_compat_same_name_callee() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::compat_var("x")),
                args: vec![PseudoExpr::field_access(PseudoExpr::compat_var("x"), "tag")].into(),
            },
            PseudoExpr::var("body"),
        ]
        .into(),
    };

    let converted = simplify::convert_expect_tag_to_constr_when(expr);

    assert!(
        matches!(
            converted,
            PseudoExpr::When { subject, clauses, .. }
                if matches!(subject.as_ref(), PseudoExpr::Var { name, id } if name == "x" && id.get().is_none())
                    && matches!(
                        &clauses[0].pattern,
                        crate::pseudo::ast::WhenPattern::Constructor { tag: 0, fields, .. }
                            if fields.is_empty()
                    )
        ),
        "both-compat same-name refs should keep legacy expect-tag conversion"
    );
}

#[test]
fn test_simplify_z_combinator_wrong_arg_order() {
    let expr = PseudoExpr::RecFn {
        name: "self".into(),
        params: vec!["acc".into()],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["next".into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("acc")),
                args: vec![PseudoExpr::var("next"), PseudoExpr::var("captured")].into(),
            }),
        }),
    };
    let result = simplify_z_combinator(expr.clone());
    assert_eq!(result, expr);
}
