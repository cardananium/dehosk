use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_let_lambda_rec_wrapper_promotes_to_direct_recfn_binding() {
    let expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["xs".to_string().into(), "pred".to_string().into()],
            body: PBox::new(PseudoExpr::Let {
                name: "rec_fn".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::RecFn {
                    name: "rec_fn".to_string().into(),
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
                                PseudoExpr::Bool(false),
                            ),
                            WhenClause::new(
                                WhenPattern::List {
                                    elements: vec!["head".into()],
                                    tail: Some("tail".into()),
                                },
                                PseudoExpr::BinOp {
                                    op: BinaryOp::Or,
                                    left: PBox::new(PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var("acc")),
                                        args: vec![PseudoExpr::var("head")].into(),
                                    }),
                                    right: PBox::new(PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var("rec_fn")),
                                        args: vec![PseudoExpr::var("tail"), PseudoExpr::var("acc")]
                                            .into(),
                                    }),
                                },
                            ),
                        ],
                    }),
                }),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("rec_fn")),
                    args: vec![PseudoExpr::var("xs"), PseudoExpr::var("pred")].into(),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![PseudoExpr::var("helper"), PseudoExpr::var("helper")].into(),
        )),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::Let { value, .. } => match value.as_ref() {
            PseudoExpr::RecFn { name, params, body } => {
                assert_eq!(name, "helper");
                assert_eq!(params, &["xs", "pred"]);
                match body.as_ref() {
                    PseudoExpr::When {
                        subject, clauses, ..
                    } => {
                        assert!(
                            matches!(subject.as_ref(), PseudoExpr::Var { name, .. } if name == "xs"),
                            "expected promoted recfn to use wrapper params, got: {:?}",
                            subject
                        );
                        assert_eq!(clauses.len(), 2);
                    }
                    other => panic!("expected When body, got: {other:?}"),
                }
            }
            other => panic!("expected promoted RecFn value, got: {other:?}"),
        },
        other => panic!("expected Let, got: {other:?}"),
    }
}

#[test]
fn test_let_lambda_rec_wrapper_promotes_captured_outer_params_into_recfn() {
    let expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                "xs".to_string().into(),
                "pred".to_string().into(),
                "seed".to_string().into(),
            ],
            body: PBox::new(PseudoExpr::Let {
                name: "rec_fn".to_string(),
                id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                value: PBox::new(PseudoExpr::RecFn {
                    name: "rec_fn".to_string().into(),
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
                                PseudoExpr::var("seed"),
                            ),
                            WhenClause::new(
                                WhenPattern::List {
                                    elements: vec!["head".into()],
                                    tail: Some("tail".into()),
                                },
                                PseudoExpr::If {
                                    condition: PBox::new(PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var("acc")),
                                        args: vec![PseudoExpr::var("head")].into(),
                                    }),
                                    then_branch: PBox::new(PseudoExpr::var("seed")),
                                    else_branch: PBox::new(PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var("rec_fn")),
                                        args: vec![PseudoExpr::var("tail"), PseudoExpr::var("acc")]
                                            .into(),
                                    }),
                                },
                            ),
                        ],
                    }),
                }),
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("rec_fn")),
                    args: vec![PseudoExpr::var("xs"), PseudoExpr::var("pred")].into(),
                }),
            }),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![PseudoExpr::var("helper"), PseudoExpr::var("helper")].into(),
        )),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::Let { value, .. } => match value.as_ref() {
            PseudoExpr::RecFn { name, params, body } => {
                assert_eq!(name, "helper");
                assert_eq!(params, &["xs", "pred", "seed"]);
                match body.as_ref() {
                    PseudoExpr::When { clauses, .. } => {
                        let recursive_call = match &clauses[1].body {
                            PseudoExpr::If { else_branch, .. } => else_branch.as_ref(),
                            other => panic!("expected recursive branch in if, got: {other:?}"),
                        };
                        assert!(
                            matches!(
                                recursive_call,
                                PseudoExpr::Apply { function, args }
                                    if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "helper")
                                        && matches!(
                                            args.as_slice(),
                                            [
                                                PseudoExpr::Var { name: tail_name, .. },
                                                PseudoExpr::Var { name: acc_name, .. },
                                                PseudoExpr::Var { name: seed_name, .. },
                                            ] if tail_name == "tail" && acc_name == "pred" && seed_name == "seed"
                                        )
                            ),
                            "expected captured outer param to be appended to recursive self-call, got: {recursive_call:?}"
                        );
                    }
                    other => panic!("expected When body, got: {other:?}"),
                }
            }
            other => panic!("expected promoted RecFn value, got: {other:?}"),
        },
        other => panic!("expected Let, got: {other:?}"),
    }
}
