use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_param_hint_avoids_shadowing_outer_same_name_ref() {
    let outer_list_id = VarId::new(9701);
    let rec_id = VarId::new(9702);
    let list_param_id = VarId::new(9703);
    let index_param_id = VarId::new(9704);
    let keep_id = VarId::new(9705);
    let head_id = VarId::new(9706);
    let tail_id = VarId::new(9707);

    let expr = PseudoExpr::Let {
        name: "list".to_string(),
        id: Some(outer_list_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("rec_fn_7", rec_id),
            params: vec![
                Binder::new("x_3", list_param_id),
                Binder::new("acc_3", index_param_id),
            ],
            body: PBox::new(PseudoExpr::Let {
                name: "keep".to_string(),
                id: Some(keep_id),
                value: PBox::new(PseudoExpr::var_with_id("list", outer_list_id)),
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var_with_id("x_3", list_param_id)),
                    subject_name: Some(Binder::new("x_3", list_param_id)),
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            PseudoExpr::constr_known(KnownConstructor::None, vec![]),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![Binder::new("head", head_id)],
                                tail: Some(Binder::new("tail", tail_id)),
                            },
                            PseudoExpr::If {
                                condition: PBox::new(PseudoExpr::BinOp {
                                    op: BinaryOp::Eq,
                                    left: PBox::new(PseudoExpr::var_with_id(
                                        "acc_3",
                                        index_param_id,
                                    )),
                                    right: PBox::new(PseudoExpr::int(0)),
                                }),
                                then_branch: PBox::new(PseudoExpr::constr_known(
                                    KnownConstructor::Some,
                                    vec![PseudoExpr::var_with_id("head", head_id)],
                                )),
                                else_branch: PBox::new(PseudoExpr::Apply {
                                    function: PBox::new(PseudoExpr::var_with_id(
                                        "rec_fn_7", rec_id,
                                    )),
                                    args: vec![
                                        PseudoExpr::var_with_id("tail", tail_id),
                                        PseudoExpr::BinOp {
                                            op: BinaryOp::Sub,
                                            left: PBox::new(PseudoExpr::var_with_id(
                                                "acc_3",
                                                index_param_id,
                                            )),
                                            right: PBox::new(PseudoExpr::int(1)),
                                        },
                                    ]
                                    .into(),
                                }),
                            },
                        ),
                    ],
                }),
            }),
        }),
    };
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr),
        "fixture must start with consistent refs"
    );

    let improved = improve_variable_names(expr);

    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&improved),
        "param hinting must not shadow an existing outer list ref with a different id"
    );

    let PseudoExpr::Let { body, .. } = improved else {
        panic!("expected outer list let");
    };
    let PseudoExpr::RecFn { params, body, .. } = body.as_ref() else {
        panic!("expected recfn body, got: {body:?}");
    };
    assert_eq!(params[0].as_str(), "list_2");
    assert_eq!(params[0].var_id(), list_param_id);
    assert_eq!(params[1].as_str(), "index");
    assert_eq!(params[1].var_id(), index_param_id);

    let PseudoExpr::Let { value, body, .. } = body.as_ref() else {
        panic!("expected wrapper let in recfn body, got: {body:?}");
    };
    assert!(
        matches!(
            value.as_ref(),
            PseudoExpr::Var { name, id } if name == "list" && *id == Some(outer_list_id)
        ),
        "outer list ref must keep its original binding identity, got: {value:?}"
    );
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::When {
                subject,
                subject_name: Some(subject_name),
                ..
            } if matches!(
                subject.as_ref(),
                PseudoExpr::Var { name, id } if name == "list_2" && *id == Some(list_param_id)
            ) && subject_name.as_str() == "list_2"
                && subject_name.var_id() == list_param_id
        ),
        "recursive list subject should use the collision-free parameter name, got: {body:?}"
    );
}

#[test]
fn test_improve_variable_names_param_fallback_ignores_same_name_foreign_binder() {
    let outer_list_id = VarId::new(9711);
    let rec_id = VarId::new(9712);
    let list_param_id = VarId::new(9713);
    let index_param_id = VarId::new(9714);
    let head_id = VarId::new(9715);
    let tail_id = VarId::new(9716);
    let foreign_param_id = VarId::new(9717);

    let rec = PseudoExpr::RecFn {
        name: Binder::new("rec_fn_7", rec_id),
        params: vec![
            Binder::new("x_3", list_param_id),
            Binder::new("acc_3", index_param_id),
        ],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("x_3", list_param_id)),
            subject_name: Some(Binder::new("x_3", list_param_id)),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::constr_known(KnownConstructor::None, vec![]),
                ),
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![Binder::new("head", head_id)],
                        tail: Some(Binder::new("tail", tail_id)),
                    },
                    PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::var_with_id("acc_3", index_param_id)),
                            right: PBox::new(PseudoExpr::int(0)),
                        }),
                        then_branch: PBox::new(PseudoExpr::constr_known(
                            KnownConstructor::Some,
                            vec![PseudoExpr::var_with_id("head", head_id)],
                        )),
                        else_branch: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var_with_id("rec_fn_7", rec_id)),
                            args: vec![
                                PseudoExpr::var_with_id("tail", tail_id),
                                PseudoExpr::BinOp {
                                    op: BinaryOp::Sub,
                                    left: PBox::new(PseudoExpr::var_with_id(
                                        "acc_3",
                                        index_param_id,
                                    )),
                                    right: PBox::new(PseudoExpr::int(1)),
                                },
                            ]
                            .into(),
                        }),
                    },
                ),
            ],
        }),
    };
    let foreign_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x_3", foreign_param_id)],
        body: PBox::new(PseudoExpr::var_with_id("list", outer_list_id)),
    };
    let expr = PseudoExpr::Let {
        name: "list".to_string(),
        id: Some(outer_list_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Tuple((vec![rec, foreign_lambda]).into())),
    };
    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr),
        "fixture must start with consistent refs"
    );

    let improved = improve_variable_names(expr);

    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&improved),
        "param fallback must not rename an unrelated same-name binder into a ref-capturing shadow"
    );

    let PseudoExpr::Let { body, .. } = improved else {
        panic!("expected outer list let");
    };
    let PseudoExpr::Tuple(items) = body.as_ref() else {
        panic!("expected tuple body, got: {body:?}");
    };
    let PseudoExpr::RecFn { params, .. } = &items[0] else {
        panic!("expected renamed recfn, got: {:?}", items[0]);
    };
    assert_eq!(params[0].as_str(), "list");
    assert_eq!(params[0].var_id(), list_param_id);
    assert_eq!(params[1].as_str(), "index");
    assert_eq!(params[1].var_id(), index_param_id);

    let PseudoExpr::Lambda { params, body } = &items[1] else {
        panic!("expected foreign lambda, got: {:?}", items[1]);
    };
    assert_eq!(params[0].as_str(), "x_3");
    assert_eq!(params[0].var_id(), foreign_param_id);
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Var { name, id } if name == "list" && *id == Some(outer_list_id)
        ),
        "foreign lambda body must keep referencing the outer list binder, got: {body:?}"
    );
}
