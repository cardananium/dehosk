use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_ignores_same_name_different_id_get_at_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "rec_fn_7".to_string(),
        id: Some(VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::RecFn {
            name: "rec_fn_7".to_string().into(),
            params: vec!["list_2".to_string().into(), "acc_3".to_string().into()],
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("list_2")),
                subject_name: Some("list_2".to_string().into()),
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
                            elements: vec!["head".into()],
                            tail: Some("tail".into()),
                        },
                        PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::BinOp {
                                op: BinaryOp::Eq,
                                left: PBox::new(PseudoExpr::var("acc_3")),
                                right: PBox::new(PseudoExpr::int(0)),
                            }),
                            then_branch: PBox::new(PseudoExpr::constr_known(
                                KnownConstructor::Some,
                                vec![PseudoExpr::var("head")],
                            )),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("rec_fn_7")),
                                args: vec![
                                    PseudoExpr::var_with_id("tail", outer_tail_id),
                                    PseudoExpr::BinOp {
                                        op: BinaryOp::Sub,
                                        left: PBox::new(PseudoExpr::var("acc_3")),
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
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("rec_fn_7")),
            args: vec![PseudoExpr::var("values"), PseudoExpr::var("idx")].into(),
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "rec_fn_7");
            let PseudoExpr::RecFn {
                name: rec_name,
                params,
                ..
            } = value.as_ref()
            else {
                panic!("expected let-bound recfn value, got: {value:?}");
            };
            assert_eq!(rec_name.as_str(), "rec_fn_7");
            assert_eq!(params[0].as_str(), "list_2");
            assert_eq!(params[1].as_str(), "acc_3");
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, .. }
                        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "rec_fn_7")
                ),
                "expected false-positive get_at helper to stay unrenamed, got: {body:?}"
            );
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}
