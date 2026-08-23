use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_renames_false_like_lookup_params_to_pairs_and_needle() {
    let expr = PseudoExpr::RecFn {
        name: "g".to_string().into(),
        params: vec!["x_3".to_string().into(), "y_2".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("x_3")),
            subject_name: Some("x_3".to_string().into()),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    PseudoExpr::bool(false),
                ),
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec!["entry".into()],
                        tail: Some("tail".into()),
                    },
                    PseudoExpr::If {
                        condition: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "fst".to_string(),
                            )),
                            right: PBox::new(PseudoExpr::var("y_2")),
                        }),
                        then_branch: PBox::new(PseudoExpr::constr_known(
                            KnownConstructor::Some,
                            vec![PseudoExpr::field_access(
                                PseudoExpr::var("entry"),
                                "snd".to_string(),
                            )],
                        )),
                        else_branch: PBox::new(PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::BinOp {
                                op: BinaryOp::Lt,
                                left: PBox::new(PseudoExpr::var("y_2")),
                                right: PBox::new(PseudoExpr::field_access(
                                    PseudoExpr::var("entry"),
                                    "fst".to_string(),
                                )),
                            }),
                            then_branch: PBox::new(PseudoExpr::bool(false)),
                            else_branch: PBox::new(PseudoExpr::Apply {
                                function: PBox::new(PseudoExpr::var("g")),
                                args: vec![PseudoExpr::var("tail"), PseudoExpr::var("y_2")].into(),
                            }),
                        }),
                    },
                ),
            ],
        }),
    };

    let improved = improve_variable_names(expr);

    match improved {
        PseudoExpr::RecFn { name, params, body } => {
            assert_eq!(name.as_str(), "lookup");
            assert_eq!(params[0].as_str(), "pairs");
            assert_eq!(params[1].as_str(), "needle");
            let body_str = format!("{body:?}");
            assert!(
                body_str.contains("subject_name: Some(Binder { name: \"pairs\"")
                    && body_str.contains("name: \"needle\"")
                    && !body_str.contains("x_3")
                    && !body_str.contains("y_2"),
                "expected false-like lookup params to rename through body, got: {body_str}"
            );
        }
        other => panic!("expected recfn, got: {other:?}"),
    }
}
