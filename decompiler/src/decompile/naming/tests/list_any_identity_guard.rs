use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_analyze_function_binding_ignores_same_name_different_id_direct_rec_any_tail_ref() {
    let outer_tail_id = VarId::fresh_binding();
    let value = PseudoExpr::RecFn {
        name: "fn_2".to_string().into(),
        params: vec!["xs".to_string().into(), "pred".to_string().into()],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("xs")),
            subject_name: Some("xs".to_string().into()),
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
                            function: PBox::new(PseudoExpr::var("pred")),
                            args: vec![PseudoExpr::var("head")].into(),
                        }),
                        right: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("fn_2")),
                            args: vec![
                                PseudoExpr::var_with_id("tail", outer_tail_id),
                                PseudoExpr::var("pred"),
                            ]
                            .into(),
                        }),
                    },
                ),
            ],
        }),
    };

    assert_eq!(analyze_function_binding("fn_2", &value), None);
}
