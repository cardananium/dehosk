use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_improve_variable_names_renames_generated_result_from_known_function_rename() {
    let expr = PseudoExpr::Let {
        name: "fn_3".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec!["xs".to_string().into(), "needle".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("any_2")),
                args: vec![
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Data.un_list"),
                        args: vec![PseudoExpr::var("xs")].into(),
                    },
                    PseudoExpr::Lambda {
                        params: vec!["item".to_string().into()],
                        body: PBox::new(PseudoExpr::BinOp {
                            op: BinaryOp::Eq,
                            left: PBox::new(PseudoExpr::var("item")),
                            right: PBox::new(PseudoExpr::var("needle")),
                        }),
                    },
                ]
                .into(),
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "fn_3_result".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("fn_3")),
                args: vec![PseudoExpr::var("inputs"), PseudoExpr::var("target")].into(),
            }),
            body: PBox::new(PseudoExpr::var("fn_3_result")),
        }),
    };

    let improved = render_improve_variable_names(expr);

    match improved {
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            assert_eq!(name, "contains");
            assert!(matches!(value.as_ref(), PseudoExpr::Lambda { .. }));
            match body.as_ref() {
                PseudoExpr::Let {
                    name, value, body, ..
                } => {
                    assert_eq!(name, "contains_result");
                    assert!(
                        matches!(
                            value.as_ref(),
                            PseudoExpr::Apply { function, .. }
                                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "contains")
                        ),
                        "expected contains call, got: {value:?}"
                    );
                    assert!(
                        matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "contains_result"),
                        "expected renamed result var, got: {body:?}"
                    );
                }
                other => panic!("expected inner let, got: {other:?}"),
            }
        }
        other => panic!("expected outer let, got: {other:?}"),
    }
}
