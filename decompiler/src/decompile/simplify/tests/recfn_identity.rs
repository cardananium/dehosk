use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_recfn_binding_identity_stays_stable_across_repeated_simplify_passes() {
    // hygienic construction — rec-fn name /
    // params share ids with their refs so retarget doesn't rewrite.
    let self_id = VarId::from_raw(9);
    let xs_id = VarId::from_raw(10);
    let pred_id = VarId::from_raw(11);

    let expr = PseudoExpr::RecFn {
        name: crate::pseudo::ast::Binder::new("rec_fn_1", self_id),
        params: vec![
            crate::pseudo::ast::Binder::new("xs", xs_id),
            crate::pseudo::ast::Binder::new("pred", pred_id),
        ],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Var {
                name: "pred".to_string(),
                id: Some(pred_id),
            }),
            then_branch: PBox::new(PseudoExpr::Var {
                name: "xs".to_string(),
                id: Some(xs_id),
            }),
            else_branch: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: "rec_fn_1".to_string(),
                    id: Some(self_id),
                }),
                args: vec![
                    PseudoExpr::Var {
                        name: "xs".to_string(),
                        id: Some(xs_id),
                    },
                    PseudoExpr::Var {
                        name: "pred".to_string(),
                        id: Some(pred_id),
                    },
                ]
                .into(),
            }),
        }),
    };

    let once = simplify(expr);
    let twice = simplify(once);

    match twice {
        PseudoExpr::RecFn { params, body, .. } => {
            assert_eq!(params, vec!["xs".to_string(), "pred".to_string()]);
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::If { condition, then_branch, else_branch }
                        if matches!(condition.as_ref(), PseudoExpr::Var { name, id, .. } if name == "pred" && id.get() == Some(pred_id))
                        && matches!(then_branch.as_ref(), PseudoExpr::Var { name, id, .. } if name == "xs" && id.get() == Some(xs_id))
                        && matches!(else_branch.as_ref(), PseudoExpr::Apply { function, args }
                            if matches!(function.as_ref(), PseudoExpr::Var { name, id, .. } if name == "rec_fn_1" && id.get() == Some(self_id))
                            && args.len() == 2
                        )
                ),
                "repeated simplify should preserve recursive and parameter identities across passes: {body:?}"
            );
        }
        other => panic!("expected rec fn after repeated simplify, got: {other:?}"),
    }
}
