use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_recfn_flattens_curried_lambda_body_into_params() {
    let expr = PseudoExpr::RecFn {
        name: "go".to_string().into(),
        params: vec!["xs".to_string().into()],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["pred".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("step")),
                args: vec![PseudoExpr::var("xs"), PseudoExpr::var("pred")].into(),
            }),
        }),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(
                params,
                &["xs", "pred"],
                "expected non-recursive rec fn params to flatten into lambda params, got: {params:?}"
            );
            assert!(
                matches!(body.as_ref(), PseudoExpr::Apply { args, .. } if args.len() == 2),
                "expected flattened lambda body, got: {:?}",
                body
            );
        }
        _ => panic!("expected Lambda, got: {:?}", simplified),
    }
}

#[test]
fn test_non_recursive_recfn_becomes_lambda() {
    let expr = PseudoExpr::RecFn {
        name: "helper".to_string().into(),
        params: vec!["xs".to_string().into(), "pred".to_string().into()],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("step")),
            args: vec![PseudoExpr::var("xs"), PseudoExpr::var("pred")].into(),
        }),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params, &["xs", "pred"]);
            assert!(
                matches!(body.as_ref(), PseudoExpr::Apply { args, .. } if args.len() == 2),
                "expected non-recursive rec fn body to become lambda body, got: {body:?}"
            );
        }
        other => panic!("expected Lambda, got: {other:?}"),
    }
}

#[test]
fn test_recursive_recfn_is_preserved() {
    let expr = PseudoExpr::RecFn {
        name: "helper".to_string().into(),
        params: vec!["xs".to_string().into()],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("helper")),
            args: vec![PseudoExpr::var("xs")].into(),
        }),
    };

    let simplified = simplify(expr.clone());
    match simplified {
        PseudoExpr::RecFn { name, params, body } => {
            assert_eq!(name, "helper");
            assert_eq!(params, vec!["xs".to_string()]);
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, args }
                        if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "helper")
                            && matches!(args.as_slice(), [PseudoExpr::Var { name, .. }] if name == "xs")
                ),
                "expected recursive body to be preserved, got: {body:?}"
            );
        }
        other => panic!("expected RecFn, got: {other:?}"),
    }
}

#[test]
fn test_recfn_without_self_refs_preserves_existing_name_id_when_recfn_retained() {
    let rec_id = VarId::new(9370);
    let ignored_id = VarId::new(9371);
    let expr = PseudoExpr::RecFn {
        name: Binder::new("helper", rec_id),
        params: vec![Binder::new("_", ignored_id)],
        body: PBox::new(PseudoExpr::int(1)),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::RecFn { name, params, body } => {
            assert_eq!(name.as_str(), "helper");
            assert_eq!(
                name.id, rec_id,
                "retained recfn without self refs must keep its existing binder id"
            );
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].as_str(), "_");
            assert_eq!(params[0].id, ignored_id);
            assert!(
                matches!(body.as_ref(), PseudoExpr::Int(_)),
                "expected recfn body to stay as a literal, got: {body:?}"
            );
        }
        other => panic!("expected RecFn to be retained, got: {other:?}"),
    }
}
