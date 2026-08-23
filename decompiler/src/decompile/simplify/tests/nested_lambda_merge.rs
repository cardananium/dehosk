use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_nested_lambda_merge_all_wildcards() {
    // fn(_) { fn(ok, _) { ok } } → fn(_, ok, _) { ok }
    let expr = PseudoExpr::Lambda {
        params: vec!["_".to_string().into()],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["ok".to_string().into(), "_".to_string().into()],
            body: PBox::new(PseudoExpr::var("ok")),
        }),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(
                params,
                &["_", "ok", "_"],
                "expected [_, ok, _], got: {:?}",
                params
            );
            assert!(
                matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "ok"),
                "expected Var(ok), got: {:?}",
                body
            );
        }
        _ => panic!("expected Lambda, got: {:?}", simplified),
    }
}

#[test]
fn test_nested_lambda_merge_when_outer_param_is_used_by_inner_body() {
    // fn(a) { fn(b) { f(a, b) } } → fn(a, b) { f(a, b) }
    let expr = PseudoExpr::Lambda {
        params: vec!["a".to_string().into()],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["b".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("f")),
                args: vec![PseudoExpr::var("a"), PseudoExpr::var("b")].into(),
            }),
        }),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(
                params,
                &["a", "b"],
                "expected merged params, got: {params:?}"
            );
            assert!(
                matches!(body.as_ref(), PseudoExpr::Apply { args, .. } if args.len() == 2),
                "expected merged apply body, got: {:?}",
                body
            );
        }
        _ => panic!("expected Lambda, got: {:?}", simplified),
    }
}

#[test]
fn test_nested_lambda_shadowed_outer_param_becomes_wildcard_before_merge() {
    // fn(a) { fn(a) { a } } → fn(_, a) { a }
    // The outer binding is truly unused after respecting inner shadowing.
    let expr = PseudoExpr::Lambda {
        params: vec!["a".to_string().into()],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["a".to_string().into()],
            body: PBox::new(PseudoExpr::var("a")),
        }),
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(
                params,
                &["_", "a"],
                "expected outer shadowed param to become wildcard, got: {params:?}"
            );
            assert!(
                matches!(body.as_ref(), PseudoExpr::Var { name, .. } if name == "a"),
                "expected body to keep inner binding, got: {:?}",
                body
            );
        }
        _ => panic!("expected Lambda, got: {:?}", simplified),
    }
}
