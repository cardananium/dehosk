use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_single_use_nonlambda_inlining() {
    // let x = Data.to_bytes(y) in Constr<1>(x)
    // > Constr<1>(Data.to_bytes(y)) (single-use, small value, inlined)
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.to_bytes"),
            args: vec![PseudoExpr::var("y")].into(),
        }),
        body: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(1, 1),
            vec![PseudoExpr::var("x")],
        )),
    };
    let simplified = simplify(expr);
    // Should inline x -> Constr<1>(Data.to_bytes(y))
    match &simplified {
        PseudoExpr::Constr { tag, fields, .. } => {
            assert_eq!(*tag, 1);
            assert_eq!(fields.len(), 1);
            assert!(
                matches!(&fields[0], PseudoExpr::BuiltinCall { name, .. } if name == "Data.to_bytes")
            );
        }
        _ => panic!("expected Constr, got: {:?}", simplified),
    }
}

#[test]
fn test_single_use_inlining_preserves_structural_access() {
    // let h = y[0] in use(h) should NOT inline; IndexAccess is kept for destructuring
    let expr = PseudoExpr::Let {
        name: "h".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(PseudoExpr::var("y")),
            index: 0,
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("use")),
            args: vec![PseudoExpr::var("h")].into(),
        }),
    };
    let simplified = simplify(expr);
    // Should keep the let binding (IndexAccess excluded from inlining)
    assert!(
        matches!(simplified, PseudoExpr::Let { .. }),
        "expected Let, got: {:?}",
        simplified
    );
}

#[test]
fn test_single_use_generated_result_binding_inlines_helper_application() {
    let expr = PseudoExpr::Let {
        name: "fn_3_result".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("contains")),
            args: vec![PseudoExpr::var("xs"), PseudoExpr::var("needle")].into(),
        }),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("expect!")),
            args: vec![PseudoExpr::var("fn_3_result"), PseudoExpr::var("ok")].into(),
        }),
    };

    let simplified = simplify(expr);

    match simplified {
        PseudoExpr::Apply { function, args } => {
            assert!(
                matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "expect!"),
                "expected expect! call, got: {function:?}"
            );
            assert_eq!(args.len(), 2, "expected expect! arity, got: {args:?}");
            assert!(
                matches!(&args[0], PseudoExpr::Apply { function, args: inner_args }
                    if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "contains")
                        && inner_args.len() == 2),
                "expected inlined contains application, got: {:?}",
                args[0]
            );
        }
        other => {
            panic!("expected expect! after inlining generated result binding, got: {other:?}")
        }
    }
}
