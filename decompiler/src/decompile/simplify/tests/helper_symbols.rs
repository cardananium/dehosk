use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_helper_symbols_use_compat_placeholder_ids() {
    assert_expect_helper_head(&PseudoExpr::expect_helper());
    assert_helper_symbol(&PseudoExpr::fix_helper(), "fix");
    assert_helper_symbol(
        &PseudoExpr::helper_symbol("__y_comb_direct"),
        "__y_comb_direct",
    );
}

fn assert_expect_not_list_empty_uses_builtin(expr: &PseudoExpr) {
    let mut current = expr;
    while let PseudoExpr::Let { body, .. } = current {
        current = body.as_ref();
    }

    let PseudoExpr::Apply { function, args } = current else {
        panic!("expected expect! application, got: {current:?}");
    };
    assert_expect_helper_head(function.as_ref());
    assert_eq!(
        args.len(),
        2,
        "expected expect!(cond, value), got: {args:?}"
    );
    let PseudoExpr::UnOp {
        op: UnaryOp::Not,
        operand,
    } = &args[0]
    else {
        panic!(
            "expected negated List.is_empty condition, got: {:?}",
            args[0]
        );
    };
    assert!(
        matches!(
            operand.as_ref(),
            PseudoExpr::BuiltinCall { name, args }
                if *name == crate::BuiltinId::ListIsEmpty
                    && matches!(args.as_slice(), [PseudoExpr::Var { name, .. }] if name == "xs")
        ),
        "expected direct List.is_empty builtin call, got: {operand:?}"
    );
}

#[test]
fn test_force_partial_choose_list_expect_uses_builtin_list_is_empty_not_scope_ref() {
    let foreign_id = VarId::new(9390);
    let expr = PseudoExpr::Let {
        name: "List.is_empty".to_string(),
        id: Some(foreign_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::ListFold,
                    args: vec![].into(),
                }))),
                args: vec![PseudoExpr::var("xs")].into(),
            }))),
            args: vec![
                PseudoExpr::Delay(PBox::new(PseudoExpr::error())),
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
            ]
            .into(),
        }))),
    };

    let simplified = simplify(expr);
    assert_expect_not_list_empty_uses_builtin(&simplified);
}

#[test]
fn test_force_list_fold_expect_uses_builtin_list_is_empty_not_scope_ref() {
    let foreign_id = VarId::new(9391);
    let expr = PseudoExpr::Let {
        name: "List.is_empty".to_string(),
        id: Some(foreign_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::ListFold,
                args: vec![].into(),
            }),
            args: vec![
                PseudoExpr::var("xs"),
                PseudoExpr::Delay(PBox::new(PseudoExpr::error())),
                PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
            ]
            .into(),
        }))),
    };

    let simplified = simplify(expr);
    assert_expect_not_list_empty_uses_builtin(&simplified);
}
