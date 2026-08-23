use super::{repair_list_prepend_alias_lets, rewrite_list_prepend_alias_uses};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

#[test]
fn rewrite_list_prepend_alias_uses_ignores_same_name_different_id_function() {
    let alias_id = VarId::new(6201);
    let unrelated_id = VarId::new(6202);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("xs", unrelated_id)),
        args: vec![PseudoExpr::int(1), PseudoExpr::var("tail")].into(),
    };

    let rewritten = rewrite_list_prepend_alias_uses(expr.clone(), "xs", alias_id);
    assert!(
        rewritten.structural_eq(&expr),
        "same-name function with different VarId must not be rewritten as the alias"
    );
}

#[test]
fn rewrite_list_prepend_alias_uses_rewrites_authoritative_outer_ref_under_shadow() {
    let alias_id = VarId::new(6211);
    let inner_id = VarId::new(6212);
    let expr = PseudoExpr::Let {
        name: "xs".to_string(),
        id: Some(inner_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("xs", alias_id)),
            args: vec![PseudoExpr::int(1), PseudoExpr::var("tail")].into(),
        }),
    };

    let rewritten = rewrite_list_prepend_alias_uses(expr, "xs", alias_id);
    assert!(
        matches!(
            rewritten,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::List { elements, tail }
                        if elements.len() == 1
                            && matches!(elements[0], PseudoExpr::Int(ref n) if *n == 1.into())
                            && matches!(tail.as_deref(), Some(PseudoExpr::Var { name, .. }) if name == "tail")
                )
        ),
        "authoritative outer alias ref should still rewrite under same-name inner shadow"
    );
}

#[test]
fn repair_list_prepend_alias_lets_drops_alias_when_only_unrelated_same_name_ref_remains() {
    let alias_id = VarId::new(6221);
    let unrelated_id = VarId::new(6222);
    let expr = PseudoExpr::Let {
        name: "xs".to_string(),
        id: Some(alias_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.prepend"),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("tail", VarId::new(6223))],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("xs", unrelated_id)),
                args: vec![PseudoExpr::int(1), PseudoExpr::var("tail")].into(),
            }),
        }),
    };

    let repaired = repair_list_prepend_alias_lets(expr);
    assert!(
        matches!(
            repaired,
            PseudoExpr::Lambda { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::Apply { function, .. }
                        if matches!(
                            function.as_ref(),
                            PseudoExpr::Var { name, id, .. } if name == "xs" && *id == Some(unrelated_id)
                        )
                )
        ),
        "late alias repair should drop the alias let when only an unrelated same-name ref remains"
    );
}
