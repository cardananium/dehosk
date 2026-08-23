use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;
use crate::pseudo::var_id::VarId;

fn church_pair(a: PseudoExpr, b: PseudoExpr, x_name: &str) -> PseudoExpr {
    let x_id = VarId::fresh_binding();
    PseudoExpr::Force(PBox::new(PseudoExpr::Lambda {
        params: vec![Binder::new(x_name, x_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id(x_name, x_id)),
            args: vec![a, b].into(),
        }),
    }))
}

fn fst_of(record: PseudoExpr) -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: PBox::new(record),
        selector: FieldSelector::PairFst,
    }
}

fn snd_of(record: PseudoExpr) -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: PBox::new(record),
        selector: FieldSelector::PairSnd,
    }
}

/// C1 positive: `Force(Lambda(x, x(a, b))).fst` → `a` when `b` is
/// pure (Int literal).
#[test]
fn c1_collapses_fst_when_discard_is_pure_literal() {
    let pair = church_pair(PseudoExpr::Int(10.into()), PseudoExpr::Int(20.into()), "x");
    let expr = fst_of(pair);
    let result = collapse_church_pair_eliminator_ast(expr);
    assert!(matches!(result, PseudoExpr::Int(ref n) if n.to_string() == "10"));
}

/// C1 positive: `.snd` → `b` when `a` is pure.
#[test]
fn c1_collapses_snd_when_discard_is_pure() {
    let pair = church_pair(PseudoExpr::Int(10.into()), PseudoExpr::Int(20.into()), "x");
    let expr = snd_of(pair);
    let result = collapse_church_pair_eliminator_ast(expr);
    assert!(matches!(result, PseudoExpr::Int(ref n) if n.to_string() == "20"));
}

/// C1 safety: refuse to collapse when the discarded side is
/// impure (here a `BuiltinCall` — must be evaluated even when
/// projecting `.fst`).
#[test]
fn c1_refuses_when_discard_is_impure_builtin_call() {
    let pair = church_pair(
        PseudoExpr::Int(10.into()),
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::Error,
            args: vec![PseudoExpr::Int(1.into()), PseudoExpr::Int(2.into())].into(),
        },
        "x",
    );
    let expr = fst_of(pair);
    let result = collapse_church_pair_eliminator_ast(expr.clone());
    // Top-level still FieldAccess — refusal.
    assert!(matches!(result, PseudoExpr::FieldAccess { .. }));
}

/// C1 safety: refuse when the discarded side is a `Let` —
/// could throw or allocate.
#[test]
fn c1_refuses_when_discard_is_let_expression() {
    let pair = church_pair(
        PseudoExpr::Int(10.into()),
        PseudoExpr::let_bind_with_id(
            "z",
            VarId::fresh_binding(),
            PseudoExpr::Int(99.into()),
            PseudoExpr::Var {
                name: "z".to_string(),
                id: None,
            },
        ),
        "x",
    );
    let expr = fst_of(pair);
    let result = collapse_church_pair_eliminator_ast(expr.clone());
    assert!(matches!(result, PseudoExpr::FieldAccess { .. }));
}

/// C1 safety: refuse when the VarId in the Apply doesn't match
/// the Lambda's param — this is a different shape, not a
/// church-pair projector.
#[test]
fn c1_refuses_when_var_id_mismatches_lambda_param() {
    let x_id = VarId::fresh_binding();
    let other_id = VarId::fresh_binding();
    let pair = PseudoExpr::Force(PBox::new(PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("y", other_id)),
            args: vec![PseudoExpr::Int(10.into()), PseudoExpr::Int(20.into())].into(),
        }),
    }));
    let expr = fst_of(pair);
    let result = collapse_church_pair_eliminator_ast(expr.clone());
    assert!(matches!(result, PseudoExpr::FieldAccess { .. }));
}

/// C1 safety: refuse `.tag` / named-field access — only PairFst /
/// PairSnd qualify as church-pair projectors.
#[test]
fn c1_refuses_non_pair_field_selector() {
    let pair = church_pair(PseudoExpr::Int(10.into()), PseudoExpr::Int(20.into()), "x");
    let expr = PseudoExpr::FieldAccess {
        record: PBox::new(pair),
        selector: FieldSelector::NamedField("tag".to_string()),
    };
    let result = collapse_church_pair_eliminator_ast(expr.clone());
    assert!(matches!(result, PseudoExpr::FieldAccess { .. }));
}

/// C1 positive: nested case — `.snd` inside a larger
/// expression is rewritten by the walk.
#[test]
fn c1_collapses_nested_inside_lambda_body() {
    let pair = church_pair(PseudoExpr::Bool(true), PseudoExpr::Int(0.into()), "x");
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("p", VarId::fresh_binding())],
        body: PBox::new(snd_of(pair)),
    };
    let result = collapse_church_pair_eliminator_ast(expr);
    let PseudoExpr::Lambda { body, .. } = result else {
        panic!("expected Lambda");
    };
    assert!(matches!(body.as_ref(), PseudoExpr::Int(_)));
}

/// C1 positive: Lambda as the discarded side is PURE (UPLC
/// lambda is a first-class value).
#[test]
fn c1_collapses_when_discard_is_lambda_value() {
    let pair = church_pair(
        PseudoExpr::Int(10.into()),
        PseudoExpr::Lambda {
            params: vec![Binder::new("y", VarId::fresh_binding())],
            body: PBox::new(PseudoExpr::Unit),
        },
        "x",
    );
    let expr = fst_of(pair);
    let result = collapse_church_pair_eliminator_ast(expr);
    assert!(matches!(result, PseudoExpr::Int(_)));
}

/// Bare `Var{name:"expect!", id:None}` is the simplifier's abort
/// sentinel. This pass must NOT treat it as pure — discarding it
/// would drop the abort.
#[test]
fn c1_refuses_when_discard_is_bare_expect_sentinel() {
    let pair = church_pair(
        PseudoExpr::Int(10.into()),
        PseudoExpr::Var {
            name: "expect!".to_string(),
            id: None,
        },
        "x",
    );
    let expr = fst_of(pair);
    let result = collapse_church_pair_eliminator_ast(expr.clone());
    assert!(
        matches!(result, PseudoExpr::FieldAccess { .. }),
        "C1 must refuse to drop bare expect! sentinel"
    );
}

/// Symmetric case: `Var "expect!"` on the .fst side,
/// projecting .snd. C1 must still refuse.
#[test]
fn c1_refuses_when_discard_is_bare_expect_sentinel_on_snd() {
    let pair = church_pair(
        PseudoExpr::Var {
            name: "expect!".to_string(),
            id: None,
        },
        PseudoExpr::Int(20.into()),
        "x",
    );
    let expr = snd_of(pair);
    let result = collapse_church_pair_eliminator_ast(expr.clone());
    assert!(matches!(result, PseudoExpr::FieldAccess { .. }));
}

/// Sanity: a regular `Var` (not the synthetic sentinel) on the
/// discarded side is STILL pure — UPLC variable refs are values.
#[test]
fn c1_collapses_when_discard_is_regular_var() {
    let user_var_id = VarId::fresh_binding();
    let pair = church_pair(
        PseudoExpr::Int(10.into()),
        PseudoExpr::Var {
            name: "user_var".to_string(),
            id: Some(user_var_id),
        },
        "x",
    );
    let expr = fst_of(pair);
    let result = collapse_church_pair_eliminator_ast(expr);
    assert!(matches!(result, PseudoExpr::Int(_)));
}
