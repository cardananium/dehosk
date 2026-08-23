use super::*;
use crate::decompile::simplify::Simplifier;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};
use std::collections::HashSet;

#[test]
fn test_inline_single_use() {
    // let x = 42 in x + 1 -> 42 + 1
    // Authoritative VarIds (`fresh_binding` / `var_with_id`) so the test
    // exercises the id-based dispatch the inliner uses.
    let x_id = crate::pseudo::var_id::VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(PseudoExpr::var_with_id("x", x_id)),
            right: PBox::new(PseudoExpr::int(1)),
        }),
    };

    let result = inline_single_use(expr);

    // Should be inlined
    if let PseudoExpr::BinOp { left, .. } = result {
        assert!(matches!(*left, PseudoExpr::Int(_)));
    } else {
        panic!("Expected BinOp");
    }
}

#[test]
fn test_no_inline_multi_use() {
    // let x = 42 in x + x -> kept (used twice)
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(PseudoExpr::var("x")),
            right: PBox::new(PseudoExpr::var("x")),
        }),
    };

    let result = inline_single_use(expr);
    assert!(
        matches!(result, PseudoExpr::Let { .. }),
        "Multi-use should not be inlined"
    );
}

#[test]
fn test_preserved_binding_is_not_inlined() {
    // Even when usage count matches the simple inline heuristics,
    // a binding in the preserve set stays as a `let`.
    let x_id = crate::pseudo::var_id::VarId::fresh_binding();
    let x_vid = x_id.get().expect("fresh binder has id");
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(PseudoExpr::var("x")),
            right: PBox::new(PseudoExpr::int(1)),
        }),
    };

    let mut preserved = HashSet::new();
    preserved.insert(x_vid);
    let result = inline_single_use_preserving(expr, &preserved);

    assert!(
        matches!(result, PseudoExpr::Let { .. }),
        "Preserved binding should stay as let, got: {:?}",
        result
    );
}

#[test]
fn test_no_inline_complex_value() {
    // let x = f(1) in x -> kept (value is not simple)
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::int(1)].into(),
        }),
        body: PBox::new(PseudoExpr::var("x")),
    };

    let result = inline_single_use(expr);
    assert!(
        matches!(result, PseudoExpr::Let { .. }),
        "Complex value should not be inlined"
    );
}

#[test]
fn test_lambda_shadowing_prevents_inline() {
    // let x = 42 in fn(x) { x }
    // The inner x (lambda param) should NOT be replaced with 42
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }),
    };

    let result = inline_single_use(expr);
    // The let inlines (count=1: the usage count sees the lambda param's
    // use), but the lambda's x param shadows the inline, so the body
    // stays Var("x") rather than Int(42).
    if let PseudoExpr::Lambda { body, .. } = result {
        assert!(
            matches!(*body, PseudoExpr::Var { .. }),
            "Lambda param should not be replaced by inline value"
        );
    }
    // It's also acceptable if the let is kept because count >= 1
}

#[test]
fn test_inline_hot_projection_lambda() {
    // Authoritative VarIds (`fresh_binding` / `var_with_id`) so the test
    // exercises the projection-lambda heuristic on both inliners:
    // compat-placeholder refs never reach the id-only nameless dispatch.
    let f_id = crate::pseudo::var_id::VarId::fresh_binding();
    let x_id = crate::pseudo::var_id::VarId::fresh_binding();
    let projection = || PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.tail"),
            args: vec![].into(),
        }),
        args: vec![PseudoExpr::field_access(
            PseudoExpr::var_with_id("x", x_id),
            "fields".to_string(),
        )]
        .into(),
    };
    let call = |arg: &str| PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
        args: vec![PseudoExpr::var(arg)].into(),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(f_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(projection()),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                call("a1"),
                call("a2"),
                call("a3"),
                call("a4"),
                call("a5"),
                call("a6"),
                call("a7"),
            ]
            .into(),
        )),
    };

    let result = inline_single_use(expr);
    assert_eq!(
        Simplifier::count_var_uses(&result, "f"),
        0,
        "hot projection helper should inline, got: {:?}",
        result
    );
    assert!(
        matches!(result, PseudoExpr::Tuple(ref items) if items.len() == 7),
        "expected tuple after helper inlining, got: {:?}",
        result
    );
}

#[test]
fn test_inline_single_use_keeps_lambda_shadow_with_different_var_ids() {
    let outer_id = VarId::new(200);
    let inner_id = VarId::new(201);

    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(42)),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("x", outer_id),
                PseudoExpr::Lambda {
                    params: vec![Binder::new("x", inner_id)],
                    body: PBox::new(PseudoExpr::var_with_id("x", inner_id)),
                },
            ]
            .into(),
        )),
    };

    let result = inline_single_use(expr);

    let PseudoExpr::Tuple(items) = result else {
        panic!("expected tuple after inlining");
    };
    assert!(matches!(items.first(), Some(PseudoExpr::Int(_))));
    let Some(PseudoExpr::Lambda { body, .. }) = items.get(1) else {
        panic!("expected lambda to remain in second tuple slot");
    };
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Var { name, id, .. }
                if name == "x" && id.get() == Some(inner_id)
        ),
        "expected lambda body to keep inner binder identity, got: {body:?}"
    );
}

#[test]
fn test_inline_single_use_avoids_alias_capture_under_lambda_shadow() {
    let outer_x_id = VarId::new(203);
    let y_id = VarId::new(204);
    let inner_x_id = VarId::new(205);

    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_x_id),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::int(0)].into(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(y_id),
            value: PBox::new(PseudoExpr::var_with_id("x", outer_x_id)),
            body: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("x", inner_x_id)],
                body: PBox::new(PseudoExpr::var_with_id("y", y_id)),
            }),
        }),
    };

    let result = inline_single_use(expr);

    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&result),
        "inline_single_use should avoid stale same-name ref capture, got: {result:?}"
    );

    let PseudoExpr::Let {
        id: Some(result_outer_x_id),
        body,
        ..
    } = result
    else {
        panic!("expected outer x let to remain");
    };
    assert_eq!(result_outer_x_id, outer_x_id);

    let PseudoExpr::Let {
        id: Some(result_y_id),
        value,
        body,
        ..
    } = body.as_ref()
    else {
        panic!("expected y let to remain when alias capture would occur");
    };
    assert_eq!(*result_y_id, y_id);
    assert!(
        matches!(
            value.as_ref(),
            PseudoExpr::Var { name, id, .. }
                if name == "x" && id.get() == Some(outer_x_id)
        ),
        "expected preserved y binding to keep authoritative outer x ref, got: {value:?}"
    );

    let PseudoExpr::Lambda { params, body } = body.as_ref() else {
        panic!("expected lambda inside preserved y let");
    };
    assert!(
        matches!(params.as_slice(), [param] if param.as_str() == "x" && param.id == inner_x_id),
        "expected lambda param to keep inner x identity, got: {params:?}"
    );
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Var { name, id, .. }
                if name == "y" && id.get() == Some(y_id)
        ),
        "expected lambda body to keep y indirection instead of capturing outer x, got: {body:?}"
    );
}

struct LetNameCollector {
    names: Vec<String>,
}

impl ExprVisitor for LetNameCollector {
    fn visit_let(
        &mut self,
        name: &str,
        _id: &Option<VarId>,
        _value: &PseudoExpr,
        _body: &PseudoExpr,
    ) {
        self.names.push(name.to_string());
    }
}

fn assert_unique_let_names(expr: &PseudoExpr) {
    let mut collector = LetNameCollector { names: Vec::new() };
    collector.walk(expr);
    let mut seen = std::collections::HashSet::new();
    for name in collector.names {
        assert!(
            seen.insert(name.clone()),
            "duplicate let name after inline: {name}"
        );
    }
}

#[test]
fn test_inline_fp_alias_chain_preserves_unique_let_names() {
    let keep_id = VarId::new(206);
    let alias_id = VarId::new(207);
    let carried_id = VarId::new(208);

    let expr = PseudoExpr::Let {
        name: "keep".to_string(),
        id: Some(keep_id),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("make")),
            args: vec![PseudoExpr::int(1)].into(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "alias".to_string(),
            id: Some(alias_id),
            value: PBox::new(PseudoExpr::int(7)),
            body: PBox::new(PseudoExpr::Let {
                name: "carried".to_string(),
                id: Some(carried_id),
                value: PBox::new(PseudoExpr::var_with_id("alias", alias_id)),
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("keep", keep_id),
                        PseudoExpr::var_with_id("carried", carried_id),
                    ]
                    .into(),
                )),
            }),
        }),
    };

    let result = inline_single_use(expr);

    assert_unique_let_names(&result);
    assert_eq!(Simplifier::count_var_uses(&result, "alias"), 0);
    assert_eq!(Simplifier::count_var_uses(&result, "carried"), 0);

    assert!(
        matches!(
            result,
            PseudoExpr::Let { name, id, body, .. }
                if name == "keep"
                    && id == Some(keep_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Tuple(items)
                            if matches!(items.as_slice(), [
                                PseudoExpr::Var { name, id, .. },
                                PseudoExpr::Int(_),
                            ] if name == "keep" && *id == Some(keep_id))
                    )
        ),
        "expected only the complex keep binding to remain after alias-chain inline"
    );
}

#[test]
fn does_not_inline_non_simple_apply_value() {
    let y_id = VarId::fresh_binding();
    let f_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(y_id),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("f", f_id)),
            args: vec![PseudoExpr::int(0)].into(),
        }),
        body: PBox::new(PseudoExpr::var_with_id("y", y_id)),
    };
    let result = inline_single_use(expr);
    assert!(
        matches!(result, PseudoExpr::Let { .. }),
        "non-simple Apply value should stay as a let, got: {result:?}"
    );
}

#[test]
fn identity_on_expr_without_lets() {
    let expr = PseudoExpr::int(7);
    assert_eq!(inline_single_use(expr.clone()), expr);
}
