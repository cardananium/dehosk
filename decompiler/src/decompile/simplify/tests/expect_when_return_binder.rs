use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_expect_when_return_binder_rewrite_retargets_outer_body_refs() {
    let let_id = VarId::from_raw(9850);
    let field_id = VarId::from_raw(9851);
    let subject_id = VarId::from_raw(9852);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(let_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(
                        ConstructorShape::unknown_data(0, 1),
                        vec![Binder::new("field", field_id)],
                    ),
                    PseudoExpr::var_with_id("field", field_id),
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("x", let_id),
                PseudoExpr::var_with_id("x", let_id),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::When { clauses, .. }
                if matches!(
                    &clauses[0].pattern,
                    WhenPattern::Constructor { fields, .. }
                        if matches!(fields.as_slice(), [binder] if binder.as_str() == "x" && binder.id == field_id)
                )
                && matches!(
                    &clauses[0].body,
                    PseudoExpr::Tuple(items)
                        if items.iter().all(|item| matches!(item, PseudoExpr::Var { name, id, .. } if name == "x" && id.get() == Some(field_id)))
                )
        ),
        "expect-pattern rewrite should retarget moved body refs to the renamed pattern binder id, got: {simplified:?}"
    );

    let report = audit_id_orphans(&simplified, &[("subject".to_string(), subject_id)]);
    assert_eq!(
        report.stranded, 0,
        "expect-pattern rewrite must not strand the removed let binder id: {:?}\n{:?}",
        report.stranded_by_name, simplified
    );
}

#[test]
fn test_expect_when_return_binder_rewrite_retargets_guard_refs() {
    let let_id = VarId::from_raw(9860);
    let field_id = VarId::from_raw(9861);
    let subject_id = VarId::from_raw(9862);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(let_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
            subject_name: None,
            clauses: vec![
                WhenClause::with_guard(
                    WhenPattern::constructor(
                        ConstructorShape::unknown_data(0, 1),
                        vec![Binder::new("field", field_id)],
                    ),
                    PseudoExpr::BinOp {
                        op: BinaryOp::Eq,
                        left: PBox::new(PseudoExpr::var_with_id("field", field_id)),
                        right: PBox::new(PseudoExpr::Int(1.into())),
                    },
                    PseudoExpr::var_with_id("field", field_id),
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("x", let_id),
                PseudoExpr::var_with_id("x", let_id),
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::When { clauses, .. }
                if matches!(
                    &clauses[0].pattern,
                    WhenPattern::Constructor { fields, .. }
                        if matches!(fields.as_slice(), [binder] if binder.as_str() == "x" && binder.id == field_id)
                )
                && matches!(
                    clauses[0].guard.as_ref(),
                    Some(PseudoExpr::BinOp { left, .. })
                        if matches!(left.as_ref(), PseudoExpr::Var { name, id, .. } if name == "x" && id.get() == Some(field_id))
                )
                && matches!(
                    &clauses[0].body,
                    PseudoExpr::Tuple(items)
                        if items.iter().all(|item| matches!(item, PseudoExpr::Var { name, id, .. } if name == "x" && id.get() == Some(field_id)))
                )
        ),
        "expect-pattern rewrite should retarget guard/body refs after renaming the pattern binder, got: {simplified:?}"
    );
}

#[test]
fn test_expect_when_return_binder_rewrite_skips_inner_new_name_binding() {
    let let_id = VarId::from_raw(9870);
    let field_id = VarId::from_raw(9871);
    let subject_id = VarId::from_raw(9872);
    let inner_x_id = VarId::from_raw(9873);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(let_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(
                        ConstructorShape::unknown_data(0, 1),
                        vec![Binder::new("field", field_id)],
                    ),
                    PseudoExpr::var_with_id("field", field_id),
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("x", let_id),
                PseudoExpr::var_with_id("x", let_id),
                PseudoExpr::Lambda {
                    params: vec![Binder::new("x", inner_x_id)],
                    body: PBox::new(PseudoExpr::var_with_id("x", let_id)),
                },
            ]
            .into(),
        )),
    };

    let simplified = simplify(expr);

    assert!(
        matches!(&simplified, PseudoExpr::Let { name, id, .. } if name == "x" && id.get() == Some(let_id)),
        "expect-pattern rewrite should keep the outer let when moving its body under pattern x would capture, got: {simplified:?}"
    );

    let report = audit_id_orphans(&simplified, &[("subject".to_string(), subject_id)]);
    assert_eq!(
        report.stranded, 0,
        "capture guard should preserve all ids: {:?}\n{:?}",
        report.stranded_by_name, simplified
    );
}

#[test]
fn walker_adapter_apply_routes_via_post_apply_hook() {
    // `Apply` must return `FoldAction::Walk` from `pre_expr` so
    // the Walker folds `function` + args first, then fires
    // `post_apply`, which alone iterates over the
    // `simplify_apply_match` results.
    use crate::pseudo::walker::{FoldAction, Walker};

    let mut simplifier = Simplifier::with_safe_mode(false);
    let apply = PseudoExpr::apply(
        PseudoExpr::var("f"),
        vec![PseudoExpr::int(1), PseudoExpr::int(2)],
    );
    match simplifier.pre_expr(&apply) {
        FoldAction::Walk => {}
        FoldAction::Replace(_) => {
            panic!("Apply must return FoldAction::Walk (post_apply runs the CPS loop)")
        }
    }
}

#[test]
fn walker_adapter_matches_simplify_on_apply_variants() {
    // Behavioural parity: `Simplifier::fold` must match `simplify()`
    // across a representative set of Apply shapes — identity, beta,
    // builtin, nested-apply, interaction-with-let. The `ContinueLoop`
    // and `Resimplify` branches of `simplify_apply_match` are
    // exercised transitively by beta and builtin rewrites.
    use crate::pseudo::walker::Walker;

    let inputs = vec![
        // No-arg application is the canonical form `f` (Done path).
        PseudoExpr::apply(PseudoExpr::var("f"), vec![]),
        // Beta reduction: `(\x -> x)(1)` -> `1` (ContinueLoop + Done).
        PseudoExpr::apply(
            PseudoExpr::Lambda {
                params: vec!["x".into()],
                body: PBox::new(PseudoExpr::var("x")),
            },
            vec![PseudoExpr::int(1)],
        ),
        // Builtin rewrite: `if_then_else(True, 1, 2)` -> `1`.
        PseudoExpr::apply(
            PseudoExpr::BuiltinCall {
                name: BuiltinId::IfThenElse,
                args: vec![].into(),
            },
            vec![
                PseudoExpr::Bool(true),
                PseudoExpr::int(1),
                PseudoExpr::int(2),
            ],
        ),
        // Nested Apply: `((f)(1))(2)` gets flattened to `f(1, 2)`.
        PseudoExpr::apply(
            PseudoExpr::apply(PseudoExpr::var("f"), vec![PseudoExpr::int(1)]),
            vec![PseudoExpr::int(2)],
        ),
        // Apply inside Let body; exercises Let + Apply interaction
        // through the Walker's native hooks.
        PseudoExpr::let_bind(
            "g",
            PseudoExpr::var("h"),
            PseudoExpr::apply(PseudoExpr::var("g"), vec![PseudoExpr::int(42)]),
        ),
    ];

    for expr in inputs {
        let via_simplify = simplify(expr.clone());
        let via_walker = Simplifier::with_safe_mode(false).fold(expr.clone());
        assert_eq!(
            via_walker, via_simplify,
            "Walker post_apply must match simplify() for {:?}",
            expr
        );
    }
}
