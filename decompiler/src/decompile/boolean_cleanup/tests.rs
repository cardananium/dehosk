use super::*;
use crate::pseudo::var_id::VarId;

#[test]
fn normalise_identity_lambdas_preserves_binder_id() {
    let param_id = VarId::new(7001);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x_17", param_id)],
        body: PBox::new(PseudoExpr::var_with_id("x_17", param_id)),
    };

    let normalized = normalise_identity_lambdas(expr);

    match normalized {
        PseudoExpr::Lambda { params, body } => {
            let [param] = params.as_slice() else {
                panic!("expected one lambda parameter, got: {params:?}");
            };
            assert_eq!(param.as_str(), "x");
            assert_eq!(param.id, param_id);
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::Var { name, id, .. } if name == "x" && *id == Some(param_id)
                ),
                "expected normalized identity lambda body to reuse the original binder id, got: {body:?}"
            );
        }
        other => panic!("expected lambda after identity normalization, got: {other:?}"),
    }
}

#[test]
fn normalise_identity_lambdas_uses_fresh_name_when_x_is_bound() {
    let outer_id = VarId::new(7002);
    let param_id = VarId::new(7003);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x_17", param_id)],
            body: PBox::new(PseudoExpr::var_with_id("x_17", param_id)),
        }),
    };

    let normalized = normalise_identity_lambdas(expr);

    match normalized {
        PseudoExpr::Let { body, .. } => match body.as_ref() {
            PseudoExpr::Lambda { params, body } => {
                let [param] = params.as_slice() else {
                    panic!("expected one lambda parameter, got: {params:?}");
                };
                assert_eq!(param.as_str(), "x_1");
                assert_eq!(param.id, param_id);
                assert!(
                    matches!(
                        body.as_ref(),
                        PseudoExpr::Var { name, id, .. } if name == "x_1" && *id == Some(param_id)
                    ),
                    "expected normalized lambda body to use fresh binder name, got: {body:?}"
                );
            }
            other => panic!("expected lambda under let after normalization, got: {other:?}"),
        },
        other => panic!("expected let after identity normalization, got: {other:?}"),
    }
}

#[test]
fn resolve_boolean_selectors_rewrites_matching_alias_id() {
    let alias_id = VarId::new(7010);
    let expr = PseudoExpr::Let {
        name: "choose_fst".to_string(),
        id: Some(alias_id),
        value: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 0),
            vec![],
        )),
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Bool(true)),
            then_branch: PBox::new(PseudoExpr::var_with_id("choose_fst", alias_id)),
            else_branch: PBox::new(PseudoExpr::Bool(false)),
        }),
    };

    let resolved = resolve_boolean_selectors(expr);

    assert!(
        matches!(
            resolved,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::If { then_branch, .. }
                        if matches!(then_branch.as_ref(), PseudoExpr::Bool(true))
                )
        ),
        "expected matching selector alias id to rewrite to Bool(true)"
    );
}

#[test]
fn resolve_boolean_selectors_rewrites_choose_snd_in_bool_operand_only() {
    // `choose_snd` (church-FALSE) in a `||` operand is provably a Bool →
    // `False`; as a Pair element it keeps its selector semantics.
    use crate::pseudo::ast::BinaryOp;
    let snd_id = VarId::new(7030);
    let snd = || PseudoExpr::var_with_id("choose_snd", snd_id);
    // cond || trace @"msg": choose_snd   (soft-assert operand)
    let or_operand = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::var("cond")),
        right: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::string("msg")),
            value: PBox::new(snd()),
        }),
    };
    // Pair(x, choose_snd)   (selector element — must be preserved)
    let pair_use = PseudoExpr::Pair(PBox::new(PseudoExpr::var("x")), PBox::new(snd()));
    let expr = PseudoExpr::Let {
        name: "choose_snd".to_string(),
        id: Some(snd_id),
        value: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(1, 0),
            vec![],
        )),
        body: PBox::new(PseudoExpr::Tuple((vec![or_operand, pair_use]).into())),
    };

    let PseudoExpr::Let { body, .. } = resolve_boolean_selectors(expr) else {
        panic!("let");
    };
    let PseudoExpr::Tuple(items) = body.into_inner() else {
        panic!("tuple")
    };
    // operand: cond || trace @"msg": False
    let PseudoExpr::BinOp { right, .. } = &items[0] else {
        panic!("binop")
    };
    let PseudoExpr::Trace { value, .. } = right.as_ref() else {
        panic!("trace")
    };
    assert!(
        matches!(value.as_ref(), PseudoExpr::Bool(false)),
        "choose_snd in a `||` operand must resolve to False, got {value:?}"
    );
    // Pair element: choose_snd preserved (selector semantics).
    let PseudoExpr::Pair(_, snd_el) = &items[1] else {
        panic!("pair")
    };
    assert!(
        matches!(snd_el.as_ref(), PseudoExpr::Var { name, .. } if name == "choose_snd"),
        "choose_snd as a Pair element must be preserved, got {snd_el:?}"
    );
}

#[test]
fn resolve_bare_bool_constrs_does_not_fold_three_way_ordering() {
    // A 3-way `int.compare`-style comparator keeps its nullary Constrs: the
    // `Constr<2>` sibling proves the tags are `Less`/`Equal`/`Greater`, not
    // a church bool. Folding tags 0/1 to `Bool` would leave the consumer
    // still dispatching on tags 0/1/2.
    use crate::pseudo::ast::BinaryOp;
    let cmp = |op| PseudoExpr::BinOp {
        op,
        left: PBox::new(PseudoExpr::var("a")),
        right: PBox::new(PseudoExpr::var("b")),
    };
    let c = |tag| PseudoExpr::constr(ConstructorShape::unknown_data(tag, 0), vec![]);
    let expr = PseudoExpr::If {
        condition: PBox::new(cmp(BinaryOp::Lt)),
        then_branch: PBox::new(c(0)),
        else_branch: PBox::new(PseudoExpr::If {
            condition: PBox::new(cmp(BinaryOp::Eq)),
            then_branch: PBox::new(c(1)),
            else_branch: PBox::new(c(2)),
        }),
    };

    let out = resolve_bare_bool_constrs(expr.clone());

    assert_eq!(
        out, expr,
        "3-way Ordering comparator (Constr<2> sibling) must NOT fold its \
         Constr<0>/Constr<1> branches into Bool, got: {out:?}"
    );
}

#[test]
fn resolve_bare_bool_constrs_still_folds_two_way_church_bool() {
    // The {0,1}-only restriction must not break legitimate recovery: a
    // 2-way church bool with no out-of-{0,1} sibling still folds to
    // `True`/`False`.
    let c = |tag| PseudoExpr::constr(ConstructorShape::unknown_data(tag, 0), vec![]);
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(c(0)),
        else_branch: PBox::new(c(1)),
    };

    let out = resolve_bare_bool_constrs(expr);

    match out {
        PseudoExpr::If {
            then_branch,
            else_branch,
            ..
        } => {
            assert!(
                matches!(then_branch.as_ref(), PseudoExpr::Bool(true)),
                "tag-0 branch of a 2-way church-bool must fold to Bool(true), got: {then_branch:?}"
            );
            assert!(
                matches!(else_branch.as_ref(), PseudoExpr::Bool(false)),
                "tag-1 branch of a 2-way church-bool must fold to Bool(false), got: {else_branch:?}"
            );
        }
        other => panic!("expected If after fold, got: {other:?}"),
    }
}

#[test]
fn resolve_boolean_selectors_ignores_same_name_different_id() {
    let alias_id = VarId::new(7020);
    let param_id = VarId::new(7021);
    let expr = PseudoExpr::Let {
        name: "choose_fst".to_string(),
        id: Some(alias_id),
        value: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 0),
            vec![],
        )),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("choose_fst", param_id)],
            body: PBox::new(PseudoExpr::var_with_id("choose_fst", param_id)),
        }),
    };

    let resolved = resolve_boolean_selectors(expr);

    assert!(
        matches!(
            resolved,
            PseudoExpr::Let { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::Lambda { params, body }
                        if matches!(params.as_slice(), [param] if param.as_str() == "choose_fst" && param.id == param_id)
                            && matches!(
                                body.as_ref(),
                                PseudoExpr::Var { name, id, .. }
                                    if name == "choose_fst" && *id == Some(param_id)
                            )
                )
        ),
        "same-name selector refs with a different authoritative id must not be rewritten"
    );
}
