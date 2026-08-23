use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_distribution_with_lambda_args() {
    // if cond { fn(_, y) { y } } else { Constr<0>(w2) }(fn(x) { x + 1 }, fn(y) { y })
    // After distribution into if branches:
    //   Then: fn(_, y) { y }(fn(x) { x + 1 }, fn(y) { y }) -> IIFE -> fn(y) { y }
    //   else: Constr<0>(w2)(fn(x) { x + 1 }, fn(y) { y }) -> Scott reversal -> fn(x) { x + 1 }(w2) -> let x = w2 in x + 1 -> w2 + 1
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond")),
            then_branch: PBox::new(PseudoExpr::Lambda {
                params: vec!["_".to_string().into(), "y".to_string().into()],
                body: PBox::new(PseudoExpr::var("y")),
            }),
            else_branch: PBox::new(PseudoExpr::constr(
                ConstructorShape::unknown_data(0, 1),
                vec![PseudoExpr::var("w2")],
            )),
        }),
        args: vec![
            PseudoExpr::Lambda {
                params: vec!["x".to_string().into()],
                body: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(PseudoExpr::var("x")),
                    right: PBox::new(PseudoExpr::Int(1.into())),
                }),
            },
            PseudoExpr::Lambda {
                params: vec!["y".to_string().into()],
                body: PBox::new(PseudoExpr::var("y")),
            },
        ]
        .into(),
    };
    let simplified = simplify(expr);
    // Should become: if cond { fn(y) { y } } else { w2 + 1 }
    match &simplified {
        PseudoExpr::If {
            then_branch,
            else_branch,
            ..
        } => {
            // then branch: fn(y) { y } (the selector picked arg[1])
            assert!(
                matches!(then_branch.as_ref(), PseudoExpr::Lambda { params, .. } if params == &["y"]),
                "expected Lambda, got {:?}",
                then_branch
            );
            // else branch: w2 + 1 (Scott reversal + IIFE)
            match else_branch.as_ref() {
                PseudoExpr::BinOp { op, left, .. } => {
                    assert!(matches!(op, BinaryOp::Add));
                    assert!(
                        matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == "w2"),
                        "expected Var(w2), got {:?}",
                        left
                    );
                }
                other => panic!("expected BinOp for else branch, got {:?}", other),
            }
        }
        _ => panic!("expected If, got {:?}", simplified),
    }
}

fn assert_apply_single_lambda_arg_uses_own_param(expr: &PseudoExpr) -> VarId {
    let PseudoExpr::Apply { args, .. } = expr else {
        panic!("expected Apply, got {expr:?}");
    };
    let [PseudoExpr::Lambda { params, body }] = args.as_slice() else {
        panic!("expected one lambda arg, got {args:?}");
    };
    let [param] = params.as_slice() else {
        panic!("expected one lambda param, got {params:?}");
    };

    assert!(
        expr_contains_var_with_id(body, param.as_str(), param.id),
        "expected lambda body ref to use branch-local param id, got: {body:?}"
    );
    param.id
}

pub(super) fn assert_lambda_expr_uses_own_param(expr: &PseudoExpr) -> VarId {
    let PseudoExpr::Lambda { params, body } = expr else {
        panic!("expected Lambda, got {expr:?}");
    };
    let [param] = params.as_slice() else {
        panic!("expected one lambda param, got {params:?}");
    };

    assert!(
        expr_contains_var_with_id(body, param.as_str(), param.id),
        "expected lambda body ref to use branch-local param id, got: {body:?}"
    );
    param.id
}

fn assert_apply_single_delayed_lambda_arg_uses_own_param(expr: &PseudoExpr) -> VarId {
    let PseudoExpr::Apply { args, .. } = expr else {
        panic!("expected Apply, got {expr:?}");
    };
    let [PseudoExpr::Delay(inner)] = args.as_slice() else {
        panic!("expected one delayed lambda arg, got {args:?}");
    };
    let PseudoExpr::Lambda { params, body } = inner.as_ref() else {
        panic!("expected delayed lambda arg, got {inner:?}");
    };
    let [param] = params.as_slice() else {
        panic!("expected one delayed lambda param, got {params:?}");
    };

    assert!(
        expr_contains_var_with_id(body, param.as_str(), param.id),
        "expected delayed lambda body ref to use branch-local param id, got: {body:?}"
    );
    param.id
}

fn expr_contains_var_with_id(expr: &PseudoExpr, target_name: &str, target_id: VarId) -> bool {
    match expr {
        PseudoExpr::Var { name, id, .. } => name == target_name && id.get() == Some(target_id),
        PseudoExpr::Lambda { body, .. }
        | PseudoExpr::RecFn { body, .. }
        | PseudoExpr::Delay(body)
        | PseudoExpr::Force(body)
        | PseudoExpr::Trace { value: body, .. } => {
            expr_contains_var_with_id(body, target_name, target_id)
        }
        PseudoExpr::Let { value, body, .. } => {
            expr_contains_var_with_id(value, target_name, target_id)
                || expr_contains_var_with_id(body, target_name, target_id)
        }
        PseudoExpr::Apply { function, args } => {
            expr_contains_var_with_id(function, target_name, target_id)
                || args
                    .iter()
                    .any(|arg| expr_contains_var_with_id(arg, target_name, target_id))
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expr_contains_var_with_id(condition, target_name, target_id)
                || expr_contains_var_with_id(then_branch, target_name, target_id)
                || expr_contains_var_with_id(else_branch, target_name, target_id)
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            expr_contains_var_with_id(subject, target_name, target_id)
                || clauses.iter().any(|clause| {
                    clause.guard.as_ref().is_some_and(|guard| {
                        expr_contains_var_with_id(guard, target_name, target_id)
                    }) || expr_contains_var_with_id(&clause.body, target_name, target_id)
                })
        }
        PseudoExpr::BinOp { left, right, .. } => {
            expr_contains_var_with_id(left, target_name, target_id)
                || expr_contains_var_with_id(right, target_name, target_id)
        }
        PseudoExpr::UnOp { operand: expr, .. } | PseudoExpr::FieldAccess { record: expr, .. } => {
            expr_contains_var_with_id(expr, target_name, target_id)
        }
        PseudoExpr::IndexAccess { collection, .. } => {
            expr_contains_var_with_id(collection, target_name, target_id)
        }
        PseudoExpr::List { elements, tail } => {
            elements
                .iter()
                .any(|element| expr_contains_var_with_id(element, target_name, target_id))
                || tail
                    .as_ref()
                    .is_some_and(|tail| expr_contains_var_with_id(tail, target_name, target_id))
        }
        PseudoExpr::Tuple(elements) => elements
            .iter()
            .any(|element| expr_contains_var_with_id(element, target_name, target_id)),
        PseudoExpr::Pair(left, right) => {
            expr_contains_var_with_id(left, target_name, target_id)
                || expr_contains_var_with_id(right, target_name, target_id)
        }
        PseudoExpr::BuiltinCall { args, .. } | PseudoExpr::Constr { fields: args, .. } => args
            .iter()
            .any(|arg| expr_contains_var_with_id(arg, target_name, target_id)),
        _ => false,
    }
}

#[test]
fn test_if_apply_distribution_freshens_lambda_arg_binder_ids() {
    let param_id = VarId::new(9_900);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond")),
            then_branch: PBox::new(PseudoExpr::var("then_fn")),
            else_branch: PBox::new(PseudoExpr::var("else_fn")),
        }),
        args: vec![PseudoExpr::Lambda {
            params: vec![Binder::new("x", param_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("x", param_id)),
                right: PBox::new(PseudoExpr::Int(1.into())),
            }),
        }]
        .into(),
    };

    let simplified = simplify(expr);
    let PseudoExpr::If {
        then_branch,
        else_branch,
        ..
    } = simplified
    else {
        panic!("expected If, got {simplified:?}");
    };

    let then_id = assert_apply_single_lambda_arg_uses_own_param(&then_branch);
    let else_id = assert_apply_single_lambda_arg_uses_own_param(&else_branch);
    assert_ne!(
        then_id, else_id,
        "distributed lambda args must not duplicate binder ids"
    );
}

#[test]
fn test_if_apply_distribution_freshens_delayed_lambda_arg_binder_ids() {
    let param_id = VarId::new(9_901);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond")),
            then_branch: PBox::new(PseudoExpr::var("then_fn")),
            else_branch: PBox::new(PseudoExpr::var("else_fn")),
        }),
        args: vec![PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", param_id)],
            body: PBox::new(PseudoExpr::var_with_id("x", param_id)),
        }))]
        .into(),
    };

    let simplified = simplify(expr);
    let PseudoExpr::If {
        then_branch,
        else_branch,
        ..
    } = simplified
    else {
        panic!("expected If, got {simplified:?}");
    };

    let then_id = assert_apply_single_delayed_lambda_arg_uses_own_param(&then_branch);
    let else_id = assert_apply_single_delayed_lambda_arg_uses_own_param(&else_branch);
    assert_ne!(
        then_id, else_id,
        "distributed delayed lambda args must not duplicate binder ids"
    );
}

#[test]
fn test_when_apply_distribution_freshens_lambda_arg_binder_ids() {
    let param_id = VarId::new(9_902);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("choice")),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::var("f0"),
                ),
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    PseudoExpr::var("f1"),
                ),
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
                    PseudoExpr::var("f2"),
                ),
            ],
        }),
        args: vec![PseudoExpr::Lambda {
            params: vec![Binder::new("x", param_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("x", param_id)),
                right: PBox::new(PseudoExpr::Int(1.into())),
            }),
        }]
        .into(),
    };

    let simplified = simplify(expr);
    let PseudoExpr::When { clauses, .. } = simplified else {
        panic!("expected When, got {simplified:?}");
    };
    assert_eq!(clauses.len(), 3);

    let ids: Vec<_> = clauses
        .iter()
        .map(|clause| assert_apply_single_lambda_arg_uses_own_param(&clause.body))
        .collect();
    assert_eq!(
        ids.iter()
            .copied()
            .collect::<std::collections::HashSet<_>>()
            .len(),
        ids.len(),
        "distributed when lambda args must not duplicate binder ids: {ids:?}"
    );
}

#[test]
fn test_when_apply_distribution_moves_original_args_into_last_clause() {
    let param_id = VarId::new(9_907);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("choice")),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::var("f0"),
                ),
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    PseudoExpr::var("f1"),
                ),
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
                    PseudoExpr::var("f2"),
                ),
            ],
        }),
        args: vec![PseudoExpr::Lambda {
            params: vec![Binder::new("x", param_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("x", param_id)),
                right: PBox::new(PseudoExpr::Int(1.into())),
            }),
        }]
        .into(),
    };

    let simplified = simplify(expr);
    let PseudoExpr::When { clauses, .. } = simplified else {
        panic!("expected When, got {simplified:?}");
    };
    assert_eq!(clauses.len(), 3);

    let ids: Vec<_> = clauses
        .iter()
        .map(|clause| assert_apply_single_lambda_arg_uses_own_param(&clause.body))
        .collect();
    assert_eq!(
        ids.last(),
        Some(&param_id),
        "the last distributed when clause should keep the original arg ids"
    );
    assert!(
        ids[..ids.len() - 1].iter().all(|id| *id != param_id),
        "non-final distributed when clauses should use fresh arg ids: {ids:?}"
    );
    assert_eq!(
        ids.iter()
            .copied()
            .collect::<std::collections::HashSet<_>>()
            .len(),
        ids.len(),
        "distributed when lambda args must not duplicate binder ids: {ids:?}"
    );
}
