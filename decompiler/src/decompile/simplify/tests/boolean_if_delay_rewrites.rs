use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_if_to_and_strips_delay_from_then() {
    // if cond { delay(expr) } else { False } -> cond && expr (no delay)
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("b")))),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::BinOp {
            op: BinaryOp::And,
            left,
            right,
        } => {
            assert!(
                matches!(*left, PseudoExpr::Var { ref name, .. } if name == "cond"),
                "expected left=cond, got: {:?}",
                left
            );
            assert!(
                matches!(*right, PseudoExpr::Var { ref name, .. } if name == "b"),
                "expected right=b (no delay), got: {:?}",
                right
            );
        }
        _ => panic!("expected And binop, got: {:?}", simplified),
    }
}

#[test]
fn test_if_to_or_strips_delay_from_else() {
    // if cond { True } else { delay(expr) } -> cond || expr (no delay)
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("b")))),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::BinOp {
            op: BinaryOp::Or,
            left,
            right,
        } => {
            assert!(
                matches!(*left, PseudoExpr::Var { ref name, .. } if name == "cond"),
                "expected left=cond, got: {:?}",
                left
            );
            assert!(
                matches!(*right, PseudoExpr::Var { ref name, .. } if name == "b"),
                "expected right=b (no delay), got: {:?}",
                right
            );
        }
        _ => panic!("expected Or binop, got: {:?}", simplified),
    }
}

#[test]
fn test_if_typed_list_condition_does_not_collapse_to_and() {
    // Without inline tipo an unknown-typed Var may collapse in boolean
    // position, so a List literal checks that a known non-bool stays an If.
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::list(vec![PseudoExpr::var("x")])),
        then_branch: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("b")))),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::If { .. }),
        "expected non-bool list condition to stay as If, got: {simplified:?}"
    );
}

#[test]
fn test_if_unknown_typed_var_condition_with_delayed_else_simplifies_to_or() {
    // Without inline tipo on Var, the simplifier force-eliminates the Delay
    // and recognizes both branches as boolean-like, converting to Or.
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("payload")),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("b")))),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            simplified,
            PseudoExpr::BinOp {
                op: BinaryOp::Or,
                ..
            }
        ),
        "expected Or after delay elimination, got: {simplified:?}"
    );
}

#[test]
fn test_if_unknown_typed_var_condition_with_bool_branches_stays_as_var() {
    // Without tipo, `if payload { True } else { False }` simplifies to just `payload`.
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("payload")),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Var { ref name, .. } if name == "payload"),
        "expected identity-if to simplify to condition var, got: {simplified:?}"
    );
}

#[test]
fn test_if_unknown_typed_var_stays_as_if() {
    // Without tipo, an unknown-typed var is a normal If.
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("purpose")),
        then_branch: PBox::new(PseudoExpr::var("spend_ok")),
        else_branch: PBox::new(PseudoExpr::var("mint_ok")),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::If { .. }),
        "expected unknown-typed var condition to stay as If, got: {simplified:?}"
    );
}

#[test]
fn test_if_var_condition_with_branch_refs_stays_if() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("payload")),
        then_branch: PBox::new(PseudoExpr::var("payload")),
        else_branch: PBox::new(PseudoExpr::var("fallback")),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::If { .. }),
        "expected branch-local payload use to keep If, got: {simplified:?}"
    );
}

#[test]
fn test_if_apply_condition_does_not_collapse_to_and() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("scan")),
            args: vec![PseudoExpr::var("xs")].into(),
        }),
        then_branch: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("payload")))),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::If { .. }),
        "expected apply condition to stay as If, got: {simplified:?}"
    );
}

#[test]
fn test_int_when_chain_recovers_boolean_collapsed_tail_clause() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var("z")),
            right: PBox::new(PseudoExpr::int(0)),
        }),
        then_branch: PBox::new(PseudoExpr::int(10)),
        else_branch: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(PseudoExpr::var("z")),
                right: PBox::new(PseudoExpr::int(1)),
            }),
            then_branch: PBox::new(PseudoExpr::int(20)),
            else_branch: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::var("z")),
                    right: PBox::new(PseudoExpr::int(2)),
                }),
                then_branch: PBox::new(PseudoExpr::var("gt_zero")),
                else_branch: PBox::new(PseudoExpr::Bool(false)),
            }),
        }),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(
                matches!(*subject, PseudoExpr::Var { ref name, .. } if name == "z"),
                "expected subject=z, got: {subject:?}"
            );
            assert_eq!(clauses.len(), 4, "expected 3 literal clauses plus wildcard");

            assert!(matches!(
                &clauses[0].pattern,
                WhenPattern::Literal(PseudoExpr::Int(n)) if *n == 0.into()
            ));
            assert!(matches!(
                &clauses[1].pattern,
                WhenPattern::Literal(PseudoExpr::Int(n)) if *n == 1.into()
            ));
            assert!(matches!(
                &clauses[2].pattern,
                WhenPattern::Literal(PseudoExpr::Int(n)) if *n == 2.into()
            ));
            assert!(matches!(&clauses[3].pattern, WhenPattern::Wildcard));

            assert!(matches!(&clauses[0].body, PseudoExpr::Int(n) if *n == 10.into()));
            assert!(matches!(&clauses[1].body, PseudoExpr::Int(n) if *n == 20.into()));
            assert!(
                matches!(&clauses[2].body, PseudoExpr::Var { name, .. } if name == "gt_zero"),
                "expected final literal clause body to stay as the original branch body, got: {:?}",
                clauses[2].body
            );
            assert!(matches!(&clauses[3].body, PseudoExpr::Bool(false)));
        }
        other => panic!("expected When, got: {other:?}"),
    }
}

#[test]
fn test_if_to_and_strips_delay_from_complex_then() {
    // if cond { delay(let x = 1 in x) } else { False } -> cond && (let x = 1 in x)
    let let_expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::var("x")),
    };
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::Delay(PBox::new(let_expr))),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            assert_eq!(*condition, PseudoExpr::var("cond"));
            assert!(
                !matches!(*then_branch, PseudoExpr::Delay(_)),
                "expected no delay wrapper on then branch, got: {:?}",
                then_branch
            );
            assert_eq!(*else_branch, PseudoExpr::Bool(false));
        }
        _ => panic!("expected If expression, got: {:?}", simplified),
    }
}

#[test]
fn test_and_strips_delay_from_lhs() {
    // delay(a) && b -> a && b
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("a")))),
        right: PBox::new(PseudoExpr::var("b")),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::BinOp {
            op: BinaryOp::And,
            left,
            right,
        } => {
            assert!(
                matches!(*left, PseudoExpr::Var { ref name, .. } if name == "a"),
                "expected left=a (no delay), got: {:?}",
                left
            );
            assert!(
                matches!(*right, PseudoExpr::Var { ref name, .. } if name == "b"),
                "expected right=b, got: {:?}",
                right
            );
        }
        _ => panic!("expected And binop, got: {:?}", simplified),
    }
}

#[test]
fn test_or_strips_delay_from_both() {
    // delay(a) || delay(b) -> a || b
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Or,
        left: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("a")))),
        right: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("b")))),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::BinOp {
            op: BinaryOp::Or,
            left,
            right,
        } => {
            assert!(
                matches!(*left, PseudoExpr::Var { ref name, .. } if name == "a"),
                "expected left=a (no delay), got: {:?}",
                left
            );
            assert!(
                matches!(*right, PseudoExpr::Var { ref name, .. } if name == "b"),
                "expected right=b (no delay), got: {:?}",
                right
            );
        }
        _ => panic!("expected Or binop, got: {:?}", simplified),
    }
}

#[test]
fn test_delay_not_stripped_from_non_bool_binop() {
    // delay(a) == delay(b) should NOT strip delays (only && and || strip)
    let expr = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("a")))),
        right: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var("b")))),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        } => {
            // Delays should be preserved for non-boolean operators
            assert!(
                matches!(*left, PseudoExpr::Delay(_)),
                "expected left to still be delayed, got: {:?}",
                left
            );
            assert!(
                matches!(*right, PseudoExpr::Delay(_)),
                "expected right to still be delayed, got: {:?}",
                right
            );
        }
        _ => panic!("expected Eq binop, got: {:?}", simplified),
    }
}
