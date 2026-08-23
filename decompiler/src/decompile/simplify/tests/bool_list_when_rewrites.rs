use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_bool_when_to_if() {
    // when x is { True -> A; False -> B } -> if x { A } else { B }
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::True, vec![]),
                guard: None,
                body: PseudoExpr::var("a"),
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::False, vec![]),
                guard: None,
                body: PseudoExpr::var("b"),
            },
        ],
    };
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::If { .. }),
        "expected If, got: {:?}",
        simplified
    );
}

#[test]
fn test_bool_when_to_if_preserves_named_subject_binder_id() {
    let subject_id = VarId::new(9_821);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("condition", subject_id)),
        subject_name: Some(Binder::new("condition", subject_id)),
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::True, vec![]),
                guard: None,
                body: PseudoExpr::int(1),
            },
            WhenClause {
                pattern: WhenPattern::constructor_known(KnownConstructor::False, vec![]),
                guard: None,
                body: PseudoExpr::int(0),
            },
        ],
    };

    let simplified = simplify(expr);

    assert!(
        matches!(
            &simplified,
            PseudoExpr::If { condition, .. }
                if matches!(
                    condition.as_ref(),
                    PseudoExpr::Var { name, id }
                        if name == "condition" && *id == Some(subject_id) && id.get().is_some()
                )
        ),
        "expected named boolean subject id to survive when-to-if rewrite, got: {simplified:?}"
    );
}

#[test]
fn test_list_bool_when_to_list_is_empty() {
    // when xs is { [] -> True; _ -> False } -> List.is_empty(xs)
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("xs")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::Bool(true),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
        ],
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            simplified,
            PseudoExpr::Apply { ref function, .. }
                if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "List.is_empty")
        ),
        "expected List.is_empty apply, got: {:?}",
        simplified
    );
}

#[test]
fn test_delay_list_bool_when_to_not_list_is_empty() {
    // delay(when xs is { [] -> False; _ -> True }) -> !List.is_empty(xs)
    let expr = PseudoExpr::Delay(PBox::new(PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("xs")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::Bool(false),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(true)),
        ],
    }));

    let simplified = simplify(expr);
    assert!(
        matches!(
            simplified,
            PseudoExpr::Delay(ref delayed)
                if matches!(
                    delayed.as_ref(),
                    PseudoExpr::UnOp {
                        op: UnaryOp::Not,
                        operand
                    } if matches!(
                        operand.as_ref(),
                        PseudoExpr::Apply { function, .. }
                            if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "List.is_empty")
                    )
                )
        ),
        "expected delay(!List.is_empty(xs)), got: {:?}",
        simplified
    );
}
