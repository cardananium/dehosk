use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_nested_when_same_subject_constructor_resolution() {
    // when x is {
    //   Constr<0>(a, b) ->
    //     when x is {
    //       Constr<0>(c, d) -> use(c, d)
    //       Constr<1> -> dead
    //     }
    // }
    // Should resolve to:
    // When x is { Constr<0>(a, b) -> use(a, b) }
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(
                ConstructorShape::unknown_data(0, 2),
                vec!["a".into(), "b".into()],
            ),
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("x")),
                subject_name: None,
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::constructor(
                            ConstructorShape::unknown_data(0, 2),
                            vec!["c".into(), "d".into()],
                        ),
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("use_fn")),
                            args: vec![PseudoExpr::var("c"), PseudoExpr::var("d")].into(),
                        },
                    ),
                    WhenClause::new(
                        WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                        PseudoExpr::int(999),
                    ),
                ],
            },
        )],
    };

    let simplified = simplify(expr);
    // Should be: when x is { Constr<0>(a, b) -> use_fn(a, b) }
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 1);
            match &clauses[0].pattern {
                WhenPattern::Constructor { tag, fields, .. } => {
                    assert_eq!(*tag, 0);
                    assert_eq!(fields, &vec!["a".to_string(), "b".to_string()]);
                }
                _ => panic!(
                    "expected Constructor pattern, got: {:?}",
                    clauses[0].pattern
                ),
            }
            // Body should reference a, b (renamed from c, d)
            match &clauses[0].body {
                PseudoExpr::Apply { args, .. } => {
                    assert!(
                        matches!(&args[0], PseudoExpr::Var { name, .. } if name == "a"),
                        "expected Var(a), got: {:?}",
                        args[0]
                    );
                    assert!(
                        matches!(&args[1], PseudoExpr::Var { name, .. } if name == "b"),
                        "expected Var(b), got: {:?}",
                        args[1]
                    );
                }
                _ => panic!("expected Apply, got: {:?}", clauses[0].body),
            }
        }
        _ => panic!("expected When, got: {:?}", simplified),
    }
}

#[test]
fn test_nested_when_same_subject_wildcard_fallback() {
    // when x is {
    //   Constr<0> ->
    //     when x is {
    //       Constr<1> -> A
    //       _ -> B
    //     }
    // }
    // Constr<0> doesn't match Constr<1>, so falls through to wildcard → B
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("x")),
                subject_name: None,
                clauses: vec![
                    WhenClause::new(
                        WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                        PseudoExpr::int(1),
                    ),
                    WhenClause::new(WhenPattern::Wildcard, PseudoExpr::int(2)),
                ],
            },
        )],
    };

    let simplified = simplify(expr);
    // Should be: when x is { Constr<0> -> 2 }
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 1);
            assert!(
                matches!(&clauses[0].pattern, WhenPattern::Constructor { tag: 0, .. }),
                "expected Constr<0>, got: {:?}",
                clauses[0].pattern
            );
            assert!(
                matches!(&clauses[0].body, PseudoExpr::Int(n) if *n == 2.into()),
                "expected Int(2), got: {:?}",
                clauses[0].body
            );
        }
        _ => panic!("expected When, got: {:?}", simplified),
    }
}
