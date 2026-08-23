use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_option_naming_in_when() {
    // when x is { Constr<0>(v) -> v; Constr<1> -> default }
    // > when x is { Some(v) -> v; None -> default }
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 1), vec!["v".into()]),
                PseudoExpr::var("v"),
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::var("default"),
            ),
        ],
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 2);
            match &clauses[0].pattern {
                WhenPattern::Constructor { shape, tag, .. } => {
                    assert_eq!(*tag, 0);
                    assert!(
                        matches!(shape, ConstructorShape::Known(KnownConstructor::Some)),
                        "expected shape Known(Some), got {:?}",
                        shape,
                    );
                }
                _ => panic!("expected Constructor, got {:?}", clauses[0].pattern),
            }
            match &clauses[1].pattern {
                WhenPattern::Constructor { shape, tag, .. } => {
                    assert_eq!(*tag, 1);
                    assert!(
                        matches!(shape, ConstructorShape::Known(KnownConstructor::None)),
                        "expected shape Known(None), got {:?}",
                        shape,
                    );
                }
                _ => panic!("expected Constructor, got {:?}", clauses[1].pattern),
            }
        }
        _ => panic!("expected When, got {:?}", simplified),
    }
}

#[test]
fn test_no_naming_for_3_constructor_type() {
    // when x is { Constr<0> -> a; Constr<1> -> b; Constr<2> -> c }
    // Should NOT be renamed (not a known 2-constructor type)
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::var("a"),
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::var("b"),
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
                PseudoExpr::var("c"),
            ),
        ],
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            // All should remain unnamed
            for c in clauses {
                if let WhenPattern::Constructor { shape, .. } = &c.pattern {
                    assert!(
                        matches!(shape, ConstructorShape::Unknown { .. }),
                        "3-constructor type should not be named"
                    );
                }
            }
        }
        _ => panic!("expected When, got {:?}", simplified),
    }
}
