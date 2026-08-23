use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_when_single_known_constr_clause_collapses() {
    let expr = PseudoExpr::Delay(PBox::new(PseudoExpr::When {
        subject: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 1),
            vec![PseudoExpr::int(7)],
        )),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(0, 1), vec!["_".into()]),
            PseudoExpr::int(42),
        )],
    }));

    let simplified = simplify(expr);
    assert_eq!(simplified, PseudoExpr::int(42));
}

#[test]
fn test_when_known_constr_multi_clause_picks_matching_constructor() {
    let expr = PseudoExpr::Delay(PBox::new(PseudoExpr::When {
        subject: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(1, 1),
            vec![PseudoExpr::int(9)],
        )),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 1), vec!["_".into()]),
                PseudoExpr::int(10),
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 1), vec!["_".into()]),
                PseudoExpr::int(20),
            ),
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::int(30)),
        ],
    }));

    let simplified = simplify(expr);
    assert_eq!(simplified, PseudoExpr::int(20));
}

#[test]
fn test_when_known_constr_with_fewer_pattern_fields_collapses_only_non_safe() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 2),
            vec![PseudoExpr::int(1), PseudoExpr::int(2)],
        )),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
            PseudoExpr::int(99),
        )],
    };

    let simplified = simplify(expr.clone());
    assert_eq!(simplified, PseudoExpr::int(99));

    let safe_simplified = simplify_with_options(expr, true);
    assert!(matches!(safe_simplified, PseudoExpr::When { .. }));
}

#[test]
fn test_when_known_constr_ignores_guard_on_non_matching_constructor_clause() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(1, 1),
            vec![PseudoExpr::int(9)],
        )),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec!["_".into()],
                ),
                guard: Some(PseudoExpr::Bool(true)),
                body: PseudoExpr::int(10),
            },
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 1), vec!["_".into()]),
                PseudoExpr::int(20),
            ),
        ],
    };

    let simplified = simplify(expr);
    assert_eq!(simplified, PseudoExpr::int(20));
}

#[test]
fn test_when_known_constr_does_not_collapse_across_matching_guarded_clause() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(1, 1),
            vec![PseudoExpr::int(9)],
        )),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(1, 1),
                    vec!["_".into()],
                ),
                guard: Some(PseudoExpr::Bool(true)),
                body: PseudoExpr::int(10),
            },
            WhenClause::new(WhenPattern::Wildcard, PseudoExpr::int(20)),
        ],
    };

    let simplified = simplify(expr);
    assert!(matches!(simplified, PseudoExpr::When { .. }));
}
