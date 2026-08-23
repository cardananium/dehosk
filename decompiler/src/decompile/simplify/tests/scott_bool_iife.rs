use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_reversed_scott_boolean_pattern() {
    // expr(True, fn(_) { False }) -> when expr is { Constr<0> -> True; Constr<1>(_) -> False }
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("x")),
        args: vec![
            PseudoExpr::Bool(true),
            PseudoExpr::Lambda {
                params: vec!["_".to_string().into()],
                body: PBox::new(PseudoExpr::Bool(false)),
            },
        ]
        .into(),
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 2);
            assert!(matches!(&clauses[0].body, PseudoExpr::Bool(true)));
            assert!(matches!(&clauses[1].body, PseudoExpr::Bool(false)));
            // Check it's Constr pattern, not List
            match &clauses[0].pattern {
                WhenPattern::Constructor { tag, fields, .. } => {
                    assert_eq!(*tag, 0);
                    assert!(fields.is_empty());
                }
                _ => panic!("expected Constructor pattern, got {:?}", clauses[0].pattern),
            }
            match &clauses[1].pattern {
                WhenPattern::Constructor { tag, fields, .. } => {
                    assert_eq!(*tag, 1);
                    assert_eq!(fields.len(), 1);
                    assert_local_simplifier_binder(&fields[0], "_");
                }
                _ => panic!("expected Constructor pattern, got {:?}", clauses[1].pattern),
            }
        }
        _ => panic!("expected When, got {:?}", simplified),
    }
}

#[test]
fn test_under_application_iife() {
    // fn(x, y, z) { x + y + z }(42) -> fn(y, z) { 42 + y + z }
    // under-application creates let, then single-use inlining removes it
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![
                "x".to_string().into(),
                "y".to_string().into(),
                "z".to_string().into(),
            ],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var("x")),
                right: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(PseudoExpr::var("y")),
                    right: PBox::new(PseudoExpr::var("z")),
                }),
            }),
        }),
        args: vec![PseudoExpr::Int(42.into())].into(),
    };
    let simplified = simplify(expr);
    // Should become: fn(y, z) { 42 + (y + z) } (x=42 inlined since single-use, size 1)
    match &simplified {
        PseudoExpr::Lambda { params, body } => {
            assert_eq!(params.len(), 2);
            assert_eq!(params[0], "y");
            assert_eq!(params[1], "z");
            // Body should be BinOp with 42 inlined
            assert!(matches!(
                body.as_ref(),
                PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    ..
                }
            ));
        }
        _ => panic!("expected Lambda, got {:?}", simplified),
    }
}

#[test]
fn test_force_wrapped_immediate_lambda_application() {
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Lambda {
            params: vec!["x".to_string().into()],
            body: PBox::new(PseudoExpr::var("x")),
        }))),
        args: vec![PseudoExpr::Int(42.into())].into(),
    };

    let simplified = simplify(expr);

    assert!(
        matches!(&simplified, PseudoExpr::Int(n) if *n == 42.into()),
        "expected force-wrapped IIFE to beta-reduce, got: {simplified:?}"
    );
}

#[test]
fn test_bool_naming_in_when() {
    // when x is { Constr<0> -> a; Constr<1> -> b }
    // Bool naming gives: when x is { False -> a; True -> b }
    // Bool when-to-if gives: if x { b } else { a }
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
        ],
    };
    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            assert!(
                matches!(condition.as_ref(), PseudoExpr::Var { name, .. } if name == "x"),
                "expected condition Var(x), got {:?}",
                condition
            );
            assert!(
                matches!(then_branch.as_ref(), PseudoExpr::Var { name, .. } if name == "b"),
                "expected then_branch Var(b), got {:?}",
                then_branch
            );
            assert!(
                matches!(else_branch.as_ref(), PseudoExpr::Var { name, .. } if name == "a"),
                "expected else_branch Var(a), got {:?}",
                else_branch
            );
        }
        _ => panic!("expected If, got {:?}", simplified),
    }
}

#[test]
fn test_bool_naming_skips_data_like_subjects_with_fields_access() {
    let fields_when = |fallback: &str| PseudoExpr::When {
        subject: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var("x"),
            "fields".to_string(),
        )),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Wildcard,
            PseudoExpr::var(fallback),
        )],
    };

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                fields_when("a"),
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                fields_when("b"),
            ),
        ],
    };

    let simplified = simplify(expr);
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 2);
            match &clauses[0].pattern {
                WhenPattern::Constructor { tag, shape, .. } => {
                    assert_eq!(*tag, 0);
                    assert!(matches!(shape, ConstructorShape::Unknown { .. }));
                }
                other => panic!("expected Constructor, got {:?}", other),
            }
            match &clauses[1].pattern {
                WhenPattern::Constructor { tag, shape, .. } => {
                    assert_eq!(*tag, 1);
                    assert!(matches!(shape, ConstructorShape::Unknown { .. }));
                }
                other => panic!("expected Constructor, got {:?}", other),
            }
        }
        _ => panic!("expected When, got {:?}", simplified),
    }
}
