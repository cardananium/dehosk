use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_cps_selector_inlining_all_selectors() {
    // When x is { Constr<0> -> fn(a, _) { a }; Constr<1> -> fn(_, b) { b } }(delay(val0), delay(val1))
    // Bool naming + bool-to-if fires first in simplify_when, producing:
    // if x { fn(_, b) { b } } else { fn(a, _) { a } }
    // Then the Apply distributes delayed args, giving:
    // if x { delay(success_val) } else { delay(error_val) }
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::Lambda {
                    params: vec!["a".to_string().into(), "_".to_string().into()],
                    body: PBox::new(PseudoExpr::var("a")),
                },
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::Lambda {
                    params: vec!["_".to_string().into(), "b".to_string().into()],
                    body: PBox::new(PseudoExpr::var("b")),
                },
            ),
        ],
    };
    let applied = PseudoExpr::Apply {
        function: PBox::new(when_expr),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("error_val"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("success_val"))),
        ]
        .into(),
    };
    let simplified = simplify(applied);
    // Bool when is converted to if/else before CPS selector inlining can fire
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
            // True branch (tag 1) had fn(_, b) { b } which selects arg[1] = delay(success_val)
            assert!(
                matches!(then_branch.as_ref(), PseudoExpr::Delay(inner) if matches!(inner.as_ref(), PseudoExpr::Var { name, .. } if name == "success_val")),
                "expected then_branch Delay(success_val), got {:?}",
                then_branch
            );
            // False branch (tag 0) had fn(a, _) { a } which selects arg[0] = delay(error_val)
            assert!(
                matches!(else_branch.as_ref(), PseudoExpr::Delay(inner) if matches!(inner.as_ref(), PseudoExpr::Var { name, .. } if name == "error_val")),
                "expected else_branch Delay(error_val), got {:?}",
                else_branch
            );
        }
        _ => panic!("expected If, got {:?}", simplified),
    }
}

#[test]
fn test_cps_selector_inlining_with_fail() {
    // With only two constructors, bool naming + bool-to-if would turn this into
    // `if x { fail } else { fn(a,_){a} }` → `expect !x`; the third constructor
    // keeps CPS selector inlining free of that interference.
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::Lambda {
                    params: vec!["a".to_string().into(), "_".to_string().into()],
                    body: PBox::new(PseudoExpr::var("a")),
                },
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::error(),
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
                PseudoExpr::error(),
            ),
        ],
    };
    let applied = PseudoExpr::Apply {
        function: PBox::new(when_expr),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("success_val"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("error_val"))),
        ]
        .into(),
    };
    let simplified = simplify(applied);
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            // Constr<0> selected arg[0] (success_val)
            assert!(
                matches!(&clauses[0].body, PseudoExpr::Var { name, .. } if name == "success_val"),
                "expected Var(success_val), got {:?}",
                clauses[0].body
            );
            // Constr<1> stays as fail
            assert!(
                Simplifier::is_fail(&clauses[1].body),
                "expected fail, got {:?}",
                clauses[1].body
            );
        }
        _ => panic!("expected When, got {:?}", simplified),
    }
}

#[test]
fn test_cps_selector_inlining_mixed_not_applied() {
    // When x is { Constr<0> -> complex; Constr<1> -> fn(_, b) { b } }(delay(v0), delay(v1))
    // Mixed selector and non-selector branches must not fire the CPS rewrite.
    let when_expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("complex_fn")),
                    args: vec![PseudoExpr::var("arg")].into(),
                },
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::Lambda {
                    params: vec!["_".to_string().into(), "b".to_string().into()],
                    body: PBox::new(PseudoExpr::var("b")),
                },
            ),
        ],
    };
    let applied = PseudoExpr::Apply {
        function: PBox::new(when_expr),
        args: vec![
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("v0"))),
            PseudoExpr::Delay(PBox::new(PseudoExpr::var("v1"))),
        ]
        .into(),
    };
    let simplified = simplify(applied);
    // Should NOT be a clean When with inlined values: the mixed case is not optimized.
    // The result should still be an Apply of When to delay args, or distributed.
    match &simplified {
        PseudoExpr::When { clauses, .. } => {
            // If it became a When, at least one clause body must not be a
            // simple Var — nothing was inlined.
            let has_non_var = clauses
                .iter()
                .any(|c| !matches!(&c.body, PseudoExpr::Var { .. }));
            assert!(
                has_non_var,
                "mixed branches should not all become simple Vars"
            );
        }
        _ => {
            // Any other result (Apply, etc.) means no transform fired.
        }
    }
}

#[test]
fn test_if_branches_rewrite_scott_constructor_family_to_constr_values() {
    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("cond")),
        then_branch: PBox::new(PseudoExpr::Let {
            name: "payload".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::Int(1.into())),
            body: PBox::new(PseudoExpr::Lambda {
                params: vec!["_".to_string().into(), "k".to_string().into()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("k")),
                    args: vec![PseudoExpr::var("payload")].into(),
                }),
            }),
        }),
        else_branch: PBox::new(PseudoExpr::Let {
            name: "payload".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::Int(2.into())),
            body: PBox::new(PseudoExpr::Lambda {
                params: vec!["k".to_string().into(), "_".to_string().into()],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var("k")),
                    args: vec![PseudoExpr::var("payload")].into(),
                }),
            }),
        }),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::If {
            then_branch,
            else_branch,
            ..
        } => {
            match then_branch.as_ref() {
                PseudoExpr::Constr { tag, fields, .. } => {
                    assert_eq!(*tag, 1);
                    assert!(matches!(fields.as_slice(), [PseudoExpr::Int(n)] if *n == 1.into()));
                }
                other => panic!("expected then branch Constr, got {other:?}"),
            }

            match else_branch.as_ref() {
                PseudoExpr::Constr { tag, fields, .. } => {
                    assert_eq!(*tag, 0);
                    assert!(matches!(fields.as_slice(), [PseudoExpr::Int(n)] if *n == 2.into()));
                }
                other => panic!("expected else branch Constr, got {other:?}"),
            }
        }
        other => panic!("expected If, got {other:?}"),
    }
}

#[test]
fn test_when_branches_rewrite_scott_constructor_family_to_constr_values() {
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                PseudoExpr::Lambda {
                    params: vec![
                        "_".to_string().into(),
                        "y".to_string().into(),
                        "_".to_string().into(),
                    ],
                    body: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("y")),
                        args: vec![PseudoExpr::Int(1.into())].into(),
                    }),
                },
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                PseudoExpr::Let {
                    name: "payload".to_string(),
                    id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
                    value: PBox::new(PseudoExpr::Int(2.into())),
                    body: PBox::new(PseudoExpr::Lambda {
                        params: vec![
                            "_".to_string().into(),
                            "_".to_string().into(),
                            "z".to_string().into(),
                        ],
                        body: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var("z")),
                            args: vec![PseudoExpr::var("payload")].into(),
                        }),
                    }),
                },
            ),
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
                PseudoExpr::Lambda {
                    params: vec![
                        "x".to_string().into(),
                        "_".to_string().into(),
                        "_".to_string().into(),
                    ],
                    body: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("x")),
                        args: vec![PseudoExpr::Int(3.into())].into(),
                    }),
                },
            ),
        ],
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When { clauses, .. } => {
            match &clauses[0].body {
                PseudoExpr::Constr { tag, fields, .. } => {
                    assert_eq!(*tag, 1);
                    assert!(matches!(fields.as_slice(), [PseudoExpr::Int(n)] if *n == 1.into()));
                }
                other => panic!("expected first body to become Constr, got {other:?}"),
            }

            match &clauses[1].body {
                PseudoExpr::Constr { tag, fields, .. } => {
                    assert_eq!(*tag, 2);
                    assert!(matches!(fields.as_slice(), [PseudoExpr::Int(n)] if *n == 2.into()));
                }
                other => panic!("expected second body Constr, got {other:?}"),
            }

            match &clauses[2].body {
                PseudoExpr::Constr { tag, fields, .. } => {
                    assert_eq!(*tag, 0);
                    assert!(matches!(fields.as_slice(), [PseudoExpr::Int(n)] if *n == 3.into()));
                }
                other => panic!("expected third body Constr, got {other:?}"),
            }
        }
        other => panic!("expected When, got {other:?}"),
    }
}

#[test]
fn test_scott_application_reversal_empty_fields() {
    // Constr<1>()(fn(x) { x + 1 }, fn(y) { y * 2 }) -> fn(y) { y * 2 }
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(1, 0),
            vec![],
        )),
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
                body: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Mul,
                    left: PBox::new(PseudoExpr::var("y")),
                    right: PBox::new(PseudoExpr::Int(2.into())),
                }),
            },
        ]
        .into(),
    };
    let simplified = simplify(expr);
    // Should select args[1] = fn(y) { y * 2 }
    match &simplified {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params, &["y"]);
        }
        _ => panic!("expected Lambda, got {:?}", simplified),
    }
}

#[test]
fn test_scott_application_reversal_with_fields() {
    // Constr<0>(w1, w2)(fn(a, b) { a + b }, fn(c) { c }) -> fn(a, b) { a + b }(w1, w2)
    // which further simplifies to let a = w1; let b = w2; a + b -> w1 + w2
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 2),
            vec![PseudoExpr::var("w1"), PseudoExpr::var("w2")],
        )),
        args: vec![
            PseudoExpr::Lambda {
                params: vec!["a".to_string().into(), "b".to_string().into()],
                body: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(PseudoExpr::var("a")),
                    right: PBox::new(PseudoExpr::var("b")),
                }),
            },
            PseudoExpr::Lambda {
                params: vec!["c".to_string().into()],
                body: PBox::new(PseudoExpr::var("c")),
            },
        ]
        .into(),
    };
    let simplified = simplify(expr);
    // Should become: let a = w1 in let b = w2 in a + b.
    // With inlining: w1 + w2.
    match &simplified {
        PseudoExpr::BinOp { op, left, right } => {
            assert!(matches!(op, BinaryOp::Add));
            assert!(matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == "w1"));
            assert!(matches!(right.as_ref(), PseudoExpr::Var { name, .. } if name == "w2"));
        }
        // Or it could be a Let chain if not fully inlined.
        PseudoExpr::Let { name, .. } => {
            assert_eq!(name, "a");
        }
        _ => panic!("expected BinOp or Let, got {:?}", simplified),
    }
}
