use super::*;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

fn expect_helper() -> PseudoExpr {
    PseudoExpr::Var {
        name: "expect!".to_string(),
        id: None,
    }
}

fn refutable_constr_pattern(tag: usize, arity: usize) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag,
        fields: vec![],
        shape: ConstructorShape::unknown_data(tag, arity),
    }
}

/// D4 positive: `Apply(expect!, [When{P→True, _→False}, tail])`
/// rewrites to `When{P→tail, _→fail}` — which the renderer turns
/// into `expect P = X; tail`.
#[test]
fn d4_rewrites_bool_when_in_expect_chain() {
    let x_id = VarId::fresh_binding();
    let input = PseudoExpr::Apply {
        function: PBox::new(expect_helper()),
        args: vec![
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
                subject_name: None,
                clauses: vec![
                    WhenClause {
                        pattern: refutable_constr_pattern(1, 0),
                        guard: None,
                        body: PseudoExpr::Bool(true),
                    },
                    WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: PseudoExpr::Bool(false),
                    },
                ],
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = rewrite_expect_when_bool(input);
    match out {
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => {
            assert!(subject_name.is_none());
            assert!(matches!(*subject, PseudoExpr::Var { ref name, .. } if name == "x"));
            assert_eq!(clauses.len(), 2);
            // First arm: refutable P → tail (Unit).
            assert!(matches!(
                &clauses[0].pattern,
                WhenPattern::Constructor { .. }
            ));
            assert!(matches!(clauses[0].body, PseudoExpr::Unit));
            // Second arm: wildcard → fail.
            assert!(matches!(&clauses[1].pattern, WhenPattern::Wildcard));
            assert!(matches!(clauses[1].body, PseudoExpr::Error { .. }));
        }
        other => panic!("expected rewritten When, got {other:?}"),
    }
}

/// D4 refusal: a wildcard True-arm is not refutable.
#[test]
fn d4_refuses_wildcard_true_arm() {
    let input = PseudoExpr::Apply {
        function: PBox::new(expect_helper()),
        args: vec![
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("x")),
                subject_name: None,
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::Bool(true),
                }],
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = rewrite_expect_when_bool(input);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

/// D4 Shape B: a matched arm body that is real logic (not
/// `Bool(true)`) is wrapped as `Apply(expect!, [body, tail])`, so
/// its Bool assertion holds and the outer `tail` still runs.
#[test]
fn d4_rewrites_shape_b_wraps_body_in_inner_expect() {
    let input = PseudoExpr::Apply {
        function: PBox::new(expect_helper()),
        args: vec![
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("x")),
                subject_name: None,
                clauses: vec![
                    WhenClause {
                        pattern: refutable_constr_pattern(1, 0),
                        guard: None,
                        body: PseudoExpr::var("computed"),
                    },
                    WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: PseudoExpr::Bool(false),
                    },
                ],
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = rewrite_expect_when_bool(input);
    match out {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 2);
            // Matched arm body is `Apply(expect!, [Var("computed"), Unit])`.
            match &clauses[0].body {
                PseudoExpr::Apply { function, args } => {
                    assert!(matches!(
                        function.as_ref(),
                        PseudoExpr::Var { name, .. } if name == "expect!"
                    ));
                    assert_eq!(args.len(), 2);
                    assert!(matches!(
                        &args[0],
                        PseudoExpr::Var { name, .. } if name == "computed"
                    ));
                    assert!(matches!(&args[1], PseudoExpr::Unit));
                }
                other => panic!("expected wrapped expect! call, got {other:?}"),
            }
            assert!(matches!(clauses[1].body, PseudoExpr::Error { .. }));
        }
        other => panic!("expected rewritten When, got {other:?}"),
    }
}

/// D4 Shape B with a non-trivial tail: the inner
/// `Apply(expect!, [body, tail])` keeps both evaluations.
#[test]
fn d4_rewrites_shape_b_with_non_trivial_tail() {
    let tail = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("side_effect")),
        args: vec![].into(),
    };
    let input = PseudoExpr::Apply {
        function: PBox::new(expect_helper()),
        args: vec![
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("x")),
                subject_name: None,
                clauses: vec![
                    WhenClause {
                        pattern: refutable_constr_pattern(1, 0),
                        guard: None,
                        body: PseudoExpr::var("real_body"),
                    },
                    WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: PseudoExpr::Bool(false),
                    },
                ],
            },
            tail,
        ]
        .into(),
    };
    let out = rewrite_expect_when_bool(input);
    match out {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 2);
            // Matched arm body is now `Apply(expect!, [real_body, side_effect()])`
            match &clauses[0].body {
                PseudoExpr::Apply { function, args } => {
                    assert!(matches!(
                        function.as_ref(),
                        PseudoExpr::Var { name, .. } if name == "expect!"
                    ));
                    assert_eq!(args.len(), 2);
                    assert!(matches!(
                        &args[0],
                        PseudoExpr::Var { name, .. } if name == "real_body"
                    ));
                    assert!(matches!(&args[1], PseudoExpr::Apply { .. }));
                }
                other => panic!("expected wrapped expect! call, got {other:?}"),
            }
            assert!(matches!(clauses[1].body, PseudoExpr::Error { .. }));
        }
        other => panic!("expected rewritten When, got {other:?}"),
    }
}

#[test]
fn d4_refuses_when_with_guard() {
    let input = PseudoExpr::Apply {
        function: PBox::new(expect_helper()),
        args: vec![
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("x")),
                subject_name: None,
                clauses: vec![
                    WhenClause {
                        pattern: refutable_constr_pattern(1, 0),
                        guard: Some(PseudoExpr::Bool(true)),
                        body: PseudoExpr::Bool(true),
                    },
                    WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: PseudoExpr::Bool(false),
                    },
                ],
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = rewrite_expect_when_bool(input);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

/// D4 refusal: `when X as Y` — the rewrite would unbind Y.
#[test]
fn d4_refuses_when_subject_name() {
    use crate::pseudo::ast::Binder;
    let input = PseudoExpr::Apply {
        function: PBox::new(expect_helper()),
        args: vec![
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("x")),
                subject_name: Some(Binder::new("y", VarId::fresh_binding())),
                clauses: vec![
                    WhenClause {
                        pattern: refutable_constr_pattern(1, 0),
                        guard: None,
                        body: PseudoExpr::Bool(true),
                    },
                    WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: PseudoExpr::Bool(false),
                    },
                ],
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = rewrite_expect_when_bool(input);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

/// D4 refusal: 3-arg expect! (fail-message form) — out of scope.
#[test]
fn d4_refuses_3_arg_expect() {
    let input = PseudoExpr::Apply {
        function: PBox::new(expect_helper()),
        args: vec![
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("x")),
                subject_name: None,
                clauses: vec![
                    WhenClause {
                        pattern: refutable_constr_pattern(1, 0),
                        guard: None,
                        body: PseudoExpr::Bool(true),
                    },
                    WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: PseudoExpr::Bool(false),
                    },
                ],
            },
            PseudoExpr::Unit,
            PseudoExpr::String("msg".to_string()),
        ]
        .into(),
    };
    let out = rewrite_expect_when_bool(input);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

/// D4 refusal: two True arms — ambiguous shape.
#[test]
fn d4_refuses_multiple_true_arms() {
    let input = PseudoExpr::Apply {
        function: PBox::new(expect_helper()),
        args: vec![
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("x")),
                subject_name: None,
                clauses: vec![
                    WhenClause {
                        pattern: refutable_constr_pattern(0, 0),
                        guard: None,
                        body: PseudoExpr::Bool(true),
                    },
                    WhenClause {
                        pattern: refutable_constr_pattern(1, 0),
                        guard: None,
                        body: PseudoExpr::Bool(true),
                    },
                    WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: PseudoExpr::Bool(false),
                    },
                ],
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = rewrite_expect_when_bool(input);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}

#[test]
fn d4_refuses_when_function_is_not_expect_helper() {
    let input = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("other")),
        args: vec![
            PseudoExpr::When {
                subject: PBox::new(PseudoExpr::var("x")),
                subject_name: None,
                clauses: vec![
                    WhenClause {
                        pattern: refutable_constr_pattern(1, 0),
                        guard: None,
                        body: PseudoExpr::Bool(true),
                    },
                    WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: PseudoExpr::Bool(false),
                    },
                ],
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = rewrite_expect_when_bool(input);
    assert!(matches!(out, PseudoExpr::Apply { .. }));
}
