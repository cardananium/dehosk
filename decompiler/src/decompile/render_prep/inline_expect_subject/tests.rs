use super::*;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

fn binder(name: &str) -> Binder {
    name.into()
}

fn fresh_id() -> VarId {
    VarId::fresh_binding()
}

fn constr_pattern(tag: usize, fields: Vec<&str>) -> WhenPattern {
    WhenPattern::Constructor {
        shape: ConstructorShape::unknown_data(tag, fields.len()),
        tag,
        fields: fields.into_iter().map(binder).collect(),
        type_hint: None,
    }
}

fn expect_chain(subject: PseudoExpr, pattern: WhenPattern, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern,
                guard: None,
                body,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
        ],
    }
}

#[test]
fn p4_3_inlines_let_then_expect_subject() {
    // `let find_result = find(...); expect Some(payload) = find_result; payload`
    // → `expect Some(payload) = find(...); payload`
    let find_id = fresh_id();
    let find_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("find")),
        args: vec![PseudoExpr::var("list_arg")].into(),
    };
    let when_body = PseudoExpr::var("payload");
    let when_expr = expect_chain(
        PseudoExpr::Var {
            name: "find_result".to_string(),
            id: Some(find_id),
        },
        constr_pattern(0, vec!["payload"]),
        when_body,
    );
    let expr = PseudoExpr::Let {
        name: "find_result".to_string(),
        id: Some(find_id),
        value: PBox::new(find_call.clone()),
        body: PBox::new(when_expr),
    };
    let folded = inline_expect_subjects(expr);
    // After: When { subject: find_call, ... } (Let stripped).
    match folded {
        PseudoExpr::When { subject, .. } => {
            assert!(matches!(*subject, PseudoExpr::Apply { .. }));
        }
        other => panic!("expected When, got {other:?}"),
    }
}

#[test]
fn p4_3_skips_when_let_binder_is_referenced_elsewhere_in_body() {
    // `let X = e; when X is { P(_) -> X; _ -> fail }` — the
    // pattern does not bind X, so the body's X is the outer
    // binder. Must NOT inline.
    let x_id = fresh_id();
    let when_body = PseudoExpr::Var {
        name: "find_result".to_string(),
        id: Some(x_id),
    };
    let expr = PseudoExpr::Let {
        name: "find_result".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::var("e")),
        body: PBox::new(expect_chain(
            PseudoExpr::Var {
                name: "find_result".to_string(),
                id: Some(x_id),
            },
            constr_pattern(0, vec!["payload"]),
            when_body, // <-- references find_result!
        )),
    };
    let folded = inline_expect_subjects(expr.clone());
    assert_eq!(
        folded, expr,
        "must NOT inline when name is referenced in body"
    );
}

#[test]
fn p4_3_skips_when_value_contains_x() {
    // `let X = (let X = ... in ...)` — value rebinds X. The outer X is
    // not free in value (shadowed), so inlining is safe in theory.
    // But conservatively bail when value's free vars include X.
    let x_id = fresh_id();
    let value = PseudoExpr::var("find_result"); // references X (free)
    let expr = PseudoExpr::Let {
        name: "find_result".to_string(),
        id: Some(x_id),
        value: PBox::new(value),
        body: PBox::new(expect_chain(
            PseudoExpr::Var {
                name: "find_result".to_string(),
                id: Some(x_id),
            },
            constr_pattern(0, vec!["payload"]),
            PseudoExpr::var("payload"),
        )),
    };
    let folded = inline_expect_subjects(expr.clone());
    assert_eq!(
        folded, expr,
        "must NOT inline when value references the binder"
    );
}

#[test]
fn p4_3_skips_let_with_two_arm_when_no_fail_fallback() {
    // 2 real arms — not an expect-pattern, leave alone. Multi-clause
    // inlining is intentionally skipped: it would strip the name from
    // `when lookup_result is { ... }`, regressing readability of
    // named option results.
    let x_id = fresh_id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::var("e")),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(x_id),
            }),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: constr_pattern(0, vec![]),
                    guard: None,
                    body: PseudoExpr::Bool(true),
                },
                WhenClause {
                    pattern: constr_pattern(1, vec![]),
                    guard: None,
                    body: PseudoExpr::Bool(false),
                },
            ],
        }),
    };
    let folded = inline_expect_subjects(expr.clone());
    assert_eq!(
        folded, expr,
        "two-arm when (not expect form) must not inline"
    );
}

#[test]
fn p4_3_skips_let_with_wildcard_only_arm() {
    // `when X is { _ -> body }` — Wildcard pattern doesn't qualify
    // as expect-form. Leave alone.
    let x_id = fresh_id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::var("e")),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(x_id),
            }),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::var("body"),
            }],
        }),
    };
    let folded = inline_expect_subjects(expr.clone());
    assert_eq!(folded, expr);
}

#[test]
fn p4_3_skips_when_with_guard() {
    // Pattern with `if` guard — not safe to skip the let.
    let x_id = fresh_id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::var("e")),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(x_id),
            }),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: constr_pattern(0, vec!["p"]),
                    guard: Some(PseudoExpr::Bool(true)),
                    body: PseudoExpr::var("body"),
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: PseudoExpr::Error { message: None },
                },
            ],
        }),
    };
    let folded = inline_expect_subjects(expr.clone());
    assert_eq!(folded, expr, "guarded clause must not inline");
}

#[test]
fn p4_3_recurses_into_nested_lets() {
    // `let outer = a; let X = find(); expect Some = X` should
    // inline the inner pair, leaving the outer let.
    let find_id = fresh_id();
    let inner_let = PseudoExpr::Let {
        name: "find_result".to_string(),
        id: Some(find_id),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("find")),
            args: vec![].into(),
        }),
        body: PBox::new(expect_chain(
            PseudoExpr::Var {
                name: "find_result".to_string(),
                id: Some(find_id),
            },
            constr_pattern(0, vec!["payload"]),
            PseudoExpr::var("payload"),
        )),
    };
    let outer_let = PseudoExpr::let_bind("outer", PseudoExpr::int(1), inner_let);
    let folded = inline_expect_subjects(outer_let);
    // The outer let stays; its body becomes a When directly.
    match folded {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "outer");
            assert!(matches!(*body, PseudoExpr::When { .. }));
        }
        other => panic!("expected outer Let, got {other:?}"),
    }
}
