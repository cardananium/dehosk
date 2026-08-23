use super::*;
use crate::pseudo::ast::{BinaryOp, Binder, WhenClause};

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `fn(_) { f(a, b, c, d) + f(a, b, c, d) }` →
/// `fn(_) { let w = f(a, b, c, d); w + w }`.
#[test]
fn extracts_duplicate_apply() {
    // 1 Apply + 4 Var args = 5 nodes, meets the ≥5 threshold.
    let dup = PseudoExpr::Apply {
        function: PBox::new(var("f", 1)),
        args: vec![var("a", 2), var("b", 3), var("c", 4), var("d", 5)].into(),
    };
    let input = PseudoExpr::Lambda {
        params: vec![Binder::new("_".to_string(), VarId::new(99))],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(dup.clone()),
            right: PBox::new(dup),
        }),
    };
    let out = extract_repeated_subexpr(input);
    let PseudoExpr::Lambda { body, .. } = out else {
        panic!("Lambda")
    };
    match body.into_inner() {
        PseudoExpr::Let {
            name, body: inner, ..
        } => {
            assert_eq!(name, "w");
            if let PseudoExpr::BinOp { left, right, .. } = inner.into_inner() {
                assert!(matches!(*left, PseudoExpr::Var { ref name, .. } if name == "w"));
                assert!(matches!(*right, PseudoExpr::Var { ref name, .. } if name == "w"));
            } else {
                panic!("expected BinOp body");
            }
        }
        other => panic!("expected Let, got {:?}", other),
    }
}

/// `if c { g(a, b) } else { fail[msg] }` — 7 nodes, contains an `Error`.
fn dup_with_abort(msg: Option<&str>) -> PseudoExpr {
    PseudoExpr::If {
        condition: PBox::new(var("c", 1)),
        then_branch: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("g", 2)),
            args: vec![var("a", 3), var("b", 4)].into(),
        }),
        else_branch: PBox::new(PseudoExpr::Error {
            message: msg.map(|s| s.to_string()),
        }),
    }
}

fn lambda_body(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![Binder::new("_".to_string(), VarId::new(99))],
        body: PBox::new(body),
    }
}

fn add(l: PseudoExpr, r: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BinOp {
        op: BinaryOp::Add,
        left: PBox::new(l),
        right: PBox::new(r),
    }
}

/// A duplicate containing ONLY a bare `Error { message: None }` (a
/// message-less abort), at the eager-spine head, IS extracted: merging
/// dominated bare aborts is sound (first eval aborts, rest never run).
#[test]
fn extracts_dominating_bare_abort() {
    let dup = dup_with_abort(None);
    let out = extract_repeated_subexpr(lambda_body(add(dup.clone(), dup)));
    let PseudoExpr::Lambda { body, .. } = out else {
        panic!("Lambda")
    };
    match body.into_inner() {
        PseudoExpr::Let {
            name, body: inner, ..
        } => {
            assert_eq!(name, "w");
            assert!(matches!(*inner, PseudoExpr::BinOp { .. }), "expected w + w");
        }
        other => panic!("bare-abort dup should extract to `let w`, got {other:?}"),
    }
}

/// A duplicate containing a `fail @"msg"` (`Error { message: Some(_) }`)
/// is NOT extracted: merging would drop an observable message.
#[test]
fn skips_messaged_fail_duplicate() {
    let dup = dup_with_abort(Some("boom"));
    let input = lambda_body(add(dup.clone(), dup));
    assert_eq!(extract_repeated_subexpr(input.clone()), input);
}

/// A duplicate containing a `Trace` is NOT extracted: merging would drop
/// a log emission.
#[test]
fn skips_trace_duplicate() {
    let dup = PseudoExpr::If {
        condition: PBox::new(var("c", 1)),
        then_branch: PBox::new(PseudoExpr::Trace {
            message: PBox::new(var("m", 2)),
            value: PBox::new(var("a", 3)),
        }),
        else_branch: PBox::new(var("b", 4)),
    };
    let input = lambda_body(add(dup.clone(), dup));
    assert_eq!(extract_repeated_subexpr(input.clone()), input);
}

/// A bare-abort duplicate that does NOT dominate (a risky op is evaluated
/// before its first occurrence) is NOT extracted: hoisting would reorder
/// its abort ahead of that earlier op.
#[test]
fn skips_non_dominating_bare_abort() {
    let dup = dup_with_abort(None);
    let earlier_risky = PseudoExpr::Apply {
        function: PBox::new(var("h", 10)),
        args: vec![var("z", 11)].into(),
    };
    let input = lambda_body(add(earlier_risky, add(dup.clone(), dup)));
    assert_eq!(extract_repeated_subexpr(input.clone()), input);
}

/// A bare-abort duplicate wrapped in a `trace` is NOT extracted: the
/// trace EMITS before the abort, so hoisting the abort to the top would
/// drop the emission. `eager_first` treats `Trace` as risky.
#[test]
fn skips_bare_abort_under_trace() {
    let traced = |dup: PseudoExpr| PseudoExpr::Trace {
        message: PBox::new(var("m", 20)),
        value: PBox::new(dup),
    };
    let dup = dup_with_abort(None);
    let input = lambda_body(add(traced(dup.clone()), traced(dup)));
    assert_eq!(extract_repeated_subexpr(input.clone()), input);
}

/// Same as above but the trace is the raw `builtin.trace` call
/// (`BuiltinCall { name: Trace }`), which render-prep keeps by default —
/// still NOT extracted.
#[test]
fn skips_bare_abort_under_builtin_trace() {
    let traced = |dup: PseudoExpr| PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::Trace,
        args: vec![var("m", 20), dup].into(),
    };
    let dup = dup_with_abort(None);
    let input = lambda_body(add(traced(dup.clone()), traced(dup)));
    assert_eq!(extract_repeated_subexpr(input.clone()), input);
}

/// `Pair(fail, p(a,b,c,d)) + Pair(fail, p(a,b,c,d))`: the abort-bearing
/// `Pair` is extracted, but the pure `p(..)` nested in its second field is
/// NOT separately hoisted (that would evaluate `p` before the abort).
/// Result: a single `let w = Pair(fail, p(..))`.
#[test]
fn extracts_abort_drops_nested_pure() {
    let p_call = PseudoExpr::Apply {
        function: PBox::new(var("p", 1)),
        args: vec![var("a", 2), var("b", 3), var("c", 4), var("d", 5)].into(),
    };
    let pair = PseudoExpr::Pair(
        PBox::new(PseudoExpr::Error { message: None }),
        PBox::new(p_call),
    );
    let out = extract_repeated_subexpr(lambda_body(add(pair.clone(), pair)));
    let PseudoExpr::Lambda { body, .. } = out else {
        panic!("Lambda")
    };
    match body.into_inner() {
        PseudoExpr::Let {
            name,
            value,
            body: inner,
            ..
        } => {
            assert_eq!(name, "w");
            // The single hoisted binding is the abort-bearing Pair (NOT the
            // nested pure `p(..)`), so `p` stays inside it.
            assert!(
                matches!(*value, PseudoExpr::Pair(ref a, _) if matches!(a.as_ref(), PseudoExpr::Error { .. })),
                "expected `let w = Pair(fail, ..)`, got value {value:?}"
            );
            assert!(
                matches!(*inner, PseudoExpr::BinOp { .. }),
                "expected w + w body"
            );
        }
        other => panic!("expected one `let w = Pair(..)`, got {other:?}"),
    }
}

/// An abort-bearing `when` whose `Literal` pattern references a LOCAL var
/// (bound by an enclosing `let`) is NOT extracted: hoisting it above that
/// `let` would leave the var unbound. The Literal-payload free-var check
/// counts the reference so the `free(rep) ⊆ free(body)` gate rejects it.
#[test]
fn skips_abort_candidate_capturing_literal_pattern_var() {
    use crate::pseudo::ast::WhenPattern;
    let x_id = VarId::new(50);
    let when_lit = || PseudoExpr::When {
        subject: PBox::new(var("s", 51)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Literal(PseudoExpr::var_with_id("x", x_id)),
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let body = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(x_id),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(add(when_lit(), when_lit())),
    };
    let input = lambda_body(body);
    assert_eq!(extract_repeated_subexpr(input.clone()), input);
}

/// Single occurrence — no extraction.
#[test]
fn skips_single_occurrence() {
    let input = PseudoExpr::Lambda {
        params: vec![Binder::new("_".to_string(), VarId::new(99))],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("f", 1)),
            args: vec![var("a", 2), var("b", 3)].into(),
        }),
    };
    let out = extract_repeated_subexpr(input.clone());
    assert_eq!(out, input);
}

/// Trivial duplicates (Var) — no extraction.
#[test]
fn skips_trivial_var() {
    let input = PseudoExpr::Lambda {
        params: vec![Binder::new("_".to_string(), VarId::new(99))],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(var("x", 1)),
            right: PBox::new(var("x", 1)),
        }),
    };
    let out = extract_repeated_subexpr(input.clone());
    assert_eq!(out, input);
}

/// Alpha-equivalent duplicates (different binder names, same shape).
#[test]
fn extracts_alpha_equivalent_when() {
    // `when v is { Pair(x, y) -> f(x, y) }` × 2 with different
    // binder ids.
    let w1 = PseudoExpr::When {
        subject: PBox::new(var("v", 100)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: crate::pseudo::ast::WhenPattern::Pair(
                Binder::new("x".to_string(), VarId::new(1)),
                Binder::new("y".to_string(), VarId::new(2)),
            ),
            guard: None,
            body: PseudoExpr::Apply {
                function: PBox::new(var("f", 50)),
                args: vec![var("x", 1), var("y", 2)].into(),
            },
        }],
    };
    let w2 = PseudoExpr::When {
        subject: PBox::new(var("v", 100)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: crate::pseudo::ast::WhenPattern::Pair(
                Binder::new("x_2".to_string(), VarId::new(3)),
                Binder::new("y_2".to_string(), VarId::new(4)),
            ),
            guard: None,
            body: PseudoExpr::Apply {
                function: PBox::new(var("f", 50)),
                args: vec![var("x_2", 3), var("y_2", 4)].into(),
            },
        }],
    };
    let input = PseudoExpr::Lambda {
        params: vec![Binder::new("_".to_string(), VarId::new(99))],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Sub,
            left: PBox::new(w1),
            right: PBox::new(w2),
        }),
    };
    let out = extract_repeated_subexpr(input);
    let PseudoExpr::Lambda { body, .. } = out else {
        panic!("Lambda")
    };
    // Body should now be Let { ..., body: BinOp { Var(w), Var(w) } }.
    match body.into_inner() {
        PseudoExpr::Let {
            name, body: inner, ..
        } => {
            assert_eq!(name, "w");
            if let PseudoExpr::BinOp { left, right, .. } = inner.into_inner() {
                assert!(matches!(*left, PseudoExpr::Var { ref name, .. } if name == "w"));
                assert!(matches!(*right, PseudoExpr::Var { ref name, .. } if name == "w"));
            } else {
                panic!("expected BinOp inside Let body");
            }
        }
        other => panic!("expected Let, got {:?}", other),
    }
}
