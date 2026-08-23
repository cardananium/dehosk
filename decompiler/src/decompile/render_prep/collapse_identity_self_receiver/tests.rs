use super::*;
use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn identity() -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![Binder::new("w".to_string(), VarId::new(900))],
        body: PBox::new(var("w", 900)),
    }
}

fn ctor_pattern(tag: usize) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag,
        fields: vec![],
        shape: ConstructorShape::unknown_data(tag, 0),
    }
}

fn run(expr: PseudoExpr) -> PseudoExpr {
    collapse_identity_self_receiver(expr)
}

/// `const n = rec fn x_111(__20) { fn(a,b,c) { when x_111(d) is
/// { 0->a; 1->b; 2->c } } }`, used externally as `n(d)`. After
/// collapse: `__20` is gone, the when-subject is bare `Var(x_111)`
/// for clarify to revert, and the external `n(d)` is bare `Var(n)`.
#[test]
fn collapses_dead_identity_self_receiver() {
    let inner_when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x_111", 100)),
            args: vec![identity()].into(),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: ctor_pattern(0),
                guard: None,
                body: var("a", 10),
            },
            WhenClause {
                pattern: ctor_pattern(1),
                guard: None,
                body: var("b", 11),
            },
            WhenClause {
                pattern: ctor_pattern(2),
                guard: None,
                body: var("c", 12),
            },
        ],
    };
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("x_111".to_string(), VarId::new(100)),
        params: vec![Binder::new("__20".to_string(), VarId::new(20))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("a".to_string(), VarId::new(10)),
                Binder::new("b".to_string(), VarId::new(11)),
                Binder::new("c".to_string(), VarId::new(12)),
            ],
            body: PBox::new(inner_when),
        }),
    };
    let input = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(rec_fn),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("n", 50)),
            args: vec![identity()].into(),
        }),
    };

    let out = run(input);
    let PseudoExpr::Let { value, body, .. } = out else {
        panic!("expected Let");
    };
    // External `n(d)` -> bare `n`.
    assert!(matches!(*body, PseudoExpr::Var { id: Some(v), .. } if v == VarId::new(50)));
    // rec-fn: dead param dropped; when-subject now bare `Var(x_111)`.
    let PseudoExpr::RecFn { params, body, .. } = value.into_inner() else {
        panic!("expected RecFn");
    };
    assert!(params.is_empty(), "the dead __20 slot must be dropped");
    let PseudoExpr::Lambda { body: lam_body, .. } = body.into_inner() else {
        panic!("expected inner Lambda preserved");
    };
    let PseudoExpr::When { subject, .. } = lam_body.into_inner() else {
        panic!("expected When preserved");
    };
    assert!(
        matches!(*subject, PseudoExpr::Var { id: Some(v), .. } if v == VarId::new(100)),
        "when-subject must be the bare self Var for clarify to revert"
    );
}

/// `__20` IS used in the body — not a dead slot, leave untouched.
#[test]
fn bails_when_slot_used() {
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("x_111".to_string(), VarId::new(100)),
        params: vec![Binder::new("__20".to_string(), VarId::new(20))],
        body: PBox::new(var("__20", 20)), // uses the slot
    };
    let input = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(rec_fn),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("n", 50)),
            args: vec![identity()].into(),
        }),
    };
    let out = run(input.clone());
    assert_eq!(out, input);
}

/// Self-call's first arg is NOT identity — not the collapse pattern.
#[test]
fn bails_on_non_identity_self_arg() {
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("x_111".to_string(), VarId::new(100)),
        params: vec![Binder::new("__20".to_string(), VarId::new(20))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("a".to_string(), VarId::new(10))],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("x_111", 100)),
                args: vec![var("not_identity", 77), var("a", 10)].into(), // non-identity first arg
            }),
        }),
    };
    let input = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(rec_fn),
        body: PBox::new(PseudoExpr::Unit),
    };
    let out = run(input.clone());
    assert_eq!(out, input);
}

/// Self-call is under-applied (fewer real args than inner arity) — flatten
/// would bail downstream, so collapse must bail here too.
#[test]
fn bails_on_under_applied_self_call() {
    // inner arity 2, but the self-call supplies only 1 real arg after identity.
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("x_111".to_string(), VarId::new(100)),
        params: vec![Binder::new("__20".to_string(), VarId::new(20))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("a".to_string(), VarId::new(10)),
                Binder::new("b".to_string(), VarId::new(11)),
            ],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(var("x_111", 100)),
                args: vec![identity(), var("a", 10)].into(), // identity + 1 real arg, arity 2
            }),
        }),
    };
    let input = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(rec_fn),
        body: PBox::new(PseudoExpr::Unit),
    };
    let out = run(input.clone());
    assert_eq!(out, input);
}

/// External reference is a bare value-use (`n` not applied) — unsafe to
/// strip arity, bail.
#[test]
fn bails_on_bare_external_ref() {
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("x_111".to_string(), VarId::new(100)),
        params: vec![Binder::new("__20".to_string(), VarId::new(20))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("a".to_string(), VarId::new(10))],
            body: PBox::new(var("a", 10)),
        }),
    };
    let input = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(rec_fn),
        // `n` used bare (e.g. passed as an argument) — not first-applied.
        body: PBox::new(PseudoExpr::Tuple(
            (vec![var("n", 50), PseudoExpr::Unit]).into(),
        )),
    };
    let out = run(input.clone());
    assert_eq!(out, input);
}

/// Let value isn't a rec-fn — nothing to do.
#[test]
fn bails_on_non_recfn_value() {
    let input = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(PseudoExpr::int(5)),
        body: PBox::new(var("n", 50)),
    };
    let out = run(input.clone());
    assert_eq!(out, input);
}

/// A bare-VALUE internal self-ref `tuple(x(d), a)` (rest-empty, NOT a
/// when-subject) would strip to a bare `Var(x)` that clarify/flatten
/// can't repair — so the pass must bail.
#[test]
fn bails_on_bare_value_internal_self_ref() {
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("x_111".to_string(), VarId::new(100)),
        params: vec![Binder::new("__20".to_string(), VarId::new(20))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("a".to_string(), VarId::new(10))],
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    // self-ref applied to identity, but used as a value (tuple elem)
                    PseudoExpr::Apply {
                        function: PBox::new(var("x_111", 100)),
                        args: vec![identity()].into(),
                    },
                    var("a", 10),
                ]
                .into(),
            )),
        }),
    };
    let input = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(rec_fn),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("n", 50)),
            args: vec![identity()].into(),
        }),
    };
    let out = run(input.clone());
    assert_eq!(out, input);
}

/// A rest-empty self-When subject `when x(id) as s is {...}` whose
/// `subject_name` binder `s` is referenced in a clause body must bail:
/// clarify drops `subject_name` when it rewrites the When to a call, so
/// `s` would dangle.
#[test]
fn bails_on_self_when_subject_name_used() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;
    let ctor = |tag: usize| WhenPattern::Constructor {
        type_hint: None,
        tag,
        fields: vec![],
        shape: ConstructorShape::unknown_data(tag, 0),
    };
    let when_named = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x_111", 100)),
            args: vec![identity()].into(),
        }),
        subject_name: Some(Binder::new("s".to_string(), VarId::new(30))),
        clauses: vec![
            WhenClause {
                pattern: ctor(0),
                guard: None,
                body: var("s", 30), // references the subject-name binder
            },
            WhenClause {
                pattern: ctor(1),
                guard: None,
                body: var("b", 11),
            },
        ],
    };
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("x_111".to_string(), VarId::new(100)),
        params: vec![Binder::new("__20".to_string(), VarId::new(20))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("a".to_string(), VarId::new(10)),
                Binder::new("b".to_string(), VarId::new(11)),
            ],
            body: PBox::new(when_named),
        }),
    };
    let input = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(rec_fn),
        body: PBox::new(PseudoExpr::Unit),
    };
    let out = run(input.clone());
    assert_eq!(out, input);
}

/// A target ref hidden inside a `WhenPattern::Literal` must block the
/// fire (the map_children strip can't reach it).
#[test]
fn bails_on_target_ref_in_literal_pattern() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let when_with_literal = PseudoExpr::When {
        subject: PBox::new(var("a", 10)),
        subject_name: None,
        clauses: vec![WhenClause {
            // literal pattern carries a self-ref expression
            pattern: WhenPattern::Literal(PseudoExpr::Apply {
                function: PBox::new(var("x_111", 100)),
                args: vec![identity()].into(),
            }),
            guard: None,
            body: var("a", 10),
        }],
    };
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("x_111".to_string(), VarId::new(100)),
        params: vec![Binder::new("__20".to_string(), VarId::new(20))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("a".to_string(), VarId::new(10))],
            body: PBox::new(when_with_literal),
        }),
    };
    let input = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(rec_fn),
        body: PBox::new(PseudoExpr::Unit),
    };
    let out = run(input.clone());
    assert_eq!(out, input);
}

/// A curried *direct* recursive call `x_111(d)(a, b, c)` (not a when)
/// collapses to `x_111(a, b, c)`.
#[test]
fn collapses_curried_direct_self_call() {
    let curried_call = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x_111", 100)),
            args: vec![identity()].into(),
        }),
        args: vec![var("a", 10), var("b", 11), var("c", 12)].into(),
    };
    let rec_fn = PseudoExpr::RecFn {
        name: Binder::new("x_111".to_string(), VarId::new(100)),
        params: vec![Binder::new("__20".to_string(), VarId::new(20))],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("a".to_string(), VarId::new(10)),
                Binder::new("b".to_string(), VarId::new(11)),
                Binder::new("c".to_string(), VarId::new(12)),
            ],
            body: PBox::new(curried_call),
        }),
    };
    let input = PseudoExpr::Let {
        name: "n".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(rec_fn),
        body: PBox::new(PseudoExpr::Unit),
    };
    let out = run(input);
    let PseudoExpr::Let { value, .. } = out else {
        panic!("expected Let");
    };
    let PseudoExpr::RecFn { params, body, .. } = value.into_inner() else {
        panic!("expected RecFn");
    };
    assert!(params.is_empty());
    let PseudoExpr::Lambda { body: lam_body, .. } = body.into_inner() else {
        panic!("expected Lambda");
    };
    // `x_111(d)(a,b,c)` -> `x_111(a,b,c)`.
    let lam_body = lam_body.into_inner();
    let PseudoExpr::Apply { function, args } = lam_body else {
        panic!("expected Apply, got {:?}", lam_body);
    };
    assert!(matches!(*function, PseudoExpr::Var { id: Some(v), .. } if v == VarId::new(100)));
    assert_eq!(args.len(), 3);
}
