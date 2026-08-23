use super::*;
use crate::decompile::TypeHintId;
use crate::pseudo::ast::Binder;

fn vid(n: u32) -> VarId {
    VarId::new(n)
}

fn var(name: &str, n: u32) -> PseudoExpr {
    PseudoExpr::Var {
        name: name.to_string(),
        id: Some(vid(n)),
    }
}

fn lam(params: &[(&str, u32)], body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: params
            .iter()
            .map(|(n, i)| Binder::new(*n, vid(*i)))
            .collect(),
        body: PBox::new(body),
    }
}

/// A stub Constr value `Unknown{tag,arity}` carrying `type_hint`, used to seed
/// the catalog (mirrors the constructor-recognition output).
fn ctor(th: &TypeHintId, tag: usize, arity: usize) -> PseudoExpr {
    PseudoExpr::Constr {
        tag,
        shape: ConstructorShape::unknown_data(tag, arity),
        fields: (0..arity).map(|_| PseudoExpr::Unit).collect(),
        type_hint: Some(th.clone()),
    }
}

fn th(s: &str) -> TypeHintId {
    TypeHintId::from(s)
}

/// Wrap `inner` so the catalog sees a 2-variant [1,3] stub type T26, and the
/// payload binder is Scott-rooted (a field of a stub-matched value).
fn with_t26_catalog_and_rooted_payload(payload_use: PseudoExpr) -> PseudoExpr {
    let t26 = th("Unknown_S_26");
    // Two Constr sites declaring T26 = { _0(Data), _1(Data,Data,Data) }.
    let decl0 = ctor(&t26, 0, 1);
    let decl1 = ctor(&t26, 1, 3);
    // `when subj is { Unknown_S_6_0(payload) -> <payload_use> }` makes `payload`
    // (VarId 100) Scott-rooted via the stub-constructor pattern.
    let t6 = th("Unknown_S_6");
    let when = PseudoExpr::When {
        subject: PBox::new(var("subj", 1)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: Some(t6),
                tag: 0,
                fields: vec![Binder::new("payload", vid(100))],
                shape: ConstructorShape::unknown_data(0, 1),
            },
            guard: None,
            body: payload_use,
        }],
    };
    // Tuple just to hold all three in one expr the pass can scan.
    PseudoExpr::Tuple((vec![decl0, decl1, when]).into())
}

fn count_when(expr: &PseudoExpr) -> usize {
    let mut n = 0;
    if let PseudoExpr::When { .. } = expr {
        n += 1;
    }
    for c in children(expr) {
        n += count_when(c);
    }
    n
}

#[test]
fn catalog_indexes_unique_signature() {
    let t26 = th("Unknown_S_26");
    let expr = PseudoExpr::Tuple((vec![ctor(&t26, 0, 1), ctor(&t26, 1, 3)]).into());
    let cat = build_stub_catalog(&expr);
    assert_eq!(cat.get(&vec![1, 3]), Some(&Some(t26)));
}

#[test]
fn catalog_keeps_ambiguous_signature_unattributed() {
    let a = th("Unknown_S_A");
    let b = th("Unknown_S_B");
    // Two distinct types with the SAME [1,1] signature → usable for
    // the structural rebuild, but with NO attributed type (naming
    // either would be a guess).
    let expr = PseudoExpr::Tuple(
        vec![
            ctor(&a, 0, 1),
            ctor(&a, 1, 1),
            ctor(&b, 0, 1),
            ctor(&b, 1, 1),
        ]
        .into(),
    );
    let cat = build_stub_catalog(&expr);
    assert_eq!(cat.get(&vec![1, 1]), Some(&None));
}

#[test]
fn rewrites_scott_rooted_eliminator_to_when() {
    // payload(fn(x){x}, fn(a,b,c){a}) where payload is Scott-rooted + T26 [1,3].
    let payload_use = PseudoExpr::Apply {
        function: PBox::new(var("payload", 100)),
        args: vec![
            lam(&[("x", 201)], var("x", 201)),
            lam(&[("a", 202), ("b", 203), ("c", 204)], var("a", 202)),
        ]
        .into(),
    };
    let expr = with_t26_catalog_and_rooted_payload(payload_use);
    let out = resolve_scott_eliminator(expr);
    // The payload(...) application became a `when` (count goes from 1 -> 2).
    assert_eq!(
        count_when(&out),
        2,
        "payload eliminator should lower to when"
    );
}

#[test]
fn does_not_rewrite_non_scott_rooted_var() {
    // Same eliminator shape but `f` (VarId 300) is NOT pattern-bound from stub
    // data (a free HOF-like param) → must stay a raw Apply.
    let t26 = th("Unknown_S_26");
    let app = PseudoExpr::Apply {
        function: PBox::new(var("f", 300)),
        args: vec![
            lam(&[("x", 201)], var("x", 201)),
            lam(&[("a", 202), ("b", 203), ("c", 204)], var("a", 202)),
        ]
        .into(),
    };
    let expr = PseudoExpr::Tuple((vec![ctor(&t26, 0, 1), ctor(&t26, 1, 3), app]).into());
    let out = resolve_scott_eliminator(expr);
    assert_eq!(
        count_when(&out),
        0,
        "non-scott-rooted var must not be rewritten"
    );
}

#[test]
fn rewrites_unattributed_when_signature_ambiguous() {
    // payload Scott-rooted with two [1,3] types → ambiguous signature.
    let a = th("Unknown_S_A");
    let b = th("Unknown_S_B");
    let payload_use = PseudoExpr::Apply {
        function: PBox::new(var("payload", 100)),
        args: vec![
            lam(&[("x", 201)], var("x", 201)),
            lam(&[("a", 202), ("b", 203), ("c", 204)], var("a", 202)),
        ]
        .into(),
    };
    let t6 = th("Unknown_S_6");
    let when = PseudoExpr::When {
        subject: PBox::new(var("subj", 1)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: Some(t6),
                tag: 0,
                fields: vec![Binder::new("payload", vid(100))],
                shape: ConstructorShape::unknown_data(0, 1),
            },
            guard: None,
            body: payload_use,
        }],
    };
    let expr = PseudoExpr::Tuple(
        vec![
            ctor(&a, 0, 1),
            ctor(&a, 1, 3),
            ctor(&b, 0, 1),
            ctor(&b, 1, 3),
            when,
        ]
        .into(),
    );
    let out = resolve_scott_eliminator(expr);
    // An ambiguous signature still REBUILDS — the arities come from the
    // eliminator's own lambda uses — but the rebuilt patterns carry NO
    // type attribution (positional Constr<tag>).
    assert_eq!(
        count_when(&out),
        2,
        "ambiguous signature must still rebuild the eliminator"
    );
    fn find_unattributed_when(expr: &PseudoExpr, seed_subject: u32) -> bool {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = expr
            && !matches!(
                subject.as_ref(),
                PseudoExpr::Var { id: Some(v), .. } if v.as_u32() == seed_subject
            )
        {
            return clauses.iter().all(|c| {
                matches!(
                    &c.pattern,
                    WhenPattern::Constructor {
                        type_hint: None,
                        ..
                    }
                )
            });
        }
        children(expr)
            .into_iter()
            .any(|c| find_unattributed_when(c, seed_subject))
    }
    assert!(
        find_unattributed_when(&out, 1),
        "rebuilt patterns must be type-unattributed"
    );
}
