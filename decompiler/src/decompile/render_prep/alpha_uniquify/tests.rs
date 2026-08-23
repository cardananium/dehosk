use super::*;

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

/// Two sibling lets with the SAME id (the clone shape): the second
/// re-mints; each body keeps referring to its own binder.
#[test]
fn sibling_duplicate_lets_split() {
    let mk = |val: i64, body_extra: PseudoExpr| PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(PseudoExpr::int(val)),
        body: PBox::new(PseudoExpr::Pair(
            PBox::new(varref("x", 7)),
            PBox::new(body_extra),
        )),
    };
    let input =
        PseudoExpr::Tuple((vec![mk(1, PseudoExpr::int(0)), mk(2, PseudoExpr::int(0))]).into());
    let out = uniquify_duplicate_binders(input);
    assert_eq!(count_duplicate_binder_ids(&out), 0);
    let PseudoExpr::Tuple(items) = &out else {
        panic!()
    };
    let ids: Vec<Option<VarId>> = items
        .iter()
        .map(|l| match l {
            PseudoExpr::Let { id, body, .. } => {
                // ref inside each body must match its own let id
                let PseudoExpr::Pair(a, _) = body.as_ref() else {
                    panic!()
                };
                let PseudoExpr::Var { id: rid, .. } = a.as_ref() else {
                    panic!()
                };
                assert_eq!(rid, id, "scope ref must follow the re-mint");
                *id
            }
            _ => panic!(),
        })
        .collect();
    assert_ne!(ids[0], ids[1]);
    assert_eq!(ids[0], Some(VarId::new(7)), "first occurrence keeps its id");
}

/// A nested duplicate: outer let X, inner pattern binder with the same
/// id. The inner re-mints; refs in the clause body follow the inner
/// binder (lexical shadowing semantics), refs outside stay on the outer.
#[test]
fn nested_duplicate_pattern_binder() {
    let input = PseudoExpr::Let {
        name: "outer".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Pair(
            PBox::new(varref("outer", 7)),
            PBox::new(PseudoExpr::When {
                subject: PBox::new(varref("s", 1)),
                subject_name: None,
                clauses: vec![WhenClause {
                    pattern: WhenPattern::Var(binder("inner", 7)),
                    guard: None,
                    body: varref("inner", 7),
                }],
            }),
        )),
    };
    let out = uniquify_duplicate_binders(input);
    assert_eq!(count_duplicate_binder_ids(&out), 0);
    let PseudoExpr::Let {
        id: outer_id, body, ..
    } = &out
    else {
        panic!()
    };
    assert_eq!(*outer_id, Some(VarId::new(7)));
    let PseudoExpr::Pair(outer_ref, when) = body.as_ref() else {
        panic!()
    };
    assert!(
        matches!(outer_ref.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == VarId::new(7)),
        "outer ref untouched"
    );
    let PseudoExpr::When { clauses, .. } = when.as_ref() else {
        panic!()
    };
    let WhenPattern::Var(inner) = &clauses[0].pattern else {
        panic!()
    };
    assert_ne!(inner.id, VarId::new(7), "inner duplicate re-minted");
    assert!(
        matches!(&clauses[0].body, PseudoExpr::Var { id: Some(v), .. } if *v == inner.id),
        "clause-body ref follows the re-minted inner binder"
    );
}

/// `let f = rec fn f` same-id pair is ONE binder — never split, and a
/// re-mint (when the pair itself is a duplicate) moves both together.
#[test]
fn let_recfn_pair_stays_collapsed() {
    let pair = |id: u32| PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(id)),
        value: PBox::new(PseudoExpr::RecFn {
            name: binder("f", id),
            params: vec![binder("x", 100 + id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(varref("f", id)),
                args: vec![varref("x", 100 + id)].into(),
            }),
        }),
        body: PBox::new(varref("f", id)),
    };
    // Two copies of the same pair (the clone shape).
    let input = PseudoExpr::Tuple((vec![pair(7), pair(7)]).into());
    let out = uniquify_duplicate_binders(input);
    assert_eq!(count_duplicate_binder_ids(&out), 0);
    let PseudoExpr::Tuple(items) = &out else {
        panic!()
    };
    for item in items {
        let PseudoExpr::Let {
            id, value, body, ..
        } = item
        else {
            panic!()
        };
        let PseudoExpr::RecFn {
            name, body: rbody, ..
        } = value.as_ref()
        else {
            panic!()
        };
        assert_eq!(Some(name.id), *id, "pair stays collapsed");
        let PseudoExpr::Apply { function, .. } = rbody.as_ref() else {
            panic!()
        };
        assert!(
            matches!(function.as_ref(), PseudoExpr::Var { id: Some(v), .. } if Some(*v) == *id),
            "self-call follows the pair"
        );
        assert!(
            matches!(body.as_ref(), PseudoExpr::Var { id: Some(v), .. } if Some(*v) == *id),
            "outer ref follows the pair"
        );
    }
}

/// Display names are never touched.
#[test]
fn names_untouched() {
    let mk = || PseudoExpr::Lambda {
        params: vec![binder("p", 9)],
        body: PBox::new(varref("p", 9)),
    };
    let out = uniquify_duplicate_binders(PseudoExpr::Pair(PBox::new(mk()), PBox::new(mk())));
    let PseudoExpr::Pair(_, second) = &out else {
        panic!()
    };
    let PseudoExpr::Lambda { params, body } = second.as_ref() else {
        panic!()
    };
    assert_eq!(params[0].name, "p");
    assert!(
        matches!(body.as_ref(), PseudoExpr::Var { name, id: Some(v) }
        if name == "p" && *v == params[0].id && *v != VarId::new(9))
    );
}

/// Idempotence: a second application changes nothing.
#[test]
fn idempotent() {
    let mk = || PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(VarId::new(3)),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(varref("x", 3)),
    };
    let once = uniquify_duplicate_binders(PseudoExpr::Pair(PBox::new(mk()), PBox::new(mk())));
    let twice = uniquify_duplicate_binders(once.clone());
    assert_eq!(twice, once);
}
