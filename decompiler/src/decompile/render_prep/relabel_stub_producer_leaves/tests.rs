use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::constructor::KnownConstructor;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn known_nullary(kc: KnownConstructor) -> PseudoExpr {
    PseudoExpr::constr_known(kc, Vec::new())
}

fn raw(tag: usize, arity: usize) -> PseudoExpr {
    raw_constr(tag, (0..arity).map(PseudoExpr::int).collect())
}

fn ctor_pat(tag: usize, arity: usize) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag,
        fields: (0..arity)
            .map(|i| binder(&format!("p{i}"), 800 + i as u32))
            .collect(),
        shape: ConstructorShape::unknown_data(tag, arity),
    }
}

fn with_marker(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "decompiled".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("ctx", 2)],
            body: PBox::new(body),
        }),
        body: PBox::new(varref("decompiled", 1)),
    }
}

/// Producer leaves Nil/None/Constr<2>×3 flow exclusively into a
/// `when Unknown_S_* {0,1,2×3}`; all three become raw Constr matching
/// the consumer tags.
fn inverse_polarity_shape() -> PseudoExpr {
    // fn f_13(x_38) { if b { Nil } else if b { None } else { Constr<2>(a,b,c) } }
    let f_13 = PseudoExpr::Lambda {
        params: vec![binder("x_38", 30)],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Bool(true)),
            then_branch: PBox::new(known_nullary(KnownConstructor::Nil)),
            else_branch: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::Bool(true)),
                then_branch: PBox::new(known_nullary(KnownConstructor::None)),
                else_branch: PBox::new(raw(2, 3)),
            }),
        }),
    };
    // fn f_14(x_37) { if b { f_13(x) } else { f_13(y) } }
    let f_14 = PseudoExpr::Lambda {
        params: vec![binder("x_37", 31)],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Bool(true)),
            then_branch: PBox::new(PseudoExpr::Apply {
                function: PBox::new(varref("f_13", 13)),
                args: vec![PseudoExpr::int(0)].into(),
            }),
            else_branch: PBox::new(PseudoExpr::Apply {
                function: PBox::new(varref("f_13", 13)),
                args: vec![PseudoExpr::int(1)].into(),
            }),
        }),
    };
    // let match_subject = if b { f_14(0) } else { f_14(1) }
    let match_subject = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Bool(true)),
        then_branch: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("f_14", 14)),
            args: vec![PseudoExpr::int(0)].into(),
        }),
        else_branch: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("f_14", 14)),
            args: vec![PseudoExpr::int(1)].into(),
        }),
    };
    let consumer = PseudoExpr::When {
        subject: PBox::new(varref("match_subject", 50)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: ctor_pat(0, 0),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: ctor_pat(1, 0),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: ctor_pat(2, 3),
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    with_marker(PseudoExpr::Let {
        name: "f_13".to_string(),
        id: Some(VarId::new(13)),
        value: PBox::new(f_13),
        body: PBox::new(PseudoExpr::Let {
            name: "f_14".to_string(),
            id: Some(VarId::new(14)),
            value: PBox::new(f_14),
            body: PBox::new(PseudoExpr::Let {
                name: "match_subject".to_string(),
                id: Some(VarId::new(50)),
                value: PBox::new(match_subject),
                body: PBox::new(consumer),
            }),
        }),
    })
}

#[test]
fn witness_finds_producer_chain() {
    let input = inverse_polarity_shape();
    let ws = collect_stub_producer_witnesses(&input);
    assert_eq!(ws.len(), 1, "one witness expected");
    let w = &ws[0];
    assert_eq!(w.scrutinee, VarId::new(50));
    assert!(w.producer_fns.contains(&VarId::new(14)));
    assert!(w.producer_fns.contains(&VarId::new(13)));
    assert_eq!(w.variants.get(&0), Some(&0));
    assert_eq!(w.variants.get(&1), Some(&0));
    assert_eq!(w.variants.get(&2), Some(&3));
}

#[test]
fn relabels_nil_and_none_leaves_to_raw() {
    let input = inverse_polarity_shape();
    let out = relabel_stub_producer_leaves(input);
    let rendered = format!("{out:?}");
    // No Known(Nil)/Known(None) leaves survive in f_13.
    assert!(
        !rendered.contains("Known(Nil)"),
        "Nil leaf must revert to raw Constr: {rendered}"
    );
    assert!(
        !rendered.contains("Known(None)"),
        "None leaf must revert to raw Constr: {rendered}"
    );
    // Raw tag0 + tag1 nullary Constrs now present.
    assert!(rendered.contains("tag: 0"));
    assert!(rendered.contains("tag: 1"));
}

/// No exclusive-flow witness (subject used twice) → nothing relabeled.
#[test]
fn non_exclusive_flow_not_touched() {
    // Producer feeds a `when` but the subject is also referenced
    // elsewhere → ref_count > 1 → no witness.
    let producer = PseudoExpr::Lambda {
        params: vec![binder("x", 30)],
        body: PBox::new(known_nullary(KnownConstructor::Nil)),
    };
    let consumer = PseudoExpr::When {
        subject: PBox::new(varref("s", 50)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: ctor_pat(0, 0),
                guard: None,
                body: varref("s", 50),
            },
            WhenClause {
                pattern: ctor_pat(1, 2),
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    let input = with_marker(PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(13)),
        value: PBox::new(producer),
        body: PBox::new(PseudoExpr::Let {
            name: "s".to_string(),
            id: Some(VarId::new(50)),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(varref("f", 13)),
                args: vec![PseudoExpr::int(0)].into(),
            }),
            body: PBox::new(consumer),
        }),
    });
    let out = relabel_stub_producer_leaves(input.clone());
    assert_eq!(out, input, "subject referenced twice → no relabel");
}

/// A genuine two-variant `Some/None` consumer presents `Known` patterns,
/// not raw Constr → the pass does not fire (Option pass owns that).
#[test]
fn known_option_consumer_not_a_stub_sum() {
    let clauses = vec![
        WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 0,
                fields: vec![binder("v", 900)],
                shape: ConstructorShape::Known(KnownConstructor::Some),
            },
            guard: None,
            body: PseudoExpr::Unit,
        },
        WhenClause {
            pattern: WhenPattern::Constructor {
                type_hint: None,
                tag: 1,
                fields: vec![],
                shape: ConstructorShape::Known(KnownConstructor::None),
            },
            guard: None,
            body: PseudoExpr::Unit,
        },
    ];
    assert!(raw_stub_sum_variants(&clauses).is_none());
}

/// PRODUCER-EXCLUSIVITY: a producer fn that ALSO flows into another
/// consumer (global ref count > in-chain calls) must NOT be relabeled —
/// its genuine Nil/None leaves belong to that other consumer.
#[test]
fn shared_producer_fn_not_relabeled() {
    // fn f(x) { if b { Nil } else { Constr<2>(a,b,c) } }  (returns a sum)
    let f = PseudoExpr::Lambda {
        params: vec![binder("x", 30)],
        body: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::Bool(true)),
            then_branch: PBox::new(known_nullary(KnownConstructor::Nil)),
            else_branch: PBox::new(raw(2, 3)),
        }),
    };
    // stub-sum consumer on s = f(0)
    let stub_consumer = PseudoExpr::When {
        subject: PBox::new(varref("s", 50)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: ctor_pat(0, 0),
                guard: None,
                body: PseudoExpr::Unit,
            },
            WhenClause {
                pattern: ctor_pat(2, 3),
                guard: None,
                body: PseudoExpr::Unit,
            },
        ],
    };
    // f is ALSO called elsewhere: let t = f(1) → escapes the chain.
    let input = with_marker(PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(13)),
        value: PBox::new(f),
        body: PBox::new(PseudoExpr::Let {
            name: "s".to_string(),
            id: Some(VarId::new(50)),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(varref("f", 13)),
                args: vec![PseudoExpr::int(0)].into(),
            }),
            body: PBox::new(PseudoExpr::Let {
                name: "t".to_string(),
                id: Some(VarId::new(51)),
                value: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(varref("f", 13)),
                    args: vec![PseudoExpr::int(1)].into(),
                }),
                // use t so it isn't dead, and keep the stub consumer.
                body: PBox::new(PseudoExpr::Let {
                    name: "_u".to_string(),
                    id: Some(VarId::new(52)),
                    value: PBox::new(varref("t", 51)),
                    body: PBox::new(stub_consumer),
                }),
            }),
        }),
    });
    // No witness: f's global ref count (2) exceeds its in-chain calls (1).
    assert!(collect_stub_producer_witnesses(&input).is_empty());
    let out = relabel_stub_producer_leaves(input.clone());
    assert_eq!(out, input, "shared producer must not be relabeled");
}

/// A single-variant nullary stub (Bool/Void territory) is not a target.
#[test]
fn single_nullary_variant_rejected() {
    let clauses = vec![WhenClause {
        pattern: ctor_pat(1, 0),
        guard: None,
        body: PseudoExpr::Unit,
    }];
    assert!(raw_stub_sum_variants(&clauses).is_none());
}
