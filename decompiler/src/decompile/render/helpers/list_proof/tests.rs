use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn un_list_data(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnList,
        args: vec![arg].into(),
    }
}

fn tail_list_apply_form(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: BuiltinId::ListTail,
            args: vec![].into(),
        }),
        args: vec![arg].into(),
    }
}

fn call(fid: u32, fname: &str, args: Vec<PseudoExpr>) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(varref(fname, fid)),
        args: args.into(),
    }
}

/// `let f = fn(p) { p[0] }; f(un_list_data(d))` — p joins S.
#[test]
fn param_proven_when_every_call_site_passes_list() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("p", 2)],
            body: PBox::new(PseudoExpr::IndexAccess {
                collection: PBox::new(varref("p", 2)),
                index: 0,
            }),
        }),
        body: PBox::new(call(
            1,
            "f",
            vec![un_list_data(PseudoExpr::var_with_id("d", VarId::new(9)))],
        )),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(s.contains(&VarId::new(2)));
}

/// `let f = rec fn g(p) { when p is { [] -> 0; [h, ..t] -> g(t) } };
/// f(un_list_data(d))` — alias merge (g→f) + rule (b): p AND t join.
#[test]
fn recursive_self_call_participates() {
    let when = PseudoExpr::When {
        subject: PBox::new(varref("p", 3)),
        subject_name: None,
        clauses: vec![
            crate::pseudo::ast::WhenClause {
                pattern: WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                guard: None,
                body: PseudoExpr::int(0),
            },
            crate::pseudo::ast::WhenClause {
                pattern: WhenPattern::List {
                    elements: vec![binder("h", 4)],
                    tail: Some(binder("t", 5)),
                },
                guard: None,
                body: call(2, "g", vec![varref("t", 5)]),
            },
        ],
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::RecFn {
            name: binder("g", 2),
            params: vec![binder("p", 3)],
            body: PBox::new(when),
        }),
        body: PBox::new(call(1, "f", vec![un_list_data(varref("d", 9))])),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(s.contains(&VarId::new(3)), "param p must join S");
    assert!(s.contains(&VarId::new(5)), "cons tail t must join S");
    assert!(
        !s.contains(&VarId::new(4)),
        "head element must NEVER join S"
    );
}

/// The fn also appears as a bare value (passed as an arg) — vetoed.
#[test]
fn value_used_fn_vetoed() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("p", 2)],
            body: PBox::new(varref("p", 2)),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                call(1, "f", vec![un_list_data(varref("d", 9))]),
                // bare value use: f stored in a tuple
                varref("f", 1),
            ]
            .into(),
        )),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(2)));
}

/// One call site passes a non-provable arg — vetoed.
#[test]
fn one_bad_call_site_vetoes() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("p", 2)],
            body: PBox::new(varref("p", 2)),
        }),
        body: PBox::new(PseudoExpr::Pair(
            PBox::new(call(1, "f", vec![un_list_data(varref("d", 9))])),
            PBox::new(call(1, "f", vec![varref("opaque", 10)])),
        )),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(2)));
}

/// An fn whose ONLY calls are self-calls (no grounded external entry)
/// must not prove its params — self-evidence cannot stand alone.
#[test]
fn self_only_calls_veto() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::RecFn {
            name: binder("g", 2),
            params: vec![binder("p", 3)],
            body: PBox::new(call(2, "g", vec![tail_list_apply_form(varref("p", 3))])),
        }),
        body: PBox::new(PseudoExpr::int(0)),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(3)));
}

/// Zero call sites: the all-quantifier must not be vacuously true.
#[test]
fn zero_call_sites_vetoes() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("p", 2)],
            body: PBox::new(varref("p", 2)),
        }),
        body: PBox::new(PseudoExpr::int(0)),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(2)));
}

/// Partial application (arity mismatch) vetoes the whole fn.
#[test]
fn arity_mismatch_vetoes() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("p", 2), binder("q", 3)],
            body: PBox::new(varref("p", 2)),
        }),
        body: PBox::new(PseudoExpr::Pair(
            PBox::new(call(
                1,
                "f",
                vec![un_list_data(varref("d", 9)), un_list_data(varref("e", 10))],
            )),
            // partial application — escaping closure
            PBox::new(call(1, "f", vec![un_list_data(varref("d", 9))])),
        )),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(2)));
    assert!(!s.contains(&VarId::new(3)));
}

/// Rule (a)+(b) chain: `let a = un_list_data(d); f(a)` with
/// `f = fn(p) { let b = p; b[0] }` — a, p, b all join (multi-round).
#[test]
fn chain_let_param_let() {
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(un_list_data(varref("d", 9))),
        body: PBox::new(PseudoExpr::Let {
            name: "f".to_string(),
            id: Some(VarId::new(2)),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![binder("p", 3)],
                body: PBox::new(PseudoExpr::Let {
                    name: "b".to_string(),
                    id: Some(VarId::new(4)),
                    value: PBox::new(varref("p", 3)),
                    body: PBox::new(PseudoExpr::IndexAccess {
                        collection: PBox::new(varref("b", 4)),
                        index: 0,
                    }),
                }),
            }),
            body: PBox::new(call(2, "f", vec![varref("a", 1)])),
        }),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(s.contains(&VarId::new(1)));
    assert!(s.contains(&VarId::new(3)));
    assert!(s.contains(&VarId::new(4)));
}

/// An id-less `Var { id: None }` sharing the fn's name anywhere vetoes
/// — including the REC-FN INNER name, not just the let name.
#[test]
fn idless_var_name_vetoes_either_name() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::RecFn {
            name: binder("g", 2),
            params: vec![binder("p", 3)],
            body: PBox::new(varref("p", 3)),
        }),
        body: PBox::new(PseudoExpr::Pair(
            PBox::new(call(1, "f", vec![un_list_data(varref("d", 9))])),
            // unattributable name-only reference to the INNER name
            PBox::new(PseudoExpr::var("g")),
        )),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(3)));
}

/// Any `Raw` node anywhere disables ALL param proofs (closed-world
/// break) but leaves let-binder proofs intact.
#[test]
fn raw_anywhere_vetoes_all_params_but_not_lets() {
    let expr = PseudoExpr::Let {
        name: "a".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(un_list_data(varref("d", 9))),
        body: PBox::new(PseudoExpr::Let {
            name: "f".to_string(),
            id: Some(VarId::new(2)),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![binder("p", 3)],
                body: PBox::new(varref("p", 3)),
            }),
            body: PBox::new(PseudoExpr::Pair(
                PBox::new(call(2, "f", vec![varref("a", 1)])),
                PBox::new(PseudoExpr::Raw {
                    uplc: "(opaque)".to_string(),
                    reason: "test".to_string(),
                }),
            )),
        }),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(s.contains(&VarId::new(1)), "rule (a) unaffected by Raw");
    assert!(!s.contains(&VarId::new(3)), "rule (c) disabled by Raw");
}

/// Ungrounded mutual recursion: f(x) { g(x) }, g(y) { f(y) }, no external
/// callers — neither param may join (the least fixpoint from empty S is
/// grounded). With tail_list-wrapped cycle args they DO join (sound:
/// applied tail_list yields a list or diverges).
#[test]
fn mutual_recursion_groundedness() {
    let build = |wrap: bool| {
        let g_arg = if wrap {
            tail_list_apply_form(varref("x", 2))
        } else {
            varref("x", 2)
        };
        let f_arg = if wrap {
            tail_list_apply_form(varref("y", 4))
        } else {
            varref("y", 4)
        };
        PseudoExpr::Let {
            name: "f".to_string(),
            id: Some(VarId::new(1)),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![binder("x", 2)],
                body: PBox::new(call(3, "g", vec![g_arg])),
            }),
            body: PBox::new(PseudoExpr::Let {
                name: "g".to_string(),
                id: Some(VarId::new(3)),
                value: PBox::new(PseudoExpr::Lambda {
                    params: vec![binder("y", 4)],
                    body: PBox::new(call(1, "f", vec![f_arg])),
                }),
                body: PBox::new(PseudoExpr::int(0)),
            }),
        }
    };
    let bare = collect_provably_list_var_ids(&build(false));
    assert!(!bare.contains(&VarId::new(2)) && !bare.contains(&VarId::new(4)));
    let wrapped = collect_provably_list_var_ids(&build(true));
    assert!(wrapped.contains(&VarId::new(2)) && wrapped.contains(&VarId::new(4)));
}

/// The Apply spelling of an applied list builtin proves a let:
/// `let j = Apply(BuiltinCall(ListTail, []), [x])`.
#[test]
fn apply_form_tail_list_proves() {
    let expr = PseudoExpr::Let {
        name: "j".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(tail_list_apply_form(un_list_data(varref("d", 9)))),
        body: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(varref("j", 1)),
            index: 0,
        }),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(s.contains(&VarId::new(1)));
}

/// when-tail rule negatives: unproven subject ⇒ tail not in S.
#[test]
fn when_tail_requires_proven_subject() {
    let expr = PseudoExpr::When {
        subject: PBox::new(varref("opaque", 1)),
        subject_name: None,
        clauses: vec![crate::pseudo::ast::WhenClause {
            pattern: WhenPattern::List {
                elements: vec![binder("h", 2)],
                tail: Some(binder("t", 3)),
            },
            guard: None,
            body: PseudoExpr::int(0),
        }],
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(3)));
}

/// Cons-Constructor-encoded pattern over a PROVEN subject: fields[1]
/// (the tail) joins, fields[0] (the head) never does.
#[test]
fn cons_constructor_pattern_tail() {
    let expr = PseudoExpr::Let {
        name: "xs".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(un_list_data(varref("d", 9))),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(varref("xs", 1)),
            subject_name: None,
            clauses: vec![crate::pseudo::ast::WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 1,
                    fields: vec![binder("h", 2), binder("t", 3)],
                    shape: ConstructorShape::Known(KnownConstructor::Cons),
                },
                guard: None,
                body: PseudoExpr::int(0),
            }],
        }),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(s.contains(&VarId::new(3)));
    assert!(!s.contains(&VarId::new(2)));
}

/// A fn that passes ITSELF as a call arg is value-used — vetoed.
#[test]
fn self_passing_fn_vetoed() {
    // let f = rec fn g(x, k) { k(x, g) }; f(un_list_data(d), cb)
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::RecFn {
            name: binder("g", 2),
            params: vec![binder("x", 3), binder("k", 4)],
            body: PBox::new(call(4, "k", vec![varref("x", 3), varref("g", 2)])),
        }),
        body: PBox::new(call(
            1,
            "f",
            vec![un_list_data(varref("d", 9)), varref("cb", 10)],
        )),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(3)));
}

/// Alias-merge trap: external call via the LET name passes a NON-list;
/// self-calls via the REC name pass tail_list — the merged call set must
/// veto (two separate records would wrongly prove via self-calls alone).
#[test]
fn alias_merged_calls_veto_external_non_list() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::RecFn {
            name: binder("g", 2),
            params: vec![binder("p", 3)],
            body: PBox::new(call(2, "g", vec![tail_list_apply_form(varref("p", 3))])),
        }),
        body: PBox::new(call(1, "f", vec![varref("some_tuple", 9)])),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(3)));
}

/// A VarId bound by TWO binders (a let and a same-id when-pattern
/// binder) is CONFLICTED: it never enters S even though the let's
/// value is provably a list.
#[test]
fn colliding_binder_id_never_proves() {
    let collided = VarId::new(7);
    let expr = PseudoExpr::Let {
        name: "xs".to_string(),
        id: Some(collided),
        value: PBox::new(un_list_data(varref("d", 9))),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(varref("opaque", 1)),
            subject_name: None,
            clauses: vec![crate::pseudo::ast::WhenClause {
                // an UNRELATED pattern binder carrying the same id
                pattern: WhenPattern::Var(binder("field_0_2", 7)),
                guard: None,
                body: PseudoExpr::int(0),
            }],
        }),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&collided));
}

/// Return join: `let r = f(xs)` proves when f's every
/// return leaf is its proven list param / a list literal / an
/// exact-arity self-call (with >=1 grounded leaf).
#[test]
fn return_join_proves_call_result_let() {
    // let f = rec fn g(p) { when p is { [] -> []; [h,..t] -> g(t) } };
    // let r = f(un_list_data(d)); r[0]
    let f_body = PseudoExpr::When {
        subject: PBox::new(varref("p", 3)),
        subject_name: None,
        clauses: vec![
            crate::pseudo::ast::WhenClause {
                pattern: WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                guard: None,
                body: PseudoExpr::List {
                    elements: vec![].into(),
                    tail: None,
                },
            },
            crate::pseudo::ast::WhenClause {
                pattern: WhenPattern::List {
                    elements: vec![binder("h", 4)],
                    tail: Some(binder("t", 5)),
                },
                guard: None,
                body: call(2, "g", vec![varref("t", 5)]),
            },
        ],
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::RecFn {
            name: binder("g", 2),
            params: vec![binder("p", 3)],
            body: PBox::new(f_body),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(VarId::new(6)),
            value: PBox::new(call(1, "f", vec![un_list_data(varref("d", 9))])),
            body: PBox::new(PseudoExpr::IndexAccess {
                collection: PBox::new(varref("r", 6)),
                index: 0,
            }),
        }),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(
        s.contains(&VarId::new(6)),
        "call-result let must join via the return join"
    );
}

/// A co-recursive return cycle (f returns g(..), g returns f(..)) must
/// NOT prove — induction is strictly self-only.
#[test]
fn return_join_rejects_corecursive_cycle() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("x", 2)],
            body: PBox::new(call(3, "g", vec![varref("x", 2)])),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "g".to_string(),
            id: Some(VarId::new(3)),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![binder("y", 4)],
                body: PBox::new(call(1, "f", vec![varref("y", 4)])),
            }),
            body: PBox::new(PseudoExpr::Let {
                name: "r".to_string(),
                id: Some(VarId::new(5)),
                value: PBox::new(call(1, "f", vec![un_list_data(varref("d", 9))])),
                body: PBox::new(varref("r", 5)),
            }),
        }),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(5)));
}

/// An fn whose every leaf is a self-call (never returns) must not enter
/// the returning set — >=1 grounded non-self leaf required.
#[test]
fn return_join_requires_grounded_leaf() {
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::RecFn {
            name: binder("g", 2),
            params: vec![binder("p", 3)],
            body: PBox::new(call(2, "g", vec![varref("p", 3)])),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(VarId::new(4)),
            value: PBox::new(call(1, "f", vec![un_list_data(varref("d", 9))])),
            body: PBox::new(varref("r", 4)),
        }),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(4)));
}

/// A partial (arity-mismatched) call of a list-returning fn is a
/// closure, not a list — the use-site arity gate vetoes.
#[test]
fn return_join_requires_exact_arity_at_use() {
    // f(a, b) returns [a]; let r = f(x) — partial — must not prove.
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("a", 2), binder("b", 3)],
            body: PBox::new(PseudoExpr::List {
                elements: vec![varref("a", 2)].into(),
                tail: None,
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "r".to_string(),
            id: Some(VarId::new(4)),
            value: PBox::new(call(1, "f", vec![varref("x", 9)])),
            body: PBox::new(varref("r", 4)),
        }),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(!s.contains(&VarId::new(4)));
}

/// Branch-tail join: a let whose value is an if/when
/// statement-block with every non-diverging tail a list literal proves;
/// the expect! display wrapper passes through to its value.
#[test]
fn branch_tail_join_proves() {
    // let z = if c { [1] } else { let v = 0; [2] }; z[0]
    let value = PseudoExpr::If {
        condition: PBox::new(varref("c", 30)),
        then_branch: PBox::new(PseudoExpr::List {
            elements: vec![PseudoExpr::int(1)].into(),
            tail: None,
        }),
        else_branch: PBox::new(PseudoExpr::Let {
            name: "v".to_string(),
            id: Some(VarId::new(31)),
            value: PBox::new(PseudoExpr::int(0)),
            body: PBox::new(PseudoExpr::List {
                elements: vec![PseudoExpr::int(2)].into(),
                tail: None,
            }),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "z".to_string(),
        id: Some(VarId::new(1)),
        value: PBox::new(value),
        body: PBox::new(PseudoExpr::IndexAccess {
            collection: PBox::new(varref("z", 1)),
            index: 0,
        }),
    };
    let s = collect_provably_list_var_ids(&expr);
    assert!(s.contains(&VarId::new(1)));

    // expect!(cond, [1]) proves through to the value.
    let s2 = HashSet::new();
    let ex = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("expect!")),
        args: vec![
            varref("cond", 40),
            PseudoExpr::List {
                elements: vec![PseudoExpr::int(1)].into(),
                tail: None,
            },
        ]
        .into(),
    };
    assert!(is_provably_list_given(&ex, &s2));
}

/// A when with a diverging arm joins over the rest; ALL-diverging has
/// no list evidence and must NOT prove.
#[test]
fn branch_tail_join_diverging_arms() {
    let mk_when = |arm: PseudoExpr| PseudoExpr::When {
        subject: PBox::new(varref("d", 50)),
        subject_name: None,
        clauses: vec![
            crate::pseudo::ast::WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: arm,
            },
            crate::pseudo::ast::WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
        ],
    };
    let s = HashSet::new();
    assert!(is_provably_list_given(
        &mk_when(PseudoExpr::List {
            elements: vec![].into(),
            tail: None
        }),
        &s
    ));
    // non-list non-diverging arm -> veto
    assert!(!is_provably_list_given(&mk_when(PseudoExpr::int(1)), &s));
    // ALL arms diverging -> no evidence -> veto
    let all_fail = PseudoExpr::When {
        subject: PBox::new(varref("d", 50)),
        subject_name: None,
        clauses: vec![crate::pseudo::ast::WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: PseudoExpr::Error { message: None },
        }],
    };
    assert!(!is_provably_list_given(&all_fail, &s));
}

/// A `Tuple` or `Pair` value never proves.
#[test]
fn tuple_pair_never_prove() {
    let s = HashSet::new();
    assert!(!is_provably_list_given(
        &PseudoExpr::Tuple((vec![PseudoExpr::int(1)]).into()),
        &s
    ));
    assert!(!is_provably_list_given(
        &PseudoExpr::Pair(PBox::new(PseudoExpr::int(2)), PBox::new(PseudoExpr::int(2))),
        &s
    ));
}
