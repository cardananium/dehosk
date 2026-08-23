use super::*;

const SUBJ: u32 = 1;

fn subj_var() -> PseudoExpr {
    PseudoExpr::var_with_id("xs", VarId::new(SUBJ))
}
fn xs_head() -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: PBox::new(subj_var()),
        selector: FieldSelector::ListHead,
    }
}
fn xs_tail() -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::ListTail,
        args: vec![subj_var()].into(),
    }
}
fn cons_pat() -> WhenPattern {
    WhenPattern::List {
        elements: vec![Binder::from("_".to_string())],
        tail: Some(Binder::from("_".to_string())),
    }
}
/// `when xs is { [] -> nil; [_, ..] -> cons }`
fn when_over_xs(cons: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(subj_var()),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::var("nil"),
            ),
            WhenClause::new(cons_pat(), cons),
        ],
    }
}

fn cons_arm(out: &PseudoExpr) -> &WhenClause {
    let PseudoExpr::When { clauses, .. } = out else {
        panic!("expected when");
    };
    &clauses[1]
}
fn pattern_binders(clause: &WhenClause) -> (String, String) {
    let WhenPattern::List {
        elements,
        tail: Some(t),
    } = &clause.pattern
    else {
        panic!("expected list pattern");
    };
    (elements[0].name.clone(), t.name.clone())
}

#[test]
fn binds_head_and_tail_and_substitutes() {
    // [_, ..] -> [f(xs.head), ..step(xs[1..])]
    let cons = PseudoExpr::List {
        elements: vec![PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![xs_head()].into(),
        }]
        .into(),
        tail: Some(PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("step")),
            args: vec![xs_tail()].into(),
        })),
    };
    let out = bind_list_cons_head_tail(when_over_xs(cons));
    let arm = cons_arm(&out);
    assert_eq!(
        pattern_binders(arm),
        ("head".to_string(), "tail".to_string())
    );
    // Body must reference the new binders, not the accessors.
    let PseudoExpr::List {
        elements,
        tail: Some(t),
    } = &arm.body
    else {
        panic!("expected cons cell");
    };
    let PseudoExpr::Apply {
        args: head_args, ..
    } = &elements[0]
    else {
        panic!("expected f(..)");
    };
    assert!(
        matches!(&head_args[0], PseudoExpr::Var { id: Some(v), name } if name == "head" && *v != VarId::new(SUBJ)),
        "head access should be the new `head` binder, got {:?}",
        head_args[0]
    );
    let PseudoExpr::Apply {
        args: tail_args, ..
    } = t.as_ref()
    else {
        panic!("expected step(..)");
    };
    assert!(
        matches!(&tail_args[0], PseudoExpr::Var { name, .. } if name == "tail"),
        "tail access should be the new `tail` binder, got {:?}",
        tail_args[0]
    );
}

#[test]
fn binds_only_head_when_tail_unused() {
    // [_, ..] -> g(xs.head)  (no tail access)
    let cons = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("g")),
        args: vec![xs_head()].into(),
    };
    let out = bind_list_cons_head_tail(when_over_xs(cons));
    // head renamed, tail left wildcard.
    assert_eq!(
        pattern_binders(cons_arm(&out)),
        ("head".to_string(), "_".to_string())
    );
}

#[test]
fn nested_xs_head_fst_substitutes_through() {
    // [_, ..] -> un_b_data(xs.head.fst)  →  head.fst
    let cons = PseudoExpr::BuiltinCall {
        name: BuiltinId::ListTail, // placeholder builtin; just need a wrapper
        args: vec![PseudoExpr::FieldAccess {
            record: PBox::new(xs_head()),
            selector: FieldSelector::PairFst,
        }]
        .into(),
    };
    let out = bind_list_cons_head_tail(when_over_xs(cons));
    let arm = cons_arm(&out);
    // head bound (the .fst access lives on xs.head); tail not used here.
    assert_eq!(pattern_binders(arm).0, "head");
    let PseudoExpr::BuiltinCall { args, .. } = &arm.body else {
        panic!("expected wrapper");
    };
    let PseudoExpr::FieldAccess { record, selector } = &args[0] else {
        panic!("expected .fst access");
    };
    assert_eq!(*selector, FieldSelector::PairFst);
    assert!(
        matches!(record.as_ref(), PseudoExpr::Var { name, .. } if name == "head"),
        "xs.head.fst should become head.fst, got {:?}",
        record
    );
}

#[test]
fn no_accessor_use_leaves_pattern_unchanged() {
    // [_, ..] -> 0  (neither head nor tail accessed)
    let out = bind_list_cons_head_tail(when_over_xs(PseudoExpr::int(0)));
    assert_eq!(
        pattern_binders(cons_arm(&out)),
        ("_".to_string(), "_".to_string())
    );
}

#[test]
fn does_not_substitute_outer_head_inside_a_nested_when() {
    // Outer `when xs is { [_, ..] -> when ys is { [_, ..] -> Pair(xs.head, ys.head) } }`.
    // The inner `ys.head` rebinds to the inner `head`; the OUTER `xs.head`
    // lives inside the nested `when`, so it must be LEFT as `xs.head`
    // (substituting it would render `Pair(head, head)` — name capture).
    // With its only use shielded, the outer head binder stays `_`.
    let ys = PseudoExpr::var_with_id("ys", VarId::new(2));
    let ys_head = PseudoExpr::FieldAccess {
        record: PBox::new(ys.clone()),
        selector: FieldSelector::ListHead,
    };
    let inner_when = PseudoExpr::When {
        subject: PBox::new(ys),
        subject_name: None,
        clauses: vec![WhenClause::new(
            cons_pat(),
            PseudoExpr::Pair(PBox::new(xs_head()), PBox::new(ys_head)),
        )],
    };
    let out = bind_list_cons_head_tail(when_over_xs(inner_when));
    // Outer pattern unchanged: `xs.head` was only used inside the nested when.
    assert_eq!(
        pattern_binders(cons_arm(&out)),
        ("_".to_string(), "_".to_string())
    );
    // Inner when rebound to `[head, ..]`, and its body keeps the OUTER
    // access as `xs.head` (a Var with the subject id — NOT renamed `head`).
    let PseudoExpr::When {
        clauses: inner_clauses,
        ..
    } = &cons_arm(&out).body
    else {
        panic!("expected nested when preserved");
    };
    assert_eq!(
        pattern_binders(&inner_clauses[0]).0,
        "head",
        "inner head should be bound"
    );
    let PseudoExpr::Pair(a, _) = &inner_clauses[0].body else {
        panic!("expected Pair body");
    };
    assert!(
        matches!(
            a.as_ref(),
            PseudoExpr::FieldAccess { record, selector: FieldSelector::ListHead }
                if is_var(record, VarId::new(SUBJ))
        ),
        "outer xs.head must remain an accessor (not captured by inner `head`), got {:?}",
        a
    );
}

#[test]
fn reuses_named_tail_binder_when_body_reslices() {
    // `[head, ..tail] -> helper(xs[1..])` — the tail is ALREADY NAMED but the
    // body re-slices `xs[1..]` instead of using it. Rewire `xs[1..]` to the
    // bound `tail` (reusing its name, not a wildcard rename).
    let named_cons = WhenPattern::List {
        elements: vec![Binder::from("head".to_string())],
        tail: Some(Binder::from("tail".to_string())),
    };
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("helper")),
        args: vec![xs_tail()].into(),
    };
    let when = PseudoExpr::When {
        subject: PBox::new(subj_var()),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::var("nil"),
            ),
            WhenClause::new(named_cons, body),
        ],
    };
    let out = bind_list_cons_head_tail(when);
    let arm = cons_arm(&out);
    // Named binders kept as-is (head/tail), not wildcard-renamed.
    assert_eq!(
        pattern_binders(arm),
        ("head".to_string(), "tail".to_string())
    );
    let PseudoExpr::Apply { args, .. } = &arm.body else {
        panic!("expected helper(..)");
    };
    assert!(
        matches!(&args[0], PseudoExpr::Var { name, .. } if name == "tail"),
        "xs[1..] should be rewired to the bound `tail`, got {:?}",
        args[0]
    );
}

#[test]
fn does_not_capture_subj_slice_inside_a_shadowing_let() {
    // `[head, ..tail] -> { let tail = foo; bar(subj[1..]) }` — the inner
    // `let tail` shadows the target name, so substituting `subj[1..]` → `tail`
    // would be captured by it. The `subj[1..]` must be LEFT as an accessor.
    let inner = PseudoExpr::Let {
        name: "tail".to_string(),
        id: Some(VarId::new(500)),
        value: PBox::new(PseudoExpr::var("foo")),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("bar")),
            args: vec![xs_tail()].into(),
        }),
    };
    let when = PseudoExpr::When {
        subject: PBox::new(subj_var()),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                PseudoExpr::var("nil"),
            ),
            WhenClause::new(
                WhenPattern::List {
                    elements: vec![Binder::from("head".to_string())],
                    tail: Some(Binder::from("tail".to_string())),
                },
                inner,
            ),
        ],
    };
    let out = bind_list_cons_head_tail(when);
    let PseudoExpr::Let { body, .. } = &cons_arm(&out).body else {
        panic!("expected let body");
    };
    let PseudoExpr::Apply { args, .. } = body.as_ref() else {
        panic!("expected bar(..)");
    };
    assert!(
        matches!(&args[0], PseudoExpr::BuiltinCall { name, .. } if *name == BuiltinId::ListTail),
        "subj[1..] inside a shadowing `let tail` must NOT be substituted, got {:?}",
        args[0]
    );
}

#[test]
fn non_var_subject_is_skipped() {
    // when f(x) is { ... } — subject is not a plain Var → no rebind.
    let when = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("f")),
            args: vec![PseudoExpr::var("x")].into(),
        }),
        subject_name: None,
        clauses: vec![WhenClause::new(
            cons_pat(),
            PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("g")),
                args: vec![PseudoExpr::FieldAccess {
                    record: PBox::new(PseudoExpr::var("anything")),
                    selector: FieldSelector::ListHead,
                }]
                .into(),
            },
        )],
    };
    let out = bind_list_cons_head_tail(when.clone());
    assert_eq!(out, when, "non-Var subject must be untouched");
}
