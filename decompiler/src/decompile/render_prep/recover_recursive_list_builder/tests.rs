use super::*;
use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn stub(tag: usize, fields: Vec<PseudoExpr>) -> PseudoExpr {
    PseudoExpr::Constr {
        tag,
        shape: ConstructorShape::unknown_data(tag, fields.len()),
        fields: fields.into(),
        type_hint: None,
    }
}

const SELF: u32 = 10;

/// `rec fn o(z) { case_list(Constr<0>, fn(x, y) { Constr<1>(x, o(y)) }, z) }`
/// — the eliminator is a CALL, so the nil sits in argument position.
fn builder(head: PseudoExpr, nil: PseudoExpr) -> PseudoExpr {
    let cons = stub(
        1,
        vec![
            head,
            PseudoExpr::Apply {
                function: PBox::new(var("o", SELF)),
                args: vec![var("y", 12)].into(),
            },
        ],
    );
    PseudoExpr::RecFn {
        name: binder("o", SELF),
        params: vec![binder("z", 11)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("case_list", 99)),
            args: vec![
                nil,
                PseudoExpr::Lambda {
                    params: vec![binder("x", 13), binder("y", 12)],
                    body: PBox::new(cons),
                },
                var("z", 11),
            ]
            .into(),
        }),
    }
}

#[test]
fn recovers_both_arms_of_a_recursive_builder() {
    let out = recover_recursive_list_builder(builder(var("x", 13), stub(0, vec![])));
    let rendered = format!("{out:?}");
    assert!(
        !rendered.contains("Constr {"),
        "both arms must become List nodes: {rendered}"
    );
    assert_eq!(
        rendered.matches("List {").count(),
        2,
        "one nil and one cons spread: {rendered}"
    );
}

/// A `map` builder wraps its head; the cell is still a cons, so both
/// arms still recover — the head simply stays whatever it was.
#[test]
fn recovers_a_mapping_builder_and_leaves_the_head_alone() {
    let mapped = PseudoExpr::Apply {
        function: PBox::new(var("g", 20)),
        args: vec![var("x", 13)].into(),
    };
    let out = recover_recursive_list_builder(builder(mapped, stub(0, vec![])));
    let rendered = format!("{out:?}");
    assert!(rendered.contains("List {"), "{rendered}");
    assert!(
        rendered.contains("\"g\""),
        "the head transform must survive: {rendered}"
    );
}

/// Without the self-call the function is not proven to build a list, so
/// the nullary stub keeps whatever else it means.
#[test]
fn leaves_a_non_recursive_function_alone() {
    let no_recursion = PseudoExpr::RecFn {
        name: binder("o", SELF),
        params: vec![binder("z", 11)],
        body: PBox::new(stub(0, vec![])),
    };
    let out = recover_recursive_list_builder(no_recursion.clone());
    assert_eq!(format!("{out:?}"), format!("{no_recursion:?}"));
}

/// Two parameters is an accumulator, not the `BuiltinList` copy this
/// proof covers.
#[test]
fn leaves_a_two_parameter_function_alone() {
    let PseudoExpr::RecFn { name, body, .. } = builder(var("x", 13), stub(0, vec![])) else {
        panic!("builder returns a RecFn");
    };
    let two_param = PseudoExpr::RecFn {
        name,
        params: vec![binder("z", 11), binder("acc", 14)],
        body,
    };
    let out = recover_recursive_list_builder(two_param.clone());
    assert_eq!(format!("{out:?}"), format!("{two_param:?}"));
}

/// A nested `RecFn` is a different builder with its own base case, so
/// the outer relabel stops at it.
#[test]
fn does_not_relabel_inside_a_nested_recfn() {
    let inner = PseudoExpr::RecFn {
        name: binder("inner", 30),
        params: vec![binder("w", 31)],
        body: PBox::new(stub(0, vec![])),
    };
    let cons = stub(
        1,
        vec![
            inner,
            PseudoExpr::Apply {
                function: PBox::new(var("o", SELF)),
                args: vec![var("y", 12)].into(),
            },
        ],
    );
    let outer = PseudoExpr::RecFn {
        name: binder("o", SELF),
        params: vec![binder("z", 11)],
        body: PBox::new(cons),
    };
    let out = recover_recursive_list_builder(outer);
    let rendered = format!("{out:?}");
    assert!(
        rendered.contains("Constr {"),
        "the nested builder's own nullary stub must survive: {rendered}"
    );
}

/// A head that is a `let` chain would render inline inside the list
/// literal — `[let x = ..\n f(x), ..t]` — so the cell is left as the
/// stub, which at least parses as one expression.
#[test]
fn leaves_a_statement_sequence_head_alone() {
    let stmt_head = PseudoExpr::Let {
        name: "head".to_string(),
        id: Some(VarId::new(40)),
        value: PBox::new(var("y", 12)),
        body: PBox::new(stub(0, vec![var("head", 40), var("head", 40)])),
    };
    let out = recover_recursive_list_builder(builder(stmt_head, stub(0, vec![])));
    let rendered = format!("{out:?}");
    assert!(
        rendered.contains("Constr {"),
        "the cons cell must stay a Constr: {rendered}"
    );
    assert!(
        !rendered.contains("List {"),
        "and its nil must not be relabelled on its own: {rendered}"
    );
}

/// A nullary stub passed as an ARGUMENT inside the cons arm is some
/// other nullary value, not the builder's base case. Calling it `[]`
/// would state something false.
#[test]
fn leaves_a_nullary_stub_in_argument_position_alone() {
    let arg_use = PseudoExpr::Apply {
        function: PBox::new(var("g", 20)),
        args: vec![stub(0, vec![])].into(),
    };
    let cons = stub(
        1,
        vec![
            arg_use,
            PseudoExpr::Apply {
                function: PBox::new(var("o", SELF)),
                args: vec![var("y", 12)].into(),
            },
        ],
    );
    let expr = PseudoExpr::RecFn {
        name: binder("o", SELF),
        params: vec![binder("z", 11)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("case_list", 99)),
            args: vec![
                stub(0, vec![]),
                PseudoExpr::Lambda {
                    params: vec![binder("x", 13), binder("y", 12)],
                    body: PBox::new(cons),
                },
                var("z", 11),
            ]
            .into(),
        }),
    };
    let out = recover_recursive_list_builder(expr);
    let rendered = format!("{out:?}");
    // The nil arm (an eliminator argument beside the cons) recovers…
    assert!(rendered.contains("List {"), "{rendered}");
    // …while `g(Constr<0>)` inside the cons arm keeps its stub.
    assert!(
        rendered.contains("Constr {"),
        "the argument-position stub must survive: {rendered}"
    );
}

/// An ordinary call that merely CONTAINS a cons in one argument is not
/// an eliminator: its other arguments are values, not arms.
#[test]
fn does_not_treat_an_ordinary_call_as_an_eliminator() {
    let cons = stub(
        1,
        vec![
            var("x", 13),
            PseudoExpr::Apply {
                function: PBox::new(var("o", SELF)),
                args: vec![var("y", 12)].into(),
            },
        ],
    );
    // `f(Constr<0>, g(cons))` — no lambda continuation anywhere.
    let call = PseudoExpr::Apply {
        function: PBox::new(var("f", 21)),
        args: vec![
            stub(0, vec![]),
            PseudoExpr::Apply {
                function: PBox::new(var("g", 22)),
                args: vec![cons].into(),
            },
        ]
        .into(),
    };
    let expr = PseudoExpr::RecFn {
        name: binder("o", SELF),
        params: vec![binder("z", 11)],
        body: PBox::new(call),
    };
    let out = recover_recursive_list_builder(expr);
    let rendered = format!("{out:?}");
    // The cons cell still folds — its own tail proves it.
    assert!(rendered.contains("List {"), "{rendered}");
    // The first argument is a value, not a nil arm.
    assert!(
        rendered.contains("Constr {"),
        "an ordinary call's argument must keep its stub: {rendered}"
    );
}

/// A nested `RecFn` calling the OUTER function supplies no evidence for
/// the outer body, which the relabel never visits.
#[test]
fn a_nested_function_does_not_prove_the_outer_one() {
    let inner_cons = stub(
        1,
        vec![
            var("w", 31),
            PseudoExpr::Apply {
                function: PBox::new(var("o", SELF)),
                args: vec![var("w", 31)].into(),
            },
        ],
    );
    let inner = PseudoExpr::RecFn {
        name: binder("inner", 30),
        params: vec![binder("w", 31)],
        body: PBox::new(inner_cons),
    };
    let outer = PseudoExpr::RecFn {
        name: binder("o", SELF),
        params: vec![binder("z", 11)],
        body: PBox::new(PseudoExpr::Let {
            name: "inner".to_string(),
            id: Some(VarId::new(30)),
            value: PBox::new(inner),
            body: PBox::new(stub(0, vec![])),
        }),
    };
    let out = recover_recursive_list_builder(outer);
    let rendered = format!("{out:?}");
    assert!(
        !rendered.contains("List {"),
        "the outer body has no cons of its own: {rendered}"
    );
}

// ---------------------------------------------------------------
// The Scott-encoded forms: `nil = fn(n, _) { n }` (which the naming
// calls `church_true`, since it is also the church True) and
// `cons h t = fn(_, c) { c(h, t) }`.
// ---------------------------------------------------------------

/// `let nil = fn(n, _) { n }; let cons = fn(h, t) { fn(_, c) { c(h, t) } }; body`
fn with_scott_defs(body: PseudoExpr) -> PseudoExpr {
    let n = Binder::new("n".to_string(), VarId::new(900));
    let dead = Binder::new("_".to_string(), VarId::new(901));
    let nil = PseudoExpr::Lambda {
        params: vec![n.clone(), dead],
        body: PBox::new(PseudoExpr::var_with_id("n", VarId::new(900))),
    };
    let h = Binder::new("h".to_string(), VarId::new(902));
    let t = Binder::new("t".to_string(), VarId::new(903));
    let dead2 = Binder::new("_".to_string(), VarId::new(904));
    let c = Binder::new("c".to_string(), VarId::new(905));
    let cons = PseudoExpr::Lambda {
        params: vec![h, t],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![dead2, c],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("c", VarId::new(905))),
                args: vec![
                    PseudoExpr::var_with_id("h", VarId::new(902)),
                    PseudoExpr::var_with_id("t", VarId::new(903)),
                ]
                .into(),
            }),
        }),
    };
    PseudoExpr::Let {
        name: "church_true".to_string(),
        id: Some(VarId::new(910)),
        value: PBox::new(nil),
        body: PBox::new(PseudoExpr::Let {
            name: "church_cons".to_string(),
            id: Some(VarId::new(911)),
            value: PBox::new(cons),
            body: PBox::new(body),
        }),
    }
}

/// `rec fn step(xs) { when xs is { [] -> <nil_arm>; [head, ..tail] -> <cons_arm> } }`
fn scott_builder(nil_arm: PseudoExpr, cons_arm: PseudoExpr) -> PseudoExpr {
    PseudoExpr::RecFn {
        name: Binder::new("step".to_string(), VarId::new(920)),
        params: vec![Binder::new("xs".to_string(), VarId::new(921))],
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("xs", VarId::new(921))),
            subject_name: None,
            clauses: vec![
                WhenClause {
                    pattern: WhenPattern::List {
                        elements: Vec::new(),
                        tail: None,
                    },
                    guard: None,
                    body: nil_arm,
                },
                WhenClause {
                    pattern: WhenPattern::List {
                        elements: vec![Binder::new("head".to_string(), VarId::new(922))],
                        tail: Some(Binder::new("tail".to_string(), VarId::new(923))),
                    },
                    guard: None,
                    body: cons_arm,
                },
            ],
        }),
    }
}

fn self_call() -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("step", VarId::new(920))),
        args: vec![PseudoExpr::var_with_id("tail", VarId::new(923))].into(),
    }
}

/// `church_cons(head, step(tail))`
fn scott_cons_call() -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("church_cons", VarId::new(911))),
        args: vec![
            PseudoExpr::var_with_id("head", VarId::new(922)),
            self_call(),
        ]
        .into(),
    }
}

fn nil_ref() -> PseudoExpr {
    PseudoExpr::var_with_id("church_true", VarId::new(910))
}

/// Dig the builder's `when` arms out of a rewritten tree.
fn arms_of(expr: &PseudoExpr) -> Vec<PseudoExpr> {
    fn find(e: &PseudoExpr) -> Option<Vec<PseudoExpr>> {
        if let PseudoExpr::When { clauses, .. } = e {
            return Some(clauses.iter().map(|c| c.body.clone()).collect());
        }
        super::super::scope_recurse::children(e)
            .into_iter()
            .find_map(find)
    }
    find(expr).expect("the builder's when survives")
}

#[test]
fn recovers_both_arms_of_a_scott_list_builder() {
    let out = recover_recursive_list_builder(with_scott_defs(scott_builder(
        nil_ref(),
        scott_cons_call(),
    )));
    let arms = arms_of(&out);
    assert!(
        matches!(&arms[0], PseudoExpr::List { elements, tail } if elements.is_empty() && tail.is_none()),
        "nil arm should become `[]`, got {:?}",
        arms[0]
    );
    assert!(
        matches!(&arms[1], PseudoExpr::List { elements, tail } if elements.len() == 1 && tail.is_some()),
        "cons arm should become `[head, ..step(tail)]`, got {:?}",
        arms[1]
    );
}

#[test]
fn leaves_a_nil_reference_outside_any_builder_alone() {
    // `fn(n, _) { n }` is also the church `True`. Referenced anywhere
    // but the result position of a PROVEN list builder it stays as it
    // is — being that term proves nothing on its own.
    let loose = with_scott_defs(PseudoExpr::Let {
        name: "flag".to_string(),
        id: Some(VarId::new(940)),
        value: PBox::new(nil_ref()),
        body: PBox::new(PseudoExpr::var_with_id("flag", VarId::new(940))),
    });
    assert_eq!(recover_recursive_list_builder(loose.clone()), loose);
}

#[test]
fn recovers_a_builder_whose_program_has_no_scott_cons() {
    // The cons arm is the already-folded spread, so the builder proves
    // itself; nothing else in the program needs to be a Scott cons.
    let n = Binder::new("n".to_string(), VarId::new(900));
    let dead = Binder::new("_".to_string(), VarId::new(901));
    let only_nil = PseudoExpr::Let {
        name: "church_true".to_string(),
        id: Some(VarId::new(910)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![n, dead],
            body: PBox::new(PseudoExpr::var_with_id("n", VarId::new(900))),
        }),
        body: PBox::new(scott_builder(
            nil_ref(),
            PseudoExpr::List {
                elements: vec![PseudoExpr::var_with_id("head", VarId::new(922))].into(),
                tail: Some(PBox::new(self_call())),
            },
        )),
    };
    let arms = arms_of(&recover_recursive_list_builder(only_nil));
    assert!(
        matches!(&arms[0], PseudoExpr::List { elements, tail } if elements.is_empty() && tail.is_none()),
        "nil arm should become `[]`, got {:?}",
        arms[0]
    );
}

#[test]
fn recovers_a_cons_reached_through_a_let_bound_self_call() {
    // `let t = step(tail)` then `[head, ..t]` — the lowering writes the
    // cell in two steps whenever the tail is used more than once.
    let cons_arm = PseudoExpr::Let {
        name: "step_result".to_string(),
        id: Some(VarId::new(930)),
        value: PBox::new(self_call()),
        body: PBox::new(PseudoExpr::List {
            elements: vec![PseudoExpr::var_with_id("head", VarId::new(922))].into(),
            tail: Some(PBox::new(PseudoExpr::var_with_id(
                "step_result",
                VarId::new(930),
            ))),
        }),
    };
    let out = recover_recursive_list_builder(with_scott_defs(scott_builder(nil_ref(), cons_arm)));
    let arms = arms_of(&out);
    assert!(
        matches!(&arms[0], PseudoExpr::List { elements, tail } if elements.is_empty() && tail.is_none()),
        "the already-recovered spread still proves the builder, got {:?}",
        arms[0]
    );
}

#[test]
fn keeps_a_nil_that_is_an_element_of_the_cons() {
    // `cons(nil, self(t))` is a list whose FIRST ELEMENT is the nil
    // term — not `[[], ..]`. Only the arm the builder RETURNS from is
    // the base case.
    let cons_arm = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("church_cons", VarId::new(911))),
        args: vec![nil_ref(), self_call()].into(),
    };
    let out = recover_recursive_list_builder(with_scott_defs(scott_builder(nil_ref(), cons_arm)));
    let arms = arms_of(&out);
    let PseudoExpr::List { elements, .. } = &arms[1] else {
        panic!("cons arm folds to a list, got {:?}", arms[1]);
    };
    assert!(
        matches!(&elements[0], PseudoExpr::Var { .. }),
        "the head element must stay the nil REFERENCE, got {:?}",
        elements[0]
    );
}
