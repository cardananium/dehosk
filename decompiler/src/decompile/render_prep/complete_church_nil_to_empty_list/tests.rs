use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

const CHURCH_TRUE_ID: u32 = 900;

/// `let church_true = True in <body>`.
fn with_church_true_const(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "church_true".to_string(),
        id: Some(VarId::new(CHURCH_TRUE_ID)),
        value: PBox::new(PseudoExpr::Bool(true)),
        body: PBox::new(body),
    }
}

/// `when xs is { [] -> <nil>; [h, ..t] -> <cons> }`.
fn list_when(nil_body: PseudoExpr, cons_body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(varref("xs", 1)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::List {
                    elements: vec![],
                    tail: None,
                },
                guard: None,
                body: nil_body,
            },
            WhenClause {
                pattern: WhenPattern::List {
                    elements: vec![binder("h", 2)],
                    tail: Some(binder("t", 3)),
                },
                guard: None,
                body: cons_body,
            },
        ],
    }
}

fn cons_cell(tail: PseudoExpr) -> PseudoExpr {
    PseudoExpr::List {
        elements: vec![varref("h", 2)].into(),
        tail: Some(PBox::new(tail)),
    }
}

fn nil_arm_of(expr: &PseudoExpr) -> &PseudoExpr {
    let PseudoExpr::Let { body, .. } = expr else {
        panic!("expected outer const let, got {expr:?}");
    };
    let PseudoExpr::When { clauses, .. } = body.as_ref() else {
        panic!("expected when, got {body:?}");
    };
    &clauses[0].body
}

fn empty_list() -> PseudoExpr {
    PseudoExpr::List {
        elements: vec![].into(),
        tail: None,
    }
}

/// Canonical shape with the `Bool(true)`-valued const: fires.
#[test]
fn fires_on_decoded_const_and_native_cons() {
    let input = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        cons_cell(PseudoExpr::Apply {
            function: PBox::new(varref("step", 10)),
            args: vec![varref("t", 3)].into(),
        }),
    ));
    let out = complete_church_nil_to_empty_list(input);
    assert_eq!(nil_arm_of(&out), &empty_list());
}

/// Same shape but the const holds the raw K lambda `fn(t, _) { t }`
/// (decode flag off): still fires.
#[test]
fn fires_on_k_lambda_const() {
    let k_lambda = PseudoExpr::Lambda {
        params: vec![binder("t", 50), binder("_", 51)],
        body: PBox::new(varref("t", 50)),
    };
    let input = PseudoExpr::Let {
        name: "church_true".to_string(),
        id: Some(VarId::new(CHURCH_TRUE_ID)),
        value: PBox::new(k_lambda),
        body: PBox::new(list_when(
            varref("church_true", CHURCH_TRUE_ID),
            cons_cell(varref("rest", 11)),
        )),
    };
    let out = complete_church_nil_to_empty_list(input);
    assert_eq!(nil_arm_of(&out), &empty_list());
}

/// The church-bool list predicate `{ [] -> church_true; [_, ..] ->
/// church_false }` must NOT fire — a pattern-only gate inverts it.
#[test]
fn veto_predicate_shaped_cons_body() {
    let input = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        varref("church_false", 901),
    ));
    let out = complete_church_nil_to_empty_list(input.clone());
    assert_eq!(out, input);
}

/// Vacuous recursion `{ [] -> church_true; [_, ..t] -> self(t) }` is a
/// church-bool `all` returning a genuine True — the Apply leaf vetoes.
#[test]
fn veto_recursive_self_call_leaf() {
    let input = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        PseudoExpr::Apply {
            function: PBox::new(varref("self", 10)),
            args: vec![varref("t", 3)].into(),
        },
    ));
    let out = complete_church_nil_to_empty_list(input.clone());
    assert_eq!(out, input);
}

/// An all-`Error` cons body is a legitimate partial Bool
/// predicate `{ [] -> True; [_, ..] -> fail }` — no list evidence, the
/// witness must require at least one real List leaf.
#[test]
fn veto_all_error_cons_body() {
    let input = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        PseudoExpr::Error { message: None },
    ));
    let out = complete_church_nil_to_empty_list(input.clone());
    assert_eq!(out, input);
}

/// The pure identity rebuild `{ [] -> church_true;
/// [h, ..t] -> [h, ..t] }` is a pass-through whose nil arm may be a
/// genuine boolean sentinel — vetoed.
#[test]
fn veto_identity_rebuild_cons_body() {
    let input = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        PseudoExpr::List {
            elements: vec![varref("h", 2)].into(),
            tail: Some(PBox::new(varref("t", 3))),
        },
    ));
    let out = complete_church_nil_to_empty_list(input.clone());
    assert_eq!(out, input);
}

/// A TRANSFORMING rebuild whose tail is the bare tail binder still
/// fires — only the full identity (head AND tail both bare binders)
/// is vetoed.
#[test]
fn fires_on_transforming_rebuild_with_bare_tail() {
    let input = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        PseudoExpr::List {
            elements: vec![PseudoExpr::Apply {
                function: PBox::new(varref("f", 40)),
                args: vec![varref("h", 2)].into(),
            }]
            .into(),
            tail: Some(PBox::new(varref("t", 3))),
        },
    ));
    let out = complete_church_nil_to_empty_list(input);
    assert_eq!(nil_arm_of(&out), &empty_list());
}

/// A literal `Bool(true)` nil body has no provenance — never rewritten.
#[test]
fn veto_literal_bool_nil_arm() {
    let input = with_church_true_const(list_when(
        PseudoExpr::Bool(true),
        cons_cell(varref("rest", 11)),
    ));
    let out = complete_church_nil_to_empty_list(input.clone());
    assert_eq!(out, input);
}

/// A guarded clause or a 3-clause `when` fails the shape gate.
#[test]
fn veto_guarded_or_extra_clauses() {
    let mut guarded = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        cons_cell(varref("rest", 11)),
    ));
    if let PseudoExpr::Let { body, .. } = &mut guarded
        && let PseudoExpr::When { clauses, .. } = body.as_mut()
    {
        clauses[1].guard = Some(PseudoExpr::Bool(true));
    }
    let out = complete_church_nil_to_empty_list(guarded.clone());
    assert_eq!(out, guarded);

    let mut three_arm = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        cons_cell(varref("rest", 11)),
    ));
    if let PseudoExpr::Let { body, .. } = &mut three_arm
        && let PseudoExpr::When { clauses, .. } = body.as_mut()
    {
        clauses.push(WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: PseudoExpr::Error { message: None },
        });
    }
    let out = complete_church_nil_to_empty_list(three_arm.clone());
    assert_eq!(out, three_arm);
}

/// Let-chain descent: `[_, ..t] -> let v = …; [f(v), ..step(t)]` fires.
#[test]
fn fires_through_let_chain() {
    let input = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        PseudoExpr::Let {
            name: "v".to_string(),
            id: Some(VarId::new(20)),
            value: PBox::new(varref("h", 2)),
            body: PBox::new(cons_cell(varref("rest", 11))),
        },
    ));
    let out = complete_church_nil_to_empty_list(input);
    assert_eq!(nil_arm_of(&out), &empty_list());
}

/// Cons body ROOT is a List cell whose TAIL slot holds a `when` that
/// can leak a non-list — still fires: the root List commits the arm
/// to a list display regardless of its tail value.
#[test]
fn fires_on_root_list_with_suspect_tail() {
    let suspect_tail = PseudoExpr::When {
        subject: PBox::new(varref("sel", 30)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: varref("x_300", 31), // function param leak
        }],
    };
    let input = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        cons_cell(suspect_tail),
    ));
    let out = complete_church_nil_to_empty_list(input);
    assert_eq!(nil_arm_of(&out), &empty_list());
}

/// The list-ADT constructor pattern encoding (`Known(Nil)` /
/// `Known(Cons)`, as emitted by the MID `chooseList` recognizer) is
/// accepted by the shape gate too.
#[test]
fn fires_on_constructor_encoded_list_patterns() {
    let input = with_church_true_const(PseudoExpr::When {
        subject: PBox::new(varref("xs", 1)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::Known(KnownConstructor::Nil),
                },
                guard: None,
                body: varref("church_true", CHURCH_TRUE_ID),
            },
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 1,
                    fields: vec![binder("h", 2), binder("t", 3)],
                    shape: ConstructorShape::Known(KnownConstructor::Cons),
                },
                guard: None,
                body: cons_cell(varref("rest", 11)),
            },
        ],
    });
    let out = complete_church_nil_to_empty_list(input);
    assert_eq!(nil_arm_of(&out), &empty_list());
}

/// A non-list Constructor pattern pair (e.g. a 2-variant user ADT with
/// the same tags/arities but `Unknown` shape) fails the shape gate.
#[test]
fn veto_unknown_constructor_patterns() {
    let input = with_church_true_const(PseudoExpr::When {
        subject: PBox::new(varref("xs", 1)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: vec![],
                    shape: ConstructorShape::unknown_data(0, 0),
                },
                guard: None,
                body: varref("church_true", CHURCH_TRUE_ID),
            },
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 1,
                    fields: vec![binder("h", 2), binder("t", 3)],
                    shape: ConstructorShape::unknown_data(1, 2),
                },
                guard: None,
                body: cons_cell(varref("rest", 11)),
            },
        ],
    });
    let out = complete_church_nil_to_empty_list(input.clone());
    assert_eq!(out, input);
}

/// Idempotence: `pass(pass(x)) == pass(x)`.
#[test]
fn idempotent() {
    let input = with_church_true_const(list_when(
        varref("church_true", CHURCH_TRUE_ID),
        cons_cell(varref("rest", 11)),
    ));
    let once = complete_church_nil_to_empty_list(input);
    let twice = complete_church_nil_to_empty_list(once.clone());
    assert_eq!(twice, once);
}

/// A differently-named `let t = True` referenced in the nil arm is not
/// provenance — unchanged.
#[test]
fn veto_name_mismatch() {
    let input = PseudoExpr::Let {
        name: "t".to_string(),
        id: Some(VarId::new(CHURCH_TRUE_ID)),
        value: PBox::new(PseudoExpr::Bool(true)),
        body: PBox::new(list_when(
            varref("t", CHURCH_TRUE_ID),
            cons_cell(varref("rest", 11)),
        )),
    };
    let out = complete_church_nil_to_empty_list(input.clone());
    assert_eq!(out, input);
}
