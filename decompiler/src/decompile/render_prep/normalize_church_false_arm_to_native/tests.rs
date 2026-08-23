use super::*;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, WhenClause, WhenPattern};

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}
fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `fn(_, f) { f }` — the church-FALSE selector.
fn church_false_lambda(dead: u32, f: u32) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder("_", dead), binder("f", f)],
        body: PBox::new(var("f", f)),
    }
}

/// `fn(t, _) { t }` — the church-TRUE selector.
fn church_true_lambda(t: u32, dead: u32) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder("t", t), binder("_", dead)],
        body: PBox::new(var("t", t)),
    }
}

fn list_empty() -> WhenPattern {
    WhenPattern::List {
        elements: vec![],
        tail: None,
    }
}
fn list_cons() -> WhenPattern {
    WhenPattern::List {
        elements: vec![binder("_", 900)],
        tail: Some(binder("_", 901)),
    }
}

/// `let church_false = fn(_, f){f}; <body-referencing-it>`.
fn wrap_with_def(cf_id: u32, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "church_false".into(),
        id: Some(VarId::new(cf_id)),
        value: PBox::new(church_false_lambda(10, 11)),
        body: PBox::new(body),
    }
}

/// (a) `when x is { [] -> church_false; [_, ..] -> a == b }` → the
/// ref becomes `Bool(false)` (the comparison sibling witnesses it).
#[test]
fn normalizes_church_false_arm_with_bool_sibling() {
    let cf = 5u32;
    let when = PseudoExpr::When {
        subject: PBox::new(var("x", 2)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: list_empty(),
                guard: None,
                body: var("church_false", cf),
            },
            WhenClause {
                pattern: list_cons(),
                guard: None,
                body: PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(var("a", 30)),
                    right: PBox::new(var("b", 31)),
                },
            },
        ],
    };
    let out = normalize_church_false_arm_to_native(wrap_with_def(cf, when));
    // The now-unreferenced `church_false` def is self-cleaned away, so the
    // wrapping `Let` is gone and `out` is the normalized `When` directly.
    let PseudoExpr::When { clauses, .. } = out else {
        panic!("expected When (dead selector def self-cleaned)")
    };
    assert_eq!(
        clauses[0].body,
        PseudoExpr::Bool(false),
        "nil arm must become False"
    );
}

/// (b) a `when` with a church_false arm but NO native-Bool sibling is
/// NOT normalized (fail-closed) — the other arm is a bare Var / list.
#[test]
fn no_op_without_bool_sibling() {
    let cf = 5u32;
    let when = PseudoExpr::When {
        subject: PBox::new(var("x", 2)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: list_empty(),
                guard: None,
                body: var("church_false", cf),
            },
            // sibling is a bare Var — NOT provably Bool.
            WhenClause {
                pattern: list_cons(),
                guard: None,
                body: var("other", 7),
            },
        ],
    };
    let out = normalize_church_false_arm_to_native(wrap_with_def(cf, when));
    // No Bool sibling => no normalization => the church_false ref (hence
    // its def) is still live, so the wrapping `Let` is retained.
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let")
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected When")
    };
    assert_eq!(
        clauses[0].body,
        var("church_false", cf),
        "without a Bool sibling the ref must be untouched"
    );
}

/// (c) a genuine `church_false(x, y)` 2-arg CALL is never touched, even
/// inside a Bool-witnessed `when`.
#[test]
fn genuine_call_is_never_touched() {
    let cf = 5u32;
    let call = PseudoExpr::Apply {
        function: PBox::new(var("church_false", cf)),
        args: vec![var("x", 20), var("y", 21)].into(),
    };
    let when = PseudoExpr::When {
        subject: PBox::new(var("s", 2)),
        subject_name: None,
        clauses: vec![
            // A real selector application in an arm body.
            WhenClause {
                pattern: list_empty(),
                guard: None,
                body: call.clone(),
            },
            // Bool sibling → the when is witnessed.
            WhenClause {
                pattern: list_cons(),
                guard: None,
                body: PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(var("a", 30)),
                    right: PBox::new(var("b", 31)),
                },
            },
        ],
    };
    let out = normalize_church_false_arm_to_native(wrap_with_def(cf, when));
    // The genuine `church_false(x, y)` call keeps a live ref to the def, so
    // the wrapping `Let` is retained (not self-cleaned).
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let")
    };
    let PseudoExpr::When { clauses, .. } = body.into_inner() else {
        panic!("expected When")
    };
    assert_eq!(
        clauses[0].body, call,
        "a genuine 2-arg call must be untouched"
    );
}

/// (d) the recognizer matches `fn(_, f){f}` (false) but not
/// `fn(t, _){t}` (true).
#[test]
fn recognizer_distinguishes_false_from_true() {
    assert!(is_church_false_selector(&church_false_lambda(10, 11)));
    assert!(!is_church_false_selector(&church_true_lambda(10, 11)));
}

/// The witness must NOT be self-satisfied: a `when` whose ONLY non-fail
/// arm is a `church_false` ref is not witnessed — the ref never grounds.
#[test]
fn church_false_arm_alone_is_not_a_witness() {
    let cf: HashSet<VarId> = [VarId::new(5)].into_iter().collect();
    let clauses = vec![
        WhenClause {
            pattern: list_empty(),
            guard: None,
            body: var("church_false", 5),
        },
        WhenClause {
            pattern: list_cons(),
            guard: None,
            body: PseudoExpr::Error { message: None },
        },
    ];
    assert!(
        !when_is_bool_typed(&clauses, &cf),
        "a church_false Var + fail is not a Bool witness"
    );
}

/// A `when` with a definite-Bool arm BUT also a concrete NON-Bool arm
/// (`Some(x)`) is VETOED, where an existence-only witness would misfire.
#[test]
fn non_bool_sibling_vetoes_even_with_a_bool_arm() {
    let cf: HashSet<VarId> = [VarId::new(5)].into_iter().collect();
    let some_x = PseudoExpr::constr(
        crate::pseudo::constructor::ConstructorShape::Known(
            crate::pseudo::constructor::KnownConstructor::Some,
        ),
        vec![var("x", 9)],
    );
    let clauses = vec![
        WhenClause {
            pattern: list_empty(),
            guard: None,
            body: var("church_false", 5),
        },
        WhenClause {
            pattern: WhenPattern::List {
                elements: vec![binder("_", 900)],
                tail: Some(binder("_", 901)),
            },
            guard: None,
            // definite Bool arm — an existence witness would pass here.
            body: PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(var("a", 30)),
                right: PBox::new(var("b", 31)),
            },
        },
        WhenClause {
            pattern: WhenPattern::List {
                elements: vec![binder("_", 902), binder("_", 903)],
                tail: Some(binder("_", 904)),
            },
            guard: None,
            body: some_x, // concrete non-Bool → VETO.
        },
    ];
    assert!(
        !when_is_bool_typed(&clauses, &cf),
        "a concrete Some(x) arm must veto the Bool-typed witness"
    );
}

/// An arm whose tail is `if c { call } else { … && call }` (opaque call
/// = neutral) is NOT a non-Bool veto, and the sibling definite-Bool arm
/// grounds the witness — so the `church_false` arm normalizes.
#[test]
fn opaque_call_arm_does_not_veto_and_bool_sibling_grounds() {
    let cf = 5u32;
    let cf_set: HashSet<VarId> = [VarId::new(cf)].into_iter().collect();
    // cons arm: if a==b { y(x) } else { c==d && y(x) }  — calls are neutral.
    let call = PseudoExpr::Apply {
        function: PBox::new(var("y", 40)),
        args: vec![var("x", 41)].into(),
    };
    let cons_body = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(var("a", 30)),
            right: PBox::new(var("b", 31)),
        }),
        then_branch: PBox::new(call.clone()),
        else_branch: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::And,
            left: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(var("c", 32)),
                right: PBox::new(var("d", 33)),
            }),
            right: PBox::new(call),
        }),
    };
    let when = PseudoExpr::When {
        subject: PBox::new(var("s", 2)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: list_empty(),
                guard: None,
                body: var("church_false", cf),
            },
            WhenClause {
                pattern: list_cons(),
                guard: None,
                body: cons_body,
            },
        ],
    };
    assert!(
        when_is_bool_typed(
            &(if let PseudoExpr::When { clauses, .. } = &when {
                clauses.clone()
            } else {
                unreachable!()
            }),
            &cf_set
        ),
        "opaque-call cons arm must not veto; the && / == leaves ground it"
    );
    let out = normalize_church_false_arm_to_native(wrap_with_def(cf, when));
    // The now-unreferenced `church_false` def is self-cleaned away, so the
    // wrapping `Let` is gone and `out` is the normalized `When` directly.
    let PseudoExpr::When { clauses, .. } = out else {
        panic!("expected When (dead selector def self-cleaned)")
    };
    assert_eq!(
        clauses[0].body,
        PseudoExpr::Bool(false),
        "church_false arm must normalize"
    );
}

/// The soundness counterexample: a `when` with a definite-Bool arm (which
/// a naive existence witness would ground on) AND a WHOLE-opaque arm (a
/// bare `Apply` with no Bool leaf) is NOT witnessed — nothing proves the
/// opaque arm, hence the `when`, Bool-typed, so a sibling `church_false`
/// is left untouched.
#[test]
fn whole_opaque_call_arm_vetoes_even_with_a_bool_sibling() {
    let cf = 5u32;
    let cf_set: HashSet<VarId> = [VarId::new(cf)].into_iter().collect();
    let clauses = vec![
        WhenClause {
            pattern: list_empty(),
            guard: None,
            body: var("church_false", cf),
        },
        // A definite-Bool sibling — would ground a bare existence witness.
        WhenClause {
            pattern: list_cons(),
            guard: None,
            body: PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(var("a", 30)),
                right: PBox::new(var("b", 31)),
            },
        },
        // …but this WHOLE-opaque arm (a bare call, no Bool leaf) vetoes.
        WhenClause {
            pattern: list_cons(),
            guard: None,
            body: PseudoExpr::Apply {
                function: PBox::new(var("some_helper", 40)),
                args: vec![var("z", 41)].into(),
            },
        },
    ];
    assert!(
        !when_is_bool_typed(&clauses, &cf_set),
        "a whole-opaque-call arm must veto even when a sibling is a definite Bool"
    );
}
