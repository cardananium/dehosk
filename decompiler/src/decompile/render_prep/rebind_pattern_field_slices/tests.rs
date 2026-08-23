use super::*;
use crate::builtins::BuiltinId;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

// ---- AST builders ----------------------------------------------------------

fn subj_fields(subject_id: VarId) -> PseudoExpr {
    // `subj.fields`
    PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::var_with_id("s", subject_id)),
        selector: FieldSelector::NamedField("fields".to_string()),
    }
}

fn list_tail(inner: PseudoExpr) -> PseudoExpr {
    // one `List.tail` step (curried Apply form)
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: BuiltinId::ListTail,
            args: vec![].into(),
        }),
        args: vec![inner].into(),
    }
}

fn list_head(inner: PseudoExpr) -> PseudoExpr {
    PseudoExpr::FieldAccess {
        record: PBox::new(inner),
        selector: FieldSelector::ListHead,
    }
}

/// `subj.fields[k..].head`
fn fields_tail_head(subject_id: VarId, k: usize) -> PseudoExpr {
    let mut e = subj_fields(subject_id);
    for _ in 0..k {
        e = list_tail(e);
    }
    list_head(e)
}

/// `subj.fields[k..]` (a tail list)
fn fields_tail(subject_id: VarId, k: usize) -> PseudoExpr {
    let mut e = subj_fields(subject_id);
    for _ in 0..k {
        e = list_tail(e);
    }
    e
}

fn expect_ctor(subject_id: VarId, binders: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
    // `expect Ctor(binders) = subj; body` == a When over subj with the
    // Constructor clause + a `_ -> fail` clause.
    let arity = binders.len();
    PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("s", subject_id)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Constructor {
                    type_hint: None,
                    tag: 0,
                    fields: binders,
                    shape: ConstructorShape::unknown_data(0, arity),
                },
                guard: None,
                body,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error {
                    message: Some("fail".to_string()),
                },
            },
        ],
    }
}

fn is_var(expr: &PseudoExpr, id: VarId) -> bool {
    matches!(expr, PseudoExpr::Var { id: Some(v), .. } if *v == id)
}

/// Extract the first clause body of the top-level `When`.
fn clause_body(expr: &PseudoExpr) -> &PseudoExpr {
    match expr {
        PseudoExpr::When { clauses, .. } => &clauses[0].body,
        _ => panic!("not a When"),
    }
}

// ---- (a) direct `s.fields[1..].head` → f1 ----------------------------------

#[test]
fn rebinds_fields_tail_head_to_pattern_binder() {
    let s = VarId::new(9000);
    let f0 = VarId::new(9001);
    let f1 = VarId::new(9002);
    let f2 = VarId::new(9003);
    let binders = vec![
        Binder::new("f0", f0),
        Binder::new("f1", f1),
        Binder::new("f2", f2),
    ];
    // body: un_i_data(s.fields[1..].head)
    let body = PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnInt,
        args: vec![fields_tail_head(s, 1)].into(),
    };
    let out = rebind_pattern_field_slices(expect_ctor(s, binders, body));
    let b = clause_body(&out);
    match b {
        PseudoExpr::BuiltinCall { args, .. } => {
            assert!(is_var(&args[0], f1), "expected Var(f1), got {:?}", args[0]);
        }
        _ => panic!("unexpected body {:?}", b),
    }
}

// ---- (b) let-alias offset: `let w = s.fields[2..]; w.head`→f2, `w[1..].head`→f3

#[test]
fn resolves_tail_alias_offset_accumulation() {
    let s = VarId::new(9100);
    let f: Vec<VarId> = (0..5).map(|i| VarId::new(9101 + i as u32)).collect();
    let binders: Vec<Binder> = f
        .iter()
        .enumerate()
        .map(|(i, id)| Binder::new(format!("f{}", i), *id))
        .collect();
    let w = VarId::new(9200);
    // let w = s.fields[2..]
    //   Tuple(w.head, w[1..].head)   -- so both survive
    let inner_body = PseudoExpr::Tuple(
        vec![
            // w.head            → field at index 2
            list_head(PseudoExpr::var_with_id("w", w)),
            // w[1..].head       → field at index 2 + 1 = 3
            list_head(list_tail(PseudoExpr::var_with_id("w", w))),
        ]
        .into(),
    );
    let body = PseudoExpr::Let {
        name: "w".to_string(),
        id: Some(w),
        value: PBox::new(fields_tail(s, 2)),
        body: PBox::new(inner_body),
    };
    let out = rebind_pattern_field_slices(expect_ctor(s, binders, body));
    // `let w` should be dropped (w now dead), leaving the Tuple with f2, f3.
    let b = clause_body(&out);
    let tuple = match b {
        PseudoExpr::Tuple(items) => items,
        // if the let survived, unwrap it (should not, but be robust)
        PseudoExpr::Let { body, .. } => match body.as_ref() {
            PseudoExpr::Tuple(items) => items,
            other => panic!("unexpected let body {:?}", other),
        },
        other => panic!("unexpected body {:?}", other),
    };
    assert!(
        is_var(&tuple[0], f[2]),
        "w.head should be f2, got {:?}",
        tuple[0]
    );
    assert!(
        is_var(&tuple[1], f[3]),
        "w[1..].head should be f3, got {:?}",
        tuple[1]
    );
    assert!(
        matches!(b, PseudoExpr::Tuple(_)),
        "dead `let w` should be dropped: {:?}",
        b
    );
}

// ---- (c) wildcard position → NOT substituted -------------------------------

#[test]
fn wildcard_position_not_substituted() {
    let s = VarId::new(9300);
    let binders = vec![
        Binder::new("f0", VarId::new(9301)),
        Binder::new("_", VarId::new(9302)),
        Binder::new("f2", VarId::new(9303)),
    ];
    // body accesses index 1, which is `_` (no binder).
    let access = fields_tail_head(s, 1);
    let body = PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnInt,
        args: vec![access.clone()].into(),
    };
    let out = rebind_pattern_field_slices(expect_ctor(s, binders, body));
    let b = clause_body(&out);
    match b {
        PseudoExpr::BuiltinCall { args, .. } => {
            assert!(
                !matches!(args[0], PseudoExpr::Var { .. }),
                "wildcard field must NOT be rebound, got {:?}",
                args[0]
            );
        }
        _ => panic!(),
    }
}

// ---- (d) different subject Var → NOT substituted ---------------------------

#[test]
fn different_subject_not_substituted() {
    let s = VarId::new(9400);
    let other = VarId::new(9499);
    let binders = vec![
        Binder::new("f0", VarId::new(9401)),
        Binder::new("f1", VarId::new(9402)),
    ];
    // body accesses OTHER.fields[1..].head, not s.
    let body = PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnInt,
        args: vec![fields_tail_head(other, 1)].into(),
    };
    let out = rebind_pattern_field_slices(expect_ctor(s, binders, body));
    let b = clause_body(&out);
    match b {
        PseudoExpr::BuiltinCall { args, .. } => {
            assert!(
                !matches!(args[0], PseudoExpr::Var { .. }),
                "foreign-subject slice must NOT be rebound, got {:?}",
                args[0]
            );
        }
        _ => panic!(),
    }
}

// ---- (e) bare `s.fields` (whole list) → NOT substituted --------------------

#[test]
fn bare_fields_whole_list_not_substituted() {
    let s = VarId::new(9500);
    let binders = vec![
        Binder::new("f0", VarId::new(9501)),
        Binder::new("f1", VarId::new(9502)),
    ];
    // body uses the bare `s.fields` list (e.g. passed to a helper).
    let body = PseudoExpr::BuiltinCall {
        name: BuiltinId::DataUnInt,
        args: vec![subj_fields(s)].into(),
    };
    let out = rebind_pattern_field_slices(expect_ctor(s, binders, body.clone()));
    let b = clause_body(&out);
    // the whole tail list is not a single field.
    assert_eq!(b, &body, "bare `.fields` must not be rebound");
}

// ---- (f) `let w = s.fields[2..].head` field-alias → `let w = f2`, keep let --

#[test]
fn field_alias_let_value_rewritten_binder_kept() {
    let s = VarId::new(9600);
    let f2 = VarId::new(9603);
    let binders = vec![
        Binder::new("f0", VarId::new(9601)),
        Binder::new("f1", VarId::new(9602)),
        Binder::new("f2", f2),
        Binder::new("f3", VarId::new(9604)),
    ];
    let w = VarId::new(9700);
    // let w = s.fields[2..].head;  <use w twice so it stays live>
    let inner = PseudoExpr::Tuple(
        vec![
            PseudoExpr::var_with_id("w", w),
            PseudoExpr::var_with_id("w", w),
        ]
        .into(),
    );
    let body = PseudoExpr::Let {
        name: "w".to_string(),
        id: Some(w),
        value: PBox::new(fields_tail_head(s, 2)),
        body: PBox::new(inner),
    };
    let out = rebind_pattern_field_slices(expect_ctor(s, binders, body));
    let b = clause_body(&out);
    match b {
        PseudoExpr::Let { value, body, .. } => {
            assert!(is_var(value, f2), "let value should be f2, got {:?}", value);
            match body.as_ref() {
                PseudoExpr::Tuple(items) => {
                    assert!(is_var(&items[0], w), "w use preserved, got {:?}", items[0]);
                }
                other => panic!("unexpected {:?}", other),
            }
        }
        other => panic!("field-alias let should be KEPT, got {:?}", other),
    }
}

// ---- (g) fail-closed: unresolved (non-constant) offset → left untouched -----

#[test]
fn unresolved_alias_left_untouched() {
    let s = VarId::new(9800);
    let binders = vec![
        Binder::new("f0", VarId::new(9801)),
        Binder::new("f1", VarId::new(9802)),
    ];
    // `foreign` is bound to an opaque call the pass cannot classify.
    let foreign = VarId::new(9900);
    let body = PseudoExpr::Let {
        name: "foreign".to_string(),
        id: Some(foreign),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: BuiltinId::DataUnInt,
            args: vec![PseudoExpr::var("opaque")].into(),
        }),
        // foreign.head — foreign is NOT a resolvable tail → no rebind.
        body: PBox::new(list_head(PseudoExpr::var_with_id("foreign", foreign))),
    };
    let out = rebind_pattern_field_slices(expect_ctor(s, binders, body));
    let b = clause_body(&out);
    // The Let survived and its .head body is unchanged (no rebind).
    match b {
        PseudoExpr::Let { body, .. } => {
            assert!(
                matches!(
                    body.as_ref(),
                    PseudoExpr::FieldAccess {
                        selector: FieldSelector::ListHead,
                        ..
                    }
                ),
                "unresolvable alias head must be untouched, got {:?}",
                body
            );
        }
        other => panic!("unexpected {:?}", other),
    }
}
