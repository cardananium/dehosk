use super::*;
use crate::BuiltinId;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};

fn identity_lambda(pid: VarId) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![Binder::new("p", pid)],
        body: PBox::new(PseudoExpr::var_with_id("p", pid)),
    }
}

/// `List.fold(xs, nil, fn(_) { cons }, k)`.
fn fold_call(xs_id: VarId, k: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: BuiltinId::ListFold,
        args: vec![
            PseudoExpr::var_with_id("xs", xs_id),
            PseudoExpr::var("nil"),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::new(9000))],
                body: PBox::new(PseudoExpr::var("cons")),
            },
            k,
        ]
        .into(),
    }
}

fn assert_lifted_to_when(out: &PseudoExpr) {
    let PseudoExpr::When { clauses, .. } = out else {
        panic!("expected the fold to lift to a `when`, got {out:?}");
    };
    assert_eq!(clauses.len(), 2, "expected [] and [_, ..] clauses");
    assert!(
        matches!(clauses[0].pattern, WhenPattern::List { ref elements, tail: None } if elements.is_empty()),
        "first clause must be the [] pattern",
    );
    assert!(
        matches!(clauses[1].pattern, WhenPattern::List { ref elements, tail: Some(_) } if elements.len() == 1),
        "second clause must be the [_, ..] pattern",
    );
}

#[test]
fn lifts_with_inline_identity_continuation() {
    let out = lift_list_fold_to_when(fold_call(VarId::new(1), identity_lambda(VarId::new(2))));
    assert_lifted_to_when(&out);
}

#[test]
fn lifts_with_named_identity_helper_continuation() {
    // 4th arg is `Var(d)` where `d` is a let-bound identity helper
    // `fn d(p) { p }`; the pass collects `d`'s VarId program-wide.
    let d_id = VarId::new(100);
    let expr = PseudoExpr::Let {
        name: "d".to_string(),
        id: Some(d_id),
        value: PBox::new(identity_lambda(VarId::new(101))),
        body: PBox::new(fold_call(VarId::new(1), PseudoExpr::var_with_id("d", d_id))),
    };
    let out = lift_list_fold_to_when(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected the Let to survive")
    };
    assert_lifted_to_when(&body);
}

#[test]
fn does_not_lift_when_fourth_arg_is_not_identity() {
    // 4th arg is a Var to a NON-identity binding → leave the fold alone.
    let g_id = VarId::new(200);
    let expr = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(g_id),
        // value is NOT an identity (a 2-param lambda).
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("a", VarId::new(201)),
                Binder::new("b", VarId::new(202)),
            ],
            body: PBox::new(PseudoExpr::var_with_id("a", VarId::new(201))),
        }),
        body: PBox::new(fold_call(VarId::new(1), PseudoExpr::var_with_id("g", g_id))),
    };
    let out = lift_list_fold_to_when(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!()
    };
    assert!(
        matches!(*body, PseudoExpr::BuiltinCall { name, .. } if name == BuiltinId::ListFold),
        "non-identity 4th arg must leave the List.fold intact, got {body:?}",
    );
}

#[test]
fn lifts_with_void_continuation() {
    // The forced-thunk form: 4th arg is `Void`/unit applied to force the
    // selected `chooseList` branch. `chooseList xs nil (fn(_){cons}) ()`.
    let out = lift_list_fold_to_when(fold_call(VarId::new(1), PseudoExpr::Unit));
    assert_lifted_to_when(&out);
    let PseudoExpr::When { clauses, .. } = &out else {
        unreachable!()
    };
    // nil here is a bare value (not a thunk) → used as-is.
    assert_eq!(clauses[0].body, PseudoExpr::var("nil"));
    assert_eq!(clauses[1].body, PseudoExpr::var("cons"));
}

#[test]
fn void_form_unwraps_a_nil_thunk() {
    // When the nil branch is still a 1-arg ignore-param thunk (not yet
    // reduced), the applied unit forces it, so it must be unwrapped to its body.
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::ListFold,
        args: vec![
            PseudoExpr::var_with_id("xs", VarId::new(1)),
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::new(8001))],
                body: PBox::new(PseudoExpr::var("nil_body")),
            },
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::new(8002))],
                body: PBox::new(PseudoExpr::var("cons")),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = lift_list_fold_to_when(expr);
    assert_lifted_to_when(&out);
    let PseudoExpr::When { clauses, .. } = &out else {
        unreachable!()
    };
    assert_eq!(
        clauses[0].body,
        PseudoExpr::var("nil_body"),
        "nil thunk must be unwrapped"
    );
}

#[test]
fn does_not_lift_void_form_when_nil_thunk_param_is_used() {
    // nil branch is `fn(u){u}` (param USED). `(fn(u){u}) ()` evaluates to
    // `unit`, NOT the lambda, so it cannot be a plain `[]` body. Bail rather
    // than keep the lambda as-is (keeping it would be `[] -> fn(u){u}`).
    let used = VarId::new(8200);
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::ListFold,
        args: vec![
            PseudoExpr::var_with_id("xs", VarId::new(1)),
            PseudoExpr::Lambda {
                params: vec![Binder::new("u", used)],
                body: PBox::new(PseudoExpr::var_with_id("u", used)),
            },
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::new(8201))],
                body: PBox::new(PseudoExpr::var("cons")),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = lift_list_fold_to_when(expr);
    assert!(
        matches!(out, PseudoExpr::BuiltinCall { name, .. } if name == BuiltinId::ListFold),
        "a used-param nil thunk must block the rewrite, got {out:?}",
    );
}

#[test]
fn does_not_lift_void_form_when_nil_is_multi_arg_lambda() {
    // nil branch is `fn(a, b){ a }` (2 params). `(fn(a,b){a}) ()` is a PARTIAL
    // application, not the lambda — must bail, not use as-is.
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::ListFold,
        args: vec![
            PseudoExpr::var_with_id("xs", VarId::new(1)),
            PseudoExpr::Lambda {
                params: vec![
                    Binder::new("a", VarId::new(8300)),
                    Binder::new("b", VarId::new(8301)),
                ],
                body: PBox::new(PseudoExpr::var_with_id("a", VarId::new(8300))),
            },
            PseudoExpr::Lambda {
                params: vec![Binder::new("_", VarId::new(8302))],
                body: PBox::new(PseudoExpr::var("cons")),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = lift_list_fold_to_when(expr);
    assert!(
        matches!(out, PseudoExpr::BuiltinCall { name, .. } if name == BuiltinId::ListFold),
        "a multi-arg nil lambda must block the rewrite, got {out:?}",
    );
}

#[test]
fn does_not_lift_void_form_when_cons_param_is_used() {
    // A cons "thunk" whose param is actually referenced is NOT a
    // unit-ignoring delay — stripping it would leave a dangling var. Bail.
    let used = VarId::new(8100);
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::ListFold,
        args: vec![
            PseudoExpr::var_with_id("xs", VarId::new(1)),
            PseudoExpr::var("nil"),
            PseudoExpr::Lambda {
                params: vec![Binder::new("u", used)],
                body: PBox::new(PseudoExpr::var_with_id("u", used)),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };
    let out = lift_list_fold_to_when(expr);
    assert!(
        matches!(out, PseudoExpr::BuiltinCall { name, .. } if name == BuiltinId::ListFold),
        "a cons thunk whose param is used must not be stripped, got {out:?}",
    );
}

#[test]
fn does_not_lift_a_same_named_non_identity() {
    // A `Var{id}` whose id is NOT in the identity set is rejected even if the
    // name coincides — provenance is by VarId, not name.
    let real_id = VarId::new(300); // not collected (no identity binding for it)
    let out = lift_list_fold_to_when(fold_call(
        VarId::new(1),
        PseudoExpr::var_with_id("d", real_id),
    ));
    assert!(
        matches!(out, PseudoExpr::BuiltinCall { name, .. } if name == BuiltinId::ListFold),
        "a Var with an uncollected id must not be treated as identity",
    );
}
