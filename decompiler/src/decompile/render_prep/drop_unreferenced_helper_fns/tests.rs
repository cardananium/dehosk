use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn lambda(param: &str, id: u32, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder(param, id)],
        body: PBox::new(body),
    }
}

fn let_(name: &str, id: u32, value: PseudoExpr, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: name.to_string(),
        id: Some(VarId::new(id)),
        value: PBox::new(value),
        body: PBox::new(body),
    }
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// The validator marker plus one called and one uncalled helper.
fn program(extra: PseudoExpr) -> PseudoExpr {
    let_(
        "decompiled",
        1,
        lambda("script_context", 2, PseudoExpr::Unit),
        extra,
    )
}

#[test]
fn drops_a_helper_nothing_calls() {
    let expr = program(let_(
        "dead",
        10,
        lambda("x", 11, PseudoExpr::Unit),
        PseudoExpr::Unit,
    ));
    let out = drop_unreferenced_helper_fns(expr);
    assert!(
        !matches!(&out, PseudoExpr::Let { body, .. } if matches!(body.as_ref(), PseudoExpr::Let { name, .. } if name == "dead")),
        "uncalled helper must be dropped: {out:?}"
    );
}

/// Its unreachable `fail` is not a reason to keep it — that is the only
/// thing `drop_dead_pure_lets` holds onto, and it cannot fire.
#[test]
fn drops_a_helper_whose_body_fails() {
    let expr = program(let_(
        "dead",
        10,
        lambda(
            "x",
            11,
            PseudoExpr::Error {
                message: Some("PT1".to_string()),
            },
        ),
        PseudoExpr::Unit,
    ));
    let out = drop_unreferenced_helper_fns(expr);
    let PseudoExpr::Let { body, .. } = &out else {
        panic!("expected the marker Let: {out:?}");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Unit),
        "a failing but uncalled helper must still go: {out:?}"
    );
}

#[test]
fn keeps_a_helper_with_a_call_site() {
    let expr = program(let_(
        "live",
        10,
        lambda("x", 11, PseudoExpr::Unit),
        var("live", 10),
    ));
    let out = drop_unreferenced_helper_fns(expr);
    let PseudoExpr::Let { body, .. } = &out else {
        panic!("expected the marker Let: {out:?}");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Let { name, .. } if name == "live"),
        "a referenced helper must survive: {out:?}"
    );
}

/// A recursive helper that only calls itself is still unreachable.
#[test]
fn discounts_a_recursive_helpers_own_self_call() {
    let rec = PseudoExpr::RecFn {
        name: binder("loop", 10),
        params: vec![binder("x", 11)],
        body: PBox::new(var("loop", 10)),
    };
    let expr = program(let_("loop", 10, rec, PseudoExpr::Unit));
    let out = drop_unreferenced_helper_fns(expr);
    let PseudoExpr::Let { body, .. } = &out else {
        panic!("expected the marker Let: {out:?}");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Unit),
        "self-reference is not an external call site: {out:?}"
    );
}

/// Dropping the only caller strands its callee; the sweep repeats.
#[test]
fn drops_a_chain_to_a_fixpoint() {
    let inner = let_("b", 20, lambda("x", 21, PseudoExpr::Unit), PseudoExpr::Unit);
    let expr = program(let_("a", 10, lambda("x", 11, var("b", 20)), inner));
    let out = drop_unreferenced_helper_fns(expr);
    let PseudoExpr::Let { body, .. } = &out else {
        panic!("expected the marker Let: {out:?}");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Unit),
        "both helpers must go: {out:?}"
    );
}

/// The validator entry has no caller by design.
#[test]
fn never_drops_the_validator_entry() {
    let expr = program(PseudoExpr::Unit);
    let out = drop_unreferenced_helper_fns(expr);
    assert!(
        matches!(&out, PseudoExpr::Let { name, .. } if name == "decompiled"),
        "the entry must survive: {out:?}"
    );
}

/// Without the marker the tree may be a fragment whose call sites live
/// outside it, so the sweep abstains.
#[test]
fn abstains_without_the_validator_marker() {
    let expr = let_(
        "dead",
        10,
        lambda("x", 11, PseudoExpr::Unit),
        PseudoExpr::Unit,
    );
    let out = drop_unreferenced_helper_fns(expr.clone());
    assert!(
        matches!(&out, PseudoExpr::Let { name, .. } if name == "dead"),
        "no marker ⇒ no sweep: {out:?}"
    );
}

/// A `Var` may carry no id and be resolved by name. An id-only scan
/// would call this helper dead and render a free call.
#[test]
fn keeps_a_helper_referenced_only_by_name() {
    let expr = program(let_(
        "live",
        10,
        lambda("x", 11, PseudoExpr::Unit),
        PseudoExpr::Var {
            name: "live".to_string(),
            id: None,
        },
    ));
    let out = drop_unreferenced_helper_fns(expr);
    let PseudoExpr::Let { body, .. } = &out else {
        panic!("expected the marker Let: {out:?}");
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Let { name, .. } if name == "live"),
        "an id-less reference is still a call site: {out:?}"
    );
}
