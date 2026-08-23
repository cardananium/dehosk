use super::*;
use crate::decompile::TypeHintId;
use crate::pseudo::ast::PBox;
use crate::pseudo::constructor::ConstructorShape;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name, VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `let f = fn(p) { ... }` called once with a Lambda arg → the slot joins
/// to `Fn`, not Scott → not-decodable (a genuine HOF parameter).
#[test]
fn lambda_arg_slot_is_not_decodable() {
    // let f = fn(p) { p } ; f(fn(x){x})
    let f = PseudoExpr::Lambda {
        params: vec![binder("p", 1)],
        body: PBox::new(var("p", 1)),
    };
    let lam_arg = PseudoExpr::Lambda {
        params: vec![binder("x", 2)],
        body: PBox::new(var("x", 2)),
    };
    let call = PseudoExpr::Apply {
        function: PBox::new(var("f", 100)),
        args: vec![lam_arg].into(),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(100)),
        value: PBox::new(f),
        body: PBox::new(call),
    };
    let prov = analyze(&expr);
    let f = prov.iter().find(|f| f.name == "f").expect("f present");
    assert_eq!(f.slots[0].1, SlotVerdict::NotDecodable(FieldKind::Fn));
}

/// A function that is VALUE-used (Scott-matched as a `when` subject, never
/// called) → its slots are Unreliable.
#[test]
fn value_used_function_is_unreliable() {
    // let helper = fn(p) { p } ; when helper is { _ -> 0 }
    let helper = PseudoExpr::Lambda {
        params: vec![binder("p", 1)],
        body: PBox::new(var("p", 1)),
    };
    let when = PseudoExpr::When {
        subject: PBox::new(var("helper", 100)),
        subject_name: None,
        clauses: vec![],
    };
    let expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(VarId::new(100)),
        value: PBox::new(helper),
        body: PBox::new(when),
    };
    let prov = analyze(&expr);
    let h = prov
        .iter()
        .find(|f| f.name == "helper")
        .expect("helper present");
    assert_eq!(h.slots[0].1, SlotVerdict::Unreliable);
}

/// Helper: declare inner's two arity-1 variants so the arity catalog is
/// complete, then build a function whose param `p` receives a Scott value
/// at both call sites. `elim_body` decides whether `p` is eliminated.
fn scott_param_setup(elim_body: PseudoExpr) -> Vec<FunctionProvenance> {
    let inner = TypeHintId::from("Unknown_S_25");
    let scott = |tag: usize| PseudoExpr::Constr {
        tag,
        shape: ConstructorShape::unknown_data(tag, 1),
        fields: vec![PseudoExpr::Unit].into(),
        type_hint: Some(inner.clone()),
    };
    let decls = PseudoExpr::Tuple((vec![scott(0), scott(1)]).into());
    let f = PseudoExpr::Lambda {
        params: vec![binder("p", 1)],
        body: PBox::new(elim_body),
    };
    let call1 = PseudoExpr::Apply {
        function: PBox::new(var("f", 100)),
        args: vec![scott(0)].into(),
    };
    let call2 = PseudoExpr::Apply {
        function: PBox::new(var("f", 100)),
        args: vec![scott(1)].into(),
    };
    let body = PseudoExpr::Tuple((vec![decls, call1, call2]).into());
    analyze(&PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(100)),
        value: PBox::new(f),
        body: PBox::new(body),
    })
}

/// Proven-Scott arg + the param is only RETURNED (not eliminated) → flows
/// through, not a rewrite target.
#[test]
fn scott_arg_only_stored_flows_through() {
    let prov = scott_param_setup(var("p", 1)); // body just returns p
    let f = prov.iter().find(|f| f.name == "f").expect("f present");
    assert_eq!(f.slots[0].1, SlotVerdict::ScottFlowsThrough(vec![1, 1]));
}

/// Proven-Scott arg AND the param is eliminated (`when p is`) → the actual
/// rewrite target.
#[test]
fn scott_arg_eliminated_is_rewrite_target() {
    let when = PseudoExpr::When {
        subject: PBox::new(var("p", 1)),
        subject_name: None,
        clauses: vec![],
    };
    let prov = scott_param_setup(when);
    let f = prov.iter().find(|f| f.name == "f").expect("f present");
    assert_eq!(f.slots[0].1, SlotVerdict::RewriteTarget(vec![1, 1]));
}

/// A Scott arg at one site + a Lambda arg at another → fail-closed to
/// not-decodable (Conflict), never Decodable.
#[test]
fn mixed_scott_and_lambda_args_fail_closed() {
    let inner = TypeHintId::from("Unknown_S_25");
    let scott = |tag: usize| PseudoExpr::Constr {
        tag,
        shape: ConstructorShape::unknown_data(tag, 1),
        fields: vec![PseudoExpr::Unit].into(),
        type_hint: Some(inner.clone()),
    };
    let decls = PseudoExpr::Tuple((vec![scott(0), scott(1)]).into());
    let f = PseudoExpr::Lambda {
        params: vec![binder("p", 1)],
        body: PBox::new(var("p", 1)),
    };
    let call_scott = PseudoExpr::Apply {
        function: PBox::new(var("f", 100)),
        args: vec![scott(0)].into(),
    };
    let call_lam = PseudoExpr::Apply {
        function: PBox::new(var("f", 100)),
        args: vec![PseudoExpr::Lambda {
            params: vec![binder("x", 2)],
            body: PBox::new(var("x", 2)),
        }]
        .into(),
    };
    let body = PseudoExpr::Tuple((vec![decls, call_scott, call_lam]).into());
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(100)),
        value: PBox::new(f),
        body: PBox::new(body),
    };
    let prov = analyze(&expr);
    let f = prov.iter().find(|f| f.name == "f").expect("f present");
    assert_eq!(f.slots[0].1, SlotVerdict::NotDecodable(FieldKind::Conflict));
}

/// SOUNDNESS: a directly-applied `(rec fn g(p){..})(hof_arg)` IIFE whose
/// body ALSO self-recursively calls `g(scott)` must NOT yield RewriteTarget
/// — the missed entry HOF arg has to be recorded so it defeats Scott.
#[test]
fn recfn_iife_entry_arg_is_recorded() {
    let inner = TypeHintId::from("Unknown_S_25");
    let scott = |tag: usize| PseudoExpr::Constr {
        tag,
        shape: ConstructorShape::unknown_data(tag, 1),
        fields: vec![PseudoExpr::Unit].into(),
        type_hint: Some(inner.clone()),
    };
    let decls = PseudoExpr::Tuple((vec![scott(0), scott(1)]).into());
    // rec fn g(p) { ( when p is {}, g(Scott) ) }
    let self_call = PseudoExpr::Apply {
        function: PBox::new(var("g", 200)),
        args: vec![scott(0)].into(),
    };
    let elim = PseudoExpr::When {
        subject: PBox::new(var("p", 1)),
        subject_name: None,
        clauses: vec![],
    };
    let g = PseudoExpr::RecFn {
        name: binder("g", 200),
        params: vec![binder("p", 1)],
        body: PBox::new(PseudoExpr::Tuple((vec![elim, self_call]).into())),
    };
    // (rec fn g(p){..})(fn(x){x})   <-- entry arg is a HOF
    let iife = PseudoExpr::Apply {
        function: PBox::new(g),
        args: vec![PseudoExpr::Lambda {
            params: vec![binder("x", 2)],
            body: PBox::new(var("x", 2)),
        }]
        .into(),
    };
    let prov = analyze(&PseudoExpr::Tuple((vec![decls, iife]).into()));
    let g = prov.iter().find(|f| f.name == "g").expect("g present");
    // entry arg = Fn, self-call arg = Scott -> join = Conflict, NOT a target.
    assert_eq!(g.slots[0].1, SlotVerdict::NotDecodable(FieldKind::Conflict));
}

/// SOUNDNESS: a standalone `rec fn g` used as a VALUE escapes — though
/// its body self-recursively calls `g(Scott)` and eliminates `p`, the
/// verdict must be Unreliable: outside callers can pass anything.
#[test]
fn value_escaped_recfn_is_unreliable() {
    let inner = TypeHintId::from("Unknown_S_25");
    let scott = |tag: usize| PseudoExpr::Constr {
        tag,
        shape: ConstructorShape::unknown_data(tag, 1),
        fields: vec![PseudoExpr::Unit].into(),
        type_hint: Some(inner.clone()),
    };
    let decls = PseudoExpr::Tuple((vec![scott(0), scott(1)]).into());
    let self_call = PseudoExpr::Apply {
        function: PBox::new(var("g", 200)),
        args: vec![scott(0)].into(),
    };
    let elim = PseudoExpr::When {
        subject: PBox::new(var("p", 1)),
        subject_name: None,
        clauses: vec![],
    };
    let g = PseudoExpr::RecFn {
        name: binder("g", 200),
        params: vec![binder("p", 1)],
        body: PBox::new(PseudoExpr::Tuple((vec![elim, self_call]).into())),
    };
    // g sits as a bare value in a tuple → escapes (not Let-bound, not IIFE).
    let prov = analyze(&PseudoExpr::Tuple((vec![decls, g]).into()));
    let g = prov.iter().find(|f| f.name == "g").expect("g present");
    assert_eq!(g.slots[0].1, SlotVerdict::Unreliable);
}

/// A declared-but-never-called function → NoCallSites.
#[test]
fn uncalled_function_has_no_call_sites() {
    let f = PseudoExpr::Lambda {
        params: vec![binder("p", 1)],
        body: PBox::new(var("p", 1)),
    };
    let expr = PseudoExpr::Let {
        name: "f".to_string(),
        id: Some(VarId::new(100)),
        value: PBox::new(f),
        body: PBox::new(PseudoExpr::Unit),
    };
    let prov = analyze(&expr);
    let f = prov.iter().find(|f| f.name == "f").expect("f present");
    assert_eq!(f.slots[0].1, SlotVerdict::NoCallSites);
}
