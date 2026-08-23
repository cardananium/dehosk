use super::*;

fn binder(name: &str, id: VarId) -> Binder {
    Binder::new(name, id)
}

fn var(name: &str, id: VarId) -> PseudoExpr {
    PseudoExpr::var_with_id(name, id)
}

/// `fn callee(a, b, z) {…}` (3-ary) + `rec fn o(dead) { callee(a, b) }`
/// → `rec fn o(z) { callee(a, b, z) }`.
#[test]
fn saturates_dead_param_knot() {
    let callee = VarId::fresh_binding();
    let o = VarId::fresh_binding();
    let dead = VarId::fresh_binding();
    let callee_lam = PseudoExpr::Lambda {
        params: vec![
            binder("a", VarId::fresh_binding()),
            binder("b", VarId::fresh_binding()),
            binder("z", VarId::fresh_binding()),
        ],
        body: PBox::new(PseudoExpr::Unit),
    };
    let rec = PseudoExpr::RecFn {
        name: binder("o", o),
        params: vec![binder("dead", dead)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("callee", callee)),
            args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
        }),
    };
    let expr = PseudoExpr::Let {
        name: "callee".into(),
        id: Some(callee),
        value: PBox::new(callee_lam),
        body: PBox::new(rec),
    };
    let out = saturate_dead_param_knot(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected Let")
    };
    let PseudoExpr::RecFn { params, body, .. } = body.into_inner() else {
        panic!("expected RecFn")
    };
    assert_eq!(params.len(), 1);
    assert_eq!(
        params[0].name, "z",
        "param renamed to callee's trailing param"
    );
    let PseudoExpr::Apply { args, .. } = body.into_inner() else {
        panic!("expected Apply")
    };
    assert_eq!(
        args.len(),
        3,
        "callee now saturated with the appended param"
    );
    assert!(matches!(&args[2], PseudoExpr::Var { id: Some(v), .. } if *v == dead));
}

/// A used parameter is left alone (not the dummy-thunk shape).
#[test]
fn leaves_used_param() {
    let callee = VarId::fresh_binding();
    let p = VarId::fresh_binding();
    let callee_lam = PseudoExpr::Lambda {
        params: vec![
            binder("a", VarId::fresh_binding()),
            binder("z", VarId::fresh_binding()),
        ],
        body: PBox::new(PseudoExpr::Unit),
    };
    let rec = PseudoExpr::RecFn {
        name: binder("o", VarId::fresh_binding()),
        params: vec![binder("p", p)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("callee", callee)),
            args: vec![var("p", p)].into(), // p is USED
        }),
    };
    let expr = PseudoExpr::Let {
        name: "callee".into(),
        id: Some(callee),
        value: PBox::new(callee_lam),
        body: PBox::new(rec),
    };
    let out = saturate_dead_param_knot(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!()
    };
    let PseudoExpr::RecFn { body, .. } = body.into_inner() else {
        panic!()
    };
    let PseudoExpr::Apply { args, .. } = body.into_inner() else {
        panic!()
    };
    assert_eq!(args.len(), 1, "used param → not saturated");
}

/// Unknown callee arity → left alone (fail-closed).
#[test]
fn leaves_unknown_callee() {
    let rec = PseudoExpr::RecFn {
        name: binder("o", VarId::fresh_binding()),
        params: vec![binder("dead", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("mystery", VarId::fresh_binding())),
            args: vec![PseudoExpr::int(1)].into(),
        }),
    };
    let out = saturate_dead_param_knot(rec);
    let PseudoExpr::RecFn { body, .. } = out else {
        panic!()
    };
    let PseudoExpr::Apply { args, .. } = body.into_inner() else {
        panic!()
    };
    assert_eq!(args.len(), 1, "unknown arity → unchanged");
}
