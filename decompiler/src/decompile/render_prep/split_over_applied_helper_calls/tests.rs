use super::*;
use crate::pseudo::ast::Binder;

fn lam(params: &[(&str, u32)], body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: params
            .iter()
            .map(|(n, i)| Binder::new(n.to_string(), VarId::new(*i)))
            .collect(),
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

fn call(name: &str, id: u32, args: Vec<PseudoExpr>) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id(name, VarId::new(id))),
        args: args.into(),
    }
}

fn arg(n: u32) -> PseudoExpr {
    PseudoExpr::var_with_id("arg", VarId::new(1000 + n))
}

/// Def is a 2-param Lambda whose body tail is a bare 1-param Lambda;
/// a 3-arg call splits to `f(a,b)(c)`.
#[test]
fn splits_lambda_tail_three_arg_call() {
    // let h = fn(a, b) { fn(c) { c } } in h(arg0, arg1, arg2)
    let def = lam(&[("a", 1), ("b", 2)], lam(&[("c", 3)], arg(3)));
    let body = call("h", 7, vec![arg(0), arg(1), arg(2)]);
    let tree = let_("h", 7, def, body);
    let out = split_over_applied_helper_calls(tree);
    let PseudoExpr::Let { body, .. } = out else {
        panic!()
    };
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        panic!("expected split outer Apply, got {body:?}");
    };
    assert_eq!(args.len(), 1, "outer apply should take the K args");
    let PseudoExpr::Apply {
        args: inner_args, ..
    } = function.as_ref()
    else {
        panic!("expected inner Apply, got {function:?}");
    };
    assert_eq!(inner_args.len(), 2, "inner apply should take the N args");
}

/// Body tail is `Let{x = RecFn[1 param]; Var(x)}`.
#[test]
fn splits_recfn_via_local_let_tail() {
    let rec = PseudoExpr::RecFn {
        name: Binder::new("x21".to_string(), VarId::new(20)),
        params: vec![Binder::new("y12".to_string(), VarId::new(21))],
        body: PBox::new(arg(0)),
    };
    let def = lam(
        &[("a", 1), ("b", 2)],
        let_(
            "x21",
            20,
            rec,
            PseudoExpr::var_with_id("x21", VarId::new(20)),
        ),
    );
    let body = call("h", 7, vec![arg(0), arg(1), arg(2)]);
    let tree = let_("h", 7, def, body);
    let out = split_over_applied_helper_calls(tree);
    let PseudoExpr::Let { body, .. } = out else {
        panic!()
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Apply { function, args }
            if args.len() == 1 && matches!(function.as_ref(), PseudoExpr::Apply { args, .. } if args.len() == 2)),
        "recfn-tail helper should split, got {body:?}"
    );
}

/// Exactly-saturated call (m == N) is untouched.
#[test]
fn keeps_exactly_saturated_call() {
    let def = lam(&[("a", 1), ("b", 2)], lam(&[("c", 3)], arg(3)));
    let body = call("h", 7, vec![arg(0), arg(1)]);
    let tree = let_("h", 7, def, body.clone());
    let out = split_over_applied_helper_calls(tree);
    let PseudoExpr::Let { body: out_body, .. } = out else {
        panic!()
    };
    assert_eq!(*out_body, body, "m == N call must be untouched");
}

/// Over-over-application (m > N+K) is untouched (no multi-level split).
#[test]
fn keeps_over_over_application() {
    let def = lam(&[("a", 1), ("b", 2)], lam(&[("c", 3)], arg(3)));
    let body = call("h", 7, vec![arg(0), arg(1), arg(2), arg(4)]); // N+K=3, given 4
    let tree = let_("h", 7, def, body.clone());
    let out = split_over_applied_helper_calls(tree);
    let PseudoExpr::Let { body: out_body, .. } = out else {
        panic!()
    };
    assert_eq!(*out_body, body, "m > N+K call must be untouched");
}

/// Non-function tail (body returns a When) yields no candidate.
#[test]
fn non_function_tail_not_a_candidate() {
    let def = lam(
        &[("a", 1), ("b", 2)],
        PseudoExpr::When {
            subject: PBox::new(arg(0)),
            subject_name: None,
            clauses: vec![],
        },
    );
    let body = call("h", 7, vec![arg(0), arg(1), arg(2)]);
    let tree = let_("h", 7, def, body.clone());
    let out = split_over_applied_helper_calls(tree);
    let PseudoExpr::Let { body: out_body, .. } = out else {
        panic!()
    };
    assert_eq!(
        *out_body, body,
        "non-function-returning helper is not a candidate"
    );
}

/// Idempotent: a second run is a no-op.
#[test]
fn idempotent() {
    let def = lam(&[("a", 1), ("b", 2)], lam(&[("c", 3)], arg(3)));
    let body = call("h", 7, vec![arg(0), arg(1), arg(2)]);
    let tree = let_("h", 7, def, body);
    let once = split_over_applied_helper_calls(tree);
    let twice = split_over_applied_helper_calls(once.clone());
    assert_eq!(once, twice);
}
