use super::*;

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

/// `fn yc(v) { rec fn s(x) { v(s, x) } }` as a Let value.
fn half_z_value() -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder("v", 100)],
        body: PBox::new(PseudoExpr::RecFn {
            name: binder("s", 101),
            params: vec![binder("x", 102)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(varref("v", 100)),
                args: vec![varref("s", 101), varref("x", 102)].into(),
            }),
        }),
    }
}

/// Driver `fn(self_p, arg_p) { self_p(arg_p) }`.
fn driver(self_id: u32, arg_id: u32) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder("self_p", self_id), binder("arg_p", arg_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("self_p", self_id)),
            args: vec![varref("arg_p", arg_id)].into(),
        }),
    }
}

/// `let yc = <half-Z>; let b = yc(driver); b` unfolds the call and
/// re-displays the rec fn + self-calls as `b`.
#[test]
fn unfolds_let_value_call_site() {
    let input = PseudoExpr::Let {
        name: "yc".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(half_z_value()),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(VarId::new(20)),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(varref("yc", 10)),
                args: vec![driver(200, 201)].into(),
            }),
            body: PBox::new(varref("b", 20)),
        }),
    };
    let out = unfold_y_comb_helper_applications(input);
    let expected_value = PseudoExpr::RecFn {
        name: binder("b", 200),
        params: vec![binder("arg_p", 201)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("b", 200)),
            args: vec![varref("arg_p", 201)].into(),
        }),
    };
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected outer let, got: {out:?}");
    };
    let inner = body.into_inner();
    let PseudoExpr::Let { value, .. } = inner else {
        panic!("expected inner let, got: {inner:?}");
    };
    assert_eq!(*value, expected_value);
}

/// A non-let call position keeps the driver's self-param display name.
#[test]
fn unfolds_bare_call_site_keeping_driver_name() {
    let input = PseudoExpr::Let {
        name: "yc".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(half_z_value()),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("f", 30)),
            args: vec![PseudoExpr::Apply {
                function: PBox::new(varref("yc", 10)),
                args: vec![driver(200, 201)].into(),
            }]
            .into(),
        }),
    };
    let out = unfold_y_comb_helper_applications(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected outer let");
    };
    let PseudoExpr::Apply { args, .. } = body.into_inner() else {
        panic!("expected f(...) apply");
    };
    let expected = PseudoExpr::RecFn {
        name: binder("self_p", 200),
        params: vec![binder("arg_p", 201)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("self_p", 200)),
            args: vec![varref("arg_p", 201)].into(),
        }),
    };
    assert_eq!(args[0], expected);
}

/// An APPLIED instantiation (`yc(driver, descent)`) unfolds to the
/// define-then-call block: `let self_p = rec fn self_p(arg_p) { … };
/// self_p(descent)` with a FRESH let-binder id wired to the call.
#[test]
fn unfolds_applied_call_site() {
    let call = PseudoExpr::Apply {
        function: PBox::new(varref("yc", 10)),
        args: vec![driver(200, 201), varref("descent", 50)].into(),
    };
    let input = PseudoExpr::Let {
        name: "yc".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(half_z_value()),
        body: PBox::new(call),
    };
    let out = unfold_y_comb_helper_applications(input);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("expected outer yc let, got: {out:?}");
    };
    let inner = body.into_inner();
    let PseudoExpr::Let {
        name,
        id: Some(let_id),
        value,
        body: call_body,
    } = inner
    else {
        panic!("expected define-then-call let, got: {inner:?}");
    };
    assert_eq!(name, "self_p");
    assert_ne!(let_id, VarId::new(200), "let binder must be FRESH");
    let PseudoExpr::RecFn { name: rec_name, .. } = value.as_ref() else {
        panic!("expected rec fn value, got: {value:?}");
    };
    assert_eq!(rec_name.display_name(), "self_p");
    assert_eq!(rec_name.var_id(), VarId::new(200));
    let call_body = call_body.into_inner();
    let PseudoExpr::Apply { function, args } = call_body else {
        panic!("expected call body, got: {call_body:?}");
    };
    assert_eq!(
        *function,
        PseudoExpr::Var {
            name: "self_p".to_string(),
            id: Some(let_id),
        },
        "call must reference the LET binder, not the rec-fn name"
    );
    assert_eq!(args, vec![varref("descent", 50)].into());
}

/// Deeper applications (3+ args) are left alone.
#[test]
fn veto_three_args() {
    let call = PseudoExpr::Apply {
        function: PBox::new(varref("yc", 10)),
        args: vec![driver(200, 201), varref("descent", 50), varref("more", 51)].into(),
    };
    let input = PseudoExpr::Let {
        name: "yc".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(half_z_value()),
        body: PBox::new(call),
    };
    let out = unfold_y_comb_helper_applications(input.clone());
    assert_eq!(out, input);
}

/// A non-lambda driver (value in the self slot) is left alone.
#[test]
fn veto_non_lambda_driver() {
    let input = PseudoExpr::Let {
        name: "yc".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(half_z_value()),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("yc", 10)),
            args: vec![varref("not_a_lambda", 60)].into(),
        }),
    };
    let out = unfold_y_comb_helper_applications(input.clone());
    assert_eq!(out, input);
}

/// The flattened variant `fn(v1, v3) { v1(fn(x) { v3(v3, x) }) }` fails
/// the half-Z predicate (2 outer params, no inner RecFn).
#[test]
fn gov_flattened_variant_is_not_half_z() {
    let flattened = PseudoExpr::Lambda {
        params: vec![binder("v1", 300), binder("v3", 301)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(varref("v1", 300)),
            args: vec![PseudoExpr::Lambda {
                params: vec![binder("x", 302)],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(varref("v3", 301)),
                    args: vec![varref("v3", 301), varref("x", 302)].into(),
                }),
            }]
            .into(),
        }),
    };
    assert!(!is_half_z_lambda(&flattened));
}

/// A helper id bound TWICE program-wide (VarId collision) is excluded.
#[test]
fn veto_collided_helper_id() {
    let call = PseudoExpr::Apply {
        function: PBox::new(varref("yc", 10)),
        args: vec![driver(200, 201)].into(),
    };
    let input = PseudoExpr::Let {
        name: "yc".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(half_z_value()),
        body: PBox::new(PseudoExpr::Let {
            // Same VarId bound again — collision.
            name: "yc2".to_string(),
            id: Some(VarId::new(10)),
            value: PBox::new(PseudoExpr::int(1)),
            body: PBox::new(call),
        }),
    };
    let out = unfold_y_comb_helper_applications(input.clone());
    assert_eq!(out, input);
}
