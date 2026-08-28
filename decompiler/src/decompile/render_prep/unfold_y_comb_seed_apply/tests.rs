use super::*;
use crate::pseudo::ast::PseudoExpr;

/// The ids a built tree exposes to its assertions.
struct Ids {
    driver: VarId,
    seed: VarId,
    arg_param: VarId,
}

/// `fn(u) { f(f, u) }` — the seed shape, over an arbitrary `f`.
fn self_app(f: VarId, f_name: &str) -> PseudoExpr {
    let u = VarId::fresh_binding();
    PseudoExpr::Lambda {
        params: vec![Binder::new("u", u)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id(f_name, f)),
            args: vec![
                PseudoExpr::var_with_id(f_name, f),
                PseudoExpr::var_with_id("u", u),
            ]
            .into(),
        }),
    }
}

/// The whole textbook-Z shape this pass exists for:
///
/// ```text
/// let d = fn(self, x) { <driver_body> }
/// let s = fn(w) { d(fn(u) { w(w, u) }) }
/// d(fn(v) { s(s, v) }, <call_args…>)
/// ```
///
/// `driver_body` is built by `body_of(self_id, arg_id)`.
fn textbook_z(
    body_of: impl FnOnce(VarId, VarId) -> PseudoExpr,
    call_args: Vec<PseudoExpr>,
) -> (Ids, PseudoExpr) {
    let driver = VarId::fresh_binding();
    let seed = VarId::fresh_binding();
    let self_param = VarId::fresh_binding();
    let arg_param = VarId::fresh_binding();
    let w = VarId::fresh_binding();

    let driver_value = PseudoExpr::Lambda {
        params: vec![Binder::new("self", self_param), Binder::new("x", arg_param)],
        body: PBox::new(body_of(self_param, arg_param)),
    };
    let seed_value = PseudoExpr::Lambda {
        params: vec![Binder::new("w", w)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("d", driver)),
            args: vec![self_app(w, "w")].into(),
        }),
    };
    let mut args = vec![self_app(seed, "s")];
    args.extend(call_args);

    let expr = PseudoExpr::Let {
        name: "d".to_string(),
        id: Some(driver),
        value: PBox::new(driver_value),
        body: PBox::new(PseudoExpr::Let {
            name: "s".to_string(),
            id: Some(seed),
            value: PBox::new(seed_value),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("d", driver)),
                args: args.into(),
            }),
        }),
    };
    (
        Ids {
            driver,
            seed,
            arg_param,
        },
        expr,
    )
}

/// `self(x)` — the driver body's recursive call.
fn self_call(self_id: VarId, arg_id: VarId) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("self", self_id)),
        args: vec![PseudoExpr::var_with_id("x", arg_id)].into(),
    }
}

/// The `let d = …` of a rewritten tree, with the seed's binding gone.
fn expect_driver_let(expr: PseudoExpr, ids: &Ids) -> (PseudoExpr, PseudoExpr) {
    let PseudoExpr::Let {
        id, value, body, ..
    } = expr
    else {
        panic!("expected the driver's Let to survive");
    };
    assert_eq!(id, Some(ids.driver));
    (value.into_inner(), body.into_inner())
}

#[test]
fn rewrites_the_driver_into_a_recfn_and_drops_the_seed() {
    let (ids, expr) = textbook_z(self_call, vec![PseudoExpr::Int(7.into())]);

    let (value, body) = expect_driver_let(unfold_y_comb_seed_applications(expr), &ids);

    // `fn(self, x) { self(x) }` → `rec fn d(x) { d(x) }`.
    let PseudoExpr::RecFn {
        name,
        params,
        body: rec_body,
    } = value
    else {
        panic!("expected the driver's value to become a RecFn");
    };
    assert_eq!(
        name.var_id(),
        ids.driver,
        "the rec fn binds the driver's id"
    );
    assert_eq!(
        params.iter().map(Binder::var_id).collect::<Vec<_>>(),
        vec![ids.arg_param],
        "the self parameter is dropped, the value parameter kept",
    );
    let PseudoExpr::Apply { function, .. } = rec_body.into_inner() else {
        panic!("expected the recursive call to survive");
    };
    assert!(
        matches!(*function, PseudoExpr::Var { id: Some(id), .. } if id == ids.driver),
        "the self parameter reads as a self-reference",
    );

    // The seed's binding is gone and the call lost its seed argument.
    let PseudoExpr::Apply { function, args } = body else {
        panic!("expected the seed's Let to be dropped, leaving the call");
    };
    assert!(matches!(*function, PseudoExpr::Var { id: Some(id), .. } if id == ids.driver));
    assert_eq!(args.len(), 1, "only the real argument is left");
    assert_eq!(args[0], PseudoExpr::Int(7.into()));
}

#[test]
fn a_seedless_call_collapses_to_the_bare_reference() {
    // `fix(d)` with nothing applied to it: the call is only the seed, so
    // dropping that argument leaves the driver's name alone.
    let (ids, expr) = textbook_z(self_call, vec![]);

    let (_value, body) = expect_driver_let(unfold_y_comb_seed_applications(expr), &ids);

    assert!(
        matches!(body, PseudoExpr::Var { id: Some(id), .. } if id == ids.driver),
        "a call with no arguments beyond the seed becomes the bare reference, got {body:?}",
    );
}

#[test]
fn declines_when_the_driver_is_read_at_its_two_parameter_arity() {
    // A second, UNSEEDED use of `d` means something reads it as the
    // two-parameter generator. Rewriting it to one parameter would
    // change what that use denotes, so the whole unfold is declined.
    let (ids, expr) = textbook_z(self_call, vec![]);
    let leaked = PseudoExpr::Let {
        name: "leak".to_string(),
        id: Some(VarId::fresh_binding()),
        value: PBox::new(PseudoExpr::var_with_id("d", ids.driver)),
        body: PBox::new(expr),
    };
    let before = leaked.clone();

    assert_eq!(
        unfold_y_comb_seed_applications(leaked),
        before,
        "an extra use of the driver must decline the unfold",
    );
}

#[test]
fn declines_when_the_seed_is_used_outside_the_seeding_lambda() {
    let (ids, expr) = textbook_z(self_call, vec![]);
    let leaked = PseudoExpr::Let {
        name: "leak".to_string(),
        id: Some(VarId::fresh_binding()),
        value: PBox::new(PseudoExpr::Int(1.into())),
        body: PBox::new(match expr {
            // Reach inside to append a stray `s` reference to the call.
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => PseudoExpr::Let {
                name,
                id,
                value,
                body: PBox::new(match body.into_inner() {
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body: PBox::new(match body.into_inner() {
                            PseudoExpr::Apply { function, args } => {
                                let mut args = args.into_vec();
                                args.push(PseudoExpr::var_with_id("s", ids.seed));
                                PseudoExpr::Apply {
                                    function,
                                    args: args.into(),
                                }
                            }
                            other => other,
                        }),
                    },
                    other => other,
                }),
            },
            other => other,
        }),
    };
    let before = leaked.clone();

    assert_eq!(
        unfold_y_comb_seed_applications(leaked),
        before,
        "a use of the seed that is not a seeding must decline the unfold",
    );
}

#[test]
fn leaves_the_half_z_in_function_position_alone() {
    // `unfold_y_comb_apply`'s shape — the half-Z applied to the driver —
    // is not this pass's business; it must pass through untouched.
    let v = VarId::fresh_binding();
    let self_id = VarId::fresh_binding();
    let x = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("v", v)],
            body: PBox::new(PseudoExpr::RecFn {
                name: Binder::new("self", self_id),
                params: vec![Binder::new("x", x)],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("v", v)),
                    args: vec![
                        PseudoExpr::var_with_id("self", self_id),
                        PseudoExpr::var_with_id("x", x),
                    ]
                    .into(),
                }),
            }),
        }),
        args: vec![PseudoExpr::var_with_id("driver", VarId::fresh_binding())].into(),
    };
    let before = expr.clone();

    assert_eq!(unfold_y_comb_seed_applications(expr), before);
}
