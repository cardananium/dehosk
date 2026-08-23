use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

/// Build the canonical Y-comb application:
/// `(fn(v) { rec fn self(x) { v(self, x) } })(driver)`.
fn ycomb_apply(driver: PseudoExpr) -> (VarId, VarId, VarId, PseudoExpr) {
    let v_id = VarId::fresh_binding();
    let self_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let inner_body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var_with_id("v", v_id)),
        args: vec![
            PseudoExpr::var_with_id("self", self_id),
            PseudoExpr::var_with_id("x", x_id),
        ]
        .into(),
    };
    let recfn = PseudoExpr::RecFn {
        name: Binder::new("self", self_id),
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(inner_body),
    };
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("v", v_id)],
        body: PBox::new(recfn),
    };
    let apply = PseudoExpr::Apply {
        function: PBox::new(outer_lambda),
        args: vec![driver].into(),
    };
    (v_id, self_id, x_id, apply)
}

#[test]
fn unfolds_canonical_ycomb_apply_with_non_lambda_driver() {
    // A non-Lambda pure driver (a `Var`) can't beta-reduce, so the unfold
    // output is the plain `RecFn { body: Apply(driver, [self, x]) }` form.
    let driver_var_id = VarId::fresh_binding();
    let driver = PseudoExpr::var_with_id("driver", driver_var_id);
    let driver_clone = driver.clone();
    let (_v_id, self_id, x_id, expr) = ycomb_apply(driver);

    let unfolded = unfold_y_comb_applications(expr);

    let PseudoExpr::RecFn { name, params, body } = unfolded else {
        panic!("expected RecFn after unfold, got something else");
    };
    assert_eq!(name.var_id(), self_id);
    assert_eq!(params.len(), 1);
    assert_eq!(params[0].var_id(), x_id);
    let PseudoExpr::Apply { function, args } = body.into_inner() else {
        panic!("expected Apply body");
    };
    assert_eq!(*function, driver_clone, "function head should be driver");
    assert_eq!(args.len(), 2);
    assert!(matches!(&args[0], PseudoExpr::Var { id: Some(id), .. } if *id == self_id));
    assert!(matches!(&args[1], PseudoExpr::Var { id: Some(id), .. } if *id == x_id));
}

#[test]
fn does_not_unfold_when_driver_is_impure() {
    // `Apply { function: Lambda, args: [impure_apply] }` — driver is
    // an Apply call, not a pure value. Must NOT unfold.
    let impure_driver = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("compute_driver")),
        args: vec![PseudoExpr::int(1)].into(),
    };
    let (_v_id, _self_id, _x_id, expr) = ycomb_apply(impure_driver);

    let result = unfold_y_comb_applications(expr.clone());

    assert!(
        matches!(&result, PseudoExpr::Apply { function, .. }
            if matches!(function.as_ref(), PseudoExpr::Lambda { .. })),
        "impure driver must prevent unfold, got: {:?}",
        result
    );
}

#[test]
fn does_not_unfold_wrong_apply_arity() {
    // Apply with 2 args — not the Y-comb instantiation shape.
    let v_id = VarId::fresh_binding();
    let self_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("v", v_id)],
        body: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("self", self_id),
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("v", v_id)),
                args: vec![
                    PseudoExpr::var_with_id("self", self_id),
                    PseudoExpr::var_with_id("x", x_id),
                ]
                .into(),
            }),
        }),
    };
    let expr = PseudoExpr::Apply {
        function: PBox::new(outer_lambda),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    };

    let result = unfold_y_comb_applications(expr);
    assert!(
        matches!(result, PseudoExpr::Apply { .. }),
        "2-arg Apply must not be unfolded"
    );
}

#[test]
fn does_not_unfold_when_recfn_body_is_not_canonical() {
    // RecFn body returns something OTHER than `v(self, x)` — e.g.,
    // `v(self)` (only one arg). Must NOT unfold.
    let v_id = VarId::fresh_binding();
    let self_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    let outer_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("v", v_id)],
        body: PBox::new(PseudoExpr::RecFn {
            name: Binder::new("self", self_id),
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("v", v_id)),
                args: vec![PseudoExpr::var_with_id("self", self_id)].into(),
            }),
        }),
    };
    let expr = PseudoExpr::Apply {
        function: PBox::new(outer_lambda),
        args: vec![PseudoExpr::Lambda {
            params: vec![Binder::new("x", VarId::fresh_binding())],
            body: PBox::new(PseudoExpr::Unit),
        }]
        .into(),
    };

    let result = unfold_y_comb_applications(expr);
    assert!(
        matches!(result, PseudoExpr::Apply { .. }),
        "non-canonical recfn body must not be unfolded"
    );
}

#[test]
fn beta_reduces_driver_lambda_body_in_unfolded_recfn() {
    // Driver is a 2-param Lambda: the unfolded `driver(self, x)`
    // beta-reduces its params to `self` and `x` in the body.
    let drv_p_self = VarId::fresh_binding();
    let drv_p_x = VarId::fresh_binding();
    let driver = PseudoExpr::Lambda {
        params: vec![
            Binder::new("rec_self", drv_p_self),
            Binder::new("payload", drv_p_x),
        ],
        // body uses both params: `rec_self(payload)`
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("rec_self", drv_p_self)),
            args: vec![PseudoExpr::var_with_id("payload", drv_p_x)].into(),
        }),
    };
    let (_v_id, self_id, x_id, expr) = ycomb_apply(driver);

    let unfolded = unfold_y_comb_applications(expr);
    let PseudoExpr::RecFn { body, .. } = unfolded else {
        panic!("expected RecFn");
    };
    // After beta-reduce, body should be `self_fn(x)` — both driver
    // params substituted away.
    let PseudoExpr::Apply { function, args } = body.into_inner() else {
        panic!("expected Apply body after beta-reduce");
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        panic!("function should be a Var");
    };
    assert_eq!(
        *fn_id, self_id,
        "function should be self_id after substitution"
    );
    assert_eq!(args.len(), 1);
    let PseudoExpr::Var {
        id: Some(arg_id), ..
    } = &args[0]
    else {
        panic!("arg should be a Var");
    };
    assert_eq!(*arg_id, x_id, "arg should be x_id after substitution");
}

#[test]
fn does_not_beta_reduce_when_driver_lambda_has_wrong_arity() {
    // Driver is a 3-param Lambda — apply has 2 args. Beta-reduce
    // must NOT fire; the unfolded recfn body keeps the Apply intact.
    let driver = PseudoExpr::Lambda {
        params: vec![
            Binder::new("a", VarId::fresh_binding()),
            Binder::new("b", VarId::fresh_binding()),
            Binder::new("c", VarId::fresh_binding()),
        ],
        body: PBox::new(PseudoExpr::Unit),
    };
    let (_v_id, _self_id, _x_id, expr) = ycomb_apply(driver);

    let unfolded = unfold_y_comb_applications(expr);
    let PseudoExpr::RecFn { body, .. } = unfolded else {
        panic!("expected RecFn");
    };
    assert!(
        matches!(*body, PseudoExpr::Apply { .. }),
        "3-param driver must not beta-reduce against 2 args"
    );
}

#[test]
fn nested_ycomb_apply_unfolds_inside_let_body() {
    // `let outer = <ycomb_apply driver> in outer` — verify the pass
    // descends into Let.value.
    let driver = PseudoExpr::Lambda {
        params: vec![Binder::new("p", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::int(7)),
    };
    let (_, _, _, ycomb) = ycomb_apply(driver);
    let outer_id = VarId::fresh_binding();
    let expr = PseudoExpr::Let {
        name: "outer".into(),
        id: Some(outer_id),
        value: PBox::new(ycomb),
        body: PBox::new(PseudoExpr::var_with_id("outer", outer_id)),
    };

    let result = unfold_y_comb_applications(expr);
    let PseudoExpr::Let { value, .. } = result else {
        panic!("expected outer Let preserved");
    };
    assert!(
        matches!(*value, PseudoExpr::RecFn { .. }),
        "Let.value should have been unfolded into RecFn, got {:?}",
        value
    );
}
