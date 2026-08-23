use crate::pseudo::ast::PBox;
use num_bigint::BigInt;

use super::recover_pair_fixpoint;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

// ---------------------------------------------------------------------
// recover_pair_fixpoint — church-pair U-comb seed
// ---------------------------------------------------------------------

// Template binder ids (see pair_fix.rs docs).
const E: u32 = 65; // pair Let binder
const F: u32 = 131; // U-comb RecFn (let id == name id)
const P0: u32 = 133; // f param 0 (driver slot)
const P1: u32 = 134; // f param 1 (consumer slot)
const G: u32 = 135; // knot Let binder
const W: u32 = 136; // knot lambda param
const A0: u32 = 140; // inj0 param
const A1: u32 = 137; // inj1 param
const D0: u32 = 66; // driver param 0 (the injected selector)
const D1: u32 = 67; // driver param 1 (pair-first continuation)
const D2: u32 = 68; // driver param 2 (pair-second continuation)
const PA0: u32 = 74; // armA param 0
const PA1: u32 = 75; // armA param 1
const PB0: u32 = 69; // armB param
const T0: u32 = 70; // nil clause fabricated trailing binder
const T1H: u32 = 71; // cons head
const T1T: u32 = 72; // cons tail
const T1V: u32 = 73; // cons fabricated trailing binder

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::Var {
        name: name.to_string(),
        id: Some(VarId::new(id)),
    }
}

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name, VarId::new(id))
}

fn apply(function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(function),
        args: args.into(),
    }
}

fn lambda(params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Lambda {
        params,
        body: PBox::new(body),
    }
}

fn plet(name: &str, id: u32, value: PseudoExpr, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: name.to_string(),
        id: Some(VarId::new(id)),
        value: PBox::new(value),
        body: PBox::new(body),
    }
}

fn int(n: i64) -> PseudoExpr {
    PseudoExpr::Int(BigInt::from(n))
}

/// One injector: `fn(a) { g(Constr{tag, [a]}) }`.
fn injector(param_id: u32, tag: usize) -> PseudoExpr {
    lambda(
        vec![binder("a", param_id)],
        apply(
            var("rec_fn_3", G),
            vec![PseudoExpr::constr(
                ConstructorShape::unknown_data(tag, 1),
                vec![var("a", param_id)],
            )],
        ),
    )
}

/// armA: `fn(pa0, pa1) { d2(pa0, pa1) }` — the second continuation is
/// used as a saturated 2-arg call.
fn arm_a() -> PseudoExpr {
    lambda(
        vec![binder("x_15", PA0), binder("y_12", PA1)],
        apply(var("z_4", D2), vec![var("x_15", PA0), var("y_12", PA1)]),
    )
}

/// armB: `fn(pb0) { when pb0 is { C0(t0) -> t0; C1(h,t,v) ->
/// if d1(h, v) { False } else { d2(t, v) } } }` — fabricated arities
/// 1 / 3 with the trailing binder of each clause being the absorbed
/// values argument.
fn arm_b() -> PseudoExpr {
    let nil_clause = WhenClause {
        pattern: WhenPattern::constructor(
            ConstructorShape::unknown_data(0, 1),
            vec![binder("v_70", T0)],
        ),
        guard: None,
        body: var("v_70", T0),
    };
    let cons_clause = WhenClause {
        pattern: WhenPattern::constructor(
            ConstructorShape::unknown_data(1, 3),
            vec![
                binder("v_71", T1H),
                binder("v_72", T1T),
                binder("v_73", T1V),
            ],
        ),
        guard: None,
        body: PseudoExpr::If {
            condition: PBox::new(apply(
                var("y_11", D1),
                vec![var("v_71", T1H), var("v_73", T1V)],
            )),
            then_branch: PBox::new(PseudoExpr::Bool(false)),
            else_branch: PBox::new(apply(
                var("z_4", D2),
                vec![var("v_72", T1T), var("v_73", T1V)],
            )),
        },
    };
    lambda(
        vec![binder("x_32", PB0)],
        PseudoExpr::When {
            subject: PBox::new(var("x_32", PB0)),
            subject_name: None,
            clauses: vec![nil_clause, cons_clause],
        },
    )
}

fn driver() -> PseudoExpr {
    lambda(
        vec![binder("x_14", D0), binder("y_11", D1), binder("z_4", D2)],
        apply(var("x_14", D0), vec![arm_a(), arm_b()]),
    )
}

/// The full `let e = (let f = rec fn f(p0,p1){…} in Force(f(driver)))`
/// template with the given consumer body.
fn pair_seed_with(consumer: PseudoExpr, driver_expr: PseudoExpr) -> PseudoExpr {
    let knot = lambda(
        vec![binder("v_136", W)],
        apply(
            PseudoExpr::Force(PBox::new(apply(var("rec_fn_4", F), vec![var("v_133", P0)]))),
            vec![apply(
                PseudoExpr::Force(PBox::new(var("v_133", P0))),
                vec![var("v_136", W)],
            )],
        ),
    );
    let tail = apply(var("v_134", P1), vec![injector(A0, 0), injector(A1, 1)]);
    let f_rec = PseudoExpr::RecFn {
        name: binder("rec_fn_4", F),
        params: vec![binder("v_133", P0), binder("v_134", P1)],
        body: PBox::new(plet("rec_fn_3", G, knot, tail)),
    };
    let partial = PseudoExpr::Force(PBox::new(apply(var("rec_fn_4", F), vec![driver_expr])));
    plet("e", E, plet("rec_fn_4", F, f_rec, partial), consumer)
}

/// `e.1st(1, 2)` — the recognized first-projection application.
fn fst_projection_call() -> PseudoExpr {
    apply(
        PseudoExpr::FieldAccess {
            record: PBox::new(var("e", E)),
            selector: FieldSelector::PairFst,
        },
        vec![int(1), int(2)],
    )
}

#[test]
fn pair_fixpoint_recovers_two_named_mutually_recursive_fns() {
    let seed = pair_seed_with(fst_projection_call(), driver());
    let result = recover_pair_fixpoint(seed);

    // Outer: let check_param_value = rec fn check_param_value(pa0, pa1)
    let PseudoExpr::Let {
        name,
        id: Some(f1_id),
        value,
        body: consumer,
    } = result
    else {
        panic!("expected outer let, got something else");
    };
    assert_eq!(name, "check_param_value");
    let PseudoExpr::RecFn {
        name: f1_name,
        params: f1_params,
        body: f1_body,
    } = value.into_inner()
    else {
        panic!("expected RecFn value");
    };
    assert_eq!(f1_name.var_id(), f1_id, "let/rec same-id convention");
    assert_eq!(
        f1_params.iter().map(Binder::var_id).collect::<Vec<_>>(),
        vec![VarId::new(PA0), VarId::new(PA1)],
        "F1 params come from armA's OWN params"
    );

    // Inner: let check_param_list = rec fn check_param_list(pb0, values)
    let PseudoExpr::Let {
        name: f2_let_name,
        id: Some(f2_id),
        value: f2_value,
        body: f1_tail,
    } = f1_body.into_inner()
    else {
        panic!("expected nested check_param_list let");
    };
    assert_eq!(f2_let_name, "check_param_list");
    let PseudoExpr::RecFn {
        name: f2_name,
        params: f2_params,
        body: f2_body,
    } = f2_value.into_inner()
    else {
        panic!("expected inner RecFn");
    };
    assert_eq!(f2_name.var_id(), f2_id);
    assert_eq!(f2_params.len(), 2, "eta-expanded to the 2 honest params");
    assert_eq!(f2_params[0].var_id(), VarId::new(PB0));
    let values_id = f2_params[1].var_id();
    assert_eq!(f2_params[1].as_str(), "values");

    // F2 body: when pb0 is { C0 -> values; C1(h, t) -> if F1(h, values)
    // { False } else { F2(t, values) } } — arities collapsed to 0 / 2,
    // trailing binders redirected to `values`, polarity untouched.
    let PseudoExpr::When { clauses, .. } = f2_body.into_inner() else {
        panic!("expected When body");
    };
    assert_eq!(clauses.len(), 2);
    let WhenPattern::Constructor { tag: 0, fields, .. } = &clauses[0].pattern else {
        panic!("expected nil pattern");
    };
    assert!(fields.is_empty(), "nil arity collapsed to 0");
    assert!(
        matches!(&clauses[0].body, PseudoExpr::Var { id, .. } if *id == Some(values_id)),
        "nil trailing binder redirected to the values param"
    );
    let WhenPattern::Constructor {
        tag: 1,
        fields: cons_fields,
        ..
    } = &clauses[1].pattern
    else {
        panic!("expected cons pattern");
    };
    assert_eq!(
        cons_fields.iter().map(Binder::var_id).collect::<Vec<_>>(),
        vec![VarId::new(T1H), VarId::new(T1T)],
        "cons arity collapsed to 2 (head, tail)"
    );
    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = &clauses[1].body
    else {
        panic!("expected If in cons body");
    };
    // d1 -> check_param_value, trailing -> values
    let PseudoExpr::Apply { function, args } = &**condition else {
        panic!("expected call condition");
    };
    assert!(matches!(&**function, PseudoExpr::Var { id, .. } if *id == Some(f1_id)));
    assert!(matches!(&args[1], PseudoExpr::Var { id, .. } if *id == Some(values_id)));
    assert!(
        matches!(&**then_branch, PseudoExpr::Bool(false)),
        "polarity preserved"
    );
    // d2 -> check_param_list
    let PseudoExpr::Apply { function: ef, .. } = &**else_branch else {
        panic!("expected recursive call in else");
    };
    assert!(matches!(&**ef, PseudoExpr::Var { id, .. } if *id == Some(f2_id)));

    // F1 tail = armA body with d2 -> check_param_list.
    let PseudoExpr::Apply { function: tf, .. } = f1_tail.into_inner() else {
        panic!("expected armA body call");
    };
    assert!(matches!(&*tf, PseudoExpr::Var { id, .. } if *id == Some(f2_id)));

    // Consumer: e.1st(1, 2) -> check_param_value(1, 2).
    let PseudoExpr::Apply {
        function: cf,
        args: cargs,
    } = consumer.into_inner()
    else {
        panic!("expected rewritten consumer call");
    };
    assert!(
        matches!(&*cf, PseudoExpr::Var { name, id } if name == "check_param_value" && *id == Some(f1_id))
    );
    assert_eq!(cargs.len(), 2);
}

#[test]
fn pair_fixpoint_is_idempotent_on_its_own_output() {
    let once = recover_pair_fixpoint(pair_seed_with(fst_projection_call(), driver()));
    let twice = recover_pair_fixpoint(once.clone());
    assert_eq!(format!("{once:?}"), format!("{twice:?}"));
}

#[test]
fn pair_fixpoint_inert_on_single_param_z_shape() {
    // rec fn f(p0) { … } — the Z-combinator family, NOT the pair shape.
    let z_like = plet(
        "e",
        E,
        plet(
            "rec_fn_4",
            F,
            PseudoExpr::RecFn {
                name: binder("rec_fn_4", F),
                params: vec![binder("v_133", P0)],
                body: PBox::new(apply(var("v_133", P0), vec![var("rec_fn_4", F)])),
            },
            apply(
                var("rec_fn_4", F),
                vec![lambda(vec![binder("x", 500)], int(0))],
            ),
        ),
        fst_projection_call(),
    );
    let before = format!("{z_like:?}");
    let after = recover_pair_fixpoint(z_like);
    assert_eq!(
        before,
        format!("{after:?}"),
        "single-param Z shape must be inert"
    );
}

#[test]
fn pair_fixpoint_inert_on_non_total_consumer() {
    // A second, BARE use of the pair value outside the recognized
    // projection-application form must abort the whole transform.
    let consumer = PseudoExpr::Tuple((vec![fst_projection_call(), var("e", E)]).into());
    let seed = pair_seed_with(consumer, driver());
    let before = format!("{seed:?}");
    let after = recover_pair_fixpoint(seed);
    assert_eq!(
        before,
        format!("{after:?}"),
        "non-total consumer must be inert"
    );
}

#[test]
fn pair_fixpoint_inert_on_second_projection_use() {
    // `e.2nd(…)` cannot be served by the nested scoping — fail closed.
    let snd_call = apply(
        PseudoExpr::FieldAccess {
            record: PBox::new(var("e", E)),
            selector: FieldSelector::PairSnd,
        },
        vec![int(1), int(2)],
    );
    let seed = pair_seed_with(snd_call, driver());
    let before = format!("{seed:?}");
    let after = recover_pair_fixpoint(seed);
    assert_eq!(before, format!("{after:?}"), "snd projection must be inert");
}

#[test]
fn pair_fixpoint_inert_on_non_literal_driver() {
    let seed = pair_seed_with(fst_projection_call(), var("some_fn", 600));
    let before = format!("{seed:?}");
    let after = recover_pair_fixpoint(seed);
    assert_eq!(
        before,
        format!("{after:?}"),
        "non-literal driver must be inert"
    );
}

#[test]
fn pair_fixpoint_inert_on_unsaturated_continuation_use() {
    // armA passes d2 as a VALUE instead of calling it with 2 args —
    // outside the saturated-call proof, must be inert.
    let bad_arm_a = lambda(
        vec![binder("x_15", PA0), binder("y_12", PA1)],
        PseudoExpr::Tuple((vec![var("z_4", D2)]).into()),
    );
    let bad_driver = lambda(
        vec![binder("x_14", D0), binder("y_11", D1), binder("z_4", D2)],
        apply(var("x_14", D0), vec![bad_arm_a, arm_b()]),
    );
    let seed = pair_seed_with(fst_projection_call(), bad_driver);
    let before = format!("{seed:?}");
    let after = recover_pair_fixpoint(seed);
    assert_eq!(
        before,
        format!("{after:?}"),
        "value-position continuation use must be inert"
    );
}
