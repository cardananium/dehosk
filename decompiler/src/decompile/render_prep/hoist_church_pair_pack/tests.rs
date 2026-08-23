use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

fn inline_pair_pack(a: PseudoExpr, b: PseudoExpr) -> PseudoExpr {
    let x_id = VarId::fresh_binding();
    PseudoExpr::Lambda {
        params: vec![Binder::new("x", x_id)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("x", x_id)),
            args: vec![a, b].into(),
        }),
    }
}

#[test]
fn hoists_when_two_or_more_packs() {
    let arg_a = VarId::fresh_binding();
    let arg_b = VarId::fresh_binding();
    let arg_c = VarId::fresh_binding();
    let arg_d = VarId::fresh_binding();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![
            inline_pair_pack(
                PseudoExpr::var_with_id("a", arg_a),
                PseudoExpr::var_with_id("b", arg_b),
            ),
            inline_pair_pack(
                PseudoExpr::var_with_id("c", arg_c),
                PseudoExpr::var_with_id("d", arg_d),
            ),
        ]
        .into(),
    };
    let result = hoist_church_pair_pack(expr);
    let PseudoExpr::Let { name, body, .. } = result else {
        panic!("expected outer Let, got something else");
    };
    assert_eq!(name, "pair_pack");
    let PseudoExpr::Apply { args, .. } = body.into_inner() else {
        panic!()
    };
    // Each arg is now a `pair_pack(a, b)` Apply.
    for (i, arg) in args.iter().enumerate() {
        let PseudoExpr::Apply {
            function,
            args: pack_args,
        } = arg
        else {
            panic!("arg {} not an Apply", i);
        };
        assert!(matches!(
            function.as_ref(),
            PseudoExpr::Var { name, .. } if name == "pair_pack"
        ));
        assert_eq!(pack_args.len(), 2);
    }
}

#[test]
fn does_not_hoist_for_single_occurrence() {
    let arg_a = VarId::fresh_binding();
    let arg_b = VarId::fresh_binding();
    let expr = inline_pair_pack(
        PseudoExpr::var_with_id("a", arg_a),
        PseudoExpr::var_with_id("b", arg_b),
    );
    let result = hoist_church_pair_pack(expr);
    // Should remain a Lambda (not wrapped in a Let).
    assert!(matches!(result, PseudoExpr::Lambda { .. }));
}

#[test]
fn does_not_match_two_param_outer_lambda() {
    // `fn(x, y) { x(y) }` — 2 outer params, not the 1-outer-2-inner shape.
    let p0 = VarId::fresh_binding();
    let p1 = VarId::fresh_binding();
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("x", p0), Binder::new("y", p1)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("x", p0)),
            args: vec![PseudoExpr::var_with_id("y", p1)].into(),
        }),
    };
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![lambda.clone(), lambda].into(),
    };
    let result = hoist_church_pair_pack(expr);
    assert!(
        matches!(result, PseudoExpr::Apply { .. }),
        "2-param outer Lambdas must not be hoisted, got {:?}",
        result
    );
}

#[test]
fn does_not_hoist_when_args_are_impure() {
    // Impure args (Apply nodes) — purity guard prevents hoist (eager-vs-lazy
    // evaluation order would differ).
    let arg_a = VarId::fresh_binding();
    let impure = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("compute_a")),
        args: vec![].into(),
    };
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![
            inline_pair_pack(impure.clone(), PseudoExpr::var_with_id("b", arg_a)),
            inline_pair_pack(impure, PseudoExpr::var_with_id("b", arg_a)),
        ]
        .into(),
    };
    let result = hoist_church_pair_pack(expr);
    // Result should remain Apply (no Let wrapper).
    assert!(
        matches!(result, PseudoExpr::Apply { .. }),
        "impure args must prevent hoist"
    );
}
