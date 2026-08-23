use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::var_id::VarId;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `fn(x) { x(a, b) }` — the inline Church-pair-pack of `(a, b)`.
fn pair_pack(a: PseudoExpr, b: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder("x", 1)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x", 1)),
            args: vec![a, b].into(),
        }),
    }
}

#[test]
fn reduces_immediately_applied_pack_to_consumer_call() {
    let input = PseudoExpr::Apply {
        function: PBox::new(pair_pack(var("a", 10), var("b", 11))),
        args: vec![var("consumer", 20)].into(),
    };
    let out = reduce_applied_church_pair_pack(input);
    match out {
        PseudoExpr::Apply { function, args } => {
            assert!(
                matches!(&*function, PseudoExpr::Var { id: Some(v), .. } if *v == VarId::new(20))
            );
            assert_eq!(args.len(), 2);
            assert!(
                matches!(&args[0], PseudoExpr::Var { id: Some(v), .. } if *v == VarId::new(10))
            );
            assert!(
                matches!(&args[1], PseudoExpr::Var { id: Some(v), .. } if *v == VarId::new(11))
            );
        }
        other => panic!("expected consumer(a, b), got {other:?}"),
    }
}

/// A non-applied Church pair (a bare value) is left for hoisting.
#[test]
fn leaves_unapplied_pack_untouched() {
    let input = pair_pack(var("a", 10), var("b", 11));
    let out = reduce_applied_church_pair_pack(input.clone());
    assert_eq!(out, input);
}

/// Recurses so a pack applied inside a larger expression is reduced.
#[test]
fn reduces_nested_occurrence() {
    let inner = PseudoExpr::Apply {
        function: PBox::new(pair_pack(var("a", 10), var("b", 11))),
        args: vec![var("consumer", 20)].into(),
    };
    let input = PseudoExpr::Tuple((vec![var("z", 99), inner]).into());
    let out = reduce_applied_church_pair_pack(input);
    match out {
        PseudoExpr::Tuple(items) => {
            assert!(
                matches!(&items[1], PseudoExpr::Apply { function, .. }
                    if matches!(&**function, PseudoExpr::Var { id: Some(v), .. } if *v == VarId::new(20))),
                "expected consumer call, got {:?}",
                items[1]
            );
        }
        other => panic!("expected Tuple, got {other:?}"),
    }
}

/// Applied to the wrong arity (not exactly one consumer) is not matched.
#[test]
fn leaves_two_arg_application_untouched() {
    let input = PseudoExpr::Apply {
        function: PBox::new(pair_pack(var("a", 10), var("b", 11))),
        args: vec![var("c1", 20), var("c2", 21)].into(),
    };
    let out = reduce_applied_church_pair_pack(input.clone());
    assert_eq!(out, input);
}

/// The parameter must occur only as the call head: `fn(x) { x(x, b) }`
/// uses `x` as a field, so reducing verbatim would leave a free `x`.
#[test]
fn leaves_param_referenced_in_field_untouched() {
    let pathological = PseudoExpr::Lambda {
        params: vec![binder("x", 1)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("x", 1)),
            args: vec![var("x", 1), var("b", 11)].into(),
        }),
    };
    let input = PseudoExpr::Apply {
        function: PBox::new(pathological),
        args: vec![var("consumer", 20)].into(),
    };
    let out = reduce_applied_church_pair_pack(input.clone());
    assert_eq!(
        out, input,
        "param used as a field must not be lifted verbatim"
    );
}

/// Body head that is not the lambda parameter is not a pair pack.
#[test]
fn leaves_non_pack_lambda_untouched() {
    let not_pack = PseudoExpr::Lambda {
        params: vec![binder("x", 1)],
        body: PBox::new(PseudoExpr::Apply {
            // head is a free `g`, not the param `x`
            function: PBox::new(var("g", 5)),
            args: vec![var("a", 10), var("b", 11)].into(),
        }),
    };
    let input = PseudoExpr::Apply {
        function: PBox::new(not_pack),
        args: vec![var("consumer", 20)].into(),
    };
    let out = reduce_applied_church_pair_pack(input.clone());
    assert_eq!(out, input);
}
