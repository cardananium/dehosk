use super::*;
use crate::pseudo::ast::Binder;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `λa.λb.λk. k a b` applied to two fields → `Pair(field0, field1)`.
fn church_pair_ctor() -> PseudoExpr {
    PseudoExpr::Lambda {
        params: vec![binder("a", 1), binder("b", 2), binder("k", 3)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("k", 3)),
            args: vec![var("a", 1), var("b", 2)].into(),
        }),
    }
}

#[test]
fn decodes_canonical_church_pair_application() {
    let input = PseudoExpr::Apply {
        function: PBox::new(church_pair_ctor()),
        args: vec![
            PseudoExpr::String("TOKEN".to_string()),
            PseudoExpr::ByteArray(vec![0x42]),
        ]
        .into(),
    };
    let out = decode_church_pair_application(input);
    match out {
        PseudoExpr::Pair(a, b) => {
            assert!(matches!(a.into_inner(), PseudoExpr::String(s) if s == "TOKEN"));
            assert!(matches!(b.into_inner(), PseudoExpr::ByteArray(bytes) if bytes == [0x42]));
        }
        other => panic!("expected Pair, got {other:?}"),
    }
}

/// Recurses into children so nested occurrences are decoded.
#[test]
fn decodes_nested_occurrence() {
    let inner = PseudoExpr::Apply {
        function: PBox::new(church_pair_ctor()),
        args: vec![var("x", 10), var("y", 11)].into(),
    };
    let input = PseudoExpr::Tuple((vec![var("z", 99), inner]).into());
    let out = decode_church_pair_application(input);
    match out {
        PseudoExpr::Tuple(items) => {
            assert_eq!(items.len(), 2);
            assert!(
                matches!(&items[1], PseudoExpr::Pair(_, _)),
                "got {:?}",
                items[1]
            );
        }
        other => panic!("expected Tuple, got {other:?}"),
    }
}

/// A 5-param Scott constructor (`λa.λb.λ_.λk.λ_. k a b`) is NOT a pair
/// and must be left untouched.
#[test]
fn leaves_five_param_scott_constructor_untouched() {
    let scott = PseudoExpr::Lambda {
        params: vec![
            binder("a", 1),
            binder("b", 2),
            binder("u1", 3),
            binder("k", 4),
            binder("u2", 5),
        ],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("k", 4)),
            args: vec![var("a", 1), var("b", 2)].into(),
        }),
    };
    let input = PseudoExpr::Apply {
        function: PBox::new(scott),
        args: vec![var("x", 10), var("y", 11)].into(),
    };
    let out = decode_church_pair_application(input.clone());
    assert_eq!(out, input, "5-param Scott ctor must not be decoded as Pair");
}

/// Wrong body order (`k(b, a)` instead of `k(a, b)`) does not match.
#[test]
fn leaves_swapped_field_order_untouched() {
    let swapped = PseudoExpr::Lambda {
        params: vec![binder("a", 1), binder("b", 2), binder("k", 3)],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(var("k", 3)),
            args: vec![var("b", 2), var("a", 1)].into(),
        }),
    };
    let input = PseudoExpr::Apply {
        function: PBox::new(swapped),
        args: vec![var("x", 10), var("y", 11)].into(),
    };
    let out = decode_church_pair_application(input.clone());
    assert_eq!(out, input);
}

/// Under/over application (not exactly 2 args) does not match.
#[test]
fn leaves_three_arg_application_untouched() {
    let input = PseudoExpr::Apply {
        function: PBox::new(church_pair_ctor()),
        args: vec![var("x", 10), var("y", 11), var("k", 12)].into(),
    };
    let out = decode_church_pair_application(input.clone());
    assert_eq!(
        out, input,
        "fully-applied church pair (3 args) is a real call, not a Pair value"
    );
}

/// A church-pair-application in FUNCTION position (the consumer is
/// applied to it: `church_pair(x, y)(k)` ≡ `k(x, y)`) must NOT be
/// collapsed to the invalid `Pair(x, y)(k)`.
#[test]
fn leaves_callee_position_church_pair_untouched() {
    let inner = PseudoExpr::Apply {
        function: PBox::new(church_pair_ctor()),
        args: vec![var("x", 10), var("y", 11)].into(),
    };
    let input = PseudoExpr::Apply {
        function: PBox::new(inner),
        args: vec![var("consumer", 12)].into(),
    };
    let out = decode_church_pair_application(input.clone());
    assert_eq!(
        out, input,
        "callee-position church pair must stay a call, not become Pair(..)(k)"
    );
}

/// A church-pair-application that is the RESULT of a wrapper node
/// (`Let` body) which is itself in function position must also be left
/// alone — `Apply(Let { body: church_pair(x,y) }, [k])` ≡ `k(x,y)`.
#[test]
fn leaves_church_pair_in_callee_let_body_untouched() {
    let inner = PseudoExpr::Apply {
        function: PBox::new(church_pair_ctor()),
        args: vec![var("x", 10), var("y", 11)].into(),
    };
    let callee = PseudoExpr::Let {
        name: "w".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(var("seed", 51)),
        body: PBox::new(inner),
    };
    let input = PseudoExpr::Apply {
        function: PBox::new(callee),
        args: vec![var("consumer", 12)].into(),
    };
    let out = decode_church_pair_application(input.clone());
    assert_eq!(
        out, input,
        "church pair in a callee Let body must not become a Pair"
    );
}
