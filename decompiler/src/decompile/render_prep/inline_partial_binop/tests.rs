use super::*;
use num_bigint::BigInt;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}
fn int(n: i64) -> PseudoExpr {
    PseudoExpr::Int(BigInt::from(n))
}
fn partial(b: BuiltinId, arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BuiltinCall {
        name: b,
        args: vec![arg].into(),
    }
}
/// `let P(id=50) = <value>; <body>`
fn let_p(value: PseudoExpr, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "Int.lt_partial_2".to_string(),
        id: Some(VarId::new(50)),
        value: PBox::new(value),
        body: PBox::new(body),
    }
}
fn call_p(arg: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(var("Int.lt_partial_2", 50)),
        args: vec![arg].into(),
    }
}
fn binop(op: BinaryOp, l: PseudoExpr, r: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BinOp {
        op,
        left: PBox::new(l),
        right: PBox::new(r),
    }
}

#[test]
fn inlines_lt_partial_and_drops_binding() {
    // let P = Int.lt(a); (P(8), P(16))  →  (a < 8, a < 16)
    let body = PseudoExpr::Tuple((vec![call_p(int(8)), call_p(int(16))]).into());
    let e = let_p(partial(BuiltinId::IntLt, var("a", 1)), body);
    let folded = inline_partial_binop(e);
    assert_eq!(
        folded,
        PseudoExpr::Tuple(
            vec![
                binop(BinaryOp::Lt, var("a", 1), int(8)),
                binop(BinaryOp::Lt, var("a", 1), int(16)),
            ]
            .into()
        )
    );
}

#[test]
fn add_and_sub_partials() {
    let e = let_p(partial(BuiltinId::IntSub, var("a", 1)), call_p(var("b", 2)));
    assert_eq!(
        inline_partial_binop(e),
        binop(BinaryOp::Sub, var("a", 1), var("b", 2))
    );
}

#[test]
fn bare_use_keeps_binding() {
    // P passed as a value (HOF) → genuinely partial → left untouched.
    let body = PseudoExpr::Apply {
        function: PBox::new(var("list.any", 9)),
        args: vec![var("xs", 8), var("Int.lt_partial_2", 50)].into(),
    };
    let e = let_p(partial(BuiltinId::IntLt, var("a", 1)), body);
    // Unchanged (still a Let with the BuiltinCall value).
    assert!(matches!(inline_partial_binop(e), PseudoExpr::Let { .. }));
}

#[test]
fn impure_arg_not_inlined() {
    // arg1 is a call (not simple) → don't duplicate → keep the binding.
    let arg1 = PseudoExpr::Apply {
        function: PBox::new(var("f", 7)),
        args: vec![var("x", 6)].into(),
    };
    let e = let_p(partial(BuiltinId::IntLt, arg1), call_p(int(8)));
    assert!(matches!(inline_partial_binop(e), PseudoExpr::Let { .. }));
}

#[test]
fn unused_binding_left_for_dead_let_pass() {
    // No use → left to `drop_dead_pure_lets`; the Let stays.
    let e = let_p(partial(BuiltinId::IntLt, var("a", 1)), int(0));
    assert!(matches!(inline_partial_binop(e), PseudoExpr::Let { .. }));
}
