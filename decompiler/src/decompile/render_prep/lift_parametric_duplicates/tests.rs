use super::*;
use crate::pseudo::ast::{BinaryOp, PBox};

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

/// `when xs is { [h, ..t] -> h + h + … ; _ -> fail }`, big enough to lift.
fn big_when(subject: PseudoExpr, head: u32, tail: u32, extra: PseudoExpr) -> PseudoExpr {
    let mut body = var("h", head);
    for _ in 0..16 {
        body = PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(body),
            right: PBox::new(extra.clone()),
        };
    }
    PseudoExpr::When {
        subject: PBox::new(subject),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::List {
                    elements: vec![Binder::new("h", VarId::new(head))],
                    tail: Some(Binder::new("t", VarId::new(tail))),
                },
                guard: None,
                body,
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error { message: None },
            },
        ],
    }
}

fn let_in(name: &str, id: u32, value: PseudoExpr, body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::let_bind_with_id(name, VarId::new(id), value, body)
}

fn count<F: Fn(&PseudoExpr) -> bool>(expr: &PseudoExpr, pred: F) -> usize {
    let mut n = 0;
    let mut stack = vec![expr];
    while let Some(cur) = stack.pop() {
        if pred(cur) {
            n += 1;
        }
        stack.extend(children(cur));
    }
    n
}

#[test]
fn copies_that_differ_in_one_variable_share_a_helper() {
    // `k` is read by both copies; only the list differs.
    let program = let_in(
        "k",
        1,
        PseudoExpr::Int(3.into()),
        let_in(
            "a",
            2,
            big_when(var("xs", 10), 20, 21, var("k", 1)),
            let_in(
                "b",
                3,
                big_when(var("ys", 11), 30, 31, var("k", 1)),
                PseudoExpr::BinOp {
                    op: BinaryOp::Add,
                    left: PBox::new(var("a", 2)),
                    right: PBox::new(var("b", 3)),
                },
            ),
        ),
    );
    let out = lift_parametric_duplicates(program);
    assert_eq!(count(&out, |e| matches!(e, PseudoExpr::When { .. })), 1, "{out:?}");
    assert_eq!(
        count(&out, |e| matches!(e, PseudoExpr::Apply { function, .. }
            if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == "lifted"))),
        2
    );
    // The helper sits inside the scope of `k`, the variable both copies share.
    let PseudoExpr::Let { body, .. } = &out else {
        panic!("outer let kept: {out:?}")
    };
    assert!(
        matches!(body.as_ref(), PseudoExpr::Let { name, .. } if name == "lifted"),
        "helper must be defined directly under `k`: {out:?}"
    );
}

#[test]
fn copies_that_differ_in_shape_are_left_alone() {
    let program = let_in(
        "a",
        2,
        big_when(var("xs", 10), 20, 21, PseudoExpr::Int(1.into())),
        let_in(
            "b",
            3,
            big_when(var("ys", 11), 30, 31, PseudoExpr::Int(2.into())),
            PseudoExpr::Unit,
        ),
    );
    let out = lift_parametric_duplicates(program);
    assert_eq!(count(&out, |e| matches!(e, PseudoExpr::When { .. })), 2);
}

#[test]
fn identical_copies_are_left_to_exact_extraction() {
    let program = let_in(
        "a",
        2,
        big_when(var("xs", 10), 20, 21, PseudoExpr::Int(1.into())),
        let_in(
            "b",
            3,
            big_when(var("xs", 10), 30, 31, PseudoExpr::Int(1.into())),
            PseudoExpr::Unit,
        ),
    );
    let out = lift_parametric_duplicates(program);
    assert_eq!(count(&out, |e| matches!(e, PseudoExpr::When { .. })), 2);
}

#[test]
fn closed_rec_fn_matching_one_in_an_enclosing_scope_is_reused() {
    fn rec_fn(name: &str, id: u32, param: u32) -> PseudoExpr {
        PseudoExpr::RecFn {
            name: Binder::new(name, VarId::new(id)),
            params: vec![Binder::new("x", VarId::new(param))],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(var("x", param)),
                right: PBox::new(PseudoExpr::Int(1.into())),
            }),
        }
    }
    let call = |f: &str, id: u32| PseudoExpr::Apply {
        function: PBox::new(var(f, id)),
        args: vec![PseudoExpr::Int(0.into())].into(),
    };
    let program = let_in(
        "f",
        1,
        rec_fn("f", 100, 101),
        let_in(
            "g",
            2,
            rec_fn("g", 200, 201),
            PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(call("f", 1)),
                right: PBox::new(call("g", 2)),
            },
        ),
    );
    let out = lift_parametric_duplicates(program);
    assert_eq!(count(&out, |e| matches!(e, PseudoExpr::RecFn { .. })), 1, "{out:?}");
    assert_eq!(
        count(&out, |e| matches!(e, PseudoExpr::Var { id: Some(v), .. } if *v == VarId::new(2))),
        0,
        "every reference to the dropped copy must be redirected"
    );
}
