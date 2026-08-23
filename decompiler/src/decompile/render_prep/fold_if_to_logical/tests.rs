use super::*;

fn cond() -> PBox {
    PBox::new(PseudoExpr::var("c"))
}

#[test]
fn folds_else_false_to_and() {
    // if c { x == y } else { False } → c && (x == y)
    let body = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::var("x")),
        right: PBox::new(PseudoExpr::var("y")),
    };
    let expr = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(body.clone()),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let out = fold_if_to_logical(expr);
    assert!(
        matches!(&out, PseudoExpr::BinOp { op: BinaryOp::And, left, right }
            if matches!(left.as_ref(), PseudoExpr::Var { name, .. } if name == "c")
                && **right == body),
        "expected `c && (x == y)`, got {out:?}"
    );
}

#[test]
fn folds_then_true_to_or() {
    // if c { True } else { f(x) } → c || f(x)  (Apply operand still folds)
    let body = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::var("f")),
        args: vec![PseudoExpr::var("x")].into(),
    };
    let expr = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(body.clone()),
    };
    let out = fold_if_to_logical(expr);
    assert!(
        matches!(&out, PseudoExpr::BinOp { op: BinaryOp::Or, right, .. } if **right == body),
        "expected `c || f(x)`, got {out:?}"
    );
}

// The fold must NOT fire when the operand is a church-bool sentinel — a
// zero-arity Constr (`Unknown_E_0_0`) or a Var to such a const —
// otherwise it becomes the non-compilable `c && e` (Bool && ADT).
fn church_sentinel() -> PseudoExpr {
    use crate::pseudo::constructor::ConstructorShape;
    PseudoExpr::Constr {
        tag: 0,
        shape: ConstructorShape::unknown_data(0, 0),
        fields: vec![].into(),
        type_hint: None,
    }
}

#[test]
fn does_not_fold_constr_then_to_and() {
    // if c { Unknown_E_0_0 } else { False }  → left as `if` (not `c && e`).
    let expr = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(church_sentinel()),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let out = fold_if_to_logical(expr.clone());
    assert_eq!(
        out, expr,
        "church-bool Constr then-branch must NOT fold to &&"
    );
}

#[test]
fn does_not_fold_church_const_var_then_to_and() {
    // const e = Unknown_E_0_0; if c { e } else { False }  → stays `if`
    // (e is a church-const Var, not a Bool).
    let inner = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(PseudoExpr::var_with_id("e", VarId::new(7))),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let expr = PseudoExpr::Let {
        name: "e".to_string(),
        id: Some(VarId::new(7)),
        value: PBox::new(church_sentinel()),
        body: PBox::new(inner.clone()),
    };
    let out = fold_if_to_logical(expr);
    let PseudoExpr::Let { body, .. } = out else {
        panic!("Let")
    };
    assert_eq!(
        *body, inner,
        "church-const Var then-branch must NOT fold to &&"
    );
}

#[test]
fn folds_plain_var_then_to_and() {
    // if c { b } else { False } where b is a plain (non-church-const) Var
    // → `c && b` (a genuine Bool var still folds).
    let expr = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(PseudoExpr::var("b")),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let out = fold_if_to_logical(expr);
    assert!(
        matches!(
            &out,
            PseudoExpr::BinOp {
                op: BinaryOp::And,
                ..
            }
        ),
        "plain Var then-branch should still fold to &&, got {out:?}"
    );
}

#[test]
fn does_not_fold_constr_else_to_or() {
    // if c { True } else { Unknown_E_0_0 } → left as `if` (not `c || e`).
    let expr = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(church_sentinel()),
    };
    let out = fold_if_to_logical(expr.clone());
    assert_eq!(
        out, expr,
        "church-bool Constr else-branch must NOT fold to ||"
    );
}

#[test]
fn does_not_fold_trace_wrapped_sentinel_else_to_or() {
    // if c { True } else { trace @"m": Unknown_E_0_0 } → stays `if`
    // (trace-wrapped church sentinel; the `||` arm must peel the Trace).
    let traced = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::var("m")),
        value: PBox::new(church_sentinel()),
    };
    let expr = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(traced),
    };
    let out = fold_if_to_logical(expr.clone());
    assert_eq!(
        out, expr,
        "trace-wrapped church sentinel must NOT fold to ||"
    );
}

#[test]
fn leaves_both_literal_identity_if_untouched() {
    // if c { True } else { False } → NOT folded here (identity, handled by
    // boolean_cleanup); folding to `c && True` would regress.
    let expr = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let out = fold_if_to_logical(expr.clone());
    assert_eq!(
        out, expr,
        "both-literal if must be left for the identity simplifier"
    );
}

#[test]
fn leaves_non_bool_if_untouched() {
    // if c { 1 } else { 2 } → unchanged (neither branch a triggering literal).
    let expr = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(PseudoExpr::int(1)),
        else_branch: PBox::new(PseudoExpr::int(2)),
    };
    let out = fold_if_to_logical(expr.clone());
    assert_eq!(out, expr);
}

#[test]
fn leaves_when_body_unfolded() {
    // if c { when x is {...} } else { False } — the THEN is a control-flow
    // block; folding to `c && (when …)` reads worse, so leave the `if`.
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let when_body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![WhenClause::new(
            WhenPattern::Wildcard,
            PseudoExpr::Bool(true),
        )],
    };
    let expr = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(when_body),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let out = fold_if_to_logical(expr.clone());
    assert_eq!(
        out, expr,
        "if with a When body must stay an `if`, not `c && (when …)`"
    );
}

#[test]
fn leaves_trace_true_then_body_unfolded_for_and() {
    // if c { trace @"m": True } else { False } must NOT fold to
    // `c && (trace: True)` — the `&& trace: True` display recognizer would
    // render it `!c?` (message-dropping AND truth-inverting). Keep the `if`.
    let expr = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(PseudoExpr::Trace {
            message: PBox::new(PseudoExpr::string("m")),
            value: PBox::new(PseudoExpr::Bool(true)),
        }),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let out = fold_if_to_logical(expr.clone());
    assert_eq!(
        out, expr,
        "Trace-True then-body must not be folded into `&&`"
    );
}

#[test]
fn nested_bool_ifs_collapse_to_and_chain() {
    // if c1 { if c2 { x == y } else { False } } else { False }
    //   → c1 && (c2 && (x == y))   (inner folds first; outer THEN is a BinOp)
    let inner = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::var("c2")),
        then_branch: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(PseudoExpr::var("x")),
            right: PBox::new(PseudoExpr::var("y")),
        }),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let outer = PseudoExpr::If {
        condition: cond(),
        then_branch: PBox::new(inner),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let out = fold_if_to_logical(outer);
    // c1 && (c2 && (x == y))
    let PseudoExpr::BinOp {
        op: BinaryOp::And,
        right,
        ..
    } = &out
    else {
        panic!("expected outer &&, got {out:?}");
    };
    assert!(
        matches!(
            right.as_ref(),
            PseudoExpr::BinOp {
                op: BinaryOp::And,
                ..
            }
        ),
        "inner if should have folded to `c2 && (x == y)`, got {right:?}"
    );
}

#[test]
fn recurses_into_children() {
    // let v = if c { x == y } else { False } in v  → the value folds
    // (Bool-typed body, so the gate permits it; demonstrates recursion).
    let body = PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::var("x")),
        right: PBox::new(PseudoExpr::var("y")),
    };
    let expr = PseudoExpr::let_bind(
        "v",
        PseudoExpr::If {
            condition: cond(),
            then_branch: PBox::new(body),
            else_branch: PBox::new(PseudoExpr::Bool(false)),
        },
        PseudoExpr::var("v"),
    );
    let out = fold_if_to_logical(expr);
    let PseudoExpr::Let { value, .. } = out else {
        panic!("let");
    };
    assert!(matches!(
        value.as_ref(),
        PseudoExpr::BinOp {
            op: BinaryOp::And,
            ..
        }
    ));
}
