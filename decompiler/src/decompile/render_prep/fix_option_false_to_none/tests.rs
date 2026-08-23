use super::*;
use crate::pseudo::ast::Binder;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn some_clause() -> WhenClause {
    WhenClause {
        pattern: WhenPattern::constructor_known(
            KnownConstructor::Some,
            vec![Binder::new("x".to_string(), VarId::new(50))],
        ),
        guard: None,
        body: var("x", 50),
    }
}

/// `let r = if c { Some(p) } else { False }; <match r as Some>` →
/// the `False` becomes `None`.
#[test]
fn relabels_false_to_none_when_binding_matched_as_option() {
    let value = PseudoExpr::If {
        condition: PBox::new(var("c", 1)),
        then_branch: PBox::new(PseudoExpr::constr_known(
            KnownConstructor::Some,
            vec![var("p", 2)],
        )),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let body = PseudoExpr::When {
        subject: PBox::new(var("r", 10)),
        subject_name: None,
        clauses: vec![some_clause()],
    };
    let input = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(value),
        body: PBox::new(body),
    };
    let out = fix_option_false_to_none(input);
    let PseudoExpr::Let { value, .. } = out else {
        panic!("expected Let")
    };
    let PseudoExpr::If { else_branch, .. } = value.into_inner() else {
        panic!("expected If value")
    };
    assert!(
        matches!(&*else_branch, PseudoExpr::Constr { shape, .. }
            if shape.as_known() == Some(KnownConstructor::None)),
        "else branch should be None, got {else_branch:?}"
    );
}

/// No `Some`/`None` match on the binding → leave `False` alone.
#[test]
fn leaves_false_when_binding_not_matched_as_option() {
    let value = PseudoExpr::If {
        condition: PBox::new(var("c", 1)),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    // body uses r in a boolean position, never matched as Some/None
    let body = PseudoExpr::BinOp {
        op: crate::pseudo::ast::BinaryOp::Eq,
        left: PBox::new(var("r", 10)),
        right: PBox::new(PseudoExpr::Bool(true)),
    };
    let input = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(value),
        body: PBox::new(body),
    };
    let out = fix_option_false_to_none(input.clone());
    assert_eq!(out, input, "genuine Bool binding must be untouched");
}

/// Only TAIL `Bool(false)` is rewritten; a `False` used as an operand
/// (non-tail) of the bound value is left alone.
#[test]
fn leaves_non_tail_false_untouched() {
    // value = (False == c) — `False` is a BinOp operand, not a tail.
    let value = PseudoExpr::BinOp {
        op: crate::pseudo::ast::BinaryOp::Eq,
        left: PBox::new(PseudoExpr::Bool(false)),
        right: PBox::new(var("c", 1)),
    };
    let body = PseudoExpr::When {
        subject: PBox::new(var("r", 10)),
        subject_name: None,
        clauses: vec![some_clause()],
    };
    let input = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(value),
        body: PBox::new(body),
    };
    let out = fix_option_false_to_none(input.clone());
    // The operand False stays a Bool (BinOp body is not a tail position).
    let PseudoExpr::Let { value, .. } = out else {
        panic!("expected Let")
    };
    let PseudoExpr::BinOp { left, .. } = value.into_inner() else {
        panic!("expected BinOp")
    };
    assert_eq!(*left, PseudoExpr::Bool(false));
}

/// `Bool(false)` in a `trace`'s value (tail) position is relabeled;
/// the message is never a tail.
#[test]
fn relabels_false_in_trace_value_tail() {
    let value = PseudoExpr::Trace {
        message: PBox::new(PseudoExpr::String("dbg".to_string())),
        value: PBox::new(PseudoExpr::Bool(false)),
    };
    let body = PseudoExpr::When {
        subject: PBox::new(var("r", 10)),
        subject_name: None,
        clauses: vec![some_clause()],
    };
    let input = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(value),
        body: PBox::new(body),
    };
    let out = fix_option_false_to_none(input);
    let PseudoExpr::Let { value, .. } = out else {
        panic!("expected Let")
    };
    let PseudoExpr::Trace {
        message,
        value: tval,
    } = value.into_inner()
    else {
        panic!("expected Trace")
    };
    assert_eq!(
        *message,
        PseudoExpr::String("dbg".to_string()),
        "message must be untouched"
    );
    assert!(
        matches!(&*tval, PseudoExpr::Constr { shape, .. }
            if shape.as_known() == Some(KnownConstructor::None)),
        "trace value tail should be None, got {tval:?}"
    );
}

/// A value with a `Bool(true)` tail sibling is provably a Bool
/// (`if c { True } else { False }` is just `c`), so even when its
/// result is matched as `Some`/`None` (a church-relabel of a Bool
/// `when`), the `False` is LEFT ALONE: `None` shares `True`'s
/// tag 1, so the flip would collapse both arms onto one tag.
#[test]
fn leaves_bool_if_untouched_when_matched_as_option() {
    let value = PseudoExpr::If {
        condition: PBox::new(var("c", 1)),
        then_branch: PBox::new(PseudoExpr::Bool(true)),
        else_branch: PBox::new(PseudoExpr::Bool(false)),
    };
    let body = PseudoExpr::When {
        subject: PBox::new(var("r", 10)),
        subject_name: None,
        clauses: vec![some_clause()],
    };
    let input = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(value),
        body: PBox::new(body),
    };
    let out = fix_option_false_to_none(input.clone());
    assert_eq!(out, input, "provably-Bool value must be untouched");
}

/// The `list.any`-predicate inversion: the bound value is a
/// tag-dispatch `when` with a comparison arm (definitely Bool) and a
/// `False` fall-through, and the result is consumed by a church-decoded
/// `{None -> .; Some(_) -> .}` relabel of `{True -> .; False -> .}`.
/// Flipping that `False` (tag 0) to `None` (tag 1) inverts the loop.
#[test]
fn leaves_false_when_value_has_comparison_tail_leaf() {
    let value = PseudoExpr::When {
        subject: PBox::new(var("entry", 5)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor_known(
                    KnownConstructor::Some,
                    vec![Binder::new("b".to_string(), VarId::new(60))],
                ),
                guard: None,
                // a == b → a definite-Bool tail leaf
                body: PseudoExpr::BinOp {
                    op: crate::pseudo::ast::BinaryOp::Eq,
                    left: PBox::new(var("b", 60)),
                    right: PBox::new(PseudoExpr::Bool(true)),
                },
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Bool(false),
            },
        ],
    };
    let body = PseudoExpr::When {
        subject: PBox::new(var("r", 10)),
        subject_name: None,
        clauses: vec![some_clause()],
    };
    let input = PseudoExpr::Let {
        name: "r".to_string(),
        id: Some(VarId::new(10)),
        value: PBox::new(value),
        body: PBox::new(body),
    };
    let out = fix_option_false_to_none(input.clone());
    assert_eq!(
        out, input,
        "Bool-tailed value must keep its False fall-through"
    );
}
