use super::*;
use crate::pseudo::ast::{Binder, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

fn var(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn none_val() -> PseudoExpr {
    PseudoExpr::constr_known(KnownConstructor::None, vec![])
}

fn eq(a: PseudoExpr, b: PseudoExpr) -> PseudoExpr {
    PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(a),
        right: PBox::new(b),
    }
}

/// A `when` conjunct whose tails mix `a == b` and `None`. As an `&&`
/// operand under InverseCip, the `None` tails become `False`.
fn mixed_bool_none_when() -> PseudoExpr {
    PseudoExpr::When {
        subject: PBox::new(var("s", 1)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec![Binder::new("a".to_string(), VarId::new(2))],
                ),
                guard: None,
                body: eq(var("a", 2), var("a", 2)),
            },
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                guard: None,
                body: none_val(),
            },
        ],
    }
}

#[test]
fn relabels_none_to_false_in_and_operand_under_inverse_cip() {
    let ctx = RenderCtx::default().with_church_polarity(ChurchPolarity::InverseCip);
    let input = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(eq(var("x", 9), var("x", 9))),
        right: PBox::new(mixed_bool_none_when()),
    };
    let out = relabel_bool_none_to_false(input, &ctx);
    let PseudoExpr::BinOp { right, .. } = out else {
        panic!("expected BinOp")
    };
    let PseudoExpr::When { clauses, .. } = right.into_inner() else {
        panic!("expected When")
    };
    assert_eq!(
        clauses[1].body,
        PseudoExpr::Bool(false),
        "None tail should become False"
    );
    // The comparison arm is untouched.
    assert!(matches!(
        clauses[0].body,
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            ..
        }
    ));
}

#[test]
fn no_op_under_cip() {
    let ctx = RenderCtx::default().with_church_polarity(ChurchPolarity::Cip);
    let input = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(eq(var("x", 9), var("x", 9))),
        right: PBox::new(mixed_bool_none_when()),
    };
    let out = relabel_bool_none_to_false(input.clone(), &ctx);
    assert_eq!(
        out, input,
        "CIP program must be byte-identical (no relabel)"
    );
}

/// One tail is `Some(payload)`, so no definite-Bool tail witnesses this
/// operand: the `None` sibling stays `None` even under InverseCip.
#[test]
fn leaves_genuine_option_operand_untouched() {
    let ctx = RenderCtx::default().with_church_polarity(ChurchPolarity::InverseCip);
    let option_when = PseudoExpr::When {
        subject: PBox::new(var("s", 1)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                guard: None,
                body: PseudoExpr::constr_known(KnownConstructor::Some, vec![var("p", 3)]),
            },
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                guard: None,
                body: none_val(),
            },
        ],
    };
    // Sits as an `&&` operand, but is not Bool (a Some tail).
    let input = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(eq(var("x", 9), var("x", 9))),
        right: PBox::new(option_when),
    };
    let out = relabel_bool_none_to_false(input.clone(), &ctx);
    assert_eq!(
        out, input,
        "operand with a Some tail is not Bool → untouched"
    );
}

/// The genuine call-site shape `if cond { None } else … { None }`: the
/// BRANCHES are Option values, never a Bool position — the `None`s stay.
#[test]
fn leaves_if_branch_nones_untouched() {
    let ctx = RenderCtx::default().with_church_polarity(ChurchPolarity::InverseCip);
    let input = PseudoExpr::If {
        condition: PBox::new(eq(var("x", 9), var("x", 9))),
        then_branch: PBox::new(none_val()),
        else_branch: PBox::new(none_val()),
    };
    let out = relabel_bool_none_to_false(input.clone(), &ctx);
    assert_eq!(
        out, input,
        "if branches are Option values, not Bool → untouched"
    );
}

/// Only TAIL `None` is rewritten; a `None` used as a non-tail sub-value
/// (e.g. a constructor field) inside a Bool operand is left alone.
#[test]
fn leaves_non_tail_none_untouched() {
    let ctx = RenderCtx::default().with_church_polarity(ChurchPolarity::InverseCip);
    // Right operand: `when { _ -> Some(None) }` — the `None` is a
    // constructor field, not a tail.
    let when_with_ctor_tail = PseudoExpr::When {
        subject: PBox::new(var("s", 1)),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            // tail is Some(None) — a constructor, NOT a bare None or Bool.
            body: PseudoExpr::constr_known(KnownConstructor::Some, vec![none_val()]),
        }],
    };
    let input = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(eq(var("x", 9), var("x", 9))),
        right: PBox::new(when_with_ctor_tail),
    };
    let out = relabel_bool_none_to_false(input.clone(), &ctx);
    assert_eq!(
        out, input,
        "Some(None) tail is a ctor, not Bool-or-None → untouched"
    );
}
