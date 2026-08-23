use super::{
    try_inline_when_adapter_let, try_normalize_sorted_assoc_lookup_if,
    try_reorder_inverted_if_arg_lets, try_repair_self_referenced_let,
};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;
use crate::pseudo::var_id::VarId;

#[test]
fn test_try_normalize_sorted_assoc_lookup_if_rewrites_lte_nested_eq_shape() {
    let needle = PseudoExpr::var("needle");
    let fst = PseudoExpr::var("fst");
    let some = PseudoExpr::constr_known(KnownConstructor::Some, vec![PseudoExpr::var("value")]);
    let none = PseudoExpr::constr_known(KnownConstructor::None, vec![]);
    let recurse = PseudoExpr::var("recurse");

    let rewritten = try_normalize_sorted_assoc_lookup_if(
        PseudoExpr::BinOp {
            op: BinaryOp::Lte,
            left: PBox::new(needle.clone()),
            right: PBox::new(fst.clone()),
        },
        PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left: PBox::new(needle.clone()),
                right: PBox::new(fst.clone()),
            }),
            then_branch: PBox::new(some.clone()),
            else_branch: PBox::new(none.clone()),
        },
        recurse.clone(),
    )
    .expect("sorted assoc lookup shape should normalize");

    let expected = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: PBox::new(needle.clone()),
            right: PBox::new(fst.clone()),
        }),
        then_branch: PBox::new(some),
        else_branch: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Lt,
                left: PBox::new(needle),
                right: PBox::new(fst),
            }),
            then_branch: PBox::new(none),
            else_branch: PBox::new(recurse),
        }),
    };

    assert!(
        rewritten.structural_eq(&expected),
        "expected normalized sorted-assoc lookup if, got: {rewritten:#?}"
    );
}

#[test]
fn test_try_repair_self_referenced_let_ignores_same_name_different_id() {
    let outer_id = VarId::new(6101);
    let unrelated_id = VarId::new(6102);

    let repaired = try_repair_self_referenced_let(
        "x".to_string(),
        outer_id,
        PseudoExpr::var_with_id("x", unrelated_id),
        PseudoExpr::Unit,
    );

    assert!(
        repaired.is_none(),
        "same-name ref with different VarId must not count as self-reference"
    );
}

#[test]
fn test_try_reorder_inverted_if_arg_lets_ignores_same_name_different_id_capture() {
    let outer_id = VarId::new(6111);
    let unrelated_id = VarId::new(6112);
    let inner_id = VarId::new(6113);

    let reordered = try_reorder_inverted_if_arg_lets(
        "x".to_string(),
        outer_id,
        PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::Bool(false)),
                then_branch: PBox::new(PseudoExpr::var_with_id("x", unrelated_id)),
                else_branch: PBox::new(PseudoExpr::var_with_id("y", inner_id)),
            }),
            body: PBox::new(PseudoExpr::Unit),
        },
        PseudoExpr::Unit,
    );

    assert!(
        reordered.is_none(),
        "reorder must not fire when only a different-id same-name ref appears in the inner if"
    );
}

#[test]
fn test_try_inline_when_adapter_let_ignores_same_name_different_id_in_clause_body() {
    let subject_id = VarId::new(6121);
    let unrelated_id = VarId::new(6122);

    let inlined = try_inline_when_adapter_let(
        "adapter".to_string(),
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("payload", subject_id)),
            subject_name: None,
            clauses: vec![WhenClause::new(
                WhenPattern::Wildcard,
                PseudoExpr::var_with_id("payload", unrelated_id),
            )],
        },
        PseudoExpr::Lambda {
            params: vec!["arg".to_string().into()],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var("adapter")),
                args: vec![PseudoExpr::var("arg")].into(),
            }),
        },
    )
    .expect("unrelated same-name ref should not block late when-adapter inline");

    assert!(
        matches!(
            &inlined,
            PseudoExpr::Lambda { body, .. }
                if matches!(
                    body.as_ref(),
                    PseudoExpr::When { subject, clauses, .. }
                        if matches!(
                            subject.as_ref(),
                            PseudoExpr::Var { name, .. } if name == "arg"
                        ) && matches!(
                            clauses.as_slice(),
                            [WhenClause { body: PseudoExpr::Var { name, id, .. }, .. }]
                                if name == "payload" && *id == Some(unrelated_id)
                        )
                )
        ),
        "expected adapter inline to proceed and preserve unrelated payload ref, got: {inlined:?}"
    );
}
