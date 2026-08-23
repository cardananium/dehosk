use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_lazy_choose_list_trigger_wrapper_rewritten_to_when() {
    let subject_id = VarId::new(100);
    let head_id = VarId::new(101);
    let tail_id = VarId::new(102);
    let empty_id = VarId::new(103);
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("choose_list"),
            args: vec![].into(),
        }),
        args: vec![
            PseudoExpr::var_with_id("xs", subject_id),
            PseudoExpr::Lambda {
                params: vec!["_".to_string().into()],
                body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::var_with_id(
                    "empty", empty_id,
                )))),
            },
            PseudoExpr::Lambda {
                params: vec![
                    Binder::new("head", head_id),
                    Binder::new("tail", tail_id),
                    "_".to_string().into(),
                ],
                body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("head", head_id),
                        PseudoExpr::var_with_id("tail", tail_id),
                    ]
                    .into(),
                )))),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            assert!(
                matches!(
                    subject.as_ref(),
                    PseudoExpr::Var { name, id } if name == "xs" && *id == Some(subject_id)
                ),
                "expected choose_list subject to keep id, got: {subject:?}"
            );
            let Some(empty_clause) = clauses.first() else {
                panic!("expected empty list clause");
            };
            assert!(
                matches!(
                    &empty_clause.body,
                    PseudoExpr::Var { name, id } if name == "empty" && *id == Some(empty_id)
                ),
                "expected empty branch to keep id, got: {:?}",
                empty_clause.body
            );
            let Some(non_empty_clause) = clauses.get(1) else {
                panic!("expected non-empty list clause");
            };
            let WhenPattern::List {
                elements,
                tail: Some(tail),
            } = &non_empty_clause.pattern
            else {
                panic!("expected list pattern, got: {:?}", non_empty_clause.pattern);
            };
            assert_eq!(elements.len(), 1);
            assert_eq!(elements[0].as_str(), "head");
            assert_eq!(elements[0].id, head_id);
            assert_eq!(tail.as_str(), "tail");
            assert_eq!(tail.id, tail_id);
            assert!(
                matches!(
                    &non_empty_clause.body,
                    PseudoExpr::Tuple(items)
                        if matches!(&items[0], PseudoExpr::Var { name, id, .. } if name == "head" && *id == Some(head_id))
                            && matches!(&items[1], PseudoExpr::Var { name, id, .. } if name == "tail" && *id == Some(tail_id))
                ),
                "expected choose_list rewrite body to preserve head/tail ids, got: {:?}",
                non_empty_clause.body
            );
        }
        other => panic!("expected when form, got: {other:?}"),
    }
}

fn lazy_choose_list_expr_with_cons_body(
    head_id: VarId,
    tail_id: VarId,
    third_id: VarId,
    cons_body: PseudoExpr,
) -> PseudoExpr {
    PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("choose_list"),
            args: vec![].into(),
        }),
        args: vec![
            PseudoExpr::var("xs"),
            PseudoExpr::Lambda {
                params: vec!["_".to_string().into()],
                body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::int(0)))),
            },
            PseudoExpr::Lambda {
                params: vec![
                    Binder::new("head", head_id),
                    Binder::new("tail", tail_id),
                    Binder::new("k", third_id),
                ],
                body: PBox::new(PseudoExpr::Delay(PBox::new(cons_body))),
            },
            PseudoExpr::Unit,
        ]
        .into(),
    }
}

#[test]
fn test_lazy_choose_list_ignores_same_name_foreign_third_ref() {
    let head_id = VarId::new(1331);
    let tail_id = VarId::new(1332);
    let third_id = VarId::new(1333);
    let foreign_third_id = VarId::new(1334);
    let expr = lazy_choose_list_expr_with_cons_body(
        head_id,
        tail_id,
        third_id,
        PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("head", head_id),
                PseudoExpr::var_with_id("tail", tail_id),
                PseudoExpr::var_with_id("k", foreign_third_id),
            ]
            .into(),
        ),
    );

    let simplified = simplify(expr);

    assert!(
        matches!(simplified, PseudoExpr::When { .. }),
        "same-name foreign third-param ref should not block choose_list rewrite, got: {simplified:?}"
    );
}

#[test]
fn test_lazy_choose_list_rejects_actual_third_param_use() {
    let head_id = VarId::new(1341);
    let tail_id = VarId::new(1342);
    let third_id = VarId::new(1343);
    let expr = lazy_choose_list_expr_with_cons_body(
        head_id,
        tail_id,
        third_id,
        PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("head", head_id),
                PseudoExpr::var_with_id("tail", tail_id),
                PseudoExpr::var_with_id("k", third_id),
            ]
            .into(),
        ),
    );

    let simplified = simplify(expr);

    assert!(
        !matches!(simplified, PseudoExpr::When { .. }),
        "actual third-param use must still block choose_list rewrite"
    );
}
