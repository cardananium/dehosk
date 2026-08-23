use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_recfn_expect_nonempty_list_search_becomes_when() {
    let expr = PseudoExpr::RecFn {
        name: "find".to_string().into(),
        params: vec!["xs".to_string().into(), "pred".to_string().into()],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("expect!")),
            args: vec![
                PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("List.is_empty")),
                        args: vec![PseudoExpr::var("xs")].into(),
                    }),
                },
                PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("pred")),
                        args: vec![PseudoExpr::field_access(
                            PseudoExpr::var("xs"),
                            "head".to_string(),
                        )]
                        .into(),
                    }),
                    then_branch: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var("xs"),
                        "head".to_string(),
                    )),
                    else_branch: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::var("find")),
                        args: vec![
                            PseudoExpr::BuiltinCall {
                                name: crate::BuiltinId::expect_known("List.tail"),
                                args: vec![PseudoExpr::var("xs")].into(),
                            },
                            PseudoExpr::var("pred"),
                        ]
                        .into(),
                    }),
                },
            ]
            .into(),
        }),
    };

    let simplified = simplify(expr);
    match simplified {
        PseudoExpr::RecFn {
            name, params, body, ..
        } => match body.as_ref() {
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                let rec_id = name.id;
                let xs_id = params[0].id;
                let pred_id = params[1].id;
                assert!(
                    matches!(
                        subject.as_ref(),
                        PseudoExpr::Var { name, id, .. }
                            if name == "xs" && id.get() == Some(xs_id)
                    ),
                    "expected xs subject, got: {subject:?}"
                );
                assert_eq!(subject_name.as_deref(), Some("xs"));
                assert_eq!(
                    subject_name.as_ref().map(|binder| binder.id),
                    Some(xs_id),
                    "expected when subject_name binder to reuse xs VarId"
                );
                assert_eq!(clauses.len(), 2, "expected two clauses, got: {clauses:?}");
                assert!(
                    matches!(
                        &clauses[0].pattern,
                        WhenPattern::List { elements, tail }
                            if elements.is_empty() && tail.is_none()
                    ),
                    "expected [] failure clause, got: {:?}",
                    clauses[0].pattern
                );
                assert!(
                    matches!(&clauses[0].body, PseudoExpr::Error { .. }),
                    "expected fail empty branch, got: {:?}",
                    clauses[0].body
                );
                let WhenPattern::List { elements, tail } = &clauses[1].pattern else {
                    panic!(
                        "expected [xs_h, ..xs_t] pattern, got: {:?}",
                        clauses[1].pattern
                    );
                };
                assert_eq!(
                    elements.len(),
                    1,
                    "expected single head binder, got: {elements:?}"
                );
                assert_eq!(
                    elements[0].as_str(),
                    "xs_h",
                    "expected head binder name xs_h, got: {:?}",
                    elements[0]
                );
                let tail_binder = tail
                    .as_ref()
                    .expect("expected non-empty list clause to bind a tail");
                assert_eq!(
                    tail_binder.as_str(),
                    "xs_t",
                    "expected tail binder name xs_t, got: {tail_binder:?}"
                );
                let body_str = format!("{:?}", clauses[1].body);
                assert!(
                    body_str.contains("xs_h") && body_str.contains("xs_t"),
                    "expected head/tail binders in rewritten body: {body_str}"
                );
                assert!(
                    !body_str.contains("List.tail") && !body_str.contains(".head"),
                    "expected structural list access rewrite, got: {body_str}"
                );
                let PseudoExpr::If { else_branch, .. } = &clauses[1].body else {
                    panic!(
                        "expected conditional body in non-empty branch, got: {:?}",
                        clauses[1].body
                    );
                };
                let PseudoExpr::Apply { function, args } = else_branch.as_ref() else {
                    panic!("expected recursive call in else branch, got: {else_branch:?}");
                };
                assert!(
                    matches!(
                        function.as_ref(),
                        PseudoExpr::Var { name, id, .. }
                            if name == "find" && id.get() == Some(rec_id)
                    ),
                    "expected recursive call to preserve recfn binder VarId, got: {function:?}"
                );
                assert!(
                    matches!(
                        args.first(),
                        Some(PseudoExpr::Var { name, id, .. })
                            if name == "xs_t" && id.get() == Some(tail_binder.id)
                    ),
                    "expected recursive tail arg to reuse tail binder VarId, got: {:?}",
                    args.first()
                );
                assert!(
                    matches!(
                        args.get(1),
                        Some(PseudoExpr::Var { name, id, .. })
                            if name == "pred" && id.get() == Some(pred_id)
                    ),
                    "expected recursive predicate arg to preserve param VarId, got: {:?}",
                    args.get(1)
                );
            }
            other => panic!("expected recfn body to become when, got: {other:?}"),
        },
        other => panic!("expected recfn after simplification, got: {other:?}"),
    }
}
