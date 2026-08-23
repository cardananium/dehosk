use super::apply_distribution::assert_lambda_expr_uses_own_param;
use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_cps_selector_inlining_freshens_shared_delayed_lambda_body_ids() {
    let subject_id = VarId::new(9_902);
    let value_id = VarId::new(9_903);
    let ignored_id = VarId::new(9_904);
    let delayed_param_id = VarId::new(9_905);
    let other_id = VarId::new(9_906);
    let subject_name_id = VarId::new(9_907);
    let select_first = || PseudoExpr::Lambda {
        params: vec![Binder::new("value", value_id), Binder::new("_", ignored_id)],
        body: PBox::new(PseudoExpr::var_with_id("value", value_id)),
    };
    let select_second = || PseudoExpr::Lambda {
        params: vec![Binder::new("_", ignored_id), Binder::new("other", other_id)],
        body: PBox::new(PseudoExpr::var_with_id("other", other_id)),
    };

    let function = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("choice", subject_id)),
        subject_name: Some(Binder::new("choice_name", subject_name_id)),
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                guard: Some(PseudoExpr::var("guard0")),
                body: select_first(),
            },
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                guard: Some(PseudoExpr::var("guard1")),
                body: select_first(),
            },
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
                select_second(),
            ),
        ],
    };
    let args = vec![
        PseudoExpr::Delay(PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", delayed_param_id)],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("x", delayed_param_id)),
                right: PBox::new(PseudoExpr::Int(1.into())),
            }),
        })),
        PseudoExpr::Delay(PBox::new(PseudoExpr::Int(0.into()))),
    ];

    let mut simplifier = Simplifier::with_safe_mode(false);
    let simplified = match simplifier.simplify_apply_match(function, args) {
        super::super::apply::ApplyAction::Done(expr) => expr,
        super::super::apply::ApplyAction::ContinueLoop { .. } => {
            panic!("expected CPS selector inlining to finish in Done")
        }
        super::super::apply::ApplyAction::Resimplify(_) => {
            panic!("expected CPS selector inlining to finish in Done")
        }
    };

    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = simplified
    else {
        panic!("expected When, got {simplified:?}");
    };
    assert!(
        matches!(subject.as_ref(), PseudoExpr::Var { name, id } if name == "choice" && *id == Some(subject_id)),
        "CPS selector inlining should move the when subject with id intact, got: {subject:?}"
    );
    assert!(
        matches!(
            subject_name.as_ref(),
            Some(binder) if binder.as_str() == "choice_name" && binder.id == subject_name_id
        ),
        "CPS selector inlining should move the when subject name, got: {subject_name:?}"
    );
    assert_eq!(clauses.len(), 3);
    assert!(
        matches!(
            clauses[0].guard.as_ref(),
            Some(PseudoExpr::Var { name, .. }) if name == "guard0"
        ),
        "CPS selector inlining should preserve clause guards, got: {:?}",
        clauses[0].guard
    );
    assert!(
        matches!(
            clauses[1].guard.as_ref(),
            Some(PseudoExpr::Var { name, .. }) if name == "guard1"
        ),
        "CPS selector inlining should preserve clause guards, got: {:?}",
        clauses[1].guard
    );

    let first_id = assert_lambda_expr_uses_own_param(&clauses[0].body);
    let second_id = assert_lambda_expr_uses_own_param(&clauses[1].body);
    assert_ne!(
        first_id, second_id,
        "shared delayed lambda body must be freshened per selected clause"
    );
    assert!(
        matches!(&clauses[2].body, PseudoExpr::Int(n) if *n == 0.into()),
        "third selector should inline the second delayed arg"
    );
}

#[test]
fn test_if_when_merge_freshens_repeated_then_branch_binder_ids() {
    let param_id = VarId::new(9_907);
    let condition = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("choice")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                guard: Some(PseudoExpr::var("guard0")),
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                guard: Some(PseudoExpr::var("guard1")),
                body: PseudoExpr::Bool(true),
            },
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(2, 0), vec![]),
                PseudoExpr::Bool(false),
            ),
        ],
    };
    let then_branch = PseudoExpr::Lambda {
        params: vec![Binder::new("x", param_id)],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var_with_id("x", param_id)),
            right: PBox::new(PseudoExpr::Int(1.into())),
        }),
    };

    let mut simplifier = Simplifier::with_safe_mode(false);
    let simplified = simplifier.simplify_if(condition, then_branch, PseudoExpr::Int(0.into()));
    let PseudoExpr::When { clauses, .. } = simplified else {
        panic!("expected When, got {simplified:?}");
    };
    assert_eq!(clauses.len(), 3);

    let first_id = assert_lambda_expr_uses_own_param(&clauses[0].body);
    let second_id = assert_lambda_expr_uses_own_param(&clauses[1].body);
    assert_ne!(
        first_id, second_id,
        "if-when merge must freshen repeated then-branch binders"
    );
    assert!(
        matches!(&clauses[2].body, PseudoExpr::Int(n) if *n == 0.into()),
        "false clause should receive the else branch"
    );
}

#[test]
fn test_constant_constructor_collapse_freshens_field_binding_when_subject_name_keeps_subject() {
    let lambda_param_id = VarId::new(9_908);
    let subject_id = VarId::new(9_909);
    let field_id = VarId::new(9_910);
    let field_value = PseudoExpr::Lambda {
        params: vec![Binder::new("x", lambda_param_id)],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::var_with_id("x", lambda_param_id)),
            right: PBox::new(PseudoExpr::Int(1.into())),
        }),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 1),
            vec![field_value],
        )),
        subject_name: Some(Binder::new("subject", subject_id)),
        clauses: vec![WhenClause::new(
            WhenPattern::constructor(
                ConstructorShape::unknown_data(0, 1),
                vec![Binder::new("field", field_id)],
            ),
            PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("subject", subject_id),
                    PseudoExpr::var_with_id("field", field_id),
                ]
                .into(),
            ),
        )],
    };

    let simplified = simplify(expr);
    let PseudoExpr::Let {
        name: subject_name,
        value: subject_value,
        body,
        ..
    } = simplified
    else {
        panic!("expected subject let, got {simplified:?}");
    };
    assert_eq!(subject_name, "subject");

    let PseudoExpr::Constr { fields, .. } = subject_value.as_ref() else {
        panic!("expected subject binding to keep constructor value, got {subject_value:?}");
    };
    let [subject_field] = fields.as_slice() else {
        panic!("expected one subject field, got {fields:?}");
    };
    let subject_field_id = assert_lambda_expr_uses_own_param(subject_field);

    let PseudoExpr::Let {
        name: field_name,
        value: field_binding,
        ..
    } = body.as_ref()
    else {
        panic!("expected field let under subject let, got {body:?}");
    };
    assert_eq!(field_name, "field");
    let field_binding_id = assert_lambda_expr_uses_own_param(field_binding);

    assert_ne!(
        subject_field_id, field_binding_id,
        "constant constructor collapse must not duplicate binder ids between subject and field bindings"
    );
}
