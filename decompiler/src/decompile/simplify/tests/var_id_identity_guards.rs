use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_if_chain_when_rejects_same_name_different_subject_id() {
    let subject_id = VarId::new(740);
    let foreign_subject_id = VarId::new(741);
    let eq_int = |id, n| PseudoExpr::BinOp {
        op: BinaryOp::Eq,
        left: PBox::new(PseudoExpr::var_with_id("x", id)),
        right: PBox::new(PseudoExpr::int(n)),
    };

    let cond = eq_int(subject_id, 0);
    let foreign_else_if = PseudoExpr::If {
        condition: PBox::new(eq_int(foreign_subject_id, 1)),
        then_branch: PBox::new(PseudoExpr::int(20)),
        else_branch: PBox::new(PseudoExpr::int(30)),
    };

    assert_eq!(
        Simplifier::try_build_when_from_if_chain(&cond, &PseudoExpr::int(10), &foreign_else_if),
        None,
        "same-name foreign-id subjects must not collapse into one when"
    );

    let matching_else_if = PseudoExpr::If {
        condition: PBox::new(eq_int(subject_id, 1)),
        then_branch: PBox::new(PseudoExpr::int(20)),
        else_branch: PBox::new(PseudoExpr::int(30)),
    };
    let Some(PseudoExpr::When {
        subject, clauses, ..
    }) = Simplifier::try_build_when_from_if_chain(&cond, &PseudoExpr::int(10), &matching_else_if)
    else {
        panic!("expected matching subject ids to collapse into a when");
    };

    assert!(
        matches!(subject.as_ref(), PseudoExpr::Var { name, id } if name == "x" && *id == Some(subject_id))
    );
    assert_eq!(clauses.len(), 3);
}

#[test]
fn test_y_combinator_rejects_same_name_different_self_apply_ids() {
    let left_id = VarId::new(800);
    let right_id = VarId::new(801);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("k", VarId::new(802))],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("d", left_id)),
            args: vec![PseudoExpr::var_with_id("d", right_id)].into(),
        }),
    };

    assert!(
        !Simplifier::is_y_combinator(&expr),
        "same-name foreign refs must not classify as self-application"
    );

    let matching = PseudoExpr::Lambda {
        params: vec![Binder::new("k", VarId::new(803))],
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("d", left_id)),
            args: vec![PseudoExpr::var_with_id("d", left_id)].into(),
        }),
    };
    assert!(Simplifier::is_y_combinator(&matching));
}

#[test]
fn test_y_combinator_rejects_same_name_foreign_let_body_call() {
    let c_id = VarId::new(804);
    let foreign_c_id = VarId::new(805);
    let m_id = VarId::new(806);
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("k", VarId::new(807))],
        body: PBox::new(PseudoExpr::Let {
            name: "c".to_string(),
            id: Some(c_id),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("m", m_id)],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("m", m_id)),
                    args: vec![PseudoExpr::var_with_id("m", m_id)].into(),
                }),
            }),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("c", foreign_c_id)),
                args: vec![PseudoExpr::int(0)].into(),
            }),
        }),
    };

    assert!(
        !Simplifier::is_y_combinator(&expr),
        "same-name foreign let-body call must not satisfy Y-combinator let recursion"
    );
}
