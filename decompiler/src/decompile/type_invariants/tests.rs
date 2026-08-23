use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, WhenClause};
use std::rc::Rc;

#[test]
fn test_validate_type_invariants_accepts_pair_pattern_through_let_body_type() {
    // The AST carries no types, so a TypeEnvironment supplies them.
    let pair_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let mut env = TypeEnvironment::new();
    env.bind_var(
        pair_id,
        Rc::new(PseudoType::Pair(
            Rc::new(PseudoType::Int),
            Rc::new(PseudoType::Bool),
        )),
    );

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Let {
            name: "subject".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
            value: PBox::new(PseudoExpr::Data(Box::new(
                crate::pseudo::ast::PseudoData::Constr(0, vec![]),
            ))),
            body: PBox::new(PseudoExpr::Var {
                name: "pair_view".to_string(),
                id: Some(pair_id),
            }),
        }),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Pair(Binder::synthetic("left"), Binder::synthetic("right")),
            guard: None,
            body: PseudoExpr::Unit,
        }],
    };

    validate_type_invariants(&expr, None, &env)
        .expect("pair pattern should validate against the let body expression type");
}

#[test]
fn test_validate_type_invariants_accepts_option_if_condition() {
    let cond_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let mut env = TypeEnvironment::new();
    env.bind_var(
        cond_id,
        Rc::new(PseudoType::Option(Rc::new(PseudoType::Unknown))),
    );

    let expr = PseudoExpr::If {
        condition: PBox::new(PseudoExpr::Var {
            name: "condition".to_string(),
            id: Some(cond_id),
        }),
        then_branch: PBox::new(PseudoExpr::Unit),
        else_branch: PBox::new(PseudoExpr::Unit),
    };

    validate_type_invariants(&expr, None, &env)
        .expect("option-like truthy sentinels should be allowed in if conditions");
}

#[test]
fn test_validate_type_invariants_accepts_not_on_data_condition() {
    let cond_id = crate::pseudo::var_id::VarId::fresh_compat_placeholder();
    let mut env = TypeEnvironment::new();
    env.bind_var(cond_id, Rc::new(PseudoType::Data));

    let expr = PseudoExpr::UnOp {
        op: UnaryOp::Not,
        operand: PBox::new(PseudoExpr::Var {
            name: "condition".to_string(),
            id: Some(cond_id),
        }),
    };

    validate_type_invariants(&expr, None, &env)
        .expect("data-like truthy sentinels should be allowed under unary not");
}
