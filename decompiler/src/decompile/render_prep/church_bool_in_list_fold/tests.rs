use super::*;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

fn nil_pattern() -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: Vec::new(),
        shape: ConstructorShape::Known(KnownConstructor::Nil),
    }
}

fn cons_pattern(h: VarId, t: VarId) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag: 1,
        fields: vec![Binder::new("h", h), Binder::new("t", t)],
        shape: ConstructorShape::Known(KnownConstructor::Cons),
    }
}

#[test]
fn rewrites_nil_true_when_cons_returns_apply() {
    let subject_id = VarId::new(30000);
    let h_id = VarId::new(30001);
    let t_id = VarId::new(30002);
    let helper_id = VarId::new(30003);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("xs", subject_id)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: nil_pattern(),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: cons_pattern(h_id, t_id),
                guard: None,
                body: PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
                    args: vec![
                        PseudoExpr::var_with_id("h", h_id),
                        PseudoExpr::var_with_id("t", t_id),
                    ]
                    .into(),
                },
            },
        ],
    };

    let rewritten = rewrite_church_bool_in_list_fold(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let nil_body = &clauses
        .iter()
        .find(|c| {
            matches!(
                c.pattern,
                WhenPattern::Constructor {
                    shape: ConstructorShape::Known(KnownConstructor::Nil),
                    ..
                }
            )
        })
        .unwrap()
        .body;
    assert!(
        matches!(nil_body, PseudoExpr::Lambda { params, .. } if params.len() == 2),
        "Nil arm Bool(true) must be rewritten to a 2-param Lambda, got {:?}",
        nil_body
    );
}

#[test]
fn does_not_rewrite_when_both_arms_are_bool() {
    // Genuine Bool When: both arms return Bool. Rewrite must NOT fire.
    let subject_id = VarId::new(31000);
    let h_id = VarId::new(31001);
    let t_id = VarId::new(31002);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("xs", subject_id)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: nil_pattern(),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: cons_pattern(h_id, t_id),
                guard: None,
                body: PseudoExpr::Bool(false),
            },
        ],
    };

    let rewritten = rewrite_church_bool_in_list_fold(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    for c in &clauses {
        assert!(
            matches!(c.body, PseudoExpr::Bool(_)),
            "Bool/Bool When must not be rewritten, got {:?}",
            c.body
        );
    }
}

#[test]
fn does_not_rewrite_when_cons_arm_evaluates_to_bool() {
    // Cons arm returns `True && False` — a BinOp evaluating to
    // Bool, so the When is genuinely Bool.
    use crate::pseudo::ast::BinaryOp;
    let subject_id = VarId::new(32000);
    let h_id = VarId::new(32001);
    let t_id = VarId::new(32002);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("xs", subject_id)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: nil_pattern(),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: cons_pattern(h_id, t_id),
                guard: None,
                body: PseudoExpr::BinOp {
                    op: BinaryOp::And,
                    left: PBox::new(PseudoExpr::Bool(true)),
                    right: PBox::new(PseudoExpr::Bool(false)),
                },
            },
        ],
    };

    let rewritten = rewrite_church_bool_in_list_fold(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let nil_body = &clauses
        .iter()
        .find(|c| {
            matches!(
                c.pattern,
                WhenPattern::Constructor {
                    shape: ConstructorShape::Known(KnownConstructor::Nil),
                    ..
                }
            )
        })
        .unwrap()
        .body;
    assert!(
        matches!(nil_body, PseudoExpr::Bool(true)),
        "Nil arm must remain Bool(true) when Cons evaluates to Bool, got {:?}",
        nil_body
    );
}

#[test]
fn rewrites_nil_false_to_church_false() {
    let subject_id = VarId::new(33000);
    let h_id = VarId::new(33001);
    let t_id = VarId::new(33002);
    let helper_id = VarId::new(33003);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("xs", subject_id)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: nil_pattern(),
                guard: None,
                body: PseudoExpr::Bool(false),
            },
            WhenClause {
                pattern: cons_pattern(h_id, t_id),
                guard: None,
                body: PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
                    args: vec![PseudoExpr::Unit].into(),
                },
            },
        ],
    };

    let rewritten = rewrite_church_bool_in_list_fold(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let nil_body = &clauses
        .iter()
        .find(|c| {
            matches!(
                c.pattern,
                WhenPattern::Constructor {
                    shape: ConstructorShape::Known(KnownConstructor::Nil),
                    ..
                }
            )
        })
        .unwrap()
        .body;
    let PseudoExpr::Lambda { params, body } = nil_body else {
        panic!("expected Lambda after rewrite, got {:?}", nil_body);
    };
    assert_eq!(params.len(), 2);
    let PseudoExpr::Var {
        id: Some(body_id), ..
    } = body.as_ref()
    else {
        panic!("expected Var body, got {:?}", body);
    };
    assert_eq!(
        *body_id,
        params[1].var_id(),
        "False arm body must reference second param"
    );
}

#[test]
fn rewrites_list_fold_nil_case_when_cons_case_is_lambda() {
    // The 4-arg `List.fold(list, True, fn(_) {...}, fn(x){x})` shape:
    // the `True` at arg 1 is a mislabeled Church-True selector.
    use crate::BuiltinId;
    let list_id = VarId::new(35000);
    let cons_case = PseudoExpr::Lambda {
        params: vec![Binder::new("_", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::Unit),
    };
    let identity_k = PseudoExpr::Lambda {
        params: vec![Binder::new("x", VarId::fresh_binding())],
        body: PBox::new(PseudoExpr::var("x")),
    };
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::ListFold,
        args: vec![
            PseudoExpr::var_with_id("list", list_id),
            PseudoExpr::Bool(true),
            cons_case,
            identity_k,
        ]
        .into(),
    };

    let rewritten = rewrite_church_bool_in_list_fold(expr);
    let PseudoExpr::BuiltinCall { args, .. } = rewritten else {
        panic!()
    };
    assert!(
        matches!(&args[1], PseudoExpr::Lambda { params, .. } if params.len() == 2),
        "nil-case Bool(true) must be rewritten to a 2-param Lambda, got {:?}",
        args[1]
    );
}

#[test]
fn does_not_rewrite_list_fold_when_cons_case_evaluates_to_bool() {
    // A Bool-evaluating cons-case makes the fold a genuine
    // Bool-returning computation.
    use crate::BuiltinId;
    use crate::pseudo::ast::BinaryOp;
    let list_id = VarId::new(35100);
    let cons_case = PseudoExpr::BinOp {
        op: BinaryOp::And,
        left: PBox::new(PseudoExpr::Bool(true)),
        right: PBox::new(PseudoExpr::Bool(false)),
    };
    let expr = PseudoExpr::BuiltinCall {
        name: BuiltinId::ListFold,
        args: vec![
            PseudoExpr::var_with_id("list", list_id),
            PseudoExpr::Bool(true),
            cons_case,
            PseudoExpr::Bool(true),
        ]
        .into(),
    };

    let rewritten = rewrite_church_bool_in_list_fold(expr);
    let PseudoExpr::BuiltinCall { args, .. } = rewritten else {
        panic!()
    };
    assert!(
        matches!(args[1], PseudoExpr::Bool(true)),
        "Bool-evaluating cons-case must NOT trigger rewrite, got {:?}",
        args[1]
    );
}

#[test]
fn does_not_rewrite_when_wildcard_fallthrough() {
    // `when xs is { Nil -> True; _ -> ... }` — no explicit Cons
    // pattern, so the pass leaves it alone.
    let subject_id = VarId::new(34000);
    let helper_id = VarId::new(34001);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("xs", subject_id)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: nil_pattern(),
                guard: None,
                body: PseudoExpr::Bool(true),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
                    args: vec![].into(),
                },
            },
        ],
    };

    let rewritten = rewrite_church_bool_in_list_fold(expr);
    let PseudoExpr::When { clauses, .. } = rewritten else {
        panic!()
    };
    let nil_body = &clauses[0].body;
    assert!(
        matches!(nil_body, PseudoExpr::Bool(true)),
        "Wildcard fall-through must NOT trigger rewrite, got {:?}",
        nil_body
    );
}
