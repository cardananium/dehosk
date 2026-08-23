use super::*;
use crate::pseudo::ast::PVec;
use crate::pseudo::ast::{Binder, WhenClause};
use crate::pseudo::constructor::ConstructorShape;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name.to_string(), VarId::new(id))
}

fn varref(name: &str, id: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, VarId::new(id))
}

fn constr0(tag: usize) -> PseudoExpr {
    PseudoExpr::Constr {
        tag,
        shape: ConstructorShape::unknown_data(tag, 0),
        fields: PVec::new(),
        type_hint: None,
    }
}

fn pat_constr(tag: usize) -> WhenPattern {
    WhenPattern::Constructor {
        type_hint: None,
        tag,
        fields: Vec::new(),
        shape: ConstructorShape::unknown_data(tag, 0),
    }
}

/// Top-level `const e = Constr0(0)`, `const b = Constr0(1)` +
/// `if cond { e } else { b }; when result is { Constr(1) -> A; _ -> B }`
/// → `if cond { B } else { A }`.
#[test]
fn rewrites_bool_residue_to_if() {
    let e_id = VarId::new(100);
    let b_id = VarId::new(101);
    let result_id = VarId::new(200);

    // Innermost: when result is { Constr(1) -> A; _ -> B }
    let when_body = PseudoExpr::When {
        subject: PBox::new(varref("result", 200)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: pat_constr(1),
                guard: None,
                body: varref("A", 1),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: varref("B", 2),
            },
        ],
    };
    // let result = if cond { e } else { b } in <when_body>
    let if_then_else = PseudoExpr::Let {
        name: "result".to_string(),
        id: Some(result_id),
        value: PBox::new(PseudoExpr::If {
            condition: PBox::new(varref("cond", 50)),
            then_branch: PBox::new(varref("e", 100)),
            else_branch: PBox::new(varref("b", 101)),
        }),
        body: PBox::new(when_body),
    };
    // Top-level: const e = Constr0(0); const b = Constr0(1); <if_then_else>
    let expr = PseudoExpr::Let {
        name: "e".to_string(),
        id: Some(e_id),
        value: PBox::new(constr0(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(b_id),
            value: PBox::new(constr0(1)),
            body: PBox::new(if_then_else),
        }),
    };

    let out = recover_church_booleans(expr);
    // Strip the const-binding chain to find the rewritten core.
    let core = unwrap_outer_lets(&out, &["e", "b"]);
    match core {
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            // cond=true matches Constr(1)? No — e has tag 0, falls to _, body=B.
            // So new_then = B, new_else = A.
            assert!(matches!(condition.as_ref(), PseudoExpr::Var { name, .. } if name == "cond"));
            assert!(matches!(then_branch.as_ref(), PseudoExpr::Var { name, .. } if name == "B"));
            assert!(matches!(else_branch.as_ref(), PseudoExpr::Var { name, .. } if name == "A"));
        }
        other => panic!("expected If after rewrite, got {:?}", other),
    }
}

fn unwrap_outer_lets<'a>(mut expr: &'a PseudoExpr, names: &[&str]) -> &'a PseudoExpr {
    for n in names {
        if let PseudoExpr::Let { name, body, .. } = expr
            && name == n
        {
            expr = body;
        }
    }
    expr
}

/// `then_tag == else_tag` → no rewrite (degenerate `if` returning same value).
#[test]
fn does_not_rewrite_when_branches_same_tag() {
    let e_id = VarId::new(100);
    let result_id = VarId::new(200);
    let when_body = PseudoExpr::When {
        subject: PBox::new(varref("result", 200)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: pat_constr(1),
                guard: None,
                body: varref("A", 1),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: varref("B", 2),
            },
        ],
    };
    let expr = PseudoExpr::Let {
        name: "e".to_string(),
        id: Some(e_id),
        value: PBox::new(constr0(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "result".to_string(),
            id: Some(result_id),
            value: PBox::new(PseudoExpr::If {
                condition: PBox::new(varref("cond", 50)),
                then_branch: PBox::new(varref("e", 100)),
                else_branch: PBox::new(varref("e", 100)),
            }),
            body: PBox::new(when_body),
        }),
    };
    let out = recover_church_booleans(expr.clone());
    assert_eq!(out, expr);
}

/// Constructor pattern with non-empty fields → no rewrite (THEN body
/// could depend on extracted fields).
#[test]
fn does_not_rewrite_when_constructor_has_fields() {
    let e_id = VarId::new(100);
    let b_id = VarId::new(101);
    let result_id = VarId::new(200);
    let constr_with_field = WhenPattern::Constructor {
        type_hint: None,
        tag: 1,
        fields: vec![binder("payload", 300)],
        shape: ConstructorShape::unknown_data(1, 1),
    };
    let when_body = PseudoExpr::When {
        subject: PBox::new(varref("result", 200)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: constr_with_field,
                guard: None,
                body: varref("payload", 300),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: varref("B", 2),
            },
        ],
    };
    let expr = PseudoExpr::Let {
        name: "e".to_string(),
        id: Some(e_id),
        value: PBox::new(constr0(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(b_id),
            value: PBox::new(constr0(1)),
            body: PBox::new(PseudoExpr::Let {
                name: "result".to_string(),
                id: Some(result_id),
                value: PBox::new(PseudoExpr::If {
                    condition: PBox::new(varref("cond", 50)),
                    then_branch: PBox::new(varref("e", 100)),
                    else_branch: PBox::new(varref("b", 101)),
                }),
                body: PBox::new(when_body),
            }),
        }),
    };
    let out = recover_church_booleans(expr.clone());
    assert_eq!(out, expr);
}
