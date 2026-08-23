use super::*;
use crate::pseudo::ast::Binder;
use crate::pseudo::ast::PBox;

fn vid(n: u32) -> VarId {
    VarId::new(n)
}
fn vref(name: &str, n: u32) -> PseudoExpr {
    PseudoExpr::var_with_id(name, vid(n))
}

fn add_helper_let(body: PseudoExpr) -> PseudoExpr {
    PseudoExpr::Let {
        name: "helper_43".to_string(),
        id: Some(vid(1000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("x".to_string(), vid(10)),
                Binder::new("y".to_string(), vid(11)),
            ],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(vref("x", 10)),
                right: PBox::new(vref("y", 11)),
            }),
        }),
        body: PBox::new(body),
    }
}

/// `helper_43 = fn(x, y) { x + y }` → renamed to `add_int`.
#[test]
fn renames_add() {
    let input = add_helper_let(vref("helper_43", 1000));
    let out = rename_semantic_helpers(input);
    let PseudoExpr::Let { name, body, .. } = out else {
        panic!("Let");
    };
    assert_eq!(name, "add_int");
    // Use-site renamed too.
    let PseudoExpr::Var { name: ref_name, .. } = body.into_inner() else {
        panic!("Var");
    };
    assert_eq!(ref_name, "add_int");
}

/// Wrap inner expression in `let e = Constr_0; let b = Constr_1; <inner>`.
fn wrap_with_church_bool_consts(inner: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::constructor::ConstructorShape;
    PseudoExpr::Let {
        name: "e".to_string(),
        id: Some(vid(9001)),
        value: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 0),
            vec![],
        )),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(vid(9002)),
            value: PBox::new(PseudoExpr::constr(
                ConstructorShape::unknown_data(1, 0),
                vec![],
            )),
            body: PBox::new(inner),
        }),
    }
}

/// `helper_30 = fn(x, y) { if x == y { e } else { b } }` → `church_eq`.
#[test]
fn renames_church_eq() {
    let helper_let = PseudoExpr::Let {
        name: "helper_30".to_string(),
        id: Some(vid(2000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("x".to_string(), vid(20)),
                Binder::new("y".to_string(), vid(21)),
            ],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(vref("x", 20)),
                    right: PBox::new(vref("y", 21)),
                }),
                then_branch: PBox::new(vref("e", 9001)),
                else_branch: PBox::new(vref("b", 9002)),
            }),
        }),
        body: PBox::new(vref("helper_30", 2000)),
    };
    let input = wrap_with_church_bool_consts(helper_let);
    let out = rename_semantic_helpers(input);
    // Peel the two outer Constr Lets (`e` and `b`).
    let PseudoExpr::Let { body, .. } = out else {
        panic!("outer Let")
    };
    let PseudoExpr::Let { body, .. } = body.into_inner() else {
        panic!("inner Let")
    };
    let PseudoExpr::Let { name, body, .. } = body.into_inner() else {
        panic!("helper Let")
    };
    assert_eq!(name, "church_eq");
    let PseudoExpr::Var { name: ref_name, .. } = body.into_inner() else {
        panic!("Var")
    };
    assert_eq!(ref_name, "church_eq");
}

/// `let outer = …; fn(_) { let e = …; let b = …; helper = … }` — the
/// `e`/`b` lets are not in the outermost chain, so no rename.
#[test]
fn skips_nested_e_b_constr_lets() {
    use crate::pseudo::constructor::ConstructorShape;
    // Build helper at the top.
    let helper_let = PseudoExpr::Let {
        name: "helper_30".to_string(),
        id: Some(vid(2000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("x".to_string(), vid(20)),
                Binder::new("y".to_string(), vid(21)),
            ],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(vref("x", 20)),
                    right: PBox::new(vref("y", 21)),
                }),
                then_branch: PBox::new(vref("e", 9001)),
                else_branch: PBox::new(vref("b", 9002)),
            }),
        }),
        body: PBox::new(vref("helper_30", 2000)),
    };
    // Wrap in a Lambda body so `e`/`b` Lets are NOT in the
    // outermost Let chain.
    let nested_e = PseudoExpr::Let {
        name: "e".to_string(),
        id: Some(vid(9001)),
        value: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 0),
            vec![],
        )),
        body: PBox::new(PseudoExpr::Let {
            name: "b".to_string(),
            id: Some(vid(9002)),
            value: PBox::new(PseudoExpr::constr(
                ConstructorShape::unknown_data(1, 0),
                vec![],
            )),
            body: PBox::new(helper_let),
        }),
    };
    let outer = PseudoExpr::Let {
        name: "outer".to_string(),
        id: Some(vid(9999)),
        value: PBox::new(PseudoExpr::Unit),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("_".to_string(), vid(8888))],
            body: PBox::new(nested_e),
        }),
    };
    let out = rename_semantic_helpers(outer.clone());
    // No rename: `e`/`b` are not in the outermost chain.
    assert_eq!(out, outer);
}

/// `if x == y { e } else { b }` where `e`/`b` are LOCAL vars (not
/// top-level Constr consts) — no church_eq rename.
#[test]
fn skips_local_e_b_shadows() {
    let helper_let = PseudoExpr::Let {
        name: "helper_30".to_string(),
        id: Some(vid(2000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("x".to_string(), vid(20)),
                Binder::new("y".to_string(), vid(21)),
            ],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::BinOp {
                    op: BinaryOp::Eq,
                    left: PBox::new(vref("x", 20)),
                    right: PBox::new(vref("y", 21)),
                }),
                // `e` / `b` have arbitrary VarIds that are NOT
                // top-level church-bool consts.
                then_branch: PBox::new(vref("e", 5555)),
                else_branch: PBox::new(vref("b", 5556)),
            }),
        }),
        body: PBox::new(vref("helper_30", 2000)),
    };
    let out = rename_semantic_helpers(helper_let.clone());
    assert_eq!(out, helper_let);
}

/// A when-clause pattern binder named `add_int` poisons the
/// `add_int` slot, so the helper gets `add_int_2`.
#[test]
fn avoids_collision_with_when_pattern_binder() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    let helper_let = PseudoExpr::Let {
        name: "helper_43".to_string(),
        id: Some(vid(1000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("x".to_string(), vid(10)),
                Binder::new("y".to_string(), vid(11)),
            ],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(vref("x", 10)),
                right: PBox::new(vref("y", 11)),
            }),
        }),
        // Body contains a `when ... is { _ as add_int -> ... }`
        // — pattern binder shadows the slot.
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(vref("helper_43", 1000)),
            subject_name: None,
            clauses: vec![WhenClause {
                pattern: WhenPattern::Var(Binder::new("add_int".to_string(), vid(12345))),
                guard: None,
                body: vref("add_int", 12345),
            }],
        }),
    };
    let out = rename_semantic_helpers(helper_let);
    let PseudoExpr::Let { name, .. } = out else {
        panic!("Let")
    };
    assert_eq!(name, "add_int_2");
}

/// Two `fn(x,y){x+y}` helpers → `add_int`, `add_int_2`.
#[test]
fn disambiguates_repeat_shapes() {
    let inner = PseudoExpr::Let {
        name: "helper_99".to_string(),
        id: Some(vid(2000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("a".to_string(), vid(30)),
                Binder::new("b".to_string(), vid(31)),
            ],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(vref("a", 30)),
                right: PBox::new(vref("b", 31)),
            }),
        }),
        body: PBox::new(vref("helper_99", 2000)),
    };
    let input = add_helper_let(inner);
    let out = rename_semantic_helpers(input);
    let PseudoExpr::Let {
        name: outer_name,
        body,
        ..
    } = out
    else {
        panic!("Let")
    };
    assert_eq!(outer_name, "add_int");
    let PseudoExpr::Let {
        name: inner_name, ..
    } = body.into_inner()
    else {
        panic!("Let")
    };
    assert_eq!(inner_name, "add_int_2");
}

/// Non-2-arg lambdas — no rename.
#[test]
fn skips_non_two_arg_helpers() {
    let input = PseudoExpr::Let {
        name: "helper_99".to_string(),
        id: Some(vid(3000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x".to_string(), vid(40))],
            body: PBox::new(vref("x", 40)),
        }),
        body: PBox::new(vref("helper_99", 3000)),
    };
    let out = rename_semantic_helpers(input.clone());
    assert_eq!(out, input);
}

/// `fn(x, y) { fn(_, k) { k(x, y) } }` → `church_cons`.
#[test]
fn renames_church_cons() {
    let input = PseudoExpr::Let {
        name: "helper_3".to_string(),
        id: Some(vid(5000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("x".to_string(), vid(60)),
                Binder::new("y".to_string(), vid(61)),
            ],
            body: PBox::new(PseudoExpr::Lambda {
                params: vec![
                    Binder::new("_".to_string(), vid(62)),
                    Binder::new("k".to_string(), vid(63)),
                ],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(vref("k", 63)),
                    args: vec![vref("x", 60), vref("y", 61)].into(),
                }),
            }),
        }),
        body: PBox::new(vref("helper_3", 5000)),
    };
    let out = rename_semantic_helpers(input);
    let PseudoExpr::Let { name, body, .. } = out else {
        panic!("Let")
    };
    assert_eq!(name, "church_cons");
    let PseudoExpr::Var { name: ref_name, .. } = body.into_inner() else {
        panic!("Var")
    };
    assert_eq!(ref_name, "church_cons");
}

/// `fn(x, y) { fn(k) { k(x, y) } }` → `church_pair`.
#[test]
fn renames_church_pair() {
    let input = PseudoExpr::Let {
        name: "helper_99".to_string(),
        id: Some(vid(6000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("x".to_string(), vid(70)),
                Binder::new("y".to_string(), vid(71)),
            ],
            body: PBox::new(PseudoExpr::Lambda {
                params: vec![Binder::new("k".to_string(), vid(72))],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(vref("k", 72)),
                    args: vec![vref("x", 70), vref("y", 71)].into(),
                }),
            }),
        }),
        body: PBox::new(vref("helper_99", 6000)),
    };
    let out = rename_semantic_helpers(input);
    let PseudoExpr::Let { name, .. } = out else {
        panic!("Let")
    };
    assert_eq!(name, "church_pair");
}

/// `fn(x, y) { y + x }` — swapped operands, no match.
#[test]
fn skips_swapped_operands() {
    let input = PseudoExpr::Let {
        name: "helper_99".to_string(),
        id: Some(vid(4000)),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![
                Binder::new("x".to_string(), vid(50)),
                Binder::new("y".to_string(), vid(51)),
            ],
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(vref("y", 51)),
                right: PBox::new(vref("x", 50)),
            }),
        }),
        body: PBox::new(vref("helper_99", 4000)),
    };
    let out = rename_semantic_helpers(input.clone());
    assert_eq!(out, input);
}
