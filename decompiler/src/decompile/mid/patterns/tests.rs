use super::*;
use crate::pseudo::mid::expr::MidLiteral;
use crate::pseudo::mid::expr_id::{MidExprId, ProvenanceBuilder};
use crate::pseudo::var_id::VarId;

fn id(n: u32) -> MidExprId {
    MidExprId::new(n)
}

fn test_provenance(max_existing_id: u32) -> ProvenanceBuilder {
    let mut provenance = ProvenanceBuilder::new();
    for _ in 0..=max_existing_id {
        provenance.fresh_id();
    }
    for n in 0..=max_existing_id {
        provenance.link(id(n), n as isize);
    }
    provenance
}

#[test]
fn test_recognize_if_then_else() {
    // Builtin(IfThenElse, [cond, then, else])
    let mut expr = MidExpr::Builtin {
        id: id(0),
        fun: DefaultFunction::IfThenElse,
        forces: 3,
        args: vec![
            MidExpr::Var {
                id: id(1),
                var: VarId::new(0),
            },
            MidExpr::Lit {
                id: id(2),
                value: MidLiteral::Integer(1.into()),
            },
            MidExpr::Lit {
                id: id(3),
                value: MidLiteral::Integer(0.into()),
            },
        ],
        folded: None,
    };

    let mut provenance = test_provenance(3);
    recognize_patterns(&mut expr, &mut provenance);

    assert!(
        matches!(expr, MidExpr::If { .. }),
        "Should be converted to If, got {:?}",
        expr
    );
}

#[test]
fn test_recognize_if_then_else_allocates_fresh_id_with_provenance() {
    let original_id = id(0);
    let mut expr = MidExpr::Builtin {
        id: original_id,
        fun: DefaultFunction::IfThenElse,
        forces: 3,
        args: vec![
            MidExpr::Var {
                id: id(1),
                var: VarId::new(0),
            },
            MidExpr::Lit {
                id: id(2),
                value: MidLiteral::Bool(true),
            },
            MidExpr::Lit {
                id: id(3),
                value: MidLiteral::Bool(false),
            },
        ],
        folded: None,
    };

    let mut provenance = test_provenance(3);
    recognize_patterns(&mut expr, &mut provenance);

    let rewritten_id = match expr {
        MidExpr::If { id, .. } => id,
        other => panic!("Expected If after rewrite, got {other:?}"),
    };

    assert_ne!(
        rewritten_id, original_id,
        "rewrite must allocate a fresh MidExprId"
    );
    assert_eq!(
        provenance.uplc_ids(rewritten_id),
        provenance.uplc_ids(original_id),
        "rewrite must preserve provenance from the replaced node"
    );
}

#[test]
fn test_recognize_trace() {
    let mut expr = MidExpr::Builtin {
        id: id(0),
        fun: DefaultFunction::Trace,
        forces: 1,
        args: vec![
            MidExpr::Lit {
                id: id(1),
                value: MidLiteral::String("error".into()),
            },
            MidExpr::Var {
                id: id(2),
                var: VarId::new(0),
            },
        ],
        folded: None,
    };

    let mut provenance = test_provenance(2);
    recognize_patterns(&mut expr, &mut provenance);

    assert!(
        matches!(expr, MidExpr::Trace { .. }),
        "Should be converted to Trace"
    );
}

#[test]
fn test_recognize_choose_list() {
    let mut expr = MidExpr::Builtin {
        id: id(0),
        fun: DefaultFunction::ChooseList,
        forces: 2,
        args: vec![
            MidExpr::Var {
                id: id(1),
                var: VarId::new(0),
            },
            MidExpr::Lit {
                id: id(2),
                value: MidLiteral::Unit,
            },
            MidExpr::Lit {
                id: id(3),
                value: MidLiteral::Integer(1.into()),
            },
        ],
        folded: None,
    };

    let mut provenance = test_provenance(3);
    recognize_patterns(&mut expr, &mut provenance);

    assert!(
        matches!(
            expr,
            MidExpr::Case {
                encoding: CaseEncoding::ChooseList,
                ..
            }
        ),
        "Should be converted to Case(ChooseList)"
    );
}

#[test]
fn test_recognize_choose_data_extended_arity() {
    let original_id = id(0);
    let mut expr = MidExpr::Builtin {
        id: original_id,
        fun: DefaultFunction::ChooseData,
        forces: 1,
        args: vec![
            MidExpr::Var {
                id: id(1),
                var: VarId::new(0),
            },
            MidExpr::Thunk {
                id: id(2),
                body: Box::new(MidExpr::Lit {
                    id: id(3),
                    value: MidLiteral::Integer(0.into()),
                }),
                cosmetic: false,
            },
            MidExpr::Thunk {
                id: id(4),
                body: Box::new(MidExpr::Lit {
                    id: id(5),
                    value: MidLiteral::Integer(1.into()),
                }),
                cosmetic: false,
            },
            MidExpr::Thunk {
                id: id(6),
                body: Box::new(MidExpr::Lit {
                    id: id(7),
                    value: MidLiteral::Integer(2.into()),
                }),
                cosmetic: false,
            },
            MidExpr::Thunk {
                id: id(8),
                body: Box::new(MidExpr::Lit {
                    id: id(9),
                    value: MidLiteral::Integer(3.into()),
                }),
                cosmetic: false,
            },
            MidExpr::Thunk {
                id: id(10),
                body: Box::new(MidExpr::Lit {
                    id: id(11),
                    value: MidLiteral::Integer(4.into()),
                }),
                cosmetic: false,
            },
            MidExpr::Thunk {
                id: id(12),
                body: Box::new(MidExpr::Lit {
                    id: id(13),
                    value: MidLiteral::Integer(5.into()),
                }),
                cosmetic: false,
            },
        ],
        folded: None,
    };

    let mut provenance = test_provenance(13);
    recognize_patterns(&mut expr, &mut provenance);

    let (rewritten_id, branches) = match expr {
        MidExpr::Case {
            id,
            encoding: CaseEncoding::IfChain,
            branches,
            ..
        } => (id, branches),
        other => panic!("Expected Case(IfChain) after rewrite, got {other:?}"),
    };

    assert_ne!(
        rewritten_id, original_id,
        "rewrite must allocate a fresh MidExprId"
    );
    assert_eq!(
        provenance.uplc_ids(rewritten_id),
        vec![0],
        "root rewrite owner should keep only operator provenance"
    );
    assert_eq!(
        branches.len(),
        6,
        "expected one branch per choose_data handler"
    );
    assert_eq!(
        branches.iter().map(|branch| branch.tag).collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 4, 5],
        "extended choose_data handlers should become explicit branch tags"
    );
    assert_eq!(provenance.uplc_ids(branches[0].body.id()), vec![3, 2]);
    assert_eq!(provenance.uplc_ids(branches[5].body.id()), vec![13, 12]);
}

#[test]
fn test_force_builtin_if_then_else_keeps_root_and_branch_wrapper_provenance_separate() {
    let mut expr = MidExpr::Force {
        id: id(0),
        body: Box::new(MidExpr::Builtin {
            id: id(1),
            fun: DefaultFunction::IfThenElse,
            forces: 1,
            args: vec![
                MidExpr::Var {
                    id: id(2),
                    var: VarId::new(0),
                },
                MidExpr::Thunk {
                    id: id(3),
                    body: Box::new(MidExpr::Lit {
                        id: id(4),
                        value: MidLiteral::Bool(true),
                    }),
                    cosmetic: false,
                },
                MidExpr::Thunk {
                    id: id(5),
                    body: Box::new(MidExpr::Lit {
                        id: id(6),
                        value: MidLiteral::Bool(false),
                    }),
                    cosmetic: false,
                },
            ],
            folded: None,
        }),
        resolved: None,
    };

    let mut provenance = test_provenance(6);
    recognize_patterns(&mut expr, &mut provenance);

    let (force_id, rewritten_id, then_id, else_id) = match expr {
        MidExpr::Force { id, body, .. } => match body.as_ref() {
            MidExpr::If {
                id: inner_id,
                then_branch,
                else_branch,
                ..
            } => (id, *inner_id, then_branch.id(), else_branch.id()),
            other => panic!("Expected Force(If) after rewrite, got inner {other:?}"),
        },
        other => panic!("Expected If after rewrite, got {other:?}"),
    };

    assert_eq!(provenance.uplc_ids(force_id), vec![0]);
    assert_eq!(provenance.uplc_ids(rewritten_id), vec![1]);
    assert_eq!(provenance.uplc_ids(then_id), vec![4, 3]);
    assert_eq!(provenance.uplc_ids(else_id), vec![6, 5]);
}

#[test]
fn test_scott_encoding_transfers_apply_and_branch_wrappers_to_surviving_owners() {
    let mut expr = MidExpr::Force {
        id: id(0),
        body: Box::new(MidExpr::Apply {
            id: id(1),
            function: Box::new(MidExpr::Force {
                id: id(2),
                body: Box::new(MidExpr::Var {
                    id: id(3),
                    var: VarId::new(0),
                }),
                resolved: None,
            }),
            args: vec![
                MidExpr::Thunk {
                    id: id(4),
                    body: Box::new(MidExpr::Lit {
                        id: id(5),
                        value: MidLiteral::Integer(0.into()),
                    }),
                    cosmetic: false,
                },
                MidExpr::Closure {
                    id: id(6),
                    params: vec![VarId::new(1)],
                    body: Box::new(MidExpr::Thunk {
                        id: id(7),
                        body: Box::new(MidExpr::Var {
                            id: id(8),
                            var: VarId::new(1),
                        }),
                        cosmetic: false,
                    }),
                    recursive: None,
                },
            ],
        }),
        resolved: None,
    };

    let mut provenance = test_provenance(8);
    recognize_patterns(&mut expr, &mut provenance);

    let (rewritten_id, scrutinee_id, branch0_id, branch1_id) = match expr {
        MidExpr::Case {
            id,
            scrutinee,
            branches,
            encoding: CaseEncoding::Scott,
        } => (
            id,
            scrutinee.id(),
            branches[0].body.id(),
            branches[1].body.id(),
        ),
        other => panic!("Expected Scott Case after rewrite, got {other:?}"),
    };

    assert_eq!(provenance.uplc_ids(rewritten_id), vec![0, 1]);
    assert_eq!(provenance.uplc_ids(scrutinee_id), vec![3, 2]);
    assert_eq!(provenance.uplc_ids(branch0_id), vec![5, 4]);
    assert_eq!(provenance.uplc_ids(branch1_id), vec![8, 7, 6]);
}

#[test]
fn test_y_combinator_detection() {
    let f = VarId::new(0);
    let x = VarId::new(1);
    // fn(f) { let g = fn(x) { f(x(x)) } in g(g) }
    let expr = MidExpr::Closure {
        id: id(0),
        params: vec![f],
        body: Box::new(MidExpr::Let {
            id: id(1),
            var: VarId::new(2),
            value: Box::new(MidExpr::Closure {
                id: id(2),
                params: vec![x],
                body: Box::new(MidExpr::Apply {
                    id: id(3),
                    function: Box::new(MidExpr::Var { id: id(4), var: f }),
                    args: vec![MidExpr::Apply {
                        id: id(5),
                        function: Box::new(MidExpr::Var { id: id(6), var: x }),
                        args: vec![MidExpr::Var { id: id(7), var: x }],
                    }],
                }),
                recursive: None,
            }),
            body: Box::new(MidExpr::Apply {
                id: id(8),
                function: Box::new(MidExpr::Var {
                    id: id(9),
                    var: VarId::new(2),
                }),
                args: vec![MidExpr::Var {
                    id: id(10),
                    var: VarId::new(2),
                }],
            }),
            use_count: 1,
        }),
        recursive: None,
    };

    assert!(is_y_combinator(&expr), "Should detect Y-combinator");
}
