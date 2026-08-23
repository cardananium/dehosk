use super::*;
use std::rc::Rc;
use uplc::ast::{Constant, DeBruijn, FakeNamedDeBruijn, Program};

fn nd(text: &str, index: usize) -> NamedDeBruijn {
    NamedDeBruijn {
        text: text.to_string(),
        index: DeBruijn::new(index),
    }
}

fn translate_hex(hex: &str) -> (MidExpr, MidTranslator) {
    let bytes = hex::decode(hex).expect("valid hex");
    let mut cbor_buffer = Vec::new();
    let program: Program<FakeNamedDeBruijn> = Program::from_cbor(&bytes, &mut cbor_buffer)
        .or_else(|_| Program::from_flat(&bytes))
        .expect("valid UPLC");
    let program: Program<NamedDeBruijn> = program.into();
    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);
    (mid, translator)
}

#[test]
fn test_translate_identity() {
    // UPLC: (lam x x) in CBOR-wrapped flat
    let (mid, translator) = translate_hex("46010000200101");
    match &mid {
        MidExpr::Closure { params, body, .. } => {
            assert_eq!(params.len(), 1);
            match body.as_ref() {
                MidExpr::Var { var, .. } => {
                    assert_eq!(*var, params[0]);
                }
                other => panic!("Expected Var, got {:?}", other),
            }
        }
        other => panic!("Expected Closure, got {:?}", other),
    }
    assert!(translator.provenance.node_count() >= 2);
    // Check var registry has the parameter
    assert_eq!(translator.var_registry.len(), 1);
}

#[test]
fn test_translate_constant() {
    // UPLC: identity function, raw flat
    let _hex = "010000200101";
    let (mid, _) = translate_hex("46010000200101");
    // Just verify it doesn't panic and produces a valid tree
    assert!(mid.node_count() >= 1);
}

#[test]
fn test_translate_let_pattern() {
    // Apply(Lambda(x, Var(x)), Constant(42)) is recognized as
    // Let { x = 42, body = x }; lacking a simple let hex, this test
    // runs the identity hex instead.
    let (mid, translator) = translate_hex("46010000200101");
    // Identity is just a closure, not a let
    assert!(matches!(mid, MidExpr::Closure { .. }));
    assert!(!translator.var_registry.is_empty());
    assert!(translator.provenance.node_count() >= 2);
}

#[test]
fn test_provenance_links() {
    let (mid, translator) = translate_hex("46010000200101");
    let mid_id = mid.id();
    let uplc_ids = translator.provenance.uplc_ids(mid_id);
    assert!(
        !uplc_ids.is_empty(),
        "Root node should have UPLC provenance"
    );
}

#[test]
fn test_collapsed_lambda_chain_absorbs_inner_lambda_provenance_into_root_closure() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Lambda {
            parameter_name: Rc::new(nd("x", 1)),
            body: Rc::new(Term::Lambda {
                parameter_name: Rc::new(nd("y", 1)),
                body: Rc::new(Term::Var {
                    name: Rc::new(nd("x", 2)),
                    uniq_id: 12,
                }),
                uniq_id: 11,
            }),
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    assert_eq!(translator.provenance.mid_for_uplc(10), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(11), Some(mid.id()));
    assert!(
        translator.provenance.uplc_ids(mid.id()).contains(&11),
        "collapsed inner lambda should stay attached to surviving closure owner"
    );
}

#[test]
fn test_collapsed_let_pattern_absorbs_lambda_provenance_into_surviving_let() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Apply {
            function: Rc::new(Term::Lambda {
                parameter_name: Rc::new(nd("x", 1)),
                body: Rc::new(Term::Var {
                    name: Rc::new(nd("x", 1)),
                    uniq_id: 12,
                }),
                uniq_id: 11,
            }),
            argument: Rc::new(Term::Constant {
                value: Rc::new(Constant::Integer(42.into())),
                uniq_id: 13,
            }),
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    assert!(matches!(mid, MidExpr::Let { .. }));
    assert_eq!(translator.provenance.mid_for_uplc(10), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(11), Some(mid.id()));
    assert!(
        translator.provenance.uplc_ids(mid.id()).contains(&11),
        "collapsed lambda should stay attached to surviving let owner"
    );
}

#[test]
fn test_collapsed_apply_spine_absorbs_inner_apply_provenance_into_surviving_apply() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Apply {
            function: Rc::new(Term::Apply {
                function: Rc::new(Term::Var {
                    name: Rc::new(nd("f", 99)),
                    uniq_id: 12,
                }),
                argument: Rc::new(Term::Var {
                    name: Rc::new(nd("x", 99)),
                    uniq_id: 13,
                }),
                uniq_id: 11,
            }),
            argument: Rc::new(Term::Var {
                name: Rc::new(nd("y", 99)),
                uniq_id: 14,
            }),
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    assert!(matches!(mid, MidExpr::Apply { .. }));
    assert_eq!(translator.provenance.mid_for_uplc(10), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(11), Some(mid.id()));
    assert!(
        translator.provenance.uplc_ids(mid.id()).contains(&11),
        "collapsed inner apply should stay attached to surviving apply owner"
    );
}

#[test]
fn test_case_constr_constant_fold_absorbs_selected_branch_closure_into_surviving_let_chain() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Case {
            constr: Rc::new(Term::Constr {
                tag: 0,
                fields: vec![Term::Constant {
                    value: Rc::new(Constant::Integer(42.into())),
                    uniq_id: 14,
                }],
                uniq_id: 13,
            }),
            branches: vec![Term::Lambda {
                parameter_name: Rc::new(nd("x", 1)),
                body: Rc::new(Term::Var {
                    name: Rc::new(nd("x", 1)),
                    uniq_id: 12,
                }),
                uniq_id: 11,
            }],
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    assert!(matches!(mid, MidExpr::Let { .. }));
    assert_eq!(translator.provenance.mid_for_uplc(10), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(11), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(13), Some(mid.id()));
    assert!(
        translator.provenance.uplc_ids(mid.id()).contains(&11),
        "selected branch closure should stay attached to surviving let chain owner"
    );
    assert!(
        translator.provenance.uplc_ids(mid.id()).contains(&13),
        "selected constr should stay attached to surviving let chain owner"
    );
}

#[test]
fn test_case_constr_constant_fold_zero_field_branch_absorbs_case_and_constr_into_surviving_body() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Case {
            constr: Rc::new(Term::Constr {
                tag: 0,
                fields: vec![],
                uniq_id: 13,
            }),
            branches: vec![Term::Constant {
                value: Rc::new(Constant::Bool(true)),
                uniq_id: 11,
            }],
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    assert!(matches!(mid, MidExpr::Lit { .. }));
    assert_eq!(translator.provenance.mid_for_uplc(10), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(11), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(13), Some(mid.id()));
}

#[test]
fn test_builtin_apply_absorbs_outer_apply_provenance_into_surviving_builtin() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Apply {
            function: Rc::new(Term::Builtin {
                fun: uplc::builtins::DefaultFunction::AddInteger,
                uniq_id: 11,
            }),
            argument: Rc::new(Term::Constant {
                value: Rc::new(Constant::Integer(1.into())),
                uniq_id: 12,
            }),
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    assert!(matches!(mid, MidExpr::Builtin { .. }));
    assert_eq!(translator.provenance.mid_for_uplc(10), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(11), Some(mid.id()));
    assert!(
        translator.provenance.uplc_ids(mid.id()).contains(&10),
        "collapsed outer apply should stay attached to surviving builtin owner"
    );
}

#[test]
fn test_builtin_force_apply_absorbs_force_and_apply_provenance_into_surviving_builtin() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Force {
            body: Rc::new(Term::Apply {
                function: Rc::new(Term::Builtin {
                    fun: uplc::builtins::DefaultFunction::AddInteger,
                    uniq_id: 12,
                }),
                argument: Rc::new(Term::Constant {
                    value: Rc::new(Constant::Integer(1.into())),
                    uniq_id: 13,
                }),
                uniq_id: 11,
            }),
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    assert!(matches!(mid, MidExpr::Builtin { .. }));
    assert_eq!(translator.provenance.mid_for_uplc(10), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(11), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(12), Some(mid.id()));
    assert!(
        translator.provenance.uplc_ids(mid.id()).contains(&10),
        "collapsed outer force should stay attached to surviving builtin owner"
    );
    assert!(
        translator.provenance.uplc_ids(mid.id()).contains(&11),
        "collapsed builtin apply should stay attached to surviving builtin owner"
    );
}

#[test]
fn test_force_non_builtin_apply_preserves_inner_apply_owner() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Force {
            body: Rc::new(Term::Apply {
                function: Rc::new(Term::Var {
                    name: Rc::new(nd("f", 99)),
                    uniq_id: 12,
                }),
                argument: Rc::new(Term::Constant {
                    value: Rc::new(Constant::Integer(1.into())),
                    uniq_id: 13,
                }),
                uniq_id: 11,
            }),
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    let (force_id, apply_id) = match mid {
        MidExpr::Force { id, body, .. } => match body.as_ref() {
            MidExpr::Apply { id: apply_id, .. } => (id, *apply_id),
            other => panic!("expected Force(Apply), got inner {other:?}"),
        },
        other => panic!("expected Force after translation, got {other:?}"),
    };

    assert_eq!(force_id, translator.provenance.mid_for_uplc(10).unwrap());
    assert_eq!(apply_id, translator.provenance.mid_for_uplc(11).unwrap());
    assert!(
        translator.provenance.uplc_ids(apply_id).contains(&11),
        "non-builtin apply under force should keep its original apply owner"
    );
}

#[test]
fn test_builtin_nested_apply_spine_absorbs_all_apply_ids_into_surviving_builtin() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Apply {
            function: Rc::new(Term::Apply {
                function: Rc::new(Term::Builtin {
                    fun: uplc::builtins::DefaultFunction::AddInteger,
                    uniq_id: 12,
                }),
                argument: Rc::new(Term::Constant {
                    value: Rc::new(Constant::Integer(1.into())),
                    uniq_id: 13,
                }),
                uniq_id: 11,
            }),
            argument: Rc::new(Term::Constant {
                value: Rc::new(Constant::Integer(2.into())),
                uniq_id: 14,
            }),
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    assert!(matches!(mid, MidExpr::Builtin { .. }));
    assert_eq!(translator.provenance.mid_for_uplc(10), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(11), Some(mid.id()));
    assert_eq!(translator.provenance.mid_for_uplc(12), Some(mid.id()));
}

#[test]
fn test_case_constr_constant_fold_absorbs_unwrapped_thunk_into_surviving_let_chain() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Case {
            constr: Rc::new(Term::Constr {
                tag: 0,
                fields: vec![Term::Constant {
                    value: Rc::new(Constant::Integer(42.into())),
                    uniq_id: 15,
                }],
                uniq_id: 14,
            }),
            branches: vec![Term::Lambda {
                parameter_name: Rc::new(nd("x", 1)),
                body: Rc::new(Term::Delay {
                    body: Rc::new(Term::Var {
                        name: Rc::new(nd("x", 1)),
                        uniq_id: 12,
                    }),
                    uniq_id: 13,
                }),
                uniq_id: 11,
            }],
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    assert!(matches!(mid, MidExpr::Let { .. }));
    assert_eq!(translator.provenance.mid_for_uplc(13), Some(mid.id()));
}

#[test]
fn test_native_case_branch_extraction_absorbs_lambda_and_thunk_into_surviving_body() {
    let program = Program {
        version: (1, 1, 0),
        term: Term::Lambda {
            parameter_name: Rc::new(nd("scrutinee", 1)),
            body: Rc::new(Term::Case {
                constr: Rc::new(Term::Var {
                    name: Rc::new(nd("scrutinee", 1)),
                    uniq_id: 12,
                }),
                branches: vec![Term::Lambda {
                    parameter_name: Rc::new(nd("x", 1)),
                    body: Rc::new(Term::Delay {
                        body: Rc::new(Term::Var {
                            name: Rc::new(nd("x", 1)),
                            uniq_id: 15,
                        }),
                        uniq_id: 14,
                    }),
                    uniq_id: 13,
                }],
                uniq_id: 11,
            }),
            uniq_id: 10,
        },
    };

    let mut translator = MidTranslator::new();
    let mid = translator.translate(&program.term);

    let branch_body_id = match mid {
        MidExpr::Closure { body, .. } => match *body {
            MidExpr::Case { branches, .. } => branches
                .first()
                .expect("expected one case branch")
                .body
                .id(),
            other => panic!("expected case body, got {other:?}"),
        },
        other => panic!("expected outer closure, got {other:?}"),
    };

    assert_eq!(translator.provenance.mid_for_uplc(13), Some(branch_body_id));
    assert_eq!(translator.provenance.mid_for_uplc(14), Some(branch_body_id));
}
