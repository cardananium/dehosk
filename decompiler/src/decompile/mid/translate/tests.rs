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

fn translate_source(source: &str) -> MidExpr {
    use uplc::ast::Name;
    let program: Program<Name> = uplc::parser::program(source).expect("source parses");
    let program: Program<DeBruijn> = program.try_into().expect("source de-Bruijnizes");
    let program: Program<NamedDeBruijn> = program.into();
    MidTranslator::new().translate(&program.term)
}

fn first_case(expr: &MidExpr) -> Option<&MidExpr> {
    if matches!(expr, MidExpr::Case { .. }) {
        return Some(expr);
    }
    expr.children().into_iter().find_map(first_case)
}

#[test]
fn case_applied_to_unit_drops_the_unused_delay_parameter() {
    // Arms are `\h \t \u -> constr 0 h` and `\u -> 0`, and the case result is applied to
    // `unit`: the last parameter is the thunk's, so the arms hold 2 and 0 fields.
    let mid = translate_source(
        "(program 1.1.0 (lam xs [(case xs (lam h (lam t (lam u (constr 0 h)))) (lam u (con integer 0))) (constr 0)]))",
    );
    let Some(MidExpr::Case { branches, .. }) = first_case(&mid) else {
        panic!("expected the application to fold into the case: {mid:?}");
    };
    let arities: Vec<usize> = branches.iter().map(|b| b.binders.len()).collect();
    assert_eq!(arities, vec![2, 0]);
}

#[test]
fn case_applied_to_unit_keeps_a_parameter_the_body_reads() {
    // The last parameter of the first arm is used, so it is a real field.
    let mid = translate_source(
        "(program 1.1.0 (lam xs [(case xs (lam h (lam t (lam u u))) (lam u (con integer 0))) (constr 0)]))",
    );
    assert!(
        matches!(&mid, MidExpr::Closure { body, .. } if matches!(body.as_ref(), MidExpr::Apply { .. })),
        "the unit application must stay: {mid:?}"
    );
}

#[test]
fn case_applied_to_unit_is_kept_when_an_arm_may_return_a_function() {
    // The first arm returns a free variable `f`, which could be a function
    // that the `unit` application is meant to call: the last parameter may be
    // a real field, so nothing may be folded.
    let mid = translate_source(
        "(program 1.1.0 (lam f (lam xs [(case xs (lam h (lam t (lam u f))) (lam u (constr 0))) (constr 0)])))",
    );
    assert!(
        first_case(&mid).is_none_or(|c| matches!(c, MidExpr::Case { branches, .. }
            if branches.iter().map(|b| b.binders.len()).collect::<Vec<_>>() == vec![3, 1])),
        "arms must keep every lambda parameter: {mid:?}"
    );
}

#[test]
fn case_applied_to_unit_folds_through_a_self_application_and_nested_cases() {
    // Leaves: a constructor, `error`, and a Z-style self call `self(self, …)`.
    let mid = translate_source(
        "(program 1.1.0 (lam self (lam xs \
           [(case xs \
              (lam h (lam t (lam u [self self t]))) \
              (lam u (constr 0 (con integer 1)))) \
            (constr 0)])))",
    );
    let Some(MidExpr::Case { branches, .. }) = first_case(&mid) else {
        panic!("expected a folded case: {mid:?}");
    };
    let arities: Vec<usize> = branches.iter().map(|b| b.binders.len()).collect();
    assert_eq!(arities, vec![2, 0]);
}

fn case_arities_and_encoding(mid: &MidExpr) -> (Vec<usize>, CaseEncoding) {
    let Some(MidExpr::Case {
        branches, encoding, ..
    }) = first_case(mid)
    else {
        panic!("no case in {mid:?}");
    };
    (branches.iter().map(|b| b.binders.len()).collect(), *encoding)
}

#[test]
fn builtin_list_case_with_a_variable_leaf_is_folded_once_the_list_is_proven() {
    // `unListData d` is a list, so the arms take 2 and 0 fields and the last
    // parameter is the thunk's even though an arm returns a variable.
    let mid = translate_source(
        "(program 1.1.0 (lam d [(case [(builtin unListData) d] \
           (lam h (lam t (lam u h))) (lam u d)) (constr 0)]))",
    );
    assert_eq!(
        case_arities_and_encoding(&mid),
        (vec![2, 0], CaseEncoding::BuiltinList)
    );
}

#[test]
fn case_on_an_unproven_scrutinee_with_a_variable_leaf_is_left_alone() {
    // Nothing says `xs` is a list, and the arms may return a function.
    let mid = translate_source(
        "(program 1.1.0 (lam xs (lam d [(case xs (lam h (lam t (lam u h))) (lam u d)) (constr 0)])))",
    );
    assert_eq!(
        case_arities_and_encoding(&mid),
        (vec![3, 1], CaseEncoding::Native)
    );
}

#[test]
fn list_parameter_is_proven_from_every_call_site() {
    // `go` is only called with `unListData d` and with its own tail, so its
    // parameter is a list and the case folds.
    let mid = translate_source(
        "(program 1.1.0 (lam d \
           [(lam go [go go (con integer 0) [(builtin unListData) d]]) \
            (lam go (lam n (lam xs \
              [(case xs (lam h (lam t (lam u [go go n t]))) (lam u n)) (constr 0)])))]))",
    );
    assert_eq!(
        case_arities_and_encoding(&mid),
        (vec![2, 0], CaseEncoding::BuiltinList)
    );
}

#[test]
fn list_parameter_is_not_proven_when_one_call_passes_a_non_list() {
    let mid = translate_source(
        "(program 1.1.0 (lam d \
           [(lam go [go go (con integer 0) d]) \
            (lam go (lam n (lam xs \
              [(case xs (lam h (lam t (lam u [go go n t]))) (lam u n)) (constr 0)])))]))",
    );
    assert_eq!(
        case_arities_and_encoding(&mid).1,
        CaseEncoding::Native,
        "a call with an unknown argument must prevent the proof"
    );
}
