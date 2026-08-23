use super::*;
use crate::decompile::{
    DecompileOptions, ref_retarget::refs_need_retarget_by_scope, render_decompiled_expr_with_spans,
    run_pipeline_with_artifacts,
};
use crate::pseudo::ast::{PseudoData, PseudoExpr, PseudoType};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::mid::expr::MidExpr;
use crate::pseudo::mid::expr_id::ProvenanceBuilder;
use crate::pseudo::var_id::VarInterner;
use std::collections::HashSet;
use std::rc::Rc;
use uplc::ast::{DeBruijn, FakeNamedDeBruijn, NamedDeBruijn, Program};
use uplc::builtins::DefaultFunction;

fn nd(text: &str, index: usize) -> NamedDeBruijn {
    NamedDeBruijn {
        text: text.to_string(),
        index: DeBruijn::new(index),
    }
}

struct LetNameCollector {
    names: Vec<String>,
}

impl ExprVisitor for LetNameCollector {
    fn visit_let(
        &mut self,
        name: &str,
        _id: &Option<crate::pseudo::var_id::VarId>,
        _value: &PseudoExpr,
        _body: &PseudoExpr,
    ) {
        self.names.push(name.to_string());
    }
}

fn let_names(expr: &PseudoExpr) -> Vec<String> {
    let mut collector = LetNameCollector { names: Vec::new() };
    collector.walk(expr);
    collector.names
}

fn has_duplicate_let_names(expr: &PseudoExpr) -> bool {
    let mut seen = HashSet::new();
    let_names(expr).into_iter().any(|name| !seen.insert(name))
}

#[test]
fn test_lower_identity() {
    let hex = "46010000200101";
    let bytes = hex::decode(hex).unwrap();
    let mut buf = Vec::new();
    let program: Program<FakeNamedDeBruijn> = Program::from_cbor(&bytes, &mut buf).unwrap();
    let program: Program<NamedDeBruijn> = program.into();

    let (pseudo, source_map, _var_reg) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");

    assert!(
        matches!(pseudo, PseudoExpr::Lambda { .. }),
        "Identity should lower to Lambda, got {:?}",
        pseudo
    );

    assert!(!source_map.var_names.is_empty(), "Should have var names");
}

#[test]
fn test_mir_lower_does_not_guarantee_unique_or_consistent_ref_ids_for_shadowed_let_names() {
    let mut interner = VarInterner::new();
    let mut provenance = ProvenanceBuilder::new();
    let first = interner.intern_fresh("x");
    let second = interner.intern_fresh("x");
    interner.rename(first, "x");
    interner.rename(second, "x");

    let mid = MidExpr::Let {
        id: provenance.fresh_id(),
        var: first,
        value: Box::new(MidExpr::Lit {
            id: provenance.fresh_id(),
            value: MidLiteral::Integer(1.into()),
        }),
        body: Box::new(MidExpr::Let {
            id: provenance.fresh_id(),
            var: second,
            value: Box::new(MidExpr::Lit {
                id: provenance.fresh_id(),
                value: MidLiteral::Integer(2.into()),
            }),
            body: Box::new(MidExpr::Builtin {
                id: provenance.fresh_id(),
                fun: DefaultFunction::AddInteger,
                forces: 0,
                args: vec![
                    MidExpr::Var {
                        id: provenance.fresh_id(),
                        var: second,
                    },
                    MidExpr::Var {
                        id: provenance.fresh_id(),
                        var: first,
                    },
                ],
                folded: None,
            }),
            use_count: 1,
        }),
        use_count: 1,
    };

    disambiguate_all_bindings(&mid, &mut interner);
    let mut lowerer = Lowerer::new(&interner, &provenance);
    let pseudo = lowerer.lower(&mid).expect("lowering should succeed");

    assert!(
        has_duplicate_let_names(&pseudo),
        "LowerMir does not disambiguate top-level duplicate let names"
    );
    assert!(
        refs_need_retarget_by_scope(&pseudo),
        "shadowed same-name lets can leave LowerMir output needing retarget"
    );
}

#[test]
fn test_lower_v3_smoke() {
    let hex = crate::decompile::tests::MIR_V3_SMOKE_HEX;

    let bytes = hex::decode(hex).unwrap();
    let mut buf = Vec::new();
    let program: Program<FakeNamedDeBruijn> = Program::from_cbor(&bytes, &mut buf).unwrap();
    let program: Program<NamedDeBruijn> = program.into();

    let (pseudo, source_map, _var_reg) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");

    let output = pseudo.to_pretty();
    assert!(
        output.len() > 50,
        "V3 smoke should produce substantial output, got {} chars",
        output.len()
    );

    println!(
        "MIR pipeline output ({} chars):\n{}",
        output.len(),
        &output[..output.len().min(2000)]
    );

    assert!(
        !source_map.mid_to_uplc.is_empty(),
        "Source map should have MidExpr → UPLC entries"
    );
}

#[test]
fn test_constant_fold_visible_in_output() {
    // Constant folding is exercised through test_lower_v3_smoke: an
    // add_integer(3, 5) in UPLC reaches the output as the literal 8.
}

#[test]
fn test_pipeline_populates_all_env_tables_on_v3_smoke() {
    // Sibling to test_mir_lower_populates_literal_types_in_type_env: same
    // hex, but asserts all three env tables get non-zero counts after
    // the full pipeline, not just MIR lowering in isolation — a post-MIR
    // pass must not reset the env, and a new writer must hit every table.
    let hex = crate::decompile::tests::MIR_V3_SMOKE_HEX;
    let bytes = hex::decode(hex).unwrap();
    let mut buf = Vec::new();
    let program: Program<FakeNamedDeBruijn> = Program::from_cbor(&bytes, &mut buf).unwrap();
    let program: Program<NamedDeBruijn> = program.into();

    let mut opts = DecompileOptions::default();
    opts.type_passes = crate::decompile::TypePasses::all_off();
    let pipeline_output =
        run_pipeline_with_artifacts(&program, opts, |_, _| {}).expect("pipeline should run");

    let env = pipeline_output.type_env;
    assert!(env.is_frozen());

    // expr_types: seeded by Lit writer + Builtin(folded+monomorphic) +
    // If/Case branch unification + Apply-result + Constr + Data + Trace.
    // Any non-trivial script has a non-zero count.
    assert!(env.expr_type_count() > 0, "expr_types should be populated");

    // var_types: seeded by Let binders whose values have a known
    // expr_type (currently Lit-valued let bindings). A real script
    // has many `let x: T = constant` which hit this path.
    assert!(
        env.var_type_count() > 0,
        "var_types should be populated by at least one Lit-valued Let"
    );

    // fn_signatures: emitted only if the body's type is already
    // recorded when the Let handler fires — true only for
    // literal/builtin/Data returns. This script reshapes enough in
    // pre-compute that zero signatures is legitimate, so the bound is
    // soft rather than an equality.
    assert!(
        env.signature_count() < env.var_type_count() * 100,
        "signature_count should be bounded by roughly the number of bindings"
    );
}

#[test]
fn test_mir_lower_populates_literal_types_in_type_env() {
    // Dual-write path end to end: the script hex has many literal
    // MIR nodes (integers, byte strings, constr payloads), so the
    // frozen TypeEnvironment must hold entries for some of them —
    // the exact count depends on pre-computation.
    let hex = crate::decompile::tests::MIR_V3_SMOKE_HEX;
    let bytes = hex::decode(hex).unwrap();
    let mut buf = Vec::new();
    let program: Program<FakeNamedDeBruijn> = Program::from_cbor(&bytes, &mut buf).unwrap();
    let program: Program<NamedDeBruijn> = program.into();

    let mut opts = DecompileOptions::default();
    opts.type_passes = crate::decompile::TypePasses::all_off();
    let pipeline_output =
        run_pipeline_with_artifacts(&program, opts, |_, _| {}).expect("pipeline should run");

    let env = pipeline_output.type_env;
    assert!(env.is_frozen(), "env must be frozen after MIR lowering");
    assert!(
        env.expr_type_count() > 0,
        "expected at least one literal type binding, got 0 expr_types in env"
    );
}

#[test]
fn test_literal_type_inference_tags_primitive_variants() {
    use crate::pseudo::ast::PseudoType;
    use crate::pseudo::mid::expr::MidLiteral;

    let integer_ty = Lowerer::literal_type(&MidLiteral::Integer(42.into()));
    assert!(matches!(integer_ty.as_ref(), PseudoType::Int));

    let bytes_ty = Lowerer::literal_type(&MidLiteral::ByteString(vec![1, 2, 3]));
    assert!(matches!(bytes_ty.as_ref(), PseudoType::ByteArray));

    let string_ty = Lowerer::literal_type(&MidLiteral::String("hi".to_string()));
    assert!(matches!(string_ty.as_ref(), PseudoType::String));

    let bool_ty = Lowerer::literal_type(&MidLiteral::Bool(true));
    assert!(matches!(bool_ty.as_ref(), PseudoType::Bool));

    let unit_ty = Lowerer::literal_type(&MidLiteral::Unit);
    assert!(matches!(unit_ty.as_ref(), PseudoType::Unit));

    // Compound: List carries the element type.
    let list_ty = Lowerer::literal_type(&MidLiteral::List(vec![MidLiteral::Integer(1.into())]));
    assert!(
        matches!(list_ty.as_ref(), PseudoType::List(elem) if matches!(elem.as_ref(), PseudoType::Int)),
        "expected List(Int) got {:?}",
        list_ty
    );

    // Compound: Pair carries both sides.
    let pair_ty = Lowerer::literal_type(&MidLiteral::Pair(
        Box::new(MidLiteral::Integer(1.into())),
        Box::new(MidLiteral::Bool(true)),
    ));
    assert!(
        matches!(pair_ty.as_ref(), PseudoType::Pair(a, b) if matches!(a.as_ref(), PseudoType::Int) && matches!(b.as_ref(), PseudoType::Bool)),
        "expected Pair(Int, Bool) got {:?}",
        pair_ty
    );
}

#[test]
fn test_literal_type_covers_data_and_bls_variants() {
    use crate::pseudo::ast::PseudoType;
    use crate::pseudo::mid::expr::MidLiteral;
    use uplc::PlutusData;

    let data_ty = Lowerer::literal_type(&MidLiteral::Data(Box::new(PlutusData::BoundedBytes(
        vec![1, 2, 3].into(),
    ))));
    assert!(matches!(data_ty.as_ref(), PseudoType::Data));

    // BLS elements stored as compressed bytes.
    let g1 = Lowerer::literal_type(&MidLiteral::Bls12_381G1(vec![0u8; 48]));
    assert!(matches!(g1.as_ref(), PseudoType::G1Element));

    let g2 = Lowerer::literal_type(&MidLiteral::Bls12_381G2(vec![0u8; 96]));
    assert!(matches!(g2.as_ref(), PseudoType::G2Element));
}

#[test]
fn test_mir_lower_propagates_let_binder_type_from_literal_value() {
    // `let x = 42 in x`: the literal's expr_type and the binder's
    // var_type must both land in the environment (Let dual-write path).
    //
    // The MidExpr is built directly so the test is not sensitive to
    // decode/recognition drift in the translator.
    use crate::pseudo::mid::expr::{MidExpr, MidLiteral};

    let mut provenance = ProvenanceBuilder::new();
    let let_id = provenance.fresh_id();
    let value_id = provenance.fresh_id();
    let body_id = provenance.fresh_id();
    provenance.link(let_id, 100);
    provenance.link(value_id, 101);
    provenance.link(body_id, 102);

    let mut interner = VarInterner::new();
    let x = interner.intern_fresh("x");

    let mid = MidExpr::Let {
        id: let_id,
        var: x,
        value: Box::new(MidExpr::Lit {
            id: value_id,
            value: MidLiteral::Integer(42.into()),
        }),
        body: Box::new(MidExpr::Var {
            id: body_id,
            var: x,
        }),
        use_count: 1,
    };

    let mut lowerer = Lowerer::new(&interner, &provenance);
    let _ = lowerer.lower(&mid).expect("lowering should succeed");
    let type_env = lowerer.type_env;

    assert!(
        matches!(
            type_env.type_of_expr(value_id).as_deref(),
            Some(PseudoType::Int)
        ),
        "literal Int value should register Int in expr_types"
    );
    assert!(
        matches!(type_env.type_of_var(x).as_deref(), Some(PseudoType::Int)),
        "let binder x should inherit Int from its literal value"
    );
    assert!(
        matches!(
            type_env.type_of_expr(body_id).as_deref(),
            Some(PseudoType::Int)
        ),
        "var reference to x should echo Int onto its own MidExprId"
    );
}

#[test]
fn test_mir_lower_emits_closure_signature_for_literal_returning_fn() {
    // `let id_like = fn(p) { 42 } in id_like` should record a
    // FnSignature for id_like with return_type = Int.
    use crate::pseudo::mid::expr::{MidExpr, MidLiteral};

    let mut provenance = ProvenanceBuilder::new();
    let let_id = provenance.fresh_id();
    let closure_id = provenance.fresh_id();
    let closure_body_id = provenance.fresh_id();
    let body_id = provenance.fresh_id();
    provenance.link(let_id, 200);
    provenance.link(closure_id, 201);
    provenance.link(closure_body_id, 202);
    provenance.link(body_id, 203);

    let mut interner = VarInterner::new();
    let id_fn = interner.intern_fresh("id_like");
    let p = interner.intern_fresh("p");

    let mid = MidExpr::Let {
        id: let_id,
        var: id_fn,
        value: Box::new(MidExpr::Closure {
            id: closure_id,
            params: vec![p],
            body: Box::new(MidExpr::Lit {
                id: closure_body_id,
                value: MidLiteral::Integer(42.into()),
            }),
            recursive: None,
        }),
        body: Box::new(MidExpr::Var {
            id: body_id,
            var: id_fn,
        }),
        use_count: 1,
    };

    let mut lowerer = Lowerer::new(&interner, &provenance);
    let _ = lowerer.lower(&mid).expect("lowering should succeed");
    let type_env = lowerer.type_env;

    let sig = type_env
        .signature_of(id_fn)
        .expect("Let-bound closure should have a FnSignature");
    assert_eq!(sig.arity(), 1, "signature should record 1 param");
    assert_eq!(sig.params[0].0, p, "param VarId should match");
    assert!(
        matches!(sig.return_type.as_ref(), PseudoType::Int),
        "closure returning literal 42 should have Int return type"
    );
    assert!(!sig.is_recursive, "non-recursive closure flag");
}

#[test]
fn test_mir_lower_closure_signature_chains_via_typed_apply_body() {
    // `let double = fn(n) { add_integer(n, n) } in double(3)`
    //
    // The body is a builtin Apply, not a literal, so the
    // arity-guarded monomorphic Builtin writer sets Int on
    // AddInteger; Closure-in-Let emission reads that body type
    // into FnSignature { return_type = Int }; and the saturated
    // outer Apply(double, 3) binds Int to its own MidExprId.
    use crate::pseudo::mid::expr::{MidExpr, MidLiteral};
    use uplc::builtins::DefaultFunction;

    let mut provenance = ProvenanceBuilder::new();
    let ids: Vec<MidExprId> = (0..9).map(|_| provenance.fresh_id()).collect();
    for (i, id) in ids.iter().enumerate() {
        provenance.link(*id, (900 + i) as isize);
    }

    let mut interner = VarInterner::new();
    let double = interner.intern_fresh("double");
    let n = interner.intern_fresh("n");

    let mid = MidExpr::Let {
        id: ids[0],
        var: double,
        value: Box::new(MidExpr::Closure {
            id: ids[1],
            params: vec![n],
            body: Box::new(MidExpr::Builtin {
                id: ids[2],
                fun: DefaultFunction::AddInteger,
                forces: 0,
                args: vec![
                    MidExpr::Var { id: ids[3], var: n },
                    MidExpr::Var { id: ids[4], var: n },
                ],
                folded: None,
            }),
            recursive: None,
        }),
        body: Box::new(MidExpr::Apply {
            id: ids[5],
            function: Box::new(MidExpr::Var {
                id: ids[6],
                var: double,
            }),
            args: vec![MidExpr::Lit {
                id: ids[7],
                value: MidLiteral::Integer(3.into()),
            }],
        }),
        use_count: 1,
    };

    let mut lowerer = Lowerer::new(&interner, &provenance);
    let _ = lowerer.lower(&mid).expect("lowering should succeed");
    let env = lowerer.type_env;

    assert!(
        matches!(env.type_of_expr(ids[2]).as_deref(), Some(PseudoType::Int)),
        "AddInteger should receive Int from monomorphic writer"
    );
    let sig = env
        .signature_of(double)
        .expect("double should have a FnSignature");
    assert!(matches!(sig.return_type.as_ref(), PseudoType::Int));
    // Outer Apply(double, 3) should inherit Int from the signature.
    assert!(matches!(
        env.type_of_expr(ids[5]).as_deref(),
        Some(PseudoType::Int)
    ));
}

#[test]
fn test_mir_lower_apply_result_type_from_signature() {
    // `let id_like = fn(p) { 42 } in id_like(0)` should record the
    // Apply node's result type as Int, read from id_like's FnSignature.
    use crate::pseudo::mid::expr::{MidExpr, MidLiteral};

    let mut provenance = ProvenanceBuilder::new();
    let let_id = provenance.fresh_id();
    let closure_id = provenance.fresh_id();
    let closure_body_id = provenance.fresh_id();
    let apply_id = provenance.fresh_id();
    let fn_ref_id = provenance.fresh_id();
    let arg_id = provenance.fresh_id();
    for (mid_id, uplc) in [
        (let_id, 300),
        (closure_id, 301),
        (closure_body_id, 302),
        (apply_id, 303),
        (fn_ref_id, 304),
        (arg_id, 305),
    ] {
        provenance.link(mid_id, uplc);
    }

    let mut interner = VarInterner::new();
    let id_fn = interner.intern_fresh("id_like");
    let p = interner.intern_fresh("p");

    let mid = MidExpr::Let {
        id: let_id,
        var: id_fn,
        value: Box::new(MidExpr::Closure {
            id: closure_id,
            params: vec![p],
            body: Box::new(MidExpr::Lit {
                id: closure_body_id,
                value: MidLiteral::Integer(42.into()),
            }),
            recursive: None,
        }),
        body: Box::new(MidExpr::Apply {
            id: apply_id,
            function: Box::new(MidExpr::Var {
                id: fn_ref_id,
                var: id_fn,
            }),
            args: vec![MidExpr::Lit {
                id: arg_id,
                value: MidLiteral::Integer(0.into()),
            }],
        }),
        use_count: 1,
    };

    let mut lowerer = Lowerer::new(&interner, &provenance);
    let _ = lowerer.lower(&mid).expect("lowering should succeed");
    let type_env = lowerer.type_env;

    assert!(
        matches!(
            type_env.type_of_expr(apply_id).as_deref(),
            Some(PseudoType::Int)
        ),
        "Apply of a FnSignature-bearing function should inherit the \
         signature's return_type; got {:?}",
        type_env.type_of_expr(apply_id)
    );
}

#[test]
fn test_mir_lower_polymorphic_builtin_head_list_from_list_arg() {
    // `let xs = [1, 2, 3] in head_list(xs)` — HeadList on a
    // List<Int> binds Int onto the call. A literal list source
    // makes the Lit writer seed expr_type = List<Int> on the
    // binding's value, which the Let handler propagates onto
    // `xs`.
    use crate::pseudo::mid::expr::{MidExpr, MidLiteral};
    use uplc::builtins::DefaultFunction;

    let mut provenance = ProvenanceBuilder::new();
    let ids: Vec<MidExprId> = (0..5).map(|_| provenance.fresh_id()).collect();
    for (i, id) in ids.iter().enumerate() {
        provenance.link(*id, (700 + i) as isize);
    }

    let mut interner = VarInterner::new();
    let xs = interner.intern_fresh("xs");

    let mid = MidExpr::Let {
        id: ids[0],
        var: xs,
        value: Box::new(MidExpr::Lit {
            id: ids[1],
            value: MidLiteral::List(vec![
                MidLiteral::Integer(1.into()),
                MidLiteral::Integer(2.into()),
                MidLiteral::Integer(3.into()),
            ]),
        }),
        body: Box::new(MidExpr::Builtin {
            id: ids[2],
            fun: DefaultFunction::HeadList,
            forces: 1,
            args: vec![MidExpr::Var {
                id: ids[3],
                var: xs,
            }],
            folded: None,
        }),
        use_count: 1,
    };

    let mut lowerer = Lowerer::new(&interner, &provenance);
    let _ = lowerer.lower(&mid).expect("lowering should succeed");
    let env = lowerer.type_env;

    assert!(
        matches!(
            env.type_of_expr(ids[1]).as_deref(),
            Some(PseudoType::List(elem)) if matches!(elem.as_ref(), PseudoType::Int)
        ),
        "List<Int> literal should have List(Int) expr_type"
    );
    // Int comes from the polymorphic-builtin derivation.
    assert!(
        matches!(env.type_of_expr(ids[2]).as_deref(), Some(PseudoType::Int)),
        "HeadList(List<Int>) should produce Int; got {:?}",
        env.type_of_expr(ids[2])
    );
}

#[test]
fn test_mir_lower_polymorphic_fst_pair_extracts_first_type() {
    // `let p = Pair(1, True) in fst_pair(p)` — FstPair on
    // Pair<Int, Bool> binds Int onto the call.
    use crate::pseudo::mid::expr::{MidExpr, MidLiteral};
    use uplc::builtins::DefaultFunction;

    let mut provenance = ProvenanceBuilder::new();
    let ids: Vec<MidExprId> = (0..4).map(|_| provenance.fresh_id()).collect();
    for (i, id) in ids.iter().enumerate() {
        provenance.link(*id, (800 + i) as isize);
    }

    let mut interner = VarInterner::new();
    let p = interner.intern_fresh("p");

    let mid = MidExpr::Let {
        id: ids[0],
        var: p,
        value: Box::new(MidExpr::Lit {
            id: ids[1],
            value: MidLiteral::Pair(
                Box::new(MidLiteral::Integer(1.into())),
                Box::new(MidLiteral::Bool(true)),
            ),
        }),
        body: Box::new(MidExpr::Builtin {
            id: ids[2],
            fun: DefaultFunction::FstPair,
            forces: 2,
            args: vec![MidExpr::Var { id: ids[3], var: p }],
            folded: None,
        }),
        use_count: 1,
    };

    let mut lowerer = Lowerer::new(&interner, &provenance);
    let _ = lowerer.lower(&mid).expect("lowering should succeed");
    let env = lowerer.type_env;

    assert!(
        matches!(env.type_of_expr(ids[2]).as_deref(), Some(PseudoType::Int)),
        "FstPair(Pair<Int, Bool>) should produce Int; got {:?}",
        env.type_of_expr(ids[2])
    );
}

#[test]
fn test_unify_branch_types_prefers_concrete_over_unknown() {
    use std::rc::Rc;
    let unknown: Option<Rc<PseudoType>> = Some(Rc::new(PseudoType::Unknown));
    let int_ty: Option<Rc<PseudoType>> = Some(Rc::new(PseudoType::Int));
    // Unknown first, Int second — should pick Int.
    let result = Lowerer::unify_branch_types(&[unknown.clone(), int_ty.clone()]);
    assert!(matches!(result.as_deref(), Some(PseudoType::Int)));
    // Int first, Unknown second — should still pick Int.
    let result = Lowerer::unify_branch_types(&[int_ty.clone(), unknown.clone()]);
    assert!(matches!(result.as_deref(), Some(PseudoType::Int)));
}

#[test]
fn test_unify_branch_types_rejects_concrete_disagreement() {
    use std::rc::Rc;
    let int_ty: Option<Rc<PseudoType>> = Some(Rc::new(PseudoType::Int));
    let bool_ty: Option<Rc<PseudoType>> = Some(Rc::new(PseudoType::Bool));
    // Two branches both typed with different concrete types — return
    // None rather than silently picking one.
    let result = Lowerer::unify_branch_types(&[int_ty, bool_ty]);
    assert!(result.is_none());
}

#[test]
fn test_unify_branch_types_none_when_all_missing() {
    let result: Option<std::rc::Rc<PseudoType>> = Lowerer::unify_branch_types(&[None, None, None]);
    assert!(result.is_none());
}

#[test]
fn test_literal_type_empty_list_is_unknown_elem() {
    use crate::pseudo::ast::PseudoType;
    use crate::pseudo::mid::expr::MidLiteral;

    // Empty list literals carry no element type at the MidLiteral
    // level, so inference falls back to Unknown; the translator drops
    // the UPLC list element type too (translate.rs ignores ProtoList's
    // type annotation).
    let list_ty = Lowerer::literal_type(&MidLiteral::List(vec![]));
    assert!(
        matches!(list_ty.as_ref(), PseudoType::List(elem) if matches!(elem.as_ref(), PseudoType::Unknown)),
        "expected List(Unknown) for empty list, got {:?}",
        list_ty
    );
}

#[test]
fn test_lower_builtin_keeps_data_constructor_and_destructor_distinct() {
    let constructor = lower_builtin(DefaultFunction::IData, vec![PseudoExpr::var("x")]).unwrap();
    let destructor = lower_builtin(DefaultFunction::UnIData, vec![PseudoExpr::var("x")]).unwrap();
    let bytes_constructor =
        lower_builtin(DefaultFunction::BData, vec![PseudoExpr::var("bytes")]).unwrap();
    let bytes_destructor =
        lower_builtin(DefaultFunction::UnBData, vec![PseudoExpr::var("bytes")]).unwrap();

    assert!(matches!(constructor, PseudoExpr::BuiltinCall { ref name, .. } if name == "Data.Int"));
    assert!(
        matches!(destructor, PseudoExpr::BuiltinCall { ref name, .. } if name == "Data.un_int")
    );
    assert!(
        matches!(bytes_constructor, PseudoExpr::BuiltinCall { ref name, .. } if name == "Data.ByteArray")
    );
    assert!(
        matches!(bytes_destructor, PseudoExpr::BuiltinCall { ref name, .. } if name == "Data.un_bytearray")
    );
}

#[test]
fn test_lower_builtin_normalizes_constr_data_to_constr() {
    let lowered = lower_builtin(
        DefaultFunction::ConstrData,
        vec![
            PseudoExpr::Int(2.into()),
            PseudoExpr::List {
                elements: vec![PseudoExpr::var("field_0")].into(),
                tail: None,
            },
        ],
    )
    .unwrap();

    match lowered {
        PseudoExpr::Constr { tag, fields, .. } => {
            assert_eq!(tag, 2);
            assert_eq!(fields.len(), 1);
        }
        other => panic!("expected normalized Constr, got: {:?}", other),
    }
}

#[test]
fn test_lowerer_reprojects_constr_data_initial_lineage_to_real_lowered_snapshot() {
    let mut interner = VarInterner::new();
    let field_x = interner.intern_fresh("field_x");
    let lambda_param = interner.intern_fresh("field_y");

    let mut provenance = ProvenanceBuilder::new();
    let root_id = provenance.fresh_id();
    let tag_id = provenance.fresh_id();
    let cons_1_id = provenance.fresh_id();
    let field_x_id = provenance.fresh_id();
    let cons_2_id = provenance.fresh_id();
    let lambda_id = provenance.fresh_id();
    let lambda_body_id = provenance.fresh_id();
    let nil_id = provenance.fresh_id();

    for (mid_id, uplc_id) in [
        (root_id, 10),
        (tag_id, 11),
        (cons_1_id, 12),
        (field_x_id, 13),
        (cons_2_id, 14),
        (lambda_id, 15),
        (lambda_body_id, 16),
        (nil_id, 17),
    ] {
        provenance.link(mid_id, uplc_id);
    }

    let mid = MidExpr::Builtin {
        id: root_id,
        fun: DefaultFunction::ConstrData,
        forces: 0,
        args: vec![
            MidExpr::Lit {
                id: tag_id,
                value: crate::pseudo::mid::expr::MidLiteral::Integer(0.into()),
            },
            MidExpr::Builtin {
                id: cons_1_id,
                fun: DefaultFunction::MkCons,
                forces: 0,
                args: vec![
                    MidExpr::Var {
                        id: field_x_id,
                        var: field_x,
                    },
                    MidExpr::Builtin {
                        id: cons_2_id,
                        fun: DefaultFunction::MkCons,
                        forces: 0,
                        args: vec![
                            MidExpr::Closure {
                                id: lambda_id,
                                params: vec![lambda_param],
                                body: Box::new(MidExpr::Var {
                                    id: lambda_body_id,
                                    var: lambda_param,
                                }),
                                recursive: None,
                            },
                            MidExpr::Lit {
                                id: nil_id,
                                value: crate::pseudo::mid::expr::MidLiteral::List(Vec::new()),
                            },
                        ],
                        folded: None,
                    },
                ],
                folded: None,
            },
        ],
        folded: None,
    };

    let mut lowerer = Lowerer::new(&interner, &provenance);
    let pseudo = lowerer.lower(&mid).expect("lowering should succeed");

    assert!(
        matches!(pseudo, PseudoExpr::Constr { .. }),
        "constr_data should normalize during lowering"
    );

    let projected_unions = crate::decompile::pseudo_lineage::trace_projected_mid_id_unions(
        &[crate::decompile::pseudo_lineage::snapshot_expr(&pseudo)],
        &lowerer.source_map.initial_pseudo_to_mid,
    );
    let expected_union = [
        root_id,
        tag_id,
        cons_1_id,
        field_x_id,
        cons_2_id,
        lambda_id,
        lambda_body_id,
        nil_id,
    ]
    .into_iter()
    .collect::<std::collections::BTreeSet<_>>();

    assert_eq!(projected_unions.len(), 1);
    assert_eq!(
        projected_unions[0], expected_union,
        "lowered constr_data snapshot should retain every originating mid id after local re-projection"
    );
}

#[test]
fn test_lowerer_registers_folded_builtin_arg_provenance_on_surviving_literal() {
    let interner = VarInterner::new();
    let mut provenance = ProvenanceBuilder::new();
    let root_id = provenance.fresh_id();
    let arg_a_id = provenance.fresh_id();
    let arg_b_id = provenance.fresh_id();

    for (mid_id, uplc_id) in [(root_id, 21), (arg_a_id, 22), (arg_b_id, 23)] {
        provenance.link(mid_id, uplc_id);
    }

    let mid = MidExpr::Builtin {
        id: root_id,
        fun: DefaultFunction::SubtractInteger,
        forces: 0,
        args: vec![
            MidExpr::Lit {
                id: arg_a_id,
                value: crate::pseudo::mid::expr::MidLiteral::Integer(5.into()),
            },
            MidExpr::Lit {
                id: arg_b_id,
                value: crate::pseudo::mid::expr::MidLiteral::Integer(3.into()),
            },
        ],
        folded: Some(crate::pseudo::mid::expr::MidLiteral::Integer(2.into())),
    };

    let mut lowerer = Lowerer::new(&interner, &provenance);
    let pseudo = lowerer.lower(&mid).expect("lowering should succeed");

    assert!(matches!(pseudo, PseudoExpr::Int(_)));
    for mid_id in [root_id, arg_a_id, arg_b_id] {
        assert!(
            lowerer.source_map.mid_to_uplc.contains_key(&mid_id),
            "folded builtin should still register skipped mid provenance for {mid_id:?}"
        );
    }

    let projected_unions = crate::decompile::pseudo_lineage::trace_projected_mid_id_unions(
        &[crate::decompile::pseudo_lineage::snapshot_expr(&pseudo)],
        &lowerer.source_map.initial_pseudo_to_mid,
    );
    let expected_union = [root_id, arg_a_id, arg_b_id]
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(projected_unions.len(), 1);
    assert_eq!(projected_unions[0], expected_union);
}

#[test]
fn test_lowerer_registers_resolved_force_body_provenance_on_surviving_root() {
    let mut interner = VarInterner::new();
    let body_var = interner.intern_fresh("body_var");
    let interner = interner;
    let mut provenance = ProvenanceBuilder::new();
    let force_id = provenance.fresh_id();
    let body_var_id = provenance.fresh_id();
    let resolved_id = provenance.fresh_id();

    for (mid_id, uplc_id) in [(force_id, 31), (body_var_id, 32), (resolved_id, 33)] {
        provenance.link(mid_id, uplc_id);
    }

    let mid = MidExpr::Force {
        id: force_id,
        body: Box::new(MidExpr::Var {
            id: body_var_id,
            var: body_var,
        }),
        resolved: Some(Box::new(MidExpr::Lit {
            id: resolved_id,
            value: crate::pseudo::mid::expr::MidLiteral::Bool(true),
        })),
    };

    let mut lowerer = Lowerer::new(&interner, &provenance);
    let pseudo = lowerer.lower(&mid).expect("lowering should succeed");

    assert!(matches!(pseudo, PseudoExpr::Bool(true)));
    for mid_id in [force_id, body_var_id, resolved_id] {
        assert!(
            lowerer.source_map.mid_to_uplc.contains_key(&mid_id),
            "resolved force should still register skipped mid provenance for {mid_id:?}"
        );
    }

    let projected_unions = crate::decompile::pseudo_lineage::trace_projected_mid_id_unions(
        &[crate::decompile::pseudo_lineage::snapshot_expr(&pseudo)],
        &lowerer.source_map.initial_pseudo_to_mid,
    );
    let expected_union = [force_id, body_var_id, resolved_id]
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(projected_unions.len(), 1);
    assert_eq!(projected_unions[0], expected_union);
}

#[test]
fn test_lower_builtin_maps_conway_bytestring_builtins() {
    // The Conway and bitwise-extension mappings wire every UPLC
    // `DefaultFunction` variant through `lower_builtin`; `AndByteString`
    // must lower to a BuiltinCall with the canonical name.
    let lowered = lower_builtin(
        DefaultFunction::AndByteString,
        vec![PseudoExpr::var("left"), PseudoExpr::var("right")],
    )
    .expect("AndByteString should now lower successfully");
    match lowered {
        PseudoExpr::BuiltinCall { name, .. } => {
            // `lower_builtin` passes the legacy `and_bytearray`
            // name; BuiltinId canonicalises it to "ByteArray.and"
            // via `name_str()`.
            assert_eq!(name.as_ref(), "ByteArray.and");
        }
        other => panic!("expected BuiltinCall, got: {other:?}"),
    }
}

#[test]
fn test_lower_convertible_data_literal_to_constr() {
    let lowered = normalize_lowered_data_expr(PseudoExpr::Data(Box::new(PseudoData::Constr(
        1,
        vec![PseudoData::Constr(0, vec![])],
    ))));

    match lowered {
        PseudoExpr::Constr { tag, fields, .. } => {
            assert_eq!(tag, 1);
            assert_eq!(fields.len(), 1);
            assert!(matches!(fields[0], PseudoExpr::Constr { tag: 0, .. }));
        }
        other => panic!("expected Constr, got: {:?}", other),
    }
}

#[test]
fn test_finalize_source_map_is_deterministic() {
    let hex = "46010000200101";
    let bytes = hex::decode(hex).unwrap();
    let mut buf = Vec::new();
    let program: Program<FakeNamedDeBruijn> = Program::from_cbor(&bytes, &mut buf).unwrap();
    let program: Program<NamedDeBruijn> = program.into();

    let (_, mut source_map_a, _) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");
    let (_, mut source_map_b, _) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");

    let source_code = "fn(v) {\n  v\n}";
    finalize_source_map(source_code, &mut source_map_a);
    finalize_source_map(source_code, &mut source_map_b);

    assert_eq!(source_map_a.mid_order, source_map_b.mid_order);
    assert_eq!(source_map_a.mid_to_source, source_map_b.mid_to_source);
    assert_eq!(source_map_a.uplc_to_source, source_map_b.uplc_to_source);
}

#[test]
fn test_finalize_source_map_from_rendered_spans_is_deterministic() {
    let hex = "46010000200101";
    let bytes = hex::decode(hex).unwrap();
    let mut buf = Vec::new();
    let program: Program<FakeNamedDeBruijn> = Program::from_cbor(&bytes, &mut buf).unwrap();
    let program: Program<NamedDeBruijn> = program.into();

    let (pseudo_a, mut source_map_a, _) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");
    let (pseudo_b, mut source_map_b, _) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");

    let (_, rendered_spans_a) = pseudo_a.to_pretty_with_spans();
    let (_, rendered_spans_b) = pseudo_b.to_pretty_with_spans();

    assert!(finalize_source_map_from_rendered_spans(
        &rendered_spans_a,
        &mut source_map_a
    ));
    assert!(finalize_source_map_from_rendered_spans(
        &rendered_spans_b,
        &mut source_map_b
    ));

    assert_eq!(source_map_a.mid_order, source_map_b.mid_order);
    assert_eq!(source_map_a.mid_to_source, source_map_b.mid_to_source);
    assert_eq!(source_map_a.uplc_to_source, source_map_b.uplc_to_source);
    assert!(
        !source_map_a.uplc_to_source.is_empty(),
        "rendered spans should populate uplc source locations"
    );
}

#[test]
fn test_finalize_source_map_from_rendered_spans_prefers_projected_pseudo_lineage() {
    use crate::pseudo::mid::expr_id::{MidExprId, SourceSpan};

    let mid_a = MidExprId::new(1);
    let mid_b = MidExprId::new(2);
    let pseudo_a = 0xabc_u64;
    let pseudo_b = 0xdef_u64;
    let span_a = SourceSpan {
        start_line: 1,
        start_col: 1,
        end_line: 1,
        end_col: 5,
    };
    let span_b = SourceSpan {
        start_line: 2,
        start_col: 1,
        end_line: 2,
        end_col: 8,
    };

    let mut source_map = SourceMap::new();
    source_map.register_mid(mid_a, &[11]);
    source_map.register_mid(mid_b, &[22]);
    source_map.set_final_pseudo_to_mid(std::collections::HashMap::from([
        (pseudo_a, vec![mid_b]),
        (pseudo_b, vec![mid_a]),
    ]));

    assert!(finalize_source_map_from_rendered_spans(
        &[(pseudo_a, span_a), (pseudo_b, span_b)],
        &mut source_map,
    ));

    assert_eq!(source_map.mid_to_source.get(&mid_a), Some(&span_b));
    assert_eq!(source_map.mid_to_source.get(&mid_b), Some(&span_a));
    assert_eq!(source_map.uplc_to_source.get(&11), Some(&span_b));
    assert_eq!(source_map.uplc_to_source.get(&22), Some(&span_a));
}

#[test]
fn test_finalize_source_map_for_program_from_rendered_spans_saturates_original_uplc_tree() {
    fn collect_term_ids(term: &uplc::ast::Term<uplc::ast::NamedDeBruijn>, ids: &mut Vec<isize>) {
        fn term_id(term: &uplc::ast::Term<uplc::ast::NamedDeBruijn>) -> isize {
            match term {
                uplc::ast::Term::Var { uniq_id, .. }
                | uplc::ast::Term::Delay { uniq_id, .. }
                | uplc::ast::Term::Lambda { uniq_id, .. }
                | uplc::ast::Term::Apply { uniq_id, .. }
                | uplc::ast::Term::Constant { uniq_id, .. }
                | uplc::ast::Term::Force { uniq_id, .. }
                | uplc::ast::Term::Error { uniq_id }
                | uplc::ast::Term::Builtin { uniq_id, .. }
                | uplc::ast::Term::Constr { uniq_id, .. }
                | uplc::ast::Term::Case { uniq_id, .. } => *uniq_id,
            }
        }

        ids.push(term_id(term));
        match term {
            uplc::ast::Term::Delay { body, .. }
            | uplc::ast::Term::Lambda { body, .. }
            | uplc::ast::Term::Force { body, .. } => collect_term_ids(body, ids),
            uplc::ast::Term::Apply {
                function, argument, ..
            } => {
                collect_term_ids(function, ids);
                collect_term_ids(argument, ids);
            }
            uplc::ast::Term::Constr { fields, .. } => {
                for field in fields {
                    collect_term_ids(field, ids);
                }
            }
            uplc::ast::Term::Case {
                constr, branches, ..
            } => {
                collect_term_ids(constr, ids);
                for branch in branches {
                    collect_term_ids(branch, ids);
                }
            }
            uplc::ast::Term::Var { .. }
            | uplc::ast::Term::Constant { .. }
            | uplc::ast::Term::Builtin { .. }
            | uplc::ast::Term::Error { .. } => {}
        }
    }

    let hex = "46010000200101";
    let bytes = hex::decode(hex).unwrap();
    let mut buf = Vec::new();
    let program: Program<FakeNamedDeBruijn> = Program::from_cbor(&bytes, &mut buf).unwrap();
    let program: Program<NamedDeBruijn> = program.into();

    let (pseudo, mut source_map, _) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");
    let (_, rendered_spans) = pseudo.to_pretty_with_spans();

    assert!(finalize_source_map_for_program_from_rendered_spans(
        &rendered_spans,
        &mut source_map,
        &program.term
    ));

    let mut term_ids = Vec::new();
    collect_term_ids(&program.term, &mut term_ids);
    for term_id in term_ids {
        assert!(
            source_map.source_for_uplc(term_id).is_some(),
            "expected direct mapping for original term id {term_id}"
        );
    }
}

#[test]
fn test_exact_rendered_lineage_covers_collapsed_nested_lambda_without_extra_saturation() {
    let program = Program {
        version: (1, 1, 0),
        term: uplc::ast::Term::Lambda {
            parameter_name: Rc::new(nd("x", 1)),
            body: Rc::new(uplc::ast::Term::Lambda {
                parameter_name: Rc::new(nd("y", 1)),
                body: Rc::new(uplc::ast::Term::Var {
                    name: Rc::new(nd("x", 2)),
                    uniq_id: 12,
                }),
                uniq_id: 11,
            }),
            uniq_id: 10,
        },
    };

    let (pseudo, mut source_map, _) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");
    let (_, rendered_spans) = pseudo.to_pretty_with_spans();

    assert!(finalize_source_map_from_rendered_spans(
        &rendered_spans,
        &mut source_map
    ));
    let inserted = source_map.saturate_uplc_term_spans(&program.term);

    assert_eq!(
        inserted, 0,
        "collapsed nested lambdas should already be covered by exact retained provenance"
    );
    for term_id in [10, 11, 12] {
        assert!(
            source_map.source_for_uplc(term_id).is_some(),
            "expected direct mapping for collapsed nested lambda term id {term_id}"
        );
    }
}

#[test]
fn test_exact_rendered_lineage_covers_constant_folded_case_branch_without_extra_saturation() {
    let program = Program {
        version: (1, 1, 0),
        term: uplc::ast::Term::Case {
            constr: Rc::new(uplc::ast::Term::Constr {
                tag: 0,
                fields: vec![uplc::ast::Term::Constant {
                    value: Rc::new(uplc::ast::Constant::Integer(42.into())),
                    uniq_id: 14,
                }],
                uniq_id: 13,
            }),
            branches: vec![uplc::ast::Term::Lambda {
                parameter_name: Rc::new(nd("x", 1)),
                body: Rc::new(uplc::ast::Term::Var {
                    name: Rc::new(nd("x", 1)),
                    uniq_id: 12,
                }),
                uniq_id: 11,
            }],
            uniq_id: 10,
        },
    };

    let mut opts = DecompileOptions::default();
    opts.type_passes = crate::decompile::TypePasses::all_off();
    let pipeline_output =
        run_pipeline_with_artifacts(&program, opts, |_, _| {}).expect("pipeline should run");
    let mut source_map = pipeline_output
        .mir_source_map
        .expect("pipeline should expose mir source map");
    let (_, rendered_spans) = render_decompiled_expr_with_spans(&pipeline_output.expr, false);

    assert!(finalize_source_map_for_program_from_rendered_spans(
        &rendered_spans,
        &mut source_map,
        &program.term
    ));
    for term_id in [10, 11, 12, 13, 14] {
        assert!(
            source_map.source_for_uplc(term_id).is_some(),
            "expected direct mapping for constant-folded case term id {term_id}"
        );
    }
}

#[test]
fn test_exact_rendered_lineage_covers_collapsed_builtin_force_apply_without_extra_saturation() {
    let program = Program {
        version: (1, 1, 0),
        term: uplc::ast::Term::Force {
            body: Rc::new(uplc::ast::Term::Apply {
                function: Rc::new(uplc::ast::Term::Builtin {
                    fun: DefaultFunction::AddInteger,
                    uniq_id: 12,
                }),
                argument: Rc::new(uplc::ast::Term::Constant {
                    value: Rc::new(uplc::ast::Constant::Integer(1.into())),
                    uniq_id: 13,
                }),
                uniq_id: 11,
            }),
            uniq_id: 10,
        },
    };

    let (pseudo, mut source_map, _) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");
    let (_, rendered_spans) = pseudo.to_pretty_with_spans();

    assert!(finalize_source_map_from_rendered_spans(
        &rendered_spans,
        &mut source_map
    ));
    let inserted = source_map.saturate_uplc_term_spans(&program.term);

    assert_eq!(
        inserted, 0,
        "collapsed builtin force/apply should already be covered by exact retained provenance"
    );
    for term_id in [10, 11, 12, 13] {
        assert!(
            source_map.source_for_uplc(term_id).is_some(),
            "expected direct mapping for collapsed builtin force/apply term id {term_id}"
        );
    }
}

#[test]
fn test_exact_rendered_lineage_covers_zero_field_constant_folded_case_without_extra_saturation() {
    let program = Program {
        version: (1, 1, 0),
        term: uplc::ast::Term::Case {
            constr: Rc::new(uplc::ast::Term::Constr {
                tag: 0,
                fields: vec![],
                uniq_id: 13,
            }),
            branches: vec![uplc::ast::Term::Constant {
                value: Rc::new(uplc::ast::Constant::Bool(true)),
                uniq_id: 11,
            }],
            uniq_id: 10,
        },
    };

    let (pseudo, mut source_map, _) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");
    let (_, rendered_spans) = pseudo.to_pretty_with_spans();

    assert!(finalize_source_map_from_rendered_spans(
        &rendered_spans,
        &mut source_map
    ));
    let inserted = source_map.saturate_uplc_term_spans(&program.term);

    assert_eq!(
        inserted, 0,
        "zero-field constant-folded case should already be covered by exact retained provenance"
    );
    for term_id in [10, 11, 13] {
        assert!(
            source_map.source_for_uplc(term_id).is_some(),
            "expected direct mapping for zero-field constant-folded case term id {term_id}"
        );
    }
}

#[test]
fn test_exact_rendered_lineage_covers_extracted_case_branch_lambda_without_extra_saturation() {
    let program = Program {
        version: (1, 1, 0),
        term: uplc::ast::Term::Lambda {
            parameter_name: Rc::new(nd("scrutinee", 1)),
            body: Rc::new(uplc::ast::Term::Case {
                constr: Rc::new(uplc::ast::Term::Var {
                    name: Rc::new(nd("scrutinee", 1)),
                    uniq_id: 12,
                }),
                branches: vec![uplc::ast::Term::Lambda {
                    parameter_name: Rc::new(nd("x", 1)),
                    body: Rc::new(uplc::ast::Term::Delay {
                        body: Rc::new(uplc::ast::Term::Var {
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

    let (pseudo, mut source_map, _) =
        decompile_via_mir(&program, None).expect("mir lowering should succeed");
    let (_, rendered_spans) = pseudo.to_pretty_with_spans();

    assert!(finalize_source_map_from_rendered_spans(
        &rendered_spans,
        &mut source_map
    ));
    let inserted = source_map.saturate_uplc_term_spans(&program.term);

    assert_eq!(
        inserted, 0,
        "extracted case-branch lambda/thunk should already be covered by exact retained provenance"
    );
    for term_id in [10, 11, 12, 13, 14, 15] {
        assert!(
            source_map.source_for_uplc(term_id).is_some(),
            "expected direct mapping for extracted case-branch term id {term_id}"
        );
    }
}

#[test]
fn test_exact_rendered_lineage_covers_nested_builtin_apply_spine_without_extra_saturation() {
    let program = Program {
        version: (1, 1, 0),
        term: uplc::ast::Term::Apply {
            function: Rc::new(uplc::ast::Term::Apply {
                function: Rc::new(uplc::ast::Term::Builtin {
                    fun: DefaultFunction::AddInteger,
                    uniq_id: 12,
                }),
                argument: Rc::new(uplc::ast::Term::Constant {
                    value: Rc::new(uplc::ast::Constant::Integer(1.into())),
                    uniq_id: 13,
                }),
                uniq_id: 11,
            }),
            argument: Rc::new(uplc::ast::Term::Constant {
                value: Rc::new(uplc::ast::Constant::Integer(2.into())),
                uniq_id: 14,
            }),
            uniq_id: 10,
        },
    };

    let mut opts = DecompileOptions::default();
    opts.type_passes = crate::decompile::TypePasses::all_off();
    let pipeline_output =
        run_pipeline_with_artifacts(&program, opts, |_, _| {}).expect("pipeline should run");
    let mut source_map = pipeline_output
        .mir_source_map
        .expect("pipeline should expose mir source map");
    let (_, rendered_spans) = render_decompiled_expr_with_spans(&pipeline_output.expr, false);

    assert!(finalize_source_map_for_program_from_rendered_spans(
        &rendered_spans,
        &mut source_map,
        &program.term
    ));
    for term_id in [10, 11, 12, 13, 14] {
        assert!(
            source_map.source_for_uplc(term_id).is_some(),
            "expected direct mapping for nested builtin apply term id {term_id}"
        );
    }
}

#[test]
fn test_exact_rendered_lineage_covers_constant_folded_case_unwrapped_thunk_without_extra_saturation()
 {
    let program = Program {
        version: (1, 1, 0),
        term: uplc::ast::Term::Case {
            constr: Rc::new(uplc::ast::Term::Constr {
                tag: 0,
                fields: vec![uplc::ast::Term::Constant {
                    value: Rc::new(uplc::ast::Constant::Integer(42.into())),
                    uniq_id: 15,
                }],
                uniq_id: 14,
            }),
            branches: vec![uplc::ast::Term::Lambda {
                parameter_name: Rc::new(nd("x", 1)),
                body: Rc::new(uplc::ast::Term::Delay {
                    body: Rc::new(uplc::ast::Term::Var {
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

    let mut opts = DecompileOptions::default();
    opts.type_passes = crate::decompile::TypePasses::all_off();
    let pipeline_output =
        run_pipeline_with_artifacts(&program, opts, |_, _| {}).expect("pipeline should run");
    let mut source_map = pipeline_output
        .mir_source_map
        .expect("pipeline should expose mir source map");
    let (_, rendered_spans) = render_decompiled_expr_with_spans(&pipeline_output.expr, false);

    assert!(finalize_source_map_for_program_from_rendered_spans(
        &rendered_spans,
        &mut source_map,
        &program.term
    ));
    for term_id in [10, 11, 12, 13, 14, 15] {
        assert!(
            source_map.source_for_uplc(term_id).is_some(),
            "expected direct mapping for constant-folded case thunk term id {term_id}"
        );
    }
}

#[test]
fn test_lowerer_collects_simplify_hints_without_pseudo_rescan() {
    let mut interner = VarInterner::new();
    let head_alias = interner.intern_fresh("head_alias");
    let unpack_alias = interner.intern_fresh("unpack_alias");
    let data_var = interner.intern_fresh("data");
    let data_var_name = interner.resolve(data_var).to_string();

    let mut provenance = ProvenanceBuilder::new();
    let let_outer = provenance.fresh_id();
    let let_inner = provenance.fresh_id();
    let head_builtin = provenance.fresh_id();
    let unpack_builtin = provenance.fresh_id();
    let data_ref = provenance.fresh_id();
    let body_ref = provenance.fresh_id();

    provenance.link(let_outer, 1);
    provenance.link(let_inner, 2);
    provenance.link(head_builtin, 3);
    provenance.link(unpack_builtin, 4);
    provenance.link(data_ref, 5);
    provenance.link(body_ref, 6);

    let expr = MidExpr::Let {
        id: let_outer,
        var: head_alias,
        value: Box::new(MidExpr::Builtin {
            id: head_builtin,
            fun: DefaultFunction::HeadList,
            forces: 0,
            args: vec![],
            folded: None,
        }),
        body: Box::new(MidExpr::Let {
            id: let_inner,
            var: unpack_alias,
            value: Box::new(MidExpr::Builtin {
                id: unpack_builtin,
                fun: DefaultFunction::UnConstrData,
                forces: 0,
                args: vec![MidExpr::Var {
                    id: data_ref,
                    var: data_var,
                }],
                folded: None,
            }),
            body: Box::new(MidExpr::Var {
                id: body_ref,
                var: unpack_alias,
            }),
            use_count: 1,
        }),
        use_count: 0,
    };

    let mut lowerer = Lowerer::new(&interner, &provenance);
    let _ = lowerer
        .lower(&expr)
        .expect("lowering should seed simplify state");

    assert_eq!(
        lowerer
            .simplify_state
            .naming
            .builtin_aliases
            .get(head_alias),
        Some(&crate::BuiltinId::ListHead)
    );
    assert!(matches!(
        lowerer
            .simplify_state
            .constructors
            .constr_unpack_subjects
            .get(unpack_alias),
        Some(PseudoExpr::Var { name, .. }) if name == &data_var_name
    ));
}
