use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_simplify_state_seeds_constr_unpack_subjects_without_harvest() {
    let unpack_id = VarId::from_raw(29115);
    let subject_id = VarId::from_raw(29116);
    let mut state = SimplifyState::default();
    state
        .constructors
        .constr_unpack_subjects
        .insert(unpack_id, PseudoExpr::var_with_id("datum", subject_id));

    let rewritten = simplify_with_state(
        PseudoExpr::BuiltinCall {
            name: BuiltinId::PairFirst,
            args: vec![PseudoExpr::var_with_id("unpacked", unpack_id)].into(),
        },
        None,
        false,
        None,
        &mut state,
    )
    .expr;

    assert!(
        matches!(
            &rewritten,
            PseudoExpr::FieldAccess { record, selector }
                if selector.as_pretty_name() == "tag"
                    && matches!(record.as_ref(), PseudoExpr::Var { name, id } if name == "datum" && *id == Some(subject_id))
        ),
        "manual constructor seed should rewrite Pair.first(unpacked) to datum.tag, got: {rewritten:?}"
    );
    assert!(
        state
            .constructors
            .constr_unpack_subjects
            .get(unpack_id)
            .is_some(),
        "seed-only constructor metadata should stay available after the pass"
    );
}

#[test]
fn test_simplify_state_does_not_harvest_discovered_constr_unpack_subjects() {
    let unpack_id = VarId::from_raw(29117);
    let subject_id = VarId::from_raw(29118);
    let mut state = SimplifyState::default();
    let _ = simplify_with_state(
        PseudoExpr::Let {
            name: "unpacked".to_string(),
            id: Some(unpack_id),
            value: PBox::new(PseudoExpr::BuiltinCall {
                name: BuiltinId::DataUnConstr,
                args: vec![PseudoExpr::var_with_id("datum", subject_id)].into(),
            }),
            body: PBox::new(PseudoExpr::Unit),
        },
        None,
        false,
        None,
        &mut state,
    );

    assert!(
        state
            .constructors
            .constr_unpack_subjects
            .get(unpack_id)
            .is_none(),
        "constructor unpack subjects discovered inside a pass must not be harvested into persistent state"
    );
}

#[test]
fn test_simplify_state_carries_next_synthetic_var_id_between_passes() {
    fn partial_comparison_param_id(expr: PseudoExpr) -> VarId {
        let PseudoExpr::Lambda { params, .. } = expr else {
            panic!("expected partial comparison to produce lambda");
        };
        let [param] = params.as_slice() else {
            panic!("expected one partial-comparison param, got: {params:?}");
        };
        param.id
    }

    let mut state = SimplifyState::default();
    let high_input_id = VarId::from_raw(29140);
    let first = simplify_with_state(
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::BuiltinCall {
                name: BuiltinId::IntEq,
                args: vec![].into(),
            }),
            args: vec![PseudoExpr::var_with_id("target", high_input_id)].into(),
        },
        None,
        false,
        None,
        &mut state,
    )
    .expr;
    let first_param_id = partial_comparison_param_id(first);
    assert!(
        first_param_id.as_u32() > high_input_id.as_u32(),
        "first synthetic id should start beyond the input high-water mark"
    );

    let second = simplify_with_state(
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::BuiltinCall {
                name: BuiltinId::IntEq,
                args: vec![].into(),
            }),
            args: vec![PseudoExpr::Int(0.into())].into(),
        },
        None,
        false,
        None,
        &mut state,
    )
    .expr;
    let second_param_id = partial_comparison_param_id(second);
    assert!(
        second_param_id.as_u32() > first_param_id.as_u32(),
        "second pass should seed from the carried synthetic counter instead of reusing ids"
    );
    assert!(
        state.identity.next_synthetic_var_id > second_param_id.as_u32(),
        "state should harvest the advanced synthetic counter"
    );
}

#[test]
fn test_simplify_state_carries_kind_annotations_between_passes() {
    let preserved_id = VarId::from_raw(29150);
    let fn_id = VarId::from_raw(29151);
    let arg_id = VarId::from_raw(29152);
    let tmp_id = VarId::from_raw(29153);
    let mut state = SimplifyState::default();
    state.var_kinds.kind_annotations.insert(
        preserved_id,
        crate::pseudo::nameless::VarKind::DataLiteralHoist,
    );

    let _ = simplify_with_state(
        PseudoExpr::Let {
            name: "tmp_21".to_string(),
            id: tmp_id.into(),
            value: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("fn_3", fn_id)),
                args: vec![PseudoExpr::var_with_id("arg", arg_id)].into(),
            }),
            body: PBox::new(PseudoExpr::BinOp {
                op: BinaryOp::Add,
                left: PBox::new(PseudoExpr::var_with_id("tmp_21", tmp_id)),
                right: PBox::new(PseudoExpr::var_with_id("tmp_21", tmp_id)),
            }),
        },
        None,
        false,
        None,
        &mut state,
    );

    assert!(
        matches!(
            state.var_kinds.kind_annotations.get(&tmp_id),
            Some(crate::pseudo::nameless::VarKind::CallResult { callee }) if *callee == fn_id
        ),
        "first pass should harvest CallResult annotation, got: {:?}",
        state.var_kinds.kind_annotations.get(&tmp_id)
    );
    assert!(
        matches!(
            state.var_kinds.kind_annotations.get(&preserved_id),
            Some(crate::pseudo::nameless::VarKind::DataLiteralHoist)
        ),
        "first pass should preserve pre-seeded VarKind annotation"
    );

    let _ = simplify_with_state(PseudoExpr::Unit, None, false, None, &mut state);
    assert!(
        matches!(
            state.var_kinds.kind_annotations.get(&tmp_id),
            Some(crate::pseudo::nameless::VarKind::CallResult { callee }) if *callee == fn_id
        ),
        "second pass should seed and re-harvest harvested VarKind annotation"
    );
    assert!(
        matches!(
            state.var_kinds.kind_annotations.get(&preserved_id),
            Some(crate::pseudo::nameless::VarKind::DataLiteralHoist)
        ),
        "second pass should seed and re-harvest pre-seeded VarKind annotation"
    );
}
