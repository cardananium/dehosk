use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn test_apply_pair_projection_moves_selected_arg_and_preserves_ids() {
    let param_id = VarId::from_raw(9905);
    let selected = PseudoExpr::Lambda {
        params: vec![Binder::new("kept", param_id)],
        body: PBox::new(PseudoExpr::var_with_id("kept", param_id)),
    };
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Pair.first"),
            args: vec![].into(),
        }),
        args: vec![PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Pair.new"),
            args: vec![selected, PseudoExpr::var("dropped")].into(),
        }]
        .into(),
    };

    let simplified = simplify(expr);
    assert!(
        matches!(
            &simplified,
            PseudoExpr::Lambda { params, body }
                if matches!(params.as_slice(), [binder] if binder.as_str() == "kept" && binder.id == param_id)
                    && matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "kept" && *id == Some(param_id))
        ),
        "Pair.first(Pair.new(selected, dropped)) should move the selected subtree without changing ids, got: {simplified:?}"
    );
}

#[test]
fn test_data_constr_tag_inline() {
    // Data.Constr(2, []).tag → 2
    let data_constr = PseudoExpr::BuiltinCall {
        name: crate::BuiltinId::expect_known("Data.Constr"),
        args: vec![
            PseudoExpr::Int(2.into()),
            PseudoExpr::List {
                elements: vec![].into(),
                tail: None,
            },
        ]
        .into(),
    };
    let expr = PseudoExpr::field_access(data_constr, "tag".to_string());
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Int(ref n) if *n == 2.into()),
        "expected Int(2), got: {:?}",
        simplified
    );
}

#[test]
fn test_constr_fields_inline() {
    let expr = PseudoExpr::field_access(
        PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 2),
            vec![PseudoExpr::var("a"), PseudoExpr::var("b")],
        ),
        "fields".to_string(),
    );
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::List { .. }),
        "expected List, got: {:?}",
        simplified
    );
}

#[test]
fn test_constr_tag_inline() {
    let expr = PseudoExpr::field_access(
        PseudoExpr::constr(ConstructorShape::unknown_data(2, 0), vec![]),
        "tag".to_string(),
    );
    let simplified = simplify(expr);
    assert!(
        matches!(simplified, PseudoExpr::Int(ref n) if *n == 2.into()),
        "expected Int(2), got: {:?}",
        simplified
    );
}
