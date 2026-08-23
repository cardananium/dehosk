use super::*;
use crate::pseudo::ast::PBox;

#[test]
fn semantic_and_render_naming_leave_extractor_temp_to_nameless_owner_without_collateral_rename() {
    let outer_g_id = VarId::new(9301);
    let inner_g_id = VarId::new(9302);
    let datum_id = VarId::new(9303);

    let expr = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(outer_g_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var_with_id("datum", datum_id)].into(),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("g", outer_g_id),
                PseudoExpr::Let {
                    name: "g".to_string(),
                    id: Some(inner_g_id),
                    value: PBox::new(PseudoExpr::int(1)),
                    body: PBox::new(PseudoExpr::var_with_id("g", inner_g_id)),
                },
            ]
            .into(),
        )),
    };

    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&expr),
        "fixture must start with clean same-name let refs"
    );

    let semantic = semantic_improve_variable_names(expr.clone());
    let render = render_improve_variable_names(expr.clone());

    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&semantic),
        "semantic naming must preserve clean ref ids"
    );
    assert_same_name_extractor_split(semantic, outer_g_id, inner_g_id, "g");

    assert!(
        !crate::decompile::ref_retarget::refs_need_retarget_by_scope(&render),
        "render extractor rename must preserve clean ref ids"
    );
    assert_same_name_extractor_split(render, outer_g_id, inner_g_id, "g");

    let hints = collect_extractor_temp_display_name_hints(&expr);
    assert_eq!(
        hints.get(&outer_g_id).map(String::as_str),
        Some("datum_bytes")
    );

    fn assert_same_name_extractor_split(
        result: PseudoExpr,
        outer_g_id: VarId,
        inner_g_id: VarId,
        expected_outer_name: &str,
    ) {
        let PseudoExpr::Let { name, id, body, .. } = result else {
            panic!("expected outer let after improve_variable_names");
        };
        assert_eq!(name, expected_outer_name);
        assert_eq!(id, Some(outer_g_id));

        let PseudoExpr::Tuple(items) = body.as_ref() else {
            panic!("expected tuple body after improve_variable_names, got: {body:?}");
        };
        assert!(
            matches!(
                items.as_slice(),
                [
                    PseudoExpr::Var { name, id, .. },
                    PseudoExpr::Let {
                        name: inner_name,
                        id: Some(inner_id),
                        body: inner_body,
                        ..
                    },
                ] if name == expected_outer_name
                    && *id == Some(outer_g_id)
                    && inner_name == "g"
                    && *inner_id == inner_g_id
                    && matches!(
                        inner_body.as_ref(),
                        PseudoExpr::Var { name, id, .. }
                            if name == "g" && *id == Some(inner_g_id)
                    )
            ),
            "expected only the targeted same-name let to be renamed by id, got: {items:?}"
        );
    }
}
