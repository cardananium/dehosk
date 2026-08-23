use super::*;
use crate::pseudo::ast::PBox;

fn binder(name: &str, id: u32) -> Binder {
    Binder::new(name, VarId::new(id))
}

fn helper_rec(name: &str, id: u32, param_name: &str, param_id: u32) -> PseudoExpr {
    let param = binder(param_name, param_id);
    PseudoExpr::RecFn {
        name: binder(name, id),
        params: vec![param.clone()],
        body: PBox::new(PseudoExpr::var_with_id(param.name.clone(), param.id)),
    }
}

#[test]
fn prepare_root_render_layout_extracts_leading_helper_chain_before_lambda() {
    let helper_id = VarId::new(10);
    let param = binder("arg", 11);
    let expr = PseudoExpr::Let {
        name: "decode".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_rec("decode", 10, "items", 12)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![param.clone()],
            body: PBox::new(PseudoExpr::var_with_id(param.name.clone(), param.id)),
        }),
    };

    match prepare_root_render_layout(&expr) {
        RootRenderLayout::LambdaWithHelpers(layout) => {
            assert_eq!(layout.helpers.len(), 1);
            assert_eq!(layout.params, [param]);
            assert!(matches!(layout.helpers[0], RootHelper::RecFn { .. }));
            assert!(matches!(layout.body, PseudoExpr::Var { .. }));
        }
        _ => panic!("expected leading helper to be extracted"),
    }
}

#[test]
fn prepare_root_render_layout_extracts_helper_from_lambda_body_prefix() {
    let param = binder("input", 20);
    let expr = PseudoExpr::Lambda {
        params: vec![param.clone()],
        body: PBox::new(PseudoExpr::Let {
            name: "lookup".to_string(),
            id: Some(VarId::new(21)),
            value: PBox::new(helper_rec("lookup", 21, "pairs", 22)),
            body: PBox::new(PseudoExpr::var_with_id(param.name.clone(), param.id)),
        }),
    };

    match prepare_root_render_layout(&expr) {
        RootRenderLayout::LambdaWithHelpers(layout) => {
            assert_eq!(layout.helpers.len(), 1);
            assert!(matches!(layout.helpers[0], RootHelper::RecFn { .. }));
            assert!(matches!(layout.body, PseudoExpr::Var { .. }));
        }
        _ => panic!("expected lambda-body helper to be extracted"),
    }
}

#[test]
fn prepare_root_render_layout_keeps_control_subject_helper_in_place() {
    let helper_id = VarId::new(30);
    let expr = PseudoExpr::Let {
        name: "cond".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![],
            body: PBox::new(PseudoExpr::bool(true)),
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("arg", 31)],
            body: PBox::new(PseudoExpr::If {
                condition: PBox::new(PseudoExpr::var_with_id("cond", helper_id)),
                then_branch: PBox::new(PseudoExpr::int(1)),
                else_branch: PBox::new(PseudoExpr::int(0)),
            }),
        }),
    };

    assert!(matches!(
        prepare_root_render_layout(&expr),
        RootRenderLayout::Plain(_)
    ));
}

#[test]
fn prepare_root_render_layout_stops_at_non_helper_barrier() {
    let expr = PseudoExpr::Let {
        name: "value".to_string(),
        id: Some(VarId::new(40)),
        value: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id("compute", VarId::new(99))),
            args: vec![].into(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "decode".to_string(),
            id: Some(VarId::new(41)),
            value: PBox::new(helper_rec("decode", 41, "items", 42)),
            body: PBox::new(PseudoExpr::Lambda {
                params: vec![binder("arg", 43)],
                body: PBox::new(PseudoExpr::int(0)),
            }),
        }),
    };

    assert!(matches!(
        prepare_root_render_layout(&expr),
        RootRenderLayout::Plain(_)
    ));
}

#[test]
fn prepare_root_render_layout_recognises_applied_parameters_with_helpers() {
    // Param prologue (Let p = Constr) → helper Let → entry lambda.
    let policy_id = vec![0xea, 0x07, 0xb7, 0x33];
    let param_id = VarId::new(60);
    let helper_id = VarId::new(61);
    let ctx = binder("script_context", 62);

    let expr = PseudoExpr::Let {
        name: "policy".to_string(),
        id: Some(param_id),
        value: PBox::new(PseudoExpr::Constr {
            type_hint: None,
            tag: 1,
            fields: vec![PseudoExpr::ByteArray(policy_id)].into(),
            shape: super::super::constructor::ConstructorShape::unknown_data(1, 1),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "decode".to_string(),
            id: Some(helper_id),
            value: PBox::new(helper_rec("decode", 61, "items", 63)),
            body: PBox::new(PseudoExpr::Lambda {
                params: vec![ctx.clone()],
                body: PBox::new(PseudoExpr::var_with_id(ctx.name.clone(), ctx.id)),
            }),
        }),
    };

    match prepare_root_render_layout(&expr) {
        RootRenderLayout::Parametrized(layout) => {
            assert_eq!(layout.parameters.len(), 1);
            assert_eq!(layout.parameters[0].name, "policy");
            assert_eq!(layout.parameters[0].var_id, param_id);
            assert!(matches!(
                layout.parameters[0].value,
                PseudoExpr::Constr { .. }
            ));
            assert_eq!(layout.main.helpers.len(), 1);
            assert!(matches!(layout.main.helpers[0], RootHelper::RecFn { .. }));
            assert_eq!(layout.main.params, [ctx]);
        }
        _ => panic!("expected Parametrized layout for applied-param prologue"),
    }
}

#[test]
fn prepare_root_render_layout_recognises_applied_parameters_without_helpers() {
    let param_id = VarId::new(70);
    let ctx = binder("script_context", 71);
    let expr = PseudoExpr::Let {
        name: "p".to_string(),
        id: Some(param_id),
        value: PBox::new(PseudoExpr::int(7)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![ctx.clone()],
            body: PBox::new(PseudoExpr::var_with_id(ctx.name.clone(), ctx.id)),
        }),
    };

    match prepare_root_render_layout(&expr) {
        RootRenderLayout::Parametrized(layout) => {
            assert_eq!(layout.parameters.len(), 1);
            assert!(layout.main.helpers.is_empty());
            assert_eq!(layout.main.params, [ctx]);
        }
        _ => panic!("expected Parametrized layout even without helpers"),
    }
}

#[test]
fn prepare_root_render_layout_keeps_pure_helper_chain_as_lambda_with_helpers() {
    // Non-param script: leading helper Lets only.
    let helper_id = VarId::new(80);
    let ctx = binder("script_context", 81);
    let expr = PseudoExpr::Let {
        name: "decode".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_rec("decode", 80, "items", 82)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![ctx.clone()],
            body: PBox::new(PseudoExpr::var_with_id(ctx.name.clone(), ctx.id)),
        }),
    };

    match prepare_root_render_layout(&expr) {
        RootRenderLayout::LambdaWithHelpers(layout) => {
            assert_eq!(layout.helpers.len(), 1);
            assert_eq!(layout.params, [ctx]);
        }
        _ => panic!("non-param script must stay LambdaWithHelpers"),
    }
}

#[test]
fn prepare_root_render_layout_does_not_false_block_on_shadowed_control_name() {
    let outer_helper_id = VarId::new(50);
    let inner_shadow_id = VarId::new(51);
    let expr = PseudoExpr::Let {
        name: "decode".to_string(),
        id: Some(outer_helper_id),
        value: PBox::new(PseudoExpr::Lambda {
            params: vec![],
            body: PBox::new(PseudoExpr::bool(true)),
        }),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![binder("arg", 52)],
            body: PBox::new(PseudoExpr::Let {
                name: "decode".to_string(),
                id: Some(inner_shadow_id),
                value: PBox::new(PseudoExpr::bool(true)),
                body: PBox::new(PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::var_with_id("decode", inner_shadow_id)),
                    then_branch: PBox::new(PseudoExpr::int(1)),
                    else_branch: PBox::new(PseudoExpr::int(0)),
                }),
            }),
        }),
    };

    match prepare_root_render_layout(&expr) {
        RootRenderLayout::LambdaWithHelpers(layout) => {
            assert_eq!(layout.helpers.len(), 1);
        }
        _ => {
            panic!("shadowed inner control subject should not block outer helper extraction")
        }
    }
}
