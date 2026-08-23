use super::*;
use crate::decompile::{
    decode_hex_to_program, decompile_program, render_decompiled_expr_with_spans,
};
use crate::pseudo::ast::PBox;
use std::rc::Rc;
use uplc::ast::{DeBruijn, NamedDeBruijn, Program};

#[test]
fn builds_bundle_with_binding_and_spans() {
    // fn(x) { x }
    let term = Term::Lambda {
        parameter_name: Rc::new(NamedDeBruijn {
            text: "x".to_string(),
            index: DeBruijn::new(1),
        }),
        body: Rc::new(Term::Var {
            name: Rc::new(NamedDeBruijn {
                text: "x".to_string(),
                index: DeBruijn::new(1),
            }),
            uniq_id: 2,
        }),
        uniq_id: 1,
    };
    let program = Program {
        version: (1, 0, 0),
        term,
    };

    let bundle = decompile_program_debug(&program).expect("bundle generation");
    assert!(!bundle.nodes.is_empty());
    assert!(!bundle.bindings.is_empty());
    assert!(!bundle.edges.is_empty());
    assert!(!bundle.binding_uses.is_empty());
    assert!(!bundle.ambiguities.is_empty());
    assert!(!bundle.uplc_source_map.is_empty());
    assert!(!bundle.code_source_map.is_empty());
    assert!(!bundle.pass_snapshots.is_empty());
    assert!(
        bundle
            .pass_snapshots
            .iter()
            .all(|s| s.nodes.iter().all(|n| n.stable_id > 0))
    );
    assert!(bundle.code.contains("fn("));
}

#[test]
fn debug_bundle_honors_mir_seed_and_render_contract() {
    let program = decode_hex_to_program("46010000200101").expect("expected valid identity program");
    let opts = DecompileOptions::default();

    let bundle = decompile_program_debug_with_options(&program, opts.clone())
        .expect("debug bundle generation");
    let rendered = decompile_program(&program, opts).expect("decompile program");

    assert_eq!(bundle.code, rendered);
    assert_eq!(
        bundle
            .pass_snapshots
            .first()
            .map(|snapshot| snapshot.pass.as_str()),
        Some("lower_mir")
    );
    assert!(
        bundle.pipeline_telemetry.fixed_point.attempted_iterations > 0,
        "debug bundle should expose fixed-point telemetry for optimized pipelines: {:?}",
        bundle.pipeline_telemetry
    );
    assert!(
        bundle
            .pass_snapshots
            .iter()
            .all(|snapshot| snapshot.pass != "decompile")
    );
}

#[test]
fn build_code_source_map_prefers_rendered_spans_for_repeated_var_names() {
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        value: PBox::new(PseudoExpr::Int(1.into())),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(crate::pseudo::var_id::VarId::fresh_compat_placeholder()),
        }),
    };

    let snapshot = snapshot_pseudo("test", &expr);
    let (code, rendered_spans) = render_decompiled_expr_with_spans(&expr, false);
    let code_source_map = build_code_source_map(Some(&snapshot), &rendered_spans, &code);

    let body_var = snapshot
        .nodes
        .iter()
        .find(|node| node.kind == "var" && node.parent == Some(snapshot.root))
        .expect("expected body var node");
    let body_span = code_source_map
        .iter()
        .find(|span| span.expr_id == body_var.id)
        .expect("expected span for body var");
    let last_x = code.rfind('x').expect("expected x in rendered code");

    assert_eq!(&code[body_span.start..body_span.end], "x");
    assert_eq!(body_span.start, last_x);
    assert_eq!(body_span.end, last_x + 1);
}
