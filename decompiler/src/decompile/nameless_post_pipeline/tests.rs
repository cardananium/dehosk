use super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

#[test]
fn nameless_orphan_guard_rejects_free_var_id_swap_with_stable_count() {
    let baseline_orphan = VarId::new(9791);
    let introduced_orphan = VarId::new(9792);
    let before = NamelessExpr::Var(baseline_orphan);
    let after = NamelessExpr::Var(introduced_orphan);
    let baseline_free_vars = nameless_free_var_id_set(&before);

    assert_eq!(baseline_free_vars.len(), 1);
    assert_eq!(nameless_free_var_id_set(&after).len(), 1);
    assert!(
        nameless_introduces_new_free_var_ids(&after, &baseline_free_vars),
        "stable orphan count with a different VarId must still trip the nameless guard"
    );
}

#[test]
fn default_nameless_post_pipeline_assigns_names_from_var_kind_annotations() {
    let source_id = VarId::new(9801);
    let field_id = VarId::new(9802);
    let data_id = VarId::new(9803);

    let expr = PseudoExpr::Let {
        name: "source".to_string(),
        id: Some(source_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "tmp_field".to_string(),
            id: Some(field_id),
            value: PBox::new(PseudoExpr::Trace {
                message: PBox::new(PseudoExpr::String("keep field".to_string())),
                value: PBox::new(PseudoExpr::int(1)),
            }),
            body: PBox::new(PseudoExpr::Let {
                name: "tmp_data".to_string(),
                id: Some(data_id),
                value: PBox::new(PseudoExpr::Trace {
                    message: PBox::new(PseudoExpr::String("keep data".to_string())),
                    value: PBox::new(PseudoExpr::byte_array(vec![0xab, 0xcd])),
                }),
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("tmp_field", field_id),
                        PseudoExpr::var_with_id("tmp_field", field_id),
                        PseudoExpr::var_with_id("tmp_data", data_id),
                        PseudoExpr::var_with_id("tmp_data", data_id),
                    ]
                    .into(),
                )),
            }),
        }),
    };

    let annotations = HashMap::from([
        (
            field_id,
            VarKind::FieldIndexAlias {
                parent: source_id,
                index: 2,
            },
        ),
        (data_id, VarKind::DataLiteralHoist),
    ]);

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &annotations);
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for annotation naming test, got: {guard_report:?}"
    );

    fn collect_id_names(
        expr: &PseudoExpr,
        target: VarId,
        binder_names: &mut Vec<String>,
        var_names: &mut Vec<String>,
    ) {
        match expr {
            PseudoExpr::Var { name, id } => {
                if *id == Some(target) {
                    var_names.push(name.clone());
                }
            }
            PseudoExpr::Lambda { params, body } => {
                for param in params {
                    if param.id == target {
                        binder_names.push(param.name.clone());
                    }
                }
                collect_id_names(body, target, binder_names, var_names);
            }
            PseudoExpr::RecFn { name, params, body } => {
                if name.id == target {
                    binder_names.push(name.name.clone());
                }
                for param in params {
                    if param.id == target {
                        binder_names.push(param.name.clone());
                    }
                }
                collect_id_names(body, target, binder_names, var_names);
            }
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                if *id == Some(target) {
                    binder_names.push(name.clone());
                }
                collect_id_names(value, target, binder_names, var_names);
                collect_id_names(body, target, binder_names, var_names);
            }
            PseudoExpr::Apply { function, args } => {
                collect_id_names(function, target, binder_names, var_names);
                for arg in args {
                    collect_id_names(arg, target, binder_names, var_names);
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                collect_id_names(condition, target, binder_names, var_names);
                collect_id_names(then_branch, target, binder_names, var_names);
                collect_id_names(else_branch, target, binder_names, var_names);
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                collect_id_names(subject, target, binder_names, var_names);
                if let Some(subject_name) = subject_name {
                    if subject_name.id == target {
                        binder_names.push(subject_name.name.clone());
                    }
                }
                for clause in clauses {
                    if let Some(guard) = &clause.guard {
                        collect_id_names(guard, target, binder_names, var_names);
                    }
                    collect_id_names(&clause.body, target, binder_names, var_names);
                }
            }
            PseudoExpr::List { elements, tail } => {
                for element in elements {
                    collect_id_names(element, target, binder_names, var_names);
                }
                if let Some(tail) = tail {
                    collect_id_names(tail, target, binder_names, var_names);
                }
            }
            PseudoExpr::Tuple(items) => {
                for item in items {
                    collect_id_names(item, target, binder_names, var_names);
                }
            }
            PseudoExpr::Pair(left, right) => {
                collect_id_names(left, target, binder_names, var_names);
                collect_id_names(right, target, binder_names, var_names);
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields {
                    collect_id_names(field, target, binder_names, var_names);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => {
                collect_id_names(record, target, binder_names, var_names);
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                collect_id_names(collection, target, binder_names, var_names);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                collect_id_names(left, target, binder_names, var_names);
                collect_id_names(right, target, binder_names, var_names);
            }
            PseudoExpr::UnOp { operand, .. } => {
                collect_id_names(operand, target, binder_names, var_names);
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    collect_id_names(arg, target, binder_names, var_names);
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                collect_id_names(inner, target, binder_names, var_names);
            }
            PseudoExpr::Trace { message, value } => {
                collect_id_names(message, target, binder_names, var_names);
                collect_id_names(value, target, binder_names, var_names);
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }

    let mut field_binders = Vec::new();
    let mut field_vars = Vec::new();
    collect_id_names(&output, field_id, &mut field_binders, &mut field_vars);
    assert_eq!(field_binders, vec!["field_2"]);
    assert_eq!(field_vars, vec!["field_2", "field_2"]);

    let mut data_binders = Vec::new();
    let mut data_vars = Vec::new();
    collect_id_names(&output, data_id, &mut data_binders, &mut data_vars);
    assert_eq!(data_binders, vec!["data_literal"]);
    assert_eq!(data_vars, vec!["data_literal", "data_literal"]);
}

#[test]
fn default_nameless_post_pipeline_respects_preserved_inline_ids() {
    use std::collections::HashSet;

    let preserved_id = VarId::new(9814);
    let expr = PseudoExpr::Let {
        name: "preserved".to_string(),
        id: Some(preserved_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::var_with_id("preserved", preserved_id)),
    };
    let preserved = HashSet::from([preserved_id]);

    let (output, guard_report) =
        run_default_nameless_post_pipeline_preserving(expr, &HashMap::new(), &preserved);
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for preserved inline id test, got: {guard_report:?}"
    );
    assert!(
        matches!(
            &output,
            PseudoExpr::Let { name, id, body, .. }
                if name == "preserved"
                    && *id == Some(preserved_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Var { name, id } if name == "preserved" && *id == Some(preserved_id)
                    )
        ),
        "preserved single-use binding should survive nameless inline, got: {output:?}"
    );
}

#[test]
fn default_nameless_post_pipeline_still_inlines_unpreserved_single_use_simple_let() {
    let helper_id = VarId::new(9815);
    let expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(helper_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::var_with_id("helper", helper_id)),
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for unpreserved inline test, got: {guard_report:?}"
    );
    assert!(
        matches!(&output, PseudoExpr::Int(value) if *value == 1.into()),
        "unpreserved single-use simple binding should still inline, got: {output:?}"
    );
}

#[test]
fn nameless_post_pipeline_assigns_extractor_temp_display_hint() {
    let temp_id = VarId::new(9822);
    let datum_id = VarId::new(9823);
    let expr = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var_with_id("datum", datum_id)].into(),
        }),
        body: PBox::new(PseudoExpr::var_with_id("g", temp_id)),
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for extractor display hint test, got: {guard_report:?}"
    );
    assert!(
        matches!(
            &output,
            PseudoExpr::Let { name, id, body, .. }
                if name == "datum_bytes"
                    && *id == Some(temp_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Var { name, id } if name == "datum_bytes" && *id == Some(temp_id)
                    )
        ),
        "extractor temp should render through display hint, got: {output:?}"
    );
}

#[test]
fn nameless_post_pipeline_extractor_temp_display_hint_is_id_scoped() {
    let temp_id = VarId::new(9824);
    let stale_ref_id = VarId::new(9825);
    let datum_id = VarId::new(9826);
    let expr = PseudoExpr::Let {
        name: "z_2".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var_with_id("datum", datum_id)].into(),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("z_2", temp_id),
                PseudoExpr::var_with_id("z_2", stale_ref_id),
            ]
            .into(),
        )),
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for id-scoped extractor display hint test, got: {guard_report:?}"
    );
    let PseudoExpr::Let { name, body, .. } = output else {
        panic!("expected let");
    };
    assert_eq!(name, "datum_bytes");
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[0],
                    PseudoExpr::Var { name, id } if name == "datum_bytes" && *id == Some(temp_id)
                ) && matches!(
                    &items[1],
                    PseudoExpr::Var { name, id } if name == "z_2" && *id == Some(stale_ref_id)
                )
        ),
        "only refs with the extractor temp VarId should follow the display hint, got: {body:?}"
    );
}

#[test]
fn nameless_post_pipeline_extractor_temp_display_hints_are_uniquified() {
    let first_id = VarId::new(9827);
    let second_id = VarId::new(9828);
    let datum_id = VarId::new(9829);
    let expr = PseudoExpr::Let {
        name: "g".to_string(),
        id: Some(first_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.un_bytearray"),
            args: vec![PseudoExpr::var_with_id("datum", datum_id)].into(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "h".to_string(),
            id: Some(second_id),
            value: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.un_bytearray"),
                args: vec![PseudoExpr::var_with_id("datum", datum_id)].into(),
            }),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("g", first_id),
                    PseudoExpr::var_with_id("h", second_id),
                ]
                .into(),
            )),
        }),
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for extractor display hint dedup test, got: {guard_report:?}"
    );
    let PseudoExpr::Let {
        name: first_name,
        body,
        ..
    } = output
    else {
        panic!("expected outer let");
    };
    let PseudoExpr::Let {
        name: second_name,
        body,
        ..
    } = body.as_ref()
    else {
        panic!("expected inner let");
    };
    assert_eq!(first_name, "datum_bytes");
    assert_eq!(second_name, "datum_bytes_2");
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[0],
                    PseudoExpr::Var { name, id } if name == "datum_bytes" && *id == Some(first_id)
                ) && matches!(
                    &items[1],
                    PseudoExpr::Var { name, id } if name == "datum_bytes_2" && *id == Some(second_id)
                )
        ),
        "deduplicated extractor display hints should retarget owned refs, got: {body:?}"
    );
}

#[test]
fn nameless_post_pipeline_assigns_field_payload_temp_display_hint() {
    let payload_id = VarId::new(9830);
    let temp_id = VarId::new(9831);
    let expr = PseudoExpr::Let {
        name: "payload".to_string(),
        id: Some(payload_id),
        value: PBox::new(PseudoExpr::var("seed")),
        body: PBox::new(PseudoExpr::Let {
            name: "q".to_string(),
            id: Some(temp_id),
            value: PBox::new(PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("payload", payload_id),
                    "fields".to_string(),
                )),
                index: 2,
            }),
            body: PBox::new(PseudoExpr::var_with_id("q", temp_id)),
        }),
    };

    let preserved = HashSet::from([payload_id, temp_id]);
    let (output, guard_report) =
        run_default_nameless_post_pipeline_preserving(expr, &HashMap::new(), &preserved);
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for field/payload display hint test, got: {guard_report:?}"
    );
    let PseudoExpr::Let { body, .. } = output else {
        panic!("expected outer let");
    };
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Let { name, id, body, .. }
                if name == "item"
                    && *id == Some(temp_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Var { name, id } if name == "item" && *id == Some(temp_id)
                    )
        ),
        "field/payload temp should render through display hint, got: {body:?}"
    );
}

#[test]
fn nameless_post_pipeline_field_payload_temp_display_hint_is_id_scoped() {
    let payload_id = VarId::new(9832);
    let temp_id = VarId::new(9833);
    let stale_ref_id = VarId::new(9834);
    let expr = PseudoExpr::Let {
        name: "payload".to_string(),
        id: Some(payload_id),
        value: PBox::new(PseudoExpr::var("seed")),
        body: PBox::new(PseudoExpr::Let {
            name: "q".to_string(),
            id: Some(temp_id),
            value: PBox::new(PseudoExpr::IndexAccess {
                collection: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::var_with_id("payload", payload_id),
                    "fields".to_string(),
                )),
                index: 2,
            }),
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::var_with_id("q", temp_id),
                    PseudoExpr::var_with_id("q", stale_ref_id),
                ]
                .into(),
            )),
        }),
    };

    let preserved = HashSet::from([payload_id, temp_id]);
    let (output, guard_report) =
        run_default_nameless_post_pipeline_preserving(expr, &HashMap::new(), &preserved);
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for id-scoped field/payload display hint test, got: {guard_report:?}"
    );
    let PseudoExpr::Let { body, .. } = output else {
        panic!("expected outer let");
    };
    let PseudoExpr::Let { name, body, .. } = body.as_ref() else {
        panic!("expected inner let");
    };
    assert_eq!(name, "item");
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[0],
                    PseudoExpr::Var { name, id } if name == "item" && *id == Some(temp_id)
                ) && matches!(
                    &items[1],
                    PseudoExpr::Var { name, id } if name == "q" && *id == Some(stale_ref_id)
                )
        ),
        "only refs with the field/payload temp VarId should follow the display hint, got: {body:?}"
    );
}

#[test]
fn nameless_post_pipeline_assigns_constructor_payload_temp_display_hint() {
    let temp_id = VarId::new(9835);
    let variant_id = VarId::new(9836);
    let expr = PseudoExpr::Let {
        name: "q3".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("variant", variant_id)),
            subject_name: Some(Binder::new("variant", variant_id)),
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    PseudoExpr::var_with_id("variant", variant_id),
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
        body: PBox::new(PseudoExpr::var_with_id("q3", temp_id)),
    };

    let preserved = HashSet::from([temp_id]);
    let (output, guard_report) =
        run_default_nameless_post_pipeline_preserving(expr, &HashMap::new(), &preserved);
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for constructor payload display hint test, got: {guard_report:?}"
    );
    assert!(
        matches!(
            &output,
            PseudoExpr::Let { name, id, body, .. }
                if name == "payload"
                    && *id == Some(temp_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Var { name, id } if name == "payload" && *id == Some(temp_id)
                    )
        ),
        "constructor payload temp should render through display hint, got: {output:?}"
    );
}

#[test]
fn nameless_post_pipeline_assigns_data_list_temp_display_hint() {
    let temp_id = VarId::new(9840);
    let rec_id = VarId::new(9841);
    let list_id = VarId::new(9842);
    let acc_id = VarId::new(9843);
    let head_id = VarId::new(9844);
    let tail_id = VarId::new(9845);
    let pairs_id = VarId::new(9846);
    let expr = PseudoExpr::Let {
        name: "to_data_partial".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::Let {
            name: "rec_fn_10".to_string(),
            id: Some(rec_id),
            value: PBox::new(PseudoExpr::RecFn {
                name: Binder::new("rec_fn_10", rec_id),
                params: vec![Binder::new("list", list_id), Binder::new("acc", acc_id)],
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(PseudoExpr::var_with_id("list", list_id)),
                    subject_name: Some(Binder::new("list", list_id)),
                    clauses: vec![
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![],
                                tail: None,
                            },
                            PseudoExpr::var_with_id("acc", acc_id),
                        ),
                        WhenClause::new(
                            WhenPattern::List {
                                elements: vec![Binder::new("head", head_id)],
                                tail: Some(Binder::new("tail", tail_id)),
                            },
                            PseudoExpr::BuiltinCall {
                                name: crate::BuiltinId::expect_known("List.cons"),
                                args: vec![
                                    PseudoExpr::var_with_id("head", head_id),
                                    PseudoExpr::Apply {
                                        function: PBox::new(PseudoExpr::var_with_id(
                                            "rec_fn_10",
                                            rec_id,
                                        )),
                                        args: vec![
                                            PseudoExpr::var_with_id("tail", tail_id),
                                            PseudoExpr::var_with_id("acc", acc_id),
                                        ]
                                        .into(),
                                    },
                                ]
                                .into(),
                            },
                        ),
                    ],
                }),
            }),
            body: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("Data.List"),
                args: vec![PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::var_with_id("rec_fn_10", rec_id)),
                    args: vec![
                        PseudoExpr::var_with_id("pairs", pairs_id),
                        PseudoExpr::List {
                            elements: vec![].into(),
                            tail: None,
                        },
                    ]
                    .into(),
                }]
                .into(),
            }),
        }),
        body: PBox::new(PseudoExpr::var_with_id("to_data_partial", temp_id)),
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for data_list display hint test, got: {guard_report:?}"
    );
    assert!(
        matches!(
            &output,
            PseudoExpr::Let { name, id, body, .. }
                if name == "data_list"
                    && *id == Some(temp_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Var { name, id } if name == "data_list" && *id == Some(temp_id)
                    )
        ),
        "data_list temp should render through display hint, got: {output:?}"
    );
}

#[test]
fn nameless_post_pipeline_assigns_option_wrapper_temp_display_hint() {
    let temp_id = VarId::new(9819);
    let expr = PseudoExpr::Let {
        name: "u2".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond")),
            then_branch: PBox::new(PseudoExpr::constr_known(
                crate::pseudo::constructor::KnownConstructor::None,
                vec![],
            )),
            else_branch: PBox::new(PseudoExpr::constr_known(
                crate::pseudo::constructor::KnownConstructor::Some,
                vec![PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Int"),
                    args: vec![PseudoExpr::var("t2")].into(),
                }],
            )),
        }),
        body: PBox::new(PseudoExpr::var_with_id("u2", temp_id)),
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for option-wrapper display hint test, got: {guard_report:?}"
    );
    assert!(
        matches!(
            &output,
            PseudoExpr::Let { name, id, body, .. }
                if name == "int_option"
                    && *id == Some(temp_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Var { name, id } if name == "int_option" && *id == Some(temp_id)
                    )
        ),
        "option-wrapper temp should render through display hint, got: {output:?}"
    );
}

#[test]
fn nameless_post_pipeline_option_wrapper_temp_display_hint_is_id_scoped() {
    let temp_id = VarId::new(9820);
    let stale_ref_id = VarId::new(9821);
    let expr = PseudoExpr::Let {
        name: "w2".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::If {
            condition: PBox::new(PseudoExpr::var("cond")),
            then_branch: PBox::new(PseudoExpr::constr_known(
                crate::pseudo::constructor::KnownConstructor::None,
                vec![],
            )),
            else_branch: PBox::new(PseudoExpr::constr_known(
                crate::pseudo::constructor::KnownConstructor::Some,
                vec![PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::expect_known("Data.Map"),
                    args: vec![PseudoExpr::var("pairs")].into(),
                }],
            )),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("w2", temp_id),
                PseudoExpr::var_with_id("w2", stale_ref_id),
            ]
            .into(),
        )),
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for id-scoped option-wrapper display hint test, got: {guard_report:?}"
    );
    let PseudoExpr::Let { name, body, .. } = output else {
        panic!("expected let");
    };
    assert_eq!(name, "map_option");
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[0],
                    PseudoExpr::Var { name, id } if name == "map_option" && *id == Some(temp_id)
                ) && matches!(
                    &items[1],
                    PseudoExpr::Var { name, id } if name == "w2" && *id == Some(stale_ref_id)
                )
        ),
        "only refs with the option-wrapper temp VarId should follow the display hint, got: {body:?}"
    );
}

#[test]
fn nameless_post_pipeline_assigns_arithmetic_temp_display_hint() {
    let temp_id = VarId::new(9816);
    let expr = PseudoExpr::Let {
        name: "t2".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(PseudoExpr::var("int")),
            right: PBox::new(PseudoExpr::var("int_2")),
        }),
        body: PBox::new(PseudoExpr::var_with_id("t2", temp_id)),
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for arithmetic display hint test, got: {guard_report:?}"
    );
    assert!(
        matches!(
            &output,
            PseudoExpr::Let { name, id, body, .. }
                if name == "sum"
                    && *id == Some(temp_id)
                    && matches!(
                        body.as_ref(),
                        PseudoExpr::Var { name, id } if name == "sum" && *id == Some(temp_id)
                    )
        ),
        "arithmetic temp should render through display hint, got: {output:?}"
    );
}

#[test]
fn nameless_post_pipeline_arithmetic_temp_display_hint_is_id_scoped() {
    let temp_id = VarId::new(9817);
    let stale_ref_id = VarId::new(9818);
    let expr = PseudoExpr::Let {
        name: "t2".to_string(),
        id: Some(temp_id),
        value: PBox::new(PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Add,
            left: PBox::new(PseudoExpr::var("count_result")),
            right: PBox::new(PseudoExpr::int(1)),
        }),
        body: PBox::new(PseudoExpr::Tuple(
            vec![
                PseudoExpr::var_with_id("t2", temp_id),
                PseudoExpr::var_with_id("t2", stale_ref_id),
            ]
            .into(),
        )),
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for id-scoped arithmetic display hint test, got: {guard_report:?}"
    );
    let PseudoExpr::Let { name, body, .. } = output else {
        panic!("expected let");
    };
    assert_eq!(name, "count");
    assert!(
        matches!(
            body.as_ref(),
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[0],
                    PseudoExpr::Var { name, id } if name == "count" && *id == Some(temp_id)
                ) && matches!(
                    &items[1],
                    PseudoExpr::Var { name, id } if name == "t2" && *id == Some(stale_ref_id)
                )
        ),
        "only refs with the arithmetic temp VarId should follow the display hint, got: {body:?}"
    );
}

#[test]
fn nameless_post_pipeline_assigns_check_temp_display_hint() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let check_id = VarId::new(9813);
    let expr = PseudoExpr::Let {
        name: "k".to_string(),
        id: Some(check_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("redeemer")),
            subject_name: None,
            clauses: vec![
                WhenClause::new(
                    WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                    PseudoExpr::Unit,
                ),
                WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Error { message: None }),
            ],
        }),
        body: PBox::new(PseudoExpr::Bool(true)),
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for check display hint test, got: {guard_report:?}"
    );

    let PseudoExpr::Let { name, id, .. } = output else {
        panic!("expected let");
    };
    assert_eq!(id, Some(check_id));
    assert_eq!(name, "check_redeemer");
}

#[test]
fn nameless_post_pipeline_assigns_when_pattern_binder_display_hint() {
    let payload_id = VarId::new(9837);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("get_at")),
            args: vec![PseudoExpr::var("items"), PseudoExpr::int(0)].into(),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor_known(
                    KnownConstructor::Some,
                    vec![Binder::new("y2_2", payload_id)],
                ),
                PseudoExpr::var_with_id("y2_2", payload_id),
            ),
            WhenClause::new(
                WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                PseudoExpr::Error { message: None },
            ),
        ],
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for when-pattern display hint test, got: {guard_report:?}"
    );
    let PseudoExpr::When { clauses, .. } = output else {
        panic!("expected when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected Some pattern");
    };
    assert_eq!(fields[0].name, "item");
    assert!(
        matches!(&clauses[0].body, PseudoExpr::Var { name, id } if name == "item" && *id == Some(payload_id)),
        "pattern body ref should follow display hint by VarId, got: {:?}",
        clauses[0].body
    );
}

#[test]
fn nameless_post_pipeline_when_pattern_binder_display_hint_is_id_scoped() {
    let payload_id = VarId::new(9838);
    let stale_ref_id = VarId::new(9839);
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var("get_at")),
            args: vec![PseudoExpr::var("items"), PseudoExpr::int(0)].into(),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause::new(
                WhenPattern::constructor_known(
                    KnownConstructor::Some,
                    vec![Binder::new("y2_2", payload_id)],
                ),
                PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("y2_2", payload_id),
                        PseudoExpr::var_with_id("y2_2", stale_ref_id),
                    ]
                    .into(),
                ),
            ),
            WhenClause::new(
                WhenPattern::constructor_known(KnownConstructor::None, vec![]),
                PseudoExpr::Error { message: None },
            ),
        ],
    };

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &HashMap::new());
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for id-scoped when-pattern display hint test, got: {guard_report:?}"
    );
    let PseudoExpr::When { clauses, .. } = output else {
        panic!("expected when");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected Some pattern");
    };
    assert_eq!(fields[0].name, "item");
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[0],
                    PseudoExpr::Var { name, id } if name == "item" && *id == Some(payload_id)
                ) && matches!(
                    &items[1],
                    PseudoExpr::Var { name, id } if name == "y2_2" && *id == Some(stale_ref_id)
                )
        ),
        "only refs with the pattern binder VarId should follow the display hint, got: {:?}",
        clauses[0].body
    );
}

#[test]
fn nameless_assign_names_guard_reverts_new_render_orphan_name() {
    let orphan_id = VarId::new(9804);
    let expr = PseudoExpr::var_with_id("tmp_orphan", orphan_id);
    let annotations = HashMap::from([(orphan_id, VarKind::DataLiteralHoist)]);

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &annotations);

    assert_eq!(
        guard_report.assign_names,
        NamelessAssignNamesGuardOutcome::RevertedNewOrphanName
    );
    assert!(
        matches!(&output, PseudoExpr::Var { name, id } if name == "tmp_orphan" && *id == Some(orphan_id)),
        "assign_names should be reverted instead of rendering a new orphan name, got: {output:?}"
    );
}

#[test]
fn nameless_assign_names_guard_ignores_unrelated_global_binder_name() {
    let decoy_id = VarId::new(9805);
    let orphan_id = VarId::new(9806);
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Let {
                name: "data_literal".to_string(),
                id: Some(decoy_id),
                value: PBox::new(PseudoExpr::int(0)),
                body: PBox::new(PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("data_literal", decoy_id),
                        PseudoExpr::var_with_id("data_literal", decoy_id),
                    ]
                    .into(),
                )),
            },
            PseudoExpr::var_with_id("tmp_orphan", orphan_id),
        ]
        .into(),
    );
    let annotations = HashMap::from([(orphan_id, VarKind::DataLiteralHoist)]);

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &annotations);

    assert_eq!(
        guard_report.assign_names,
        NamelessAssignNamesGuardOutcome::RevertedNewOrphanName
    );
    assert!(
        matches!(
            &output,
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[1],
                    PseudoExpr::Var { name, id } if name == "tmp_orphan" && *id == Some(orphan_id)
                )
        ),
        "an unrelated global binder name must not mask a new lexical render orphan, got: {output:?}"
    );
}

#[test]
fn nameless_post_pipeline_keeps_pattern_binder_names_in_orphan_guard() {
    // assign_names preserves an existing display/name hint on ConstrPayload
    // binders (Cardano context naming, validator params, etc.); only binders
    // without a meaningful hint get the canonical `item_{index}` name.
    // This test covers the preserve side for a binder already named
    // `payload_tmp`; `assign_names::tests::constr_payload_assigns_item_n`
    // covers the rename-when-unnamed case.
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let subject_id = VarId::new(9811);
    let payload_id = VarId::new(9812);
    let expr = PseudoExpr::Let {
        name: "subject".to_string(),
        id: Some(subject_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("subject", subject_id)),
            subject_name: None,
            clauses: vec![WhenClause::new(
                WhenPattern::constructor(
                    ConstructorShape::unknown_data(0, 1),
                    vec![Binder::new("payload_tmp", payload_id)],
                ),
                PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::var_with_id("payload_tmp", payload_id),
                        PseudoExpr::var_with_id("payload_tmp", payload_id),
                    ]
                    .into(),
                ),
            )],
        }),
    };

    let annotations = HashMap::from([(
        payload_id,
        VarKind::ConstrPayload {
            pattern_id: 0,
            index: 0,
        },
    )]);

    let (output, guard_report) = run_default_nameless_post_pipeline(expr, &annotations);
    assert!(
        guard_report.all_accepted(),
        "default nameless guard report should stay accepted for pattern binder naming test, got: {guard_report:?}"
    );

    let when = match &output {
        PseudoExpr::Let { body, .. } => body.as_ref(),
        other => other,
    };
    let PseudoExpr::When { clauses, .. } = when else {
        panic!("expected when body, got: {output:?}");
    };
    let WhenPattern::Constructor { fields, .. } = &clauses[0].pattern else {
        panic!("expected constructor pattern");
    };
    // assign_names keeps the meaningful `payload_tmp` hint rather than
    // the canonical `item_{index}` form.
    assert_eq!(fields[0].as_str(), "payload_tmp");
    assert_eq!(fields[0].var_id(), payload_id);
    assert!(
        matches!(
            &clauses[0].body,
            PseudoExpr::Tuple(items)
                if matches!(
                    &items[0],
                    PseudoExpr::Var { name, id } if name == "payload_tmp" && *id == Some(payload_id)
                ) && matches!(
                    &items[1],
                    PseudoExpr::Var { name, id } if name == "payload_tmp" && *id == Some(payload_id)
                )
        ),
        "pattern binder refs must follow the preserved binder name, got: {:?}",
        clauses[0].body
    );
}
