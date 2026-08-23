use super::*;
use crate::pseudo::ast::{BinaryOp, HelperIntrinsic};
use num_bigint::BigInt;

fn id() -> VarId {
    VarId::fresh_compat_placeholder()
}

#[test]
fn round_trip_int_literal() {
    let expr = PseudoExpr::Int(BigInt::from(42));
    let (nameless, table) = pseudo_to_nameless(&expr);
    let raised = nameless_to_pseudo(&nameless, &table);
    match raised {
        PseudoExpr::Int(n) => assert_eq!(n, BigInt::from(42)),
        _ => panic!("expected Int"),
    }
}

#[test]
fn round_trip_var_preserves_name_and_id() {
    let v_id = id();
    let expr = PseudoExpr::Var {
        name: "script_context".to_string(),
        id: Some(v_id),
    };
    let (nameless, table) = pseudo_to_nameless(&expr);
    match &nameless {
        NamelessExpr::Var(actual) => assert_eq!(*actual, v_id),
        _ => panic!("expected Var"),
    }
    let raised = nameless_to_pseudo(&nameless, &table);
    match raised {
        PseudoExpr::Var { name, id } => {
            assert_eq!(name, "script_context");
            assert_eq!(id, Some(v_id));
        }
        _ => panic!("expected Var"),
    }
}

#[test]
fn round_trip_let_binding() {
    let v_id = id();
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(v_id),
        value: PBox::new(PseudoExpr::Int(BigInt::from(1))),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(v_id),
        }),
    };
    let (nameless, table) = pseudo_to_nameless(&expr);
    let raised = nameless_to_pseudo(&nameless, &table);
    match raised {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "x");
            match body.into_inner() {
                PseudoExpr::Var { name, .. } => assert_eq!(name, "x"),
                _ => panic!("expected body Var"),
            }
        }
        _ => panic!("expected Let"),
    }
}

#[test]
fn round_trip_lambda_with_params() {
    let p1 = id();
    let p2 = id();
    let expr = PseudoExpr::Lambda {
        params: vec![Binder::new("x", p1), Binder::new("y", p2)],
        body: PBox::new(PseudoExpr::BinOp {
            op: BinaryOp::Add,
            left: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(p1),
            }),
            right: PBox::new(PseudoExpr::Var {
                name: "y".to_string(),
                id: Some(p2),
            }),
        }),
    };
    let (nameless, table) = pseudo_to_nameless(&expr);
    let raised = nameless_to_pseudo(&nameless, &table);
    match raised {
        PseudoExpr::Lambda { params, .. } => {
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].name, "x");
            assert_eq!(params[1].name, "y");
        }
        _ => panic!("expected Lambda"),
    }
}

#[test]
fn round_trip_when_with_constructor_pattern() {
    let payload = id();
    let pattern = PseudoWhenPattern::Constructor {
        type_hint: None,
        tag: 0,
        fields: vec![Binder::new("x", payload)],
        shape: crate::pseudo::constructor::ConstructorShape::unknown_data(0, 1),
    };
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Unit),
        subject_name: None,
        clauses: vec![PseudoWhenClause {
            pattern,
            guard: None,
            body: PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(payload),
            },
        }],
    };
    let (nameless, table) = pseudo_to_nameless(&expr);
    let raised = nameless_to_pseudo(&nameless, &table);
    match raised {
        PseudoExpr::When { mut clauses, .. } => {
            let clause = clauses.remove(0);
            match clause.pattern {
                PseudoWhenPattern::Constructor { fields, .. } => {
                    assert_eq!(fields.len(), 1);
                    assert_eq!(fields[0].name, "x");
                }
                _ => panic!("expected Constructor"),
            }
        }
        _ => panic!("expected When"),
    }
}

#[test]
fn pseudo_to_nameless_records_every_id_needed_by_raise() {
    let free_id = id();
    let binding_id = id();
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Var {
                name: "free_ref".to_string(),
                id: Some(free_id),
            },
            PseudoExpr::Let {
                name: "x".to_string(),
                id: Some(binding_id),
                value: PBox::new(PseudoExpr::Int(BigInt::from(1))),
                body: PBox::new(PseudoExpr::Var {
                    name: "x".to_string(),
                    id: Some(binding_id),
                }),
            },
        ]
        .into(),
    );

    let (nameless, table) = pseudo_to_nameless(&expr);
    assert!(table.contains(free_id));
    assert!(table.contains(binding_id));

    let raised = nameless_to_pseudo(&nameless, &table);
    match raised {
        PseudoExpr::Tuple(items) => {
            assert!(
                matches!(&items[0], PseudoExpr::Var { name, id } if name == "free_ref" && *id == Some(free_id)),
                "ordinary lowering should retain a table name for free refs"
            );
            assert!(
                matches!(&items[1], PseudoExpr::Let { name, id, body, .. }
                    if name == "x"
                        && *id == Some(binding_id)
                        && matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "x" && *id == Some(binding_id))),
                "ordinary lowering should retain table names for binders and refs"
            );
        }
        _ => panic!("expected Tuple"),
    }
}

#[test]
fn nameless_to_pseudo_prefers_display_name_hint_without_losing_source_hint() {
    let binding_id = id();
    let expr = PseudoExpr::Let {
        name: "tmp_field".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::Int(BigInt::from(1))),
        body: PBox::new(PseudoExpr::Var {
            name: "tmp_field".to_string(),
            id: Some(binding_id),
        }),
    };

    let (nameless, mut table) = pseudo_to_nameless(&expr);
    let metadata = table
        .get_mut(binding_id)
        .expect("lowering should record the let binder");
    assert_eq!(metadata.name_hint.as_deref(), Some("tmp_field"));
    metadata.display_name_hint = Some("field_2".to_string());

    let raised = nameless_to_pseudo(&nameless, &table);
    match raised {
        PseudoExpr::Let { name, body, .. } => {
            assert_eq!(name, "field_2");
            assert!(
                matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "field_2" && *id == Some(binding_id)),
                "display hint should drive both binder and refs, got: {body:?}"
            );
        }
        other => panic!("expected Let, got: {other:?}"),
    }
    assert_eq!(
        table.get(binding_id).and_then(|m| m.name_hint.as_deref()),
        Some("tmp_field"),
        "display naming must not overwrite the original source hint"
    );
}

#[test]
fn raise_tableless_var_uses_diagnostic_v_id_fallback() {
    let table = VarTable::new();
    let unknown_id = id();
    let nameless = NamelessExpr::Var(unknown_id);
    let raised = nameless_to_pseudo(&nameless, &table);
    match raised {
        PseudoExpr::Var { name, id } => {
            assert!(
                name.starts_with("v_"),
                "expected fallback name `v_<id>`, got {name:?}"
            );
            assert_eq!(id, Some(unknown_id));
        }
        _ => panic!("expected Var"),
    }
}

#[test]
fn round_trip_helper_symbol_fix() {
    let expr = PseudoExpr::HelperSymbol(HelperIntrinsic::Fix);
    let (nameless, table) = pseudo_to_nameless(&expr);
    match &nameless {
        NamelessExpr::HelperSymbol(intrinsic) => {
            assert_eq!(*intrinsic, HelperIntrinsic::Fix);
        }
        other => panic!("expected NamelessExpr::HelperSymbol, got {other:?}"),
    }
    let raised = nameless_to_pseudo(&nameless, &table);
    match raised {
        PseudoExpr::HelperSymbol(intrinsic) => assert_eq!(intrinsic, HelperIntrinsic::Fix),
        other => panic!("expected PseudoExpr::HelperSymbol after raise, got {other:?}"),
    }
}

#[test]
fn round_trip_apply_of_helper_symbol() {
    // The Y-combinator's canonical applied form is Apply(fix, [arg]).
    let arg_id = id();
    let expr = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::HelperSymbol(HelperIntrinsic::Fix)),
        args: vec![PseudoExpr::var_with_id("recursive_helper", arg_id)].into(),
    };
    let (nameless, table) = pseudo_to_nameless(&expr);
    let raised = nameless_to_pseudo(&nameless, &table);
    match raised {
        PseudoExpr::Apply { function, args } => {
            assert!(matches!(
                *function,
                PseudoExpr::HelperSymbol(HelperIntrinsic::Fix)
            ));
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected Apply(HelperSymbol, ...), got {other:?}"),
    }
}
