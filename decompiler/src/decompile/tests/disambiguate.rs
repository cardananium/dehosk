//! Unit tests for `disambiguate_constructors`.

#![cfg(test)]

use crate::DecompileOptions;
use crate::ScriptVersion;
use crate::decompile::adt_disambiguation::disambiguate_constructors;
use crate::decompile::blueprint_registry::BlueprintHintRegistry;
use crate::decompile::cardano_context_naming::propagate_types_and_name_constructors_with_blueprint;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

#[test]
fn test_blueprint_hints_default_is_none() {
    let opts = DecompileOptions::default();
    assert!(opts.blueprint_hints.is_none());
}

/// Build a BlueprintHints for testing with a custom enum type.
fn make_test_blueprint_hints() -> crate::cardano::BlueprintHints {
    use crate::cardano::blueprint::{ConstructorDef, FieldDef, TypeDefinition};
    use std::collections::HashMap;

    let mut types = HashMap::new();
    let mut constructor_names = HashMap::new();

    let type_name = "Action".to_string();
    let type_def = TypeDefinition {
        name: type_name.clone(),
        constructors: vec![
            ConstructorDef {
                name: "Mint".to_string(),
                tag: 0,
                fields: vec![],
            },
            ConstructorDef {
                name: "Burn".to_string(),
                tag: 1,
                fields: vec![FieldDef {
                    name: Some("amount".to_string()),
                    type_ref: Some("Int".to_string()),
                    index: 0,
                }],
            },
            ConstructorDef {
                name: "Transfer".to_string(),
                tag: 2,
                fields: vec![
                    FieldDef {
                        name: Some("to".to_string()),
                        type_ref: Some("ByteString".to_string()),
                        index: 0,
                    },
                    FieldDef {
                        name: Some("value".to_string()),
                        type_ref: Some("Int".to_string()),
                        index: 1,
                    },
                ],
            },
        ],
        is_record: false,
    };
    for ctor in &type_def.constructors {
        constructor_names.insert((type_name.clone(), ctor.tag), ctor.name.clone());
    }
    types.insert(type_name, type_def);

    crate::cardano::BlueprintHints {
        param_names: vec!["datum".to_string(), "redeemer".to_string()],
        types,
        constructor_names,
    }
}

#[test]
fn test_disambiguate_constructors_with_blueprint_hints() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};

    let hints = make_test_blueprint_hints();

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                guard: None,
                body: PseudoExpr::Int(1.into()),
            },
            WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(1, 1),
                    vec!["field_0".into()],
                ),
                guard: None,
                body: PseudoExpr::Int(2.into()),
            },
            WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(2, 2),
                    vec!["field_0".into(), "field_1".into()],
                ),
                guard: None,
                body: PseudoExpr::Int(3.into()),
            },
        ],
    };

    let mut registry = BlueprintHintRegistry::new();
    let result = disambiguate_constructors(expr, Some(&hints), &mut registry, false);
    let pretty = result
        .to_pretty_with_spans_config_and_registry(
            crate::decompile::render::PrettyConfig::default(),
            std::rc::Rc::new(registry),
        )
        .0;

    assert!(
        pretty.contains("Mint"),
        "Expected 'Mint' from blueprint: {pretty}"
    );
    assert!(
        pretty.contains("Burn"),
        "Expected 'Burn' from blueprint: {pretty}"
    );
    assert!(
        pretty.contains("Transfer"),
        "Expected 'Transfer' from blueprint: {pretty}"
    );
}

#[test]
fn test_disambiguate_constructors_blueprint_single_branch_resolved() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};

    let hints = make_test_blueprint_hints();

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(
                    ConstructorShape::unknown_data(1, 1),
                    vec!["field_0".into()],
                ),
                guard: None,
                body: PseudoExpr::Int(42.into()),
            },
            WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: PseudoExpr::Error {
                    message: Some("bad".to_string()),
                },
            },
        ],
    };

    let mut registry = BlueprintHintRegistry::new();
    let result = disambiguate_constructors(expr, Some(&hints), &mut registry, false);
    let pretty = result
        .to_pretty_with_spans_config_and_registry(
            crate::decompile::render::PrettyConfig::default(),
            std::rc::Rc::new(registry),
        )
        .0;

    assert!(
        pretty.contains("Burn"),
        "Expected 'Burn' from blueprint even for single-branch + wildcard: {pretty}"
    );
}

#[test]
fn test_disambiguate_constructors_no_hints_falls_back() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                guard: None,
                body: PseudoExpr::Int(0.into()),
            },
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                guard: None,
                body: PseudoExpr::Int(1.into()),
            },
        ],
    };

    let mut registry = BlueprintHintRegistry::new();
    let result = disambiguate_constructors(expr, None, &mut registry, false);
    let pretty = result.to_pretty();

    assert!(
        pretty.contains("False") || pretty.contains("True"),
        "Expected Bool disambiguation from arity fallback: {pretty}"
    );
}

#[test]
fn test_disambiguate_constructors_skips_arity_fallback_for_raw_fields_usage() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::var_id::VarId;

    let x_id = VarId::fresh_compat_placeholder();

    let fields_when = |value: i64| PseudoExpr::When {
        subject: PBox::new(PseudoExpr::field_access(
            PseudoExpr::var_with_id("x", x_id),
            "fields".to_string(),
        )),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Wildcard,
            guard: None,
            body: PseudoExpr::Int(value.into()),
        }],
    };

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var_with_id("x", x_id)),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(0, 0), vec![]),
                guard: None,
                body: fields_when(0),
            },
            WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                guard: None,
                body: fields_when(1),
            },
        ],
    };

    let mut registry = BlueprintHintRegistry::new();
    let result = disambiguate_constructors(expr, None, &mut registry, false);
    match result {
        PseudoExpr::When { clauses, .. } => {
            assert_eq!(clauses.len(), 2);
            match &clauses[0].pattern {
                WhenPattern::Constructor { tag, shape, .. } => {
                    assert_eq!(*tag, 0);
                    assert!(
                        matches!(shape, ConstructorShape::Unknown { .. }),
                        "expected Unknown shape, got {shape:?}"
                    );
                }
                other => panic!("expected Constructor, got {:?}", other),
            }
            match &clauses[1].pattern {
                WhenPattern::Constructor { tag, shape, .. } => {
                    assert_eq!(*tag, 1);
                    assert!(
                        matches!(shape, ConstructorShape::Unknown { .. }),
                        "expected Unknown shape, got {shape:?}"
                    );
                }
                other => panic!("expected Constructor, got {:?}", other),
            }
        }
        other => panic!("expected When, got {:?}", other),
    }
}

// Blueprint-driven user-ADT field binder naming.
//
// `propagate_types_and_name_constructors_with_blueprint` annotates
// pattern field-binders with `VarKind::UserAdtField` when the pattern
// carries a `TypeHintId` (attached upstream by
// `disambiguate_constructors`), `blueprint_hints.types` has that type
// name, and the matching constructor names the field at that index.

/// `MyData` blueprint: `Amount(amount)` at tag 0 and
/// `Recipient(addr, _)` at tag 1, whose second field has `name: None`
/// to exercise the skip-unnamed path.
fn make_user_adt_blueprint_hints() -> crate::cardano::BlueprintHints {
    use crate::cardano::blueprint::{ConstructorDef, FieldDef, TypeDefinition};
    use std::collections::HashMap;

    let mut types = HashMap::new();
    let mut constructor_names = HashMap::new();
    let type_name = "MyData".to_string();
    let type_def = TypeDefinition {
        name: type_name.clone(),
        constructors: vec![
            ConstructorDef {
                name: "Amount".to_string(),
                tag: 0,
                fields: vec![FieldDef {
                    name: Some("amount".to_string()),
                    type_ref: Some("Int".to_string()),
                    index: 0,
                }],
            },
            ConstructorDef {
                name: "Recipient".to_string(),
                tag: 1,
                fields: vec![
                    FieldDef {
                        name: Some("addr".to_string()),
                        type_ref: Some("ByteString".to_string()),
                        index: 0,
                    },
                    // Anonymous field — propagator must leave the binder alone.
                    FieldDef {
                        name: None,
                        type_ref: Some("Int".to_string()),
                        index: 1,
                    },
                ],
            },
        ],
        is_record: false,
    };
    for ctor in &type_def.constructors {
        constructor_names.insert((type_name.clone(), ctor.tag), ctor.name.clone());
    }
    types.insert(type_name, type_def);

    crate::cardano::BlueprintHints {
        param_names: vec!["datum".to_string(), "redeemer".to_string()],
        types,
        constructor_names,
    }
}

#[test]
fn improvement_e_annotates_user_adt_field_kind_from_blueprint() {
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};

    let hints = make_user_adt_blueprint_hints();

    // The *post-disambiguate* shape: patterns already carry the `type_hint`
    // `adt_disambiguation::disambiguate_constructors` attaches.
    let amount_field = Binder::new("field_0", VarId::fresh_binding());
    let addr_field = Binder::new("field_0", VarId::fresh_binding());
    let anon_field = Binder::new("field_1", VarId::fresh_binding());

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::Constructor {
                    tag: 0,
                    fields: vec![amount_field.clone()],
                    shape: ConstructorShape::unknown_data(0, 1),
                    type_hint: Some("MyData".into()),
                },
                guard: None,
                body: PseudoExpr::Int(1.into()),
            },
            WhenClause {
                pattern: WhenPattern::Constructor {
                    tag: 1,
                    fields: vec![addr_field.clone(), anon_field.clone()],
                    shape: ConstructorShape::unknown_data(1, 2),
                    type_hint: Some("MyData".into()),
                },
                guard: None,
                body: PseudoExpr::Int(2.into()),
            },
        ],
    };

    let mut registry = BlueprintHintRegistry::new();
    let mut kinds = std::collections::HashMap::new();

    let _ = propagate_types_and_name_constructors_with_blueprint(
        expr,
        ScriptVersion::PlutusV2,
        &mut registry,
        Some(&hints),
        &mut kinds,
    );

    match kinds.get(&amount_field.var_id()) {
        Some(VarKind::UserAdtField {
            type_name,
            field_name,
        }) => {
            assert_eq!(type_name, "MyData");
            assert_eq!(field_name, "amount");
        }
        other => panic!("expected UserAdtField for amount, got {other:?}"),
    }
    match kinds.get(&addr_field.var_id()) {
        Some(VarKind::UserAdtField {
            type_name,
            field_name,
        }) => {
            assert_eq!(type_name, "MyData");
            assert_eq!(field_name, "addr");
        }
        other => panic!("expected UserAdtField for addr, got {other:?}"),
    }
    assert!(
        !kinds.contains_key(&anon_field.var_id()),
        "anonymous blueprint field should not produce a UserAdtField annotation"
    );
}

#[test]
fn improvement_e_without_blueprint_hints_no_user_adt_annotation() {
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};

    let field = Binder::new("field_0", VarId::fresh_binding());
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                tag: 0,
                fields: vec![field.clone()],
                shape: ConstructorShape::unknown_data(0, 1),
                type_hint: Some("MyData".into()),
            },
            guard: None,
            body: PseudoExpr::Int(1.into()),
        }],
    };

    let mut registry = BlueprintHintRegistry::new();
    let mut kinds = std::collections::HashMap::new();

    let _ = propagate_types_and_name_constructors_with_blueprint(
        expr,
        ScriptVersion::PlutusV2,
        &mut registry,
        None, // <-- no blueprint hints
        &mut kinds,
    );

    assert!(
        !kinds.contains_key(&field.var_id()),
        "no blueprint hints -> no UserAdtField annotation"
    );
}

#[test]
fn improvement_e_skips_cardano_schema_sum_types() {
    use crate::cardano::blueprint::{ConstructorDef, FieldDef, TypeDefinition};
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};
    use std::collections::HashMap;

    // A `"purpose"` entry collides with the Cardano-schema sum
    // type (`SumTypeId::Purpose`); the propagator must skip the
    // user-ADT path there so `resolve_cardano_field_names` stays
    // the naming authority.
    let mut types = HashMap::new();
    let type_def = TypeDefinition {
        name: "purpose".to_string(),
        constructors: vec![ConstructorDef {
            name: "Spend".to_string(),
            tag: 1,
            fields: vec![FieldDef {
                name: Some("output_ref".to_string()),
                type_ref: Some("OutputReference".to_string()),
                index: 0,
            }],
        }],
        is_record: false,
    };
    types.insert("purpose".to_string(), type_def);
    let hints = crate::cardano::BlueprintHints {
        param_names: vec![],
        types,
        constructor_names: HashMap::new(),
    };

    let field = Binder::new("field_0", VarId::fresh_binding());
    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                tag: 1,
                fields: vec![field.clone()],
                shape: ConstructorShape::unknown_data(1, 1),
                type_hint: Some("purpose".into()),
            },
            guard: None,
            body: PseudoExpr::Int(1.into()),
        }],
    };

    let mut registry = BlueprintHintRegistry::new();
    let mut kinds = std::collections::HashMap::new();

    let _ = propagate_types_and_name_constructors_with_blueprint(
        expr,
        ScriptVersion::PlutusV2,
        &mut registry,
        Some(&hints),
        &mut kinds,
    );

    assert!(
        !matches!(
            kinds.get(&field.var_id()),
            Some(VarKind::UserAdtField { .. })
        ),
        "Cardano-schema sum type fields must not get UserAdtField, got {:?}",
        kinds.get(&field.var_id())
    );
}

#[test]
fn improvement_e_does_not_clobber_existing_annotation() {
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};

    let hints = make_user_adt_blueprint_hints();
    let field = Binder::new("field_0", VarId::fresh_binding());

    // The propagator must not overwrite an existing kind:
    // first-write-wins via `entry().or_insert_with`.
    let mut kinds = std::collections::HashMap::new();
    kinds.insert(field.var_id(), VarKind::User);

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                tag: 0,
                fields: vec![field.clone()],
                shape: ConstructorShape::unknown_data(0, 1),
                type_hint: Some("MyData".into()),
            },
            guard: None,
            body: PseudoExpr::Int(1.into()),
        }],
    };

    let mut registry = BlueprintHintRegistry::new();
    let _ = propagate_types_and_name_constructors_with_blueprint(
        expr,
        ScriptVersion::PlutusV2,
        &mut registry,
        Some(&hints),
        &mut kinds,
    );

    assert!(
        matches!(kinds.get(&field.var_id()), Some(VarKind::User)),
        "existing User annotation must not be clobbered"
    );
}

#[test]
fn improvement_e_unknown_type_name_no_annotation() {
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};

    let hints = make_user_adt_blueprint_hints();
    let field = Binder::new("field_0", VarId::fresh_binding());

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                tag: 0,
                fields: vec![field.clone()],
                shape: ConstructorShape::unknown_data(0, 1),
                // Type hint references a type NOT in blueprint_hints.types.
                type_hint: Some("NotInBlueprint".into()),
            },
            guard: None,
            body: PseudoExpr::Int(1.into()),
        }],
    };

    let mut registry = BlueprintHintRegistry::new();
    let mut kinds = std::collections::HashMap::new();

    let _ = propagate_types_and_name_constructors_with_blueprint(
        expr,
        ScriptVersion::PlutusV2,
        &mut registry,
        Some(&hints),
        &mut kinds,
    );

    assert!(
        !kinds.contains_key(&field.var_id()),
        "unknown type name -> no UserAdtField annotation, got {:?}",
        kinds.get(&field.var_id())
    );
}

#[test]
fn improvement_e_no_type_hint_no_annotation() {
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};

    let hints = make_user_adt_blueprint_hints();
    let field = Binder::new("field_0", VarId::fresh_binding());

    let expr = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::var("x")),
        subject_name: None,
        clauses: vec![WhenClause {
            pattern: WhenPattern::Constructor {
                tag: 0,
                fields: vec![field.clone()],
                shape: ConstructorShape::unknown_data(0, 1),
                // No type_hint attached (pre-disambiguate shape).
                type_hint: None,
            },
            guard: None,
            body: PseudoExpr::Int(1.into()),
        }],
    };

    let mut registry = BlueprintHintRegistry::new();
    let mut kinds = std::collections::HashMap::new();

    let _ = propagate_types_and_name_constructors_with_blueprint(
        expr,
        ScriptVersion::PlutusV2,
        &mut registry,
        Some(&hints),
        &mut kinds,
    );

    assert!(
        !kinds.contains_key(&field.var_id()),
        "no type_hint -> no UserAdtField annotation"
    );
}

#[test]
fn improvement_e_candidate_name_renders_blueprint_field_name() {
    // A `UserAdtField` annotation must make `assign_names` render
    // the sanitized blueprint field name.
    use crate::decompile::assign_names::assign_names;
    use crate::pseudo::nameless::{VarMetadata, VarOrigin, VarTable};

    let id = VarId::fresh_compat_placeholder();
    let mut table = VarTable::new();
    table.insert(
        id,
        VarMetadata {
            origin: VarOrigin::LetBinder,
            name_hint: Some("field_0".to_string()),
            display_name_hint: None,
            kind: VarKind::UserAdtField {
                type_name: "MyData".to_string(),
                field_name: "amount".to_string(),
            },
        },
    );
    let rewritten = assign_names(&mut table);
    assert_eq!(rewritten, 1, "UserAdtField should trigger a rename");
    assert_eq!(
        table.get(id).and_then(|m| m.render_name_hint()),
        Some("amount"),
        "expected blueprint field name `amount`"
    );
    // Preserves original source hint.
    assert_eq!(
        table.get(id).and_then(|m| m.name_hint.as_deref()),
        Some("field_0")
    );
}

#[test]
fn improvement_e_candidate_name_sanitizes_invalid_identifier() {
    // Blueprint field names need not be valid surface syntax identifiers.
    // `candidate_name` sanitizes them like a CallResult name.
    use crate::decompile::assign_names::assign_names;
    use crate::pseudo::nameless::{VarMetadata, VarOrigin, VarTable};

    let id = VarId::fresh_compat_placeholder();
    let mut table = VarTable::new();
    table.insert(
        id,
        VarMetadata {
            origin: VarOrigin::LetBinder,
            name_hint: None,
            display_name_hint: None,
            kind: VarKind::UserAdtField {
                type_name: "MyData".to_string(),
                field_name: "User-Name".to_string(),
            },
        },
    );
    assign_names(&mut table);
    let rendered = table.get(id).and_then(|m| m.render_name_hint()).unwrap();
    // `sanitize` lowercases ASCII alphanumerics and drops everything
    // but `_`, so `User-Name` collapses to `username`.
    assert_eq!(rendered, "username");
}

#[test]
fn improvement_e_candidate_name_dedups_colliding_field_names() {
    // Two UserAdtField binders with the same blueprint field name
    // must get unique suffixes via `fresh_name`.
    use crate::decompile::assign_names::assign_names;
    use crate::pseudo::nameless::{VarMetadata, VarOrigin, VarTable};

    let a = VarId::fresh_compat_placeholder();
    let b = VarId::fresh_compat_placeholder();
    let mut table = VarTable::new();
    for id in &[a, b] {
        table.insert(
            *id,
            VarMetadata {
                origin: VarOrigin::LetBinder,
                name_hint: None,
                display_name_hint: None,
                kind: VarKind::UserAdtField {
                    type_name: "MyData".to_string(),
                    field_name: "amount".to_string(),
                },
            },
        );
    }
    assign_names(&mut table);
    let names: Vec<String> = [a, b]
        .iter()
        .map(|id| {
            table
                .get(*id)
                .and_then(|m| m.render_name_hint())
                .unwrap()
                .to_string()
        })
        .collect();
    // First one wins `amount`, second gets `amount_2` (suffixes start at _2).
    assert!(names.contains(&"amount".to_string()));
    assert!(names.contains(&"amount_2".to_string()));
}

#[test]
fn ordering_names_flag_gates_the_ordering_signature() {
    use crate::decompile::{BlueprintHintRegistry, disambiguate_constructors};
    use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
    use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

    let mk = || {
        let subject_id = VarId::fresh_binding();
        PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var_with_id("x", subject_id)),
            subject_name: None,
            clauses: (0..3)
                .map(|tag| WhenClause {
                    pattern: WhenPattern::constructor(
                        ConstructorShape::unknown_data(tag, 0),
                        vec![],
                    ),
                    guard: None,
                    body: PseudoExpr::int(tag as i64),
                })
                .collect(),
        }
    };

    // Default OFF: the 3-nullary shape stays un-named (no Less/Equal/Greater).
    let mut registry = BlueprintHintRegistry::new();
    let off = disambiguate_constructors(mk(), None, &mut registry, false);
    let PseudoExpr::When { clauses, .. } = &off else {
        panic!()
    };
    for c in clauses {
        let WhenPattern::Constructor { shape, .. } = &c.pattern else {
            panic!()
        };
        assert!(
            matches!(shape, ConstructorShape::Unknown { .. }),
            "ordering_names=false must keep honest Unknown shapes, got {shape:?}"
        );
    }

    // Opt-in ON: the signature names the arms Less/Equal/Greater.
    let mut registry = BlueprintHintRegistry::new();
    let on = disambiguate_constructors(mk(), None, &mut registry, true);
    let PseudoExpr::When { clauses, .. } = &on else {
        panic!()
    };
    let kinds: Vec<_> = clauses
        .iter()
        .map(|c| {
            let WhenPattern::Constructor { shape, .. } = &c.pattern else {
                panic!()
            };
            shape.as_known()
        })
        .collect();
    assert_eq!(
        kinds,
        vec![
            Some(KnownConstructor::Less),
            Some(KnownConstructor::Equal),
            Some(KnownConstructor::Greater)
        ],
        "ordering_names=true must name the 3-nullary shape as Ordering"
    );
}
