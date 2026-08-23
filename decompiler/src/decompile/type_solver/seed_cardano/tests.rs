use super::super::*;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, PseudoType};
use crate::pseudo::var_id::VarId;

#[test]
fn p3_2_seeds_script_context_param_with_named_type() {
    // V2/V3 entry `fn(redeemer, script_context) { 0 }`: called
    // directly (production gates the seeder on `ScriptVersion`),
    // it types `script_context` as `Named("ScriptContext")` and
    // leaves `redeemer` alone.
    use crate::decompile::final_type_table::FinalTypeTable;

    let r_id = VarId::new(3300);
    let sc_id = VarId::new(3301);
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("redeemer", r_id),
            Binder::new("script_context", sc_id),
        ],
        body: PBox::new(PseudoExpr::int(0)),
    };

    let mut table = FinalTypeTable::new();
    super::seed_cardano_context_types(&lambda, &mut table);

    assert!(
        matches!(
            table.type_of_var(sc_id).as_deref(),
            Some(PseudoType::Named(name)) if name == "ScriptContext"
        ),
        "script_context must be seeded as Named(\"ScriptContext\"), got {:?}",
        table.type_of_var(sc_id)
    );
    assert!(
        table.type_of_var(r_id).is_none(),
        "P3.2 scope does NOT seed redeemer; got {:?}",
        table.type_of_var(r_id)
    );
}

#[test]
fn p3_2_overrides_data_default_with_named_script_context() {
    // `Data` is the implicit default (display-suppressed by
    // `resolve_type`), so the seeder must overwrite it with
    // `Named("ScriptContext")`.
    use crate::decompile::final_type_table::FinalTypeTable;
    use std::rc::Rc;

    let sc_id = VarId::new(3380);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
    };

    let mut table = FinalTypeTable::new();
    // Simulate the V3 solver landing Data on the context param.
    table.bind_var(sc_id, Rc::new(PseudoType::Data));
    super::seed_cardano_context_types(&lambda, &mut table);

    assert!(
        matches!(
            table.type_of_var(sc_id).as_deref(),
            Some(PseudoType::Named(name)) if name == "ScriptContext"
        ),
        "Data is the implicit default; seeder must overwrite with Named, got {:?}",
        table.type_of_var(sc_id)
    );
}

#[test]
fn p3_2_does_not_override_concrete_solver_type() {
    // A concrete solver type — here Bool on `script_context` —
    // must survive the seeder: the conservative-merge guarantee.
    use crate::decompile::final_type_table::FinalTypeTable;
    use std::rc::Rc;

    let sc_id = VarId::new(3310);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
    };
    let entry_id = VarId::new(3311);
    let expr = PseudoExpr::Let {
        name: "entry".to_string(),
        id: Some(entry_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::var_with_id("entry", entry_id)),
    };

    // Run only the seeder, not the full solver, to control
    // the pre-state.
    let mut table = FinalTypeTable::new();
    table.bind_var(sc_id, Rc::new(PseudoType::Bool));
    super::seed_cardano_context_types(&expr, &mut table);

    assert!(
        matches!(table.type_of_var(sc_id).as_deref(), Some(PseudoType::Bool)),
        "seeder must not overwrite a concrete solver-derived type; got {:?}",
        table.type_of_var(sc_id)
    );
}

#[test]
fn p3_2_v3_solver_path_records_script_context_in_final_table() {
    // `solve_type_constraints_with_final_table_versioned` with
    // `Some(PlutusV3)` fires the seeder, so the ScriptContext type
    // lands in the final table.
    use crate::decompile::ScriptVersion;

    let sc_id = VarId::new(3330);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
    };
    let entry_id = VarId::new(3331);
    let expr = PseudoExpr::Let {
        name: "validator".to_string(),
        id: Some(entry_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::var_with_id("validator", entry_id)),
    };

    let (_expr, table) =
        solve_type_constraints_with_final_table_versioned(expr, Some(ScriptVersion::PlutusV3));

    assert!(
        matches!(
            table.type_of_var(sc_id).as_deref(),
            Some(PseudoType::Named(name)) if name == "ScriptContext"
        ),
        "V3 solver path must seed script_context, got {:?}",
        table.type_of_var(sc_id)
    );
}

#[test]
fn p3_2_v2_solver_path_does_not_seed_script_context() {
    // V2's `script_context` is Data-typed at the protocol level and
    // sometimes pair-pattern-matched after inlining. The seeder
    // must NOT fire on V2.
    use crate::decompile::ScriptVersion;

    let sc_id = VarId::new(3340);
    let lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
    };
    let entry_id = VarId::new(3341);
    let expr = PseudoExpr::Let {
        name: "validator".to_string(),
        id: Some(entry_id),
        value: PBox::new(lambda),
        body: PBox::new(PseudoExpr::var_with_id("validator", entry_id)),
    };

    let (_expr, table) =
        solve_type_constraints_with_final_table_versioned(expr, Some(ScriptVersion::PlutusV2));

    assert!(
        !matches!(
            table.type_of_var(sc_id).as_deref(),
            Some(PseudoType::Named(name)) if name == "ScriptContext"
        ),
        "V2 solver path must NOT seed script_context, got {:?}",
        table.type_of_var(sc_id)
    );
}

#[test]
fn p3_2_unit_tail_picks_last_lambda_prefix_as_entry() {
    // `let helper = fn(script_context) {...}; let
    // entry = fn(script_context) {...}; Unit` — the entry is the
    // LAST Lambda-valued let-prefix, not the first.
    use crate::decompile::final_type_table::FinalTypeTable;

    let helper_id = VarId::new(3360);
    let helper_sc_id = VarId::new(3361);
    let entry_id = VarId::new(3362);
    let entry_sc_id = VarId::new(3363);

    let helper_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", helper_sc_id)],
        body: PBox::new(PseudoExpr::int(0)),
    };
    let entry_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", entry_sc_id)],
        body: PBox::new(PseudoExpr::int(1)),
    };
    let expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(PseudoExpr::Let {
            name: "entry".to_string(),
            id: Some(entry_id),
            value: PBox::new(entry_lambda),
            body: PBox::new(PseudoExpr::Unit),
        }),
    };

    let mut table = FinalTypeTable::new();
    super::seed_cardano_context_types(&expr, &mut table);

    assert!(
        matches!(
            table.type_of_var(entry_sc_id).as_deref(),
            Some(PseudoType::Named(name)) if name == "ScriptContext"
        ),
        "entry's script_context (last Lambda-valued prefix) must be seeded, got {:?}",
        table.type_of_var(entry_sc_id)
    );
    assert!(
        table.type_of_var(helper_sc_id).is_none(),
        "helper's script_context must NOT be seeded (it's an earlier prefix), got {:?}",
        table.type_of_var(helper_sc_id)
    );
}

#[test]
fn p3_2_var_tail_picks_matching_prefix_by_id() {
    // `let helper = fn(script_context) {...}; let
    // entry = fn(script_context) {...}; entry` — the Var-tail names
    // `entry`, so the seeder picks `entry`'s prefix by id, not the
    // last-Lambda-prefix rule.
    use crate::decompile::final_type_table::FinalTypeTable;

    let helper_id = VarId::new(3370);
    let helper_sc_id = VarId::new(3371);
    let entry_id = VarId::new(3372);
    let entry_sc_id = VarId::new(3373);

    let helper_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", helper_sc_id)],
        body: PBox::new(PseudoExpr::int(0)),
    };
    let entry_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", entry_sc_id)],
        body: PBox::new(PseudoExpr::int(1)),
    };
    let expr = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(PseudoExpr::Let {
            name: "entry".to_string(),
            id: Some(entry_id),
            value: PBox::new(entry_lambda),
            body: PBox::new(PseudoExpr::var_with_id("entry", entry_id)),
        }),
    };

    let mut table = FinalTypeTable::new();
    super::seed_cardano_context_types(&expr, &mut table);

    assert!(
        matches!(
            table.type_of_var(entry_sc_id).as_deref(),
            Some(PseudoType::Named(name)) if name == "ScriptContext"
        ),
        "Var-tail target's script_context must be seeded, got {:?}",
        table.type_of_var(entry_sc_id)
    );
    assert!(
        table.type_of_var(helper_sc_id).is_none(),
        "non-target prefix's script_context must NOT be seeded, got {:?}",
        table.type_of_var(helper_sc_id)
    );
}

#[test]
fn p3_2_does_not_seed_nested_helper_param_named_script_context() {
    // An inner helper Lambda with a param coincidentally named
    // `script_context` must not be seeded: the spine walk reaches only
    // the validator-entry Lambda, never helper bodies.
    //
    // Shape: `fn(real_sc) { let helper = fn(script_context) { 0 } in 1 }`;
    // only `real_sc` is an entry param.
    use crate::decompile::final_type_table::FinalTypeTable;

    let entry_sc_id = VarId::new(3350);
    let helper_id = VarId::new(3351);
    let helper_param_id = VarId::new(3352);

    let helper_lambda = PseudoExpr::Lambda {
        // Helper's param happens to be named `script_context` (rare,
        // but possible after rename collisions or user-named code).
        params: vec![Binder::new("script_context", helper_param_id)],
        body: PBox::new(PseudoExpr::int(0)),
    };
    let entry_body = PseudoExpr::Let {
        name: "helper".to_string(),
        id: Some(helper_id),
        value: PBox::new(helper_lambda),
        body: PBox::new(PseudoExpr::int(1)),
    };
    let entry_lambda = PseudoExpr::Lambda {
        // Entry's actual context param has a DIFFERENT name.
        params: vec![Binder::new("real_sc", entry_sc_id)],
        body: PBox::new(entry_body),
    };

    let mut table = FinalTypeTable::new();
    super::seed_cardano_context_types(&entry_lambda, &mut table);

    // Neither binder is seeded: `real_sc` is not spelled
    // `script_context`, and the helper's param is nested.
    assert!(
        table.type_of_var(entry_sc_id).is_none(),
        "entry's `real_sc` (not literally named `script_context`) must not be seeded"
    );
    assert!(
        table.type_of_var(helper_param_id).is_none(),
        "nested helper's `script_context` must NOT be seeded; got {:?}",
        table.type_of_var(helper_param_id)
    );
}

#[test]
fn p3_2_field_seeds_tx_info_redeemer_script_info_from_script_context_access() {
    // `let tx_info = script_context.tx_info` seeds the let-binder
    // with `Named("TxInfo")`; likewise `redeemer` →
    // `Named("Redeemer")` and `script_info` → `Named("ScriptInfo")`,
    // per CIP-0035.
    use crate::decompile::final_type_table::FinalTypeTable;
    use crate::pseudo::field_selector::FieldSelector;

    let sc_id = VarId::new(3400);
    let tx_info_id = VarId::new(3401);
    let redeemer_id = VarId::new(3402);
    let script_info_id = VarId::new(3403);

    let body = PseudoExpr::Let {
        name: "tx_info".to_string(),
        id: Some(tx_info_id),
        value: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
            selector: FieldSelector::NamedField("tx_info".to_string()),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "redeemer".to_string(),
            id: Some(redeemer_id),
            value: PBox::new(PseudoExpr::FieldAccess {
                record: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
                selector: FieldSelector::NamedField("redeemer".to_string()),
            }),
            body: PBox::new(PseudoExpr::Let {
                name: "script_info".to_string(),
                id: Some(script_info_id),
                value: PBox::new(PseudoExpr::FieldAccess {
                    record: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
                    selector: FieldSelector::NamedField("script_info".to_string()),
                }),
                body: PBox::new(PseudoExpr::var_with_id("tx_info", tx_info_id)),
            }),
        }),
    };
    let entry_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(body),
    };

    let mut table = FinalTypeTable::new();
    super::seed_cardano_context_types(&entry_lambda, &mut table);

    assert!(
        matches!(
            table.type_of_var(tx_info_id).as_deref(),
            Some(PseudoType::Named(name)) if name == "TxInfo"
        ),
        "tx_info let-binder must be seeded as TxInfo, got {:?}",
        table.type_of_var(tx_info_id)
    );
    assert!(
        matches!(
            table.type_of_var(redeemer_id).as_deref(),
            Some(PseudoType::Named(name)) if name == "Redeemer"
        ),
        "redeemer let-binder must be seeded as Redeemer, got {:?}",
        table.type_of_var(redeemer_id)
    );
    assert!(
        matches!(
            table.type_of_var(script_info_id).as_deref(),
            Some(PseudoType::Named(name)) if name == "ScriptInfo"
        ),
        "script_info let-binder must be seeded as ScriptInfo, got {:?}",
        table.type_of_var(script_info_id)
    );
}

#[test]
fn p3_2_field_does_not_seed_unknown_field_names() {
    // Only `tx_info`, `redeemer` and `script_info` are recognized;
    // any other field name is left untouched.
    use crate::decompile::final_type_table::FinalTypeTable;
    use crate::pseudo::field_selector::FieldSelector;

    let sc_id = VarId::new(3410);
    let bogus_id = VarId::new(3411);

    let body = PseudoExpr::Let {
        name: "bogus".to_string(),
        id: Some(bogus_id),
        value: PBox::new(PseudoExpr::FieldAccess {
            record: PBox::new(PseudoExpr::var_with_id("script_context", sc_id)),
            selector: FieldSelector::NamedField("unknown_field".to_string()),
        }),
        body: PBox::new(PseudoExpr::var_with_id("bogus", bogus_id)),
    };
    let entry_lambda = PseudoExpr::Lambda {
        params: vec![Binder::new("script_context", sc_id)],
        body: PBox::new(body),
    };

    let mut table = FinalTypeTable::new();
    super::seed_cardano_context_types(&entry_lambda, &mut table);

    assert!(
        table.type_of_var(bogus_id).is_none(),
        "unknown field must not be seeded; got {:?}",
        table.type_of_var(bogus_id)
    );
}

#[test]
fn p3_2_skips_non_script_context_params() {
    // Other param names (redeemer, datum, x, etc.) are not seeded.
    use crate::decompile::final_type_table::FinalTypeTable;

    let r_id = VarId::new(3320);
    let d_id = VarId::new(3321);
    let x_id = VarId::new(3322);
    let lambda = PseudoExpr::Lambda {
        params: vec![
            Binder::new("redeemer", r_id),
            Binder::new("datum", d_id),
            Binder::new("x", x_id),
        ],
        body: PBox::new(PseudoExpr::int(0)),
    };

    let mut table = FinalTypeTable::new();
    super::seed_cardano_context_types(&lambda, &mut table);

    assert!(
        table.type_of_var(r_id).is_none(),
        "P3.2 must not seed redeemer"
    );
    assert!(
        table.type_of_var(d_id).is_none(),
        "P3.2 must not seed datum"
    );
    assert!(
        table.type_of_var(x_id).is_none(),
        "P3.2 must not seed arbitrary names"
    );
}
