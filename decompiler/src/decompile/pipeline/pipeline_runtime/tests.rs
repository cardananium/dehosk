use super::{PassContract, PipelineExecutor};
use crate::decompile::pipeline_passes::{PipelinePassId, PipelineProperty};
use crate::decompile::ref_retarget::refs_need_retarget_by_scope;
use crate::decompile::{
    cancel_force_delay_vars, collapse_tail_chains, deduplicate_var_ids, flatten_let_chains,
    normalize_list_cons_literals, simplify_boolean_and_identity, strip_cosmetic_delays,
};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PVec;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;
use std::cell::RefCell;

const CONSISTENT_REF_IDS_ONLY: &[PipelineProperty] = &[PipelineProperty::ConsistentRefIds];

fn stale_let_expr(binding_id: VarId, stale_ref_id: VarId) -> PseudoExpr {
    PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(stale_ref_id),
        }),
    }
}

#[test]
fn ensure_consistent_ref_ids_retargets_once_and_then_skips() {
    let binding_id = VarId::new(9001);
    let stale_ref_id = VarId::new(9002);
    let passes = RefCell::new(Vec::new());
    let retargeted = {
        let mut on_pass = |pass: &'static str, _expr: &PseudoExpr| {
            passes.borrow_mut().push(pass.to_string());
        };
        let mut executor = PipelineExecutor::new(&mut on_pass, false);

        let retargeted =
            executor.ensure_consistent_ref_ids(stale_let_expr(binding_id, stale_ref_id));
        match &retargeted {
            PseudoExpr::Let { body, .. } => {
                assert!(
                    matches!(body.as_ref(), PseudoExpr::Var { name, id } if name == "x" && *id == Some(binding_id))
                );
            }
            other => panic!("expected let after retarget, got {other:?}"),
        }
        let again = executor.ensure_consistent_ref_ids(retargeted.clone());
        assert_eq!(again, retargeted);

        retargeted
    };

    assert_eq!(retargeted, stale_let_expr(binding_id, binding_id));
    assert_eq!(*passes.borrow(), vec!["retarget_refs_by_scope"]);
}

#[test]
fn ensure_consistent_ref_ids_reruns_after_invalidating_pass_when_expr_needs_it() {
    let binding_id = VarId::new(9011);
    let stale_ref_id = VarId::new(9012);
    let passes = RefCell::new(Vec::new());
    let output = {
        let mut on_pass = |pass: &'static str, _expr: &PseudoExpr| {
            passes.borrow_mut().push(pass.to_string());
        };
        let mut executor = PipelineExecutor::new(&mut on_pass, false);

        let retargeted =
            executor.ensure_consistent_ref_ids(stale_let_expr(binding_id, stale_ref_id));
        executor.properties.remove_all(CONSISTENT_REF_IDS_ONLY);
        passes
            .borrow_mut()
            .push("synthetic_ref_id_invalidator".to_string());
        let again = executor.ensure_consistent_ref_ids(stale_let_expr(binding_id, stale_ref_id));
        assert_eq!(again, retargeted);

        again
    };

    assert_eq!(output, stale_let_expr(binding_id, binding_id));
    assert_eq!(
        *passes.borrow(),
        vec![
            "retarget_refs_by_scope",
            "synthetic_ref_id_invalidator",
            "retarget_refs_by_scope",
        ]
    );
}

#[test]
fn ensure_consistent_ref_ids_reruns_after_inline_dangling_field_aliases_invalidator() {
    let binding_id = VarId::new(9013);
    let stale_ref_id = VarId::new(9014);
    let passes = RefCell::new(Vec::new());
    let output = {
        let mut on_pass = |pass: &'static str, _expr: &PseudoExpr| {
            passes.borrow_mut().push(pass.to_string());
        };
        let mut executor = PipelineExecutor::new(&mut on_pass, false);

        let retargeted =
            executor.ensure_consistent_ref_ids(stale_let_expr(binding_id, stale_ref_id));
        executor
            .properties
            .insert(PipelineProperty::CardanoFieldNamesResolved);
        executor.emit(PipelinePassId::InlineDanglingFieldAliases, &retargeted);
        let again = executor.ensure_consistent_ref_ids(stale_let_expr(binding_id, stale_ref_id));
        assert_eq!(again, retargeted);

        again
    };

    assert_eq!(output, stale_let_expr(binding_id, binding_id));
    assert_eq!(
        *passes.borrow(),
        vec![
            "retarget_refs_by_scope",
            "inline_dangling_field_aliases",
            "retarget_refs_by_scope",
        ]
    );
}

#[test]
fn ensure_consistent_ref_ids_marks_consistent_expr_without_emitting_pass() {
    let binding_id = VarId::new(9021);
    let passes = RefCell::new(Vec::new());
    let expr = stale_let_expr(binding_id, binding_id);

    let output = {
        let mut on_pass = |pass: &'static str, _expr: &PseudoExpr| {
            passes.borrow_mut().push(pass.to_string());
        };
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        let first = executor.ensure_consistent_ref_ids(expr.clone());
        let second = executor.ensure_consistent_ref_ids(first.clone());
        assert_eq!(second, first);
        first
    };

    assert_eq!(output, expr);
    assert!(
        passes.borrow().is_empty(),
        "consistent expr should reestablish the property without a retarget pass"
    );
}

#[test]
fn ensure_consistent_ref_ids_reestablishes_property_without_retarget_when_invalidated_expr_stays_consistent()
 {
    let binding_id = VarId::new(9031);
    let passes = RefCell::new(Vec::new());
    let expr = stale_let_expr(binding_id, binding_id);

    let output = {
        let mut on_pass = |pass: &'static str, _expr: &PseudoExpr| {
            passes.borrow_mut().push(pass.to_string());
        };
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        let consistent = executor.ensure_consistent_ref_ids(expr.clone());
        executor.properties.insert(PipelineProperty::UniqueLetNames);
        executor.emit(PipelinePassId::ImproveVariableNamesPostLate, &consistent);
        let reestablished = executor.ensure_consistent_ref_ids(consistent.clone());
        assert_eq!(reestablished, consistent);
        reestablished
    };

    assert_eq!(output, expr);
    assert_eq!(*passes.borrow(), vec!["improve_variable_names_post_late"]);
}

#[test]
fn consistent_ref_id_contract_allows_invalidating_pass_to_drop_property() {
    let binding_id = VarId::new(9041);
    let stale_ref_id = VarId::new(9042);

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &stale_let_expr(binding_id, stale_ref_id),
            PassContract {
                requires: &[],
                produces: &[],
                invalidates: CONSISTENT_REF_IDS_ONLY,
            },
            true,
        ),
        None,
    );
}

#[test]
fn normalize_display_rewrites_emit_requires_and_invalidates_consistent_ref_ids_while_preserving_unique_names()
 {
    let binding_id = VarId::new(9046);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::NormalizeDisplayRewrites, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn rename_variables_emit_produces_renamed_variables_and_unique_let_names() {
    let binding_id = VarId::new(9067);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);

    executor.emit(PipelinePassId::RenameVariables, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::RenamedVariables])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
}

#[test]
fn lower_mir_emit_does_not_claim_unique_or_consistent_ref_id_properties() {
    let binding_id = VarId::new(9068);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);

    executor.emit(PipelinePassId::LowerMir, &expr);

    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
}

#[test]
fn convert_expect_tag_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9066);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ConvertExpectTag, &expr);
    }));

    let err = result.expect_err("expect-tag conversion must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn convert_expect_tag_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9173);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::ConvertExpectTag, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn strip_cosmetic_delays_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9146);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::StripCosmeticDelays, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn strip_cosmetic_delays_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9070);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::StripCosmeticDelays, &expr);
    }));

    let err = result.expect_err("cosmetic delay stripping must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn normalize_list_cons_literals_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9147);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::NormalizeListConsLiterals, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn normalize_list_cons_literals_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9071);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::NormalizeListConsLiterals, &expr);
    }));

    let err = result.expect_err("list-cons normalization must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn cancel_force_delay_vars_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9148);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::CancelForceDelayVars, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn cancel_force_delay_vars_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9069);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::CancelForceDelayVars, &expr);
    }));

    let err = result.expect_err("cancel force/delay pass must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn flatten_let_chains_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9149);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::FlattenLetChains,
        PipelinePassId::FlattenLetChainsPostInline,
        PipelinePassId::FlattenLetChainsPostReadability,
    ] {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
            PipelineProperty::ConsistentRefIds,
        ]);

        executor.emit(pass, &expr);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
        );
    }
}

#[test]
fn flatten_let_chains_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9068);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::FlattenLetChains,
        PipelinePassId::FlattenLetChainsPostInline,
        PipelinePassId::FlattenLetChainsPostReadability,
    ] {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor.properties.insert(PipelineProperty::UniqueLetNames);

            executor.emit(pass, &expr);
        }));

        let err = result.expect_err("flatten pass must require consistent ref ids");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("consistent_ref_ids"),
            "expected missing-property panic for {} to mention consistent_ref_ids, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn simplify_boolean_and_identity_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9150);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::SimplifyBooleanAndIdentity,
        PipelinePassId::SimplifyBooleanAndIdentityPostReadability,
        PipelinePassId::SimplifyBooleanAndIdentityLate,
    ] {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
            PipelineProperty::ConsistentRefIds,
        ]);

        executor.emit(pass, &expr);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
        );
    }
}

#[test]
fn extract_complex_when_subjects_emit_produces_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9151);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::ExtractComplexWhenSubjects, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn eta_pair_when_subject_cleanup_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9157);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::CollapseEtaPairSelectorWhenSubjects,
        PipelinePassId::CollapseEtaPairSelectorWhenSubjectsPostReadability,
    ] {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
            PipelineProperty::ConsistentRefIds,
        ]);

        executor.emit(pass, &expr);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
        );
    }
}

#[test]
fn extract_complex_when_subjects_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9152);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ExtractComplexWhenSubjects, &expr);
    }));

    let err = result.expect_err("complex when-subject extraction must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn eta_pair_selector_when_subject_passes_emit_require_consistent_ref_ids() {
    let binding_id = VarId::new(9158);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::CollapseEtaPairSelectorWhenSubjects,
        PipelinePassId::CollapseEtaPairSelectorWhenSubjectsPostReadability,
    ] {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor.properties.insert(PipelineProperty::UniqueLetNames);

            executor.emit(pass, &expr);
        }));

        let err = result.expect_err("eta pair selector pass must require consistent ref ids");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("consistent_ref_ids"),
            "expected missing-property panic for {} to mention consistent_ref_ids, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn simplify_double_rec_fn_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9159);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::SimplifyDoubleRecFn, &expr);
    }));

    let err = result.expect_err("double-rec simplification must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn simplify_double_rec_fn_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9160);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::SimplifyDoubleRecFn, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn simplify_z_combinator_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9161);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::SimplifyZCombinator, &expr);
    }));

    let err = result.expect_err("Z-combinator simplification must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn simplify_z_combinator_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9162);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::SimplifyZCombinator, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn resolve_immediate_applications_emit_produces_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9152);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::ResolveImmediateApplications, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn resolve_immediate_applications_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9153);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ResolveImmediateApplications, &expr);
    }));

    let err = result.expect_err("base immediate application pass must require consistent refs");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn resolve_immediate_applications_late_emit_produces_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9152);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::ResolveImmediateApplicationsLate, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn resolve_expect_constr_unpack_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9154);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::ResolveExpectConstrUnpack, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn resolve_expect_constr_unpack_emit_requires_unique_and_consistent_ref_ids() {
    let binding_id = VarId::new(9155);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for (seed, expected_missing) in [
        (PipelineProperty::UniqueLetNames, "consistent_ref_ids"),
        (PipelineProperty::ConsistentRefIds, "unique_let_names"),
    ] {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor.properties.insert(seed);

            executor.emit(PipelinePassId::ResolveExpectConstrUnpack, &expr);
        }));

        let err = result
            .expect_err("expect constructor unpack pass must require both hygiene properties");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains(expected_missing),
            "expected missing-property panic to mention {expected_missing}, got: {message}"
        );
    }
}

#[test]
fn extract_heavy_constants_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9153);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::ExtractHeavyConstants, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn extract_heavy_constants_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9154);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ExtractHeavyConstants, &expr);
    }));

    let err = result.expect_err("heavy-constant extraction must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn display_helper_passes_emit_require_unique_let_names() {
    let binding_id = VarId::new(9155);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::HoistLocalHelpers,
        PipelinePassId::ExtractHeavyConstants,
        PipelinePassId::NormalizeDisplayRewrites,
        PipelinePassId::HoistLocalHelpersPostNormalize,
    ] {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor
                .properties
                .insert(PipelineProperty::ConsistentRefIds);

            executor.emit(pass, &expr);
        }));

        let err = result.expect_err("display/helper pass must require unique let names");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("unique_let_names"),
            "expected missing-property panic for {} to mention unique_let_names, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn inline_dangling_field_aliases_emit_invalidates_consistent_ref_ids_while_preserving_unique_names()
{
    let binding_id = VarId::new(9047);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::InlineDanglingFieldAliases, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn inline_dangling_field_aliases_emit_requires_cardano_field_names_resolved() {
    let binding_id = VarId::new(9066);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::ConsistentRefIds,
        ]);

        executor.emit(PipelinePassId::InlineDanglingFieldAliases, &expr);
    }));

    let err = result.expect_err("dangling field alias inline must require resolved Cardano names");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("cardano_field_names_resolved"),
        "expected missing-property panic to mention cardano_field_names_resolved, got: {message}"
    );
}

#[test]
fn inline_dangling_field_aliases_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9067);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor
            .properties
            .insert(PipelineProperty::CardanoFieldNamesResolved);

        executor.emit(PipelinePassId::InlineDanglingFieldAliases, &expr);
    }));

    let err = result.expect_err("dangling field alias inline must require consistent refs");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn resolve_field_accesses_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9048);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::ResolveFieldAccesses, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn resolve_field_accesses_emit_requires_consistent_ref_ids_but_not_unique_let_names() {
    let binding_id = VarId::new(9067);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ResolveFieldAccesses, &expr);
    }));

    let err = result.expect_err("field access resolution must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );

    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor
        .properties
        .insert(PipelineProperty::ConsistentRefIds);

    executor.emit(PipelinePassId::ResolveFieldAccesses, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
}

#[test]
fn when_destructure_passes_emit_preserve_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9049);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::LiftUnpackTagWhenSubjects,
        PipelinePassId::DestructureWhenFields,
    ] {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
            PipelineProperty::ConsistentRefIds,
        ]);

        executor.emit(pass, &expr);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
        );
    }
}

#[test]
fn when_destructure_passes_emit_require_consistent_ref_ids() {
    let binding_id = VarId::new(9070);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::LiftUnpackTagWhenSubjects,
        PipelinePassId::DestructureWhenFields,
    ] {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor.properties.insert(PipelineProperty::UniqueLetNames);

            executor.emit(pass, &expr);
        }));

        let err = result.expect_err("when destructure pass must require consistent ref ids");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("consistent_ref_ids"),
            "expected missing-property panic for {} to mention consistent_ref_ids, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn hoist_local_helpers_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9050);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::HoistLocalHelpers,
        PipelinePassId::HoistLocalHelpersPostNormalize,
    ] {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
            PipelineProperty::ConsistentRefIds,
        ]);

        executor.emit(pass, &expr);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
        );
    }
}

#[test]
fn hoist_local_helpers_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9069);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::HoistLocalHelpers,
        PipelinePassId::HoistLocalHelpersPostNormalize,
    ] {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor.properties.insert(PipelineProperty::UniqueLetNames);

            executor.emit(pass, &expr);
        }));

        let err = result.expect_err("helper hoist pass must require consistent ref ids");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("consistent_ref_ids"),
            "expected missing-property panic for {} to mention consistent_ref_ids, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn improve_variable_names_emit_preserves_all_properties() {
    let binding_id = VarId::new(9051);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::ImproveVariableNames,
        PipelinePassId::ImproveVariableNamesPostLate,
    ] {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
            PipelineProperty::ConsistentRefIds,
            PipelineProperty::ValidatorParamNamesRenamed,
        ]);

        executor.emit(pass, &expr);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ValidatorParamNamesRenamed])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
        );
    }
}

#[test]
fn resolve_immediate_applications_late_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9065);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ResolveImmediateApplicationsLate, &expr);
    }));

    let err = result.expect_err("late immediate application pass must require consistent refs");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn hoist_local_helpers_post_normalize_stays_ref_id_preserver_not_producer() {
    let contract = PipelinePassId::HoistLocalHelpersPostNormalize.contract();
    assert!(
        contract
            .requires
            .contains(&PipelineProperty::ConsistentRefIds)
    );
    assert!(
        !contract
            .produces
            .contains(&PipelineProperty::ConsistentRefIds)
    );

    let binding_id = VarId::new(9066);
    let stale_ref_id = VarId::new(9067);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", stale_ref_id)),
    };

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr, contract, true,
        ),
        Some("preserver"),
    );
}

#[test]
fn improve_variable_name_passes_emit_require_consistent_ref_ids() {
    let binding_id = VarId::new(9052);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::ImproveVariableNames,
        PipelinePassId::ImproveVariableNamesPostLate,
    ] {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor.properties.insert(PipelineProperty::UniqueLetNames);

            executor.emit(pass, &expr);
        }));

        let err = result.expect_err("improve variable names pass must require consistent refs");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("consistent_ref_ids"),
            "expected missing-property panic for {} to mention consistent_ref_ids, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn improve_variable_names_post_late_emit_requires_unique_let_names() {
    let binding_id = VarId::new(9053);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor
            .properties
            .insert(PipelineProperty::ConsistentRefIds);

        executor.emit(PipelinePassId::ImproveVariableNamesPostLate, &expr);
    }));

    let err = result.expect_err("post-late improve variable names must require unique let names");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("unique_let_names"),
        "expected missing-property panic to mention unique_let_names, got: {message}"
    );
}

#[test]
fn resolve_scott_constructor_lambdas_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9056);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ResolveScottConstructorLambdas, &expr);
    }));

    let err = result.expect_err("base Scott constructor pass must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn resolve_scott_constructor_lambdas_late_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9053);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ResolveScottConstructorLambdasLate, &expr);
    }));

    let err = result.expect_err("late Scott constructor pass must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn resolve_data_constr_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9058);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ResolveDataConstr, &expr);
    }));

    let err = result.expect_err("Data.Constr pass must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn resolve_data_constr_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9059);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::ResolveDataConstr, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn resolve_scott_constructor_lambdas_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9057);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::ResolveScottConstructorLambdas,
        PipelinePassId::ResolveScottConstructorLambdasLate,
    ] {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
            PipelineProperty::ConsistentRefIds,
        ]);

        executor.emit(pass, &expr);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
        );
    }
}

#[test]
fn resolve_data_case_late_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9054);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ResolveDataCaseLate, &expr);
    }));

    let err = result.expect_err("late Data.case pass must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn resolve_data_case_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9072);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::ResolveDataCase, &expr);
    }));

    let err = result.expect_err("Data.case pass must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn simplify_boolean_and_identity_passes_emit_require_consistent_ref_ids() {
    let binding_id = VarId::new(9055);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::SimplifyBooleanAndIdentity,
        PipelinePassId::SimplifyBooleanAndIdentityPostReadability,
        PipelinePassId::SimplifyBooleanAndIdentityLate,
    ] {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor.properties.insert(PipelineProperty::UniqueLetNames);

            executor.emit(pass, &expr);
        }));

        let err = result.expect_err("boolean cleanup pass must require consistent ref ids");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("consistent_ref_ids"),
            "expected missing-property panic for {} to mention consistent_ref_ids, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn inline_single_use_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9055);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::InlineSingleUse, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn inline_single_use_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9068);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::InlineSingleUse, &expr);
    }));

    let err = result.expect_err("single-use inline must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn inline_fp_emit_produces_unique_names_and_preserves_consistent_ref_ids() {
    let binding_id = VarId::new(9052);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::InlineFp, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn inline_post_readability_emit_produces_unique_names_and_preserves_consistent_ref_ids() {
    let binding_id = VarId::new(9053);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::InlinePostReadability, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn inline_wrapper_passes_emit_require_consistent_ref_ids() {
    let binding_id = VarId::new(9070);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::InlineFp,
        PipelinePassId::InlinePostReadability,
    ] {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor.properties.insert(PipelineProperty::UniqueLetNames);

            executor.emit(pass, &expr);
        }));

        let err = result.expect_err("inline wrapper pass must require consistent ref ids");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("consistent_ref_ids"),
            "expected missing-property panic for {} to mention consistent_ref_ids, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn simplify_post_readability_emit_invalidates_consistent_ref_ids_while_preserving_unique_names() {
    let binding_id = VarId::new(9054);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
    ]);

    executor.emit(PipelinePassId::SimplifyPostReadability, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn broad_simplify_stage_outputs_produce_unique_and_consistent_ref_id_properties() {
    for pass in [
        PipelinePassId::Simplify1,
        PipelinePassId::Simplify2,
        PipelinePassId::SimplifyFp,
    ] {
        let binding_id = VarId::new(90540 + pass as u32);
        let expr = PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(binding_id),
            value: PBox::new(PseudoExpr::int(0)),
            body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
        };
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
        ]);

        executor.emit(pass, &expr);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames]),
            "{pass:?} must preserve UniqueLetNames"
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds]),
            "{pass:?} must preserve ConsistentRefIds"
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved]),
            "{pass:?} must still invalidate solved type properties"
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated]),
            "{pass:?} must still invalidate propagated type properties"
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved]),
            "{pass:?} must still invalidate field-name type properties"
        );
    }
}

#[test]
fn structural_final_cleanup_emit_produces_consistent_ref_ids_while_preserving_unique_names() {
    let binding_id = VarId::new(9055);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
    ]);

    executor.emit(PipelinePassId::StructuralFinalCleanup, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn deduplicate_var_ids_emit_boundaries_invalidate_consistent_ref_ids_while_preserving_unique_names()
{
    let duplicate_id = VarId::new(9058);
    let expr = PseudoExpr::Let {
        name: "outer".to_string(),
        id: Some(duplicate_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "inner".to_string(),
            id: Some(duplicate_id),
            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(PseudoExpr::var_with_id("outer", duplicate_id)),
        }),
    };
    assert!(
        !refs_need_retarget_by_scope(&expr),
        "duplicate-id fixture should start scope-consistent: {expr:?}"
    );

    let deduped = deduplicate_var_ids(expr);
    assert!(
        refs_need_retarget_by_scope(&deduped),
        "dedup can retarget duplicate ids onto a different-name binder id: {deduped:?}"
    );

    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    for pass in [
        PipelinePassId::DeduplicateVarIdsForTypeRefinement,
        PipelinePassId::DeduplicateVarIdsFinal,
    ] {
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
            PipelineProperty::ConsistentRefIds,
        ]);
        executor.emit(pass, &deduped);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames]),
            "{} should preserve unique let names",
            pass.label()
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds]),
            "{} should invalidate consistent ref ids",
            pass.label()
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved]),
            "{} should invalidate solved type constraints",
            pass.label()
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated]),
            "{} should invalidate propagated types",
            pass.label()
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved]),
            "{} should invalidate Cardano field names",
            pass.label()
        );
    }
}

#[test]
fn non_final_solve_type_passes_preserve_consistent_ref_ids_after_explicit_dedup_boundary() {
    let binding_id = VarId::new(9069);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::SolveTypeConstraints,
        PipelinePassId::SolveTypeConstraintsLate,
        PipelinePassId::SolveTypeConstraintsPostLateStructural,
    ] {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::ConsistentRefIds,
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
        ]);

        executor.emit(pass, &expr);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames]),
            "{} should preserve unique let names",
            pass.label()
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds]),
            "{} should preserve consistent ref ids",
            pass.label()
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved]),
            "{} should produce solved type constraints",
            pass.label()
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated]),
            "{} should invalidate propagated types",
            pass.label()
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved]),
            "{} should invalidate Cardano field names",
            pass.label()
        );
    }
}

#[test]
fn propagate_type_passes_emit_require_validator_param_names_and_solved_constraints() {
    let binding_id = VarId::new(9072);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::PropagateTypes,
        PipelinePassId::PropagateTypesLate,
        PipelinePassId::PropagateTypesPostLateStructural,
        PipelinePassId::PropagateTypesFinal,
    ] {
        let missing_validator = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor
                .properties
                .insert(PipelineProperty::TypeConstraintsSolved);

            executor.emit(pass, &expr);
        }));
        let err =
            missing_validator.expect_err("type propagation must require validator parameter names");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("validator_param_names_renamed"),
            "expected missing-property panic for {} to mention validator_param_names_renamed, got: {message}",
            pass.label()
        );

        let missing_solved = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor
                .properties
                .insert(PipelineProperty::ValidatorParamNamesRenamed);

            executor.emit(pass, &expr);
        }));
        let err =
            missing_solved.expect_err("type propagation must require solved type constraints");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("type_constraints_solved"),
            "expected missing-property panic for {} to mention type_constraints_solved, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn resolve_cardano_field_name_passes_emit_require_validator_param_names_and_propagated_types() {
    let binding_id = VarId::new(9073);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::ResolveCardanoFieldNames,
        PipelinePassId::ResolveCardanoFieldNamesLate,
        PipelinePassId::ResolveCardanoFieldNamesPostLateStructural,
        PipelinePassId::ResolveCardanoFieldNamesFinal,
    ] {
        let missing_validator = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor
                .properties
                .insert(PipelineProperty::TypesPropagated);

            executor.emit(pass, &expr);
        }));
        let err = missing_validator
            .expect_err("Cardano field-name resolution must require validator parameter names");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("validator_param_names_renamed"),
            "expected missing-property panic for {} to mention validator_param_names_renamed, got: {message}",
            pass.label()
        );

        let missing_propagated = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor
                .properties
                .insert(PipelineProperty::ValidatorParamNamesRenamed);

            executor.emit(pass, &expr);
        }));
        let err = missing_propagated
            .expect_err("Cardano field-name resolution must require propagated types");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("types_propagated"),
            "expected missing-property panic for {} to mention types_propagated, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn final_type_refinement_passes_preserve_consistent_ref_ids_after_explicit_dedup_boundary() {
    let binding_id = VarId::new(9059);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::ConsistentRefIds,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ValidatorParamNamesRenamed,
    ]);

    executor.emit(PipelinePassId::SolveTypeConstraintsFinal, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ValidatorParamNamesRenamed])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );

    executor
        .properties
        .insert(PipelineProperty::CardanoFieldNamesResolved);
    executor.emit(PipelinePassId::PropagateTypesFinal, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ValidatorParamNamesRenamed])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );

    executor.emit(PipelinePassId::ResolveCardanoFieldNamesFinal, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ValidatorParamNamesRenamed])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn propagate_types_final_emit_requires_solved_type_constraints() {
    let binding_id = VarId::new(9063);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::ConsistentRefIds,
            PipelineProperty::CardanoFieldNamesResolved,
        ]);

        executor.emit(PipelinePassId::PropagateTypesFinal, &expr);
    }));

    let err = result.expect_err("final type propagation must require solved constraints");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("type_constraints_solved"),
        "expected missing-property panic to mention type_constraints_solved, got: {message}"
    );
}

#[test]
fn consistent_ref_id_contract_rejects_preserver_with_stale_refs() {
    let binding_id = VarId::new(9056);
    let stale_ref_id = VarId::new(9057);

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &stale_let_expr(binding_id, stale_ref_id),
            PipelinePassId::ResolveCardanoFieldNamesFinal.contract(),
            true,
        ),
        Some("preserver"),
    );
}

#[test]
fn consistent_ref_id_contract_rejects_stale_producer_output() {
    let binding_id = VarId::new(9061);
    let stale_ref_id = VarId::new(9062);

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &stale_let_expr(binding_id, stale_ref_id),
            PipelinePassId::RetargetRefsByScope.contract(),
            false,
        ),
        Some("producer"),
    );
}

#[test]
fn consistent_ref_id_contract_accepts_clean_producer_output() {
    let binding_id = VarId::new(9071);

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &stale_let_expr(binding_id, binding_id),
            PipelinePassId::RetargetRefsByScope.contract(),
            false,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_strip_cosmetic_delays_output() {
    let outer_id = VarId::new(9081);
    let inner_id = VarId::new(9082);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::int(2)),
            body: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(inner_id),
            }),
        }))),
    };
    let out = strip_cosmetic_delays(expr);

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &out,
            PipelinePassId::StripCosmeticDelays.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_normalize_list_cons_literals_output() {
    let alias_id = VarId::new(9091);
    let item_id = VarId::new(9092);
    let expr = PseudoExpr::Let {
        name: "cons".to_string(),
        id: Some(alias_id),
        value: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("List.cons"),
            args: PVec::new(),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "item".to_string(),
            id: Some(item_id),
            value: PBox::new(PseudoExpr::int(1)),
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: "cons".to_string(),
                    id: Some(alias_id),
                }),
                args: vec![
                    PseudoExpr::Var {
                        name: "item".to_string(),
                        id: Some(item_id),
                    },
                    PseudoExpr::List {
                        elements: PVec::new(),
                        tail: None,
                    },
                ]
                .into(),
            }),
        }),
    };
    let out = normalize_list_cons_literals(expr);

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &out,
            PipelinePassId::NormalizeListConsLiterals.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_flatten_let_chains_outputs() {
    let outer_id = VarId::new(9101);
    let inner_id = VarId::new(9102);
    let shadow_id = VarId::new(9103);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(outer_id),
        value: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(inner_id),
            value: PBox::new(PseudoExpr::int(1)),
            body: PBox::new(PseudoExpr::Var {
                name: "y".to_string(),
                id: Some(inner_id),
            }),
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "y".to_string(),
            id: Some(shadow_id),
            value: PBox::new(PseudoExpr::int(0)),
            body: PBox::new(PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(outer_id),
            }),
        }),
    };
    let out = flatten_let_chains(expr);

    for pass in [
        PipelinePassId::FlattenLetChains,
        PipelinePassId::FlattenLetChainsPostInline,
        PipelinePassId::FlattenLetChainsPostReadability,
    ] {
        assert_eq!(
            PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
                &out,
                pass.contract(),
                true,
            ),
            None,
            "{} should preserve consistent ref ids",
            pass.label(),
        );
    }
}

#[test]
fn consistent_ref_id_contract_accepts_cancel_force_delay_vars_output() {
    let outer_y_id = VarId::new(9111);
    let x_id = VarId::new(9112);
    let inner_y_id = VarId::new(9113);
    let expr = PseudoExpr::Let {
        name: "y".to_string(),
        id: Some(outer_y_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(x_id),
            value: PBox::new(PseudoExpr::Delay(PBox::new(PseudoExpr::Var {
                name: "y".to_string(),
                id: Some(outer_y_id),
            }))),
            body: PBox::new(PseudoExpr::Let {
                name: "y".to_string(),
                id: Some(inner_y_id),
                value: PBox::new(PseudoExpr::int(0)),
                body: PBox::new(PseudoExpr::Force(PBox::new(PseudoExpr::Var {
                    name: "x".to_string(),
                    id: Some(x_id),
                }))),
            }),
        }),
    };
    let out = cancel_force_delay_vars(expr);

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &out,
            PipelinePassId::CancelForceDelayVars.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_simplify_boolean_and_identity_output() {
    let param_id = VarId::new(9121);
    let choose_id = VarId::new(9122);
    let expr = PseudoExpr::Tuple(
        vec![
            PseudoExpr::Lambda {
                params: vec![crate::pseudo::ast::Binder::new("x_17", param_id)],
                body: PBox::new(PseudoExpr::Var {
                    name: "x_17".to_string(),
                    id: Some(param_id),
                }),
            },
            PseudoExpr::Let {
                name: "choose_fst".to_string(),
                id: Some(choose_id),
                value: PBox::new(PseudoExpr::Constr {
                    type_hint: None,
                    tag: 0,
                    fields: PVec::new(),
                    shape: crate::pseudo::constructor::ConstructorShape::unknown_data(0, 0),
                }),
                body: PBox::new(PseudoExpr::If {
                    condition: PBox::new(PseudoExpr::Bool(true)),
                    then_branch: PBox::new(PseudoExpr::Var {
                        name: "choose_fst".to_string(),
                        id: Some(choose_id),
                    }),
                    else_branch: PBox::new(PseudoExpr::Bool(false)),
                }),
            },
        ]
        .into(),
    );
    let out = simplify_boolean_and_identity(expr, None);

    for pass in [
        PipelinePassId::SimplifyBooleanAndIdentity,
        PipelinePassId::SimplifyBooleanAndIdentityPostReadability,
        PipelinePassId::SimplifyBooleanAndIdentityLate,
    ] {
        assert_eq!(
            PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
                &out,
                pass.contract(),
                true,
            ),
            None,
            "{} should preserve consistent ref ids",
            pass.label(),
        );
    }
}

#[test]
fn consistent_ref_id_contract_accepts_collapse_tail_chains_output() {
    let xs_id = VarId::new(9131);
    let tail_id = VarId::new(9132);
    let param_id = VarId::new(9133);
    let expr = PseudoExpr::Let {
        name: "xs".to_string(),
        id: Some(xs_id),
        value: PBox::new(PseudoExpr::List {
            elements: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
            tail: None,
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "xs_tail".to_string(),
            id: Some(tail_id),
            value: PBox::new(PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::expect_known("List.tail"),
                args: vec![PseudoExpr::Var {
                    name: "xs".to_string(),
                    id: Some(xs_id),
                }]
                .into(),
            }),
            body: PBox::new(PseudoExpr::Lambda {
                params: vec![crate::pseudo::ast::Binder::new("acc", param_id)],
                body: PBox::new(PseudoExpr::Var {
                    name: "xs_tail".to_string(),
                    id: Some(tail_id),
                }),
            }),
        }),
    };
    let out = collapse_tail_chains(expr);

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &out,
            PipelinePassId::CollapseTailChains.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn collapse_tail_chains_emit_requires_consistent_ref_ids() {
    let expr = PseudoExpr::int(0);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::CollapseTailChains, &expr);
    }));

    let err = result.expect_err("tail-chain collapse must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn collapse_tail_chains_emit_preserves_unique_and_consistent_ref_id_properties() {
    let expr = PseudoExpr::int(0);
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::ConsistentRefIds,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
    ]);

    executor.emit(PipelinePassId::CollapseTailChains, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn consistent_ref_id_contract_accepts_simplify_double_rec_fn_output() {
    let outer_param_id = VarId::new(9136);
    let inner_param_id = VarId::new(9137);
    let captured_id = VarId::new(9138);
    let expr = crate::decompile::simplify_double_rec_fn(PseudoExpr::Let {
        name: "captured".to_string(),
        id: Some(captured_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::RecFn {
            name: crate::pseudo::ast::Binder::new("outer", VarId::new(9139)),
            params: vec![crate::pseudo::ast::Binder::new("acc", outer_param_id)],
            body: PBox::new(PseudoExpr::RecFn {
                name: crate::pseudo::ast::Binder::new("inner", VarId::new(9140)),
                params: vec![crate::pseudo::ast::Binder::new("x", inner_param_id)],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::Var {
                        name: "acc".to_string(),
                        id: Some(outer_param_id),
                    }),
                    args: vec![
                        PseudoExpr::Var {
                            name: "captured".to_string(),
                            id: Some(captured_id),
                        },
                        PseudoExpr::Var {
                            name: "x".to_string(),
                            id: Some(inner_param_id),
                        },
                    ]
                    .into(),
                }),
            }),
        }),
    });

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::SimplifyDoubleRecFn.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_simplify_z_combinator_output() {
    let acc_id = VarId::new(9141);
    let next_id = VarId::new(9142);
    let captured_id = VarId::new(9143);
    let expr = crate::decompile::simplify_z_combinator(PseudoExpr::RecFn {
        name: crate::pseudo::ast::Binder::new("self", VarId::new(9144)),
        params: vec![crate::pseudo::ast::Binder::new("acc", acc_id)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![crate::pseudo::ast::Binder::new("next", next_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: "acc".to_string(),
                    id: Some(acc_id),
                }),
                args: vec![
                    PseudoExpr::Var {
                        name: "captured".to_string(),
                        id: Some(captured_id),
                    },
                    PseudoExpr::Var {
                        name: "next".to_string(),
                        id: Some(next_id),
                    },
                ]
                .into(),
            }),
        }),
    });

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::SimplifyZCombinator.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_resolve_immediate_applications_output() {
    let x_id = VarId::new(9141);
    let y_id = VarId::new(9142);
    let expr = crate::decompile::resolve_immediate_applications(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Lambda {
            params: vec![
                crate::pseudo::ast::Binder::new("x", x_id),
                crate::pseudo::ast::Binder::new("y", y_id),
            ],
            body: PBox::new(PseudoExpr::BinOp {
                op: crate::pseudo::ast::BinaryOp::Eq,
                left: PBox::new(PseudoExpr::Var {
                    name: "x".to_string(),
                    id: Some(x_id),
                }),
                right: PBox::new(PseudoExpr::Var {
                    name: "y".to_string(),
                    id: Some(y_id),
                }),
            }),
        }),
        args: vec![PseudoExpr::int(1), PseudoExpr::int(2)].into(),
    });

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::ResolveImmediateApplications.contract(),
            true,
        ),
        None,
    );
    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::ResolveImmediateApplicationsLate.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_resolve_expect_constr_unpack_output() {
    let subject_id = VarId::new(9151);
    let expr = crate::decompile::resolve_expect_constr_unpack(
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::expect_helper()),
            args: vec![
                PseudoExpr::BinOp {
                    op: crate::pseudo::ast::BinaryOp::Eq,
                    left: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::builtin(
                            "Constr.unpack",
                            vec![PseudoExpr::var_with_id("x", subject_id)],
                        ),
                        "fst".to_string(),
                    )),
                    right: PBox::new(PseudoExpr::int(0)),
                },
                PseudoExpr::IndexAccess {
                    collection: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("x", subject_id),
                        "fields".to_string(),
                    )),
                    index: 0,
                },
            ]
            .into(),
        },
        None,
    );

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::ResolveExpectConstrUnpack.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_convert_expect_tag_output() {
    let subject_id = VarId::new(9156);
    let expr = crate::decompile::simplify::convert_expect_tag_to_constr_when(PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::expect_helper()),
        args: vec![
            PseudoExpr::BinOp {
                op: crate::pseudo::ast::BinaryOp::Eq,
                left: PBox::new(PseudoExpr::field_access(
                    PseudoExpr::BuiltinCall {
                        name: crate::BuiltinId::expect_known("Constr.unpack"),
                        args: vec![PseudoExpr::Var {
                            name: "x".to_string(),
                            id: Some(subject_id),
                        }]
                        .into(),
                    },
                    "fst".to_string(),
                )),
                right: PBox::new(PseudoExpr::int(0)),
            },
            PseudoExpr::Var {
                name: "x".to_string(),
                id: Some(subject_id),
            },
        ]
        .into(),
    });

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::ConvertExpectTag.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_recover_let_bound_tag_if_dispatch_output() {
    let tag_id = VarId::new(9159);
    let expr = crate::decompile::recover_let_bound_tag_if_dispatch(PseudoExpr::Let {
        name: "tag".to_string(),
        id: Some(tag_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Var {
            name: "tag".to_string(),
            id: Some(tag_id),
        }),
    });

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::RecoverLetBoundTagIfDispatch.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn recover_let_bound_tag_if_dispatch_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9160);
    let expr = PseudoExpr::Let {
        name: "tag".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("tag", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::RecoverLetBoundTagIfDispatch, &expr);
    }));

    let err = result.expect_err("tag-dispatch recovery must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn recover_let_bound_tag_if_dispatch_emit_preserves_all_properties() {
    let binding_id = VarId::new(9162);
    let expr = PseudoExpr::Let {
        name: "tag".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("tag", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
        PipelineProperty::ValidatorParamNamesRenamed,
    ]);

    executor.emit(PipelinePassId::RecoverLetBoundTagIfDispatch, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ValidatorParamNamesRenamed])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn rename_validator_params_emit_produces_validator_param_names_and_invalidates_type_metadata() {
    let binding_id = VarId::new(9064);
    let expr = PseudoExpr::Let {
        name: "script_context".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("script_context", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::ConsistentRefIds,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
    ]);

    executor.emit(PipelinePassId::RenameValidatorParams, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ValidatorParamNamesRenamed])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn consistent_ref_id_contract_accepts_rename_validator_params_output() {
    let context_id = VarId::new(9160);
    let inner_id = VarId::new(9161);
    let expr = crate::decompile::simplify::rename_validator_params(
        PseudoExpr::Lambda {
            params: vec![crate::pseudo::ast::Binder::new("__context__", context_id)],
            body: PBox::new(PseudoExpr::Tuple(
                vec![
                    PseudoExpr::Var {
                        name: "__context__".to_string(),
                        id: Some(context_id),
                    },
                    PseudoExpr::Lambda {
                        params: vec![crate::pseudo::ast::Binder::new("__context__", inner_id)],
                        body: PBox::new(PseudoExpr::Var {
                            name: "__context__".to_string(),
                            id: Some(inner_id),
                        }),
                    },
                ]
                .into(),
            )),
        },
        Some(crate::decompile::ScriptVersion::PlutusV3),
    );

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::RenameValidatorParams.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_eliminate_dead_lets_output() {
    let live_id = VarId::new(9161);
    let expr = crate::decompile::eliminate_dead_lets_pseudo(PseudoExpr::Let {
        name: "dead".to_string(),
        id: Some(VarId::new(9162)),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::Let {
            name: "live".to_string(),
            id: Some(live_id),
            value: PBox::new(PseudoExpr::int(1)),
            body: PBox::new(PseudoExpr::Var {
                name: "live".to_string(),
                id: Some(live_id),
            }),
        }),
    });

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::EliminateDeadLets.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn eliminate_dead_lets_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9166);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::EliminateDeadLets, &expr);
    }));

    let err = result.expect_err("dead-let elimination must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn eliminate_dead_lets_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9167);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::EliminateDeadLets, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn consistent_ref_id_contract_accepts_improve_variable_names_outputs() {
    let outer_check_id = VarId::new(9163);
    let inner_check_id = VarId::new(9164);
    let expr = crate::decompile::improve_variable_names(PseudoExpr::Let {
        name: "check_2".to_string(),
        id: Some(outer_check_id),
        value: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::var("redeemer")),
            subject_name: Some(crate::pseudo::ast::Binder::new(
                "redeemer",
                VarId::new(9165),
            )),
            clauses: vec![
                crate::pseudo::ast::WhenClause::new(
                    crate::pseudo::ast::WhenPattern::constructor(
                        crate::pseudo::constructor::ConstructorShape::unknown_data(0, 0),
                        vec![],
                    ),
                    PseudoExpr::Unit,
                ),
                crate::pseudo::ast::WhenClause::new(
                    crate::pseudo::ast::WhenPattern::Wildcard,
                    PseudoExpr::Error { message: None },
                ),
            ],
        }),
        body: PBox::new(PseudoExpr::Let {
            name: "check_2".to_string(),
            id: Some(inner_check_id),
            value: PBox::new(PseudoExpr::Bool(false)),
            body: PBox::new(PseudoExpr::var_with_id("check_2", inner_check_id)),
        }),
    });

    for pass in [
        PipelinePassId::ImproveVariableNames,
        PipelinePassId::ImproveVariableNamesPostLate,
    ] {
        assert_eq!(
            PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
                &expr,
                pass.contract(),
                true,
            ),
            None,
            "{} should preserve consistent ref ids",
            pass.label(),
        );
    }
}

#[test]
fn consistent_ref_id_contract_accepts_eliminate_cps_selectors_outputs() {
    let choose_fst_id = VarId::new(9166);
    let choose_snd_id = VarId::new(9167);
    let pick_id = VarId::new(9168);
    let cond_id = VarId::new(9169);
    let fst_x_id = VarId::new(9170);
    let fst_ignored_id = VarId::new(9171);
    let snd_ignored_id = VarId::new(9172);
    let snd_y_id = VarId::new(9173);
    let expr = crate::decompile::simplify::eliminate_cps_selectors(
        PseudoExpr::Let {
            name: "choose_fst".to_string(),
            id: Some(choose_fst_id),
            value: PBox::new(PseudoExpr::Lambda {
                params: vec![
                    crate::pseudo::ast::Binder::new("x", fst_x_id),
                    crate::pseudo::ast::Binder::new("_", fst_ignored_id),
                ],
                body: PBox::new(PseudoExpr::Var {
                    name: "x".to_string(),
                    id: Some(fst_x_id),
                }),
            }),
            body: PBox::new(PseudoExpr::Let {
                name: "choose_snd".to_string(),
                id: Some(choose_snd_id),
                value: PBox::new(PseudoExpr::Lambda {
                    params: vec![
                        crate::pseudo::ast::Binder::new("_", snd_ignored_id),
                        crate::pseudo::ast::Binder::new("y", snd_y_id),
                    ],
                    body: PBox::new(PseudoExpr::Var {
                        name: "y".to_string(),
                        id: Some(snd_y_id),
                    }),
                }),
                body: PBox::new(PseudoExpr::Let {
                    name: "pick".to_string(),
                    id: Some(pick_id),
                    value: PBox::new(PseudoExpr::Lambda {
                        params: vec![crate::pseudo::ast::Binder::new("cond", cond_id)],
                        body: PBox::new(PseudoExpr::If {
                            condition: PBox::new(PseudoExpr::Var {
                                name: "cond".to_string(),
                                id: Some(cond_id),
                            }),
                            then_branch: PBox::new(PseudoExpr::Var {
                                name: "choose_fst".to_string(),
                                id: Some(choose_fst_id),
                            }),
                            else_branch: PBox::new(PseudoExpr::Var {
                                name: "choose_snd".to_string(),
                                id: Some(choose_snd_id),
                            }),
                        }),
                    }),
                    body: PBox::new(PseudoExpr::Apply {
                        function: PBox::new(PseudoExpr::Var {
                            name: "pick".to_string(),
                            id: Some(pick_id),
                        }),
                        args: vec![
                            PseudoExpr::Bool(true),
                            PseudoExpr::Delay(PBox::new(PseudoExpr::int(1))),
                            PseudoExpr::Delay(PBox::new(PseudoExpr::int(2))),
                        ]
                        .into(),
                    }),
                }),
            }),
        },
        None,
    );

    for pass in [
        PipelinePassId::EliminateCpsSelectors,
        PipelinePassId::EliminateCpsSelectorsPostReadability,
    ] {
        assert_eq!(
            PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
                &expr,
                pass.contract(),
                true,
            ),
            None,
            "{} should preserve consistent ref ids",
            pass.label(),
        );
    }
}

#[test]
fn eliminate_cps_selector_passes_emit_require_consistent_ref_ids() {
    let binding_id = VarId::new(9174);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    for pass in [
        PipelinePassId::EliminateCpsSelectors,
        PipelinePassId::EliminateCpsSelectorsPostReadability,
    ] {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
            let mut executor = PipelineExecutor::new(&mut on_pass, false);
            executor.properties.insert(PipelineProperty::UniqueLetNames);

            executor.emit(pass, &expr);
        }));

        let err = result.expect_err("CPS selector elimination must require consistent ref ids");
        let message = if let Some(message) = err.downcast_ref::<String>() {
            message.as_str()
        } else if let Some(message) = err.downcast_ref::<&str>() {
            message
        } else {
            ""
        };
        assert!(
            message.contains("consistent_ref_ids"),
            "expected missing-property panic for {} to mention consistent_ref_ids, got: {message}",
            pass.label()
        );
    }
}

#[test]
fn consistent_ref_id_contract_accepts_resolve_data_constr_output() {
    let fields_id = VarId::new(9161);
    let expr = crate::decompile::resolve_data_constr(PseudoExpr::Let {
        name: "fields".to_string(),
        id: Some(fields_id),
        value: PBox::new(PseudoExpr::List {
            elements: vec![PseudoExpr::int(1)].into(),
            tail: None,
        }),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.Constr"),
            args: vec![
                PseudoExpr::int(0),
                PseudoExpr::Var {
                    name: "fields".to_string(),
                    id: Some(fields_id),
                },
            ]
            .into(),
        }),
    });

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::ResolveDataConstr.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_resolve_scott_constructor_lambdas_output() {
    let field_id = VarId::new(9166);
    let some_id = VarId::new(9167);
    let none_id = VarId::new(9168);
    let expr = crate::decompile::resolve_scott_constructor_lambdas(PseudoExpr::Let {
        name: "field".to_string(),
        id: Some(field_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![
                crate::pseudo::ast::Binder::new("some", some_id),
                crate::pseudo::ast::Binder::new("none", none_id),
            ],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: "some".to_string(),
                    id: Some(some_id),
                }),
                args: vec![PseudoExpr::Var {
                    name: "field".to_string(),
                    id: Some(field_id),
                }]
                .into(),
            }),
        }),
    });

    for pass in [
        PipelinePassId::ResolveScottConstructorLambdas,
        PipelinePassId::ResolveScottConstructorLambdasLate,
    ] {
        assert_eq!(
            PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
                &expr,
                pass.contract(),
                true,
            ),
            None,
            "{} should preserve consistent ref ids",
            pass.label(),
        );
    }
}

#[test]
fn consistent_ref_id_contract_accepts_disambiguate_constructors_output() {
    use crate::pseudo::ast::{WhenClause, WhenPattern};
    use crate::pseudo::constructor::ConstructorShape;

    let subject_id = VarId::new(9171);
    let expr = crate::decompile::disambiguate_constructors(
        PseudoExpr::Let {
            name: "x".to_string(),
            id: Some(subject_id),
            value: PBox::new(PseudoExpr::Constr {
                type_hint: None,
                tag: 0,
                fields: PVec::new(),
                shape: ConstructorShape::unknown_data(0, 0),
            }),
            body: PBox::new(PseudoExpr::When {
                subject: PBox::new(PseudoExpr::Var {
                    name: "x".to_string(),
                    id: Some(subject_id),
                }),
                subject_name: None,
                clauses: vec![
                    WhenClause {
                        pattern: WhenPattern::constructor(
                            ConstructorShape::unknown_data(0, 0),
                            vec![],
                        ),
                        guard: None,
                        body: PseudoExpr::Var {
                            name: "x".to_string(),
                            id: Some(subject_id),
                        },
                    },
                    WhenClause {
                        pattern: WhenPattern::constructor(
                            ConstructorShape::unknown_data(1, 0),
                            vec![],
                        ),
                        guard: None,
                        body: PseudoExpr::Var {
                            name: "x".to_string(),
                            id: Some(subject_id),
                        },
                    },
                ],
            }),
        },
        None,
        &mut crate::decompile::BlueprintHintRegistry::new(),
        false,
    );

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::DisambiguateConstructors.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn disambiguate_constructors_emit_requires_consistent_ref_ids() {
    let binding_id = VarId::new(9172);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert(PipelineProperty::UniqueLetNames);

        executor.emit(PipelinePassId::DisambiguateConstructors, &expr);
    }));

    let err = result.expect_err("constructor disambiguation must require consistent ref ids");
    let message = if let Some(message) = err.downcast_ref::<String>() {
        message.as_str()
    } else if let Some(message) = err.downcast_ref::<&str>() {
        message
    } else {
        ""
    };
    assert!(
        message.contains("consistent_ref_ids"),
        "expected missing-property panic to mention consistent_ref_ids, got: {message}"
    );
}

#[test]
fn disambiguate_constructors_emit_preserves_unique_and_consistent_ref_id_properties() {
    let binding_id = VarId::new(9173);
    let expr = PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(binding_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::var_with_id("x", binding_id)),
    };
    let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
    let mut executor = PipelineExecutor::new(&mut on_pass, false);
    executor.properties.insert_all(&[
        PipelineProperty::UniqueLetNames,
        PipelineProperty::TypeConstraintsSolved,
        PipelineProperty::TypesPropagated,
        PipelineProperty::CardanoFieldNamesResolved,
        PipelineProperty::ConsistentRefIds,
    ]);

    executor.emit(PipelinePassId::DisambiguateConstructors, &expr);

    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::UniqueLetNames])
    );
    assert!(
        executor
            .properties
            .satisfies(&[PipelineProperty::ConsistentRefIds])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypeConstraintsSolved])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::TypesPropagated])
    );
    assert!(
        !executor
            .properties
            .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
    );
}

#[test]
fn consistent_ref_id_contract_accepts_resolve_data_case_output() {
    use crate::pseudo::constructor::ConstructorShape;

    let subject_id = VarId::new(9181);
    let payload_id = VarId::new(9182);
    let fallback = PseudoExpr::Constr {
        type_hint: None,
        tag: 2,
        fields: PVec::new(),
        shape: ConstructorShape::unknown_data(2, 0),
    };
    let expr = crate::decompile::resolve_data_case(PseudoExpr::Let {
        name: "x".to_string(),
        id: Some(subject_id),
        value: PBox::new(PseudoExpr::Constr {
            type_hint: None,
            tag: 0,
            fields: PVec::new(),
            shape: ConstructorShape::unknown_data(0, 0),
        }),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.case"),
            args: vec![
                PseudoExpr::Var {
                    name: "x".to_string(),
                    id: Some(subject_id),
                },
                PseudoExpr::Lambda {
                    params: vec![crate::pseudo::ast::Binder::new("x", payload_id)],
                    body: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::Var {
                            name: "x".to_string(),
                            id: Some(payload_id),
                        },
                        "fields".to_string(),
                    )),
                },
                fallback.clone(),
                fallback.clone(),
                fallback.clone(),
                fallback,
            ]
            .into(),
        }),
    });

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::ResolveDataCase.contract(),
            true,
        ),
        None,
    );
    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::ResolveDataCaseLate.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn resolve_data_case_emit_preserves_unique_and_consistent_ref_id_properties() {
    use crate::pseudo::ast::Binder;
    use crate::pseudo::constructor::ConstructorShape;

    let outer_payload_id = VarId::new(9183);
    let data_id = VarId::new(9184);
    let handler_payload_id = VarId::new(9185);
    let fallback = PseudoExpr::Constr {
        type_hint: None,
        tag: 2,
        fields: PVec::new(),
        shape: ConstructorShape::unknown_data(2, 0),
    };
    let expr = crate::decompile::resolve_data_case(PseudoExpr::Let {
        name: "payload".to_string(),
        id: Some(outer_payload_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::expect_known("Data.case"),
            args: vec![
                PseudoExpr::var_with_id("data", data_id),
                PseudoExpr::Lambda {
                    params: vec![Binder::new("payload", handler_payload_id)],
                    body: PBox::new(PseudoExpr::field_access(
                        PseudoExpr::var_with_id("payload", handler_payload_id),
                        "fields".to_string(),
                    )),
                },
                fallback.clone(),
                fallback.clone(),
                fallback.clone(),
                fallback,
            ]
            .into(),
        }),
    });

    for pass in [
        PipelinePassId::ResolveDataCase,
        PipelinePassId::ResolveDataCaseLate,
    ] {
        let mut on_pass = |_: &'static str, _: &PseudoExpr| {};
        let mut executor = PipelineExecutor::new(&mut on_pass, false);
        executor.properties.insert_all(&[
            PipelineProperty::UniqueLetNames,
            PipelineProperty::TypeConstraintsSolved,
            PipelineProperty::TypesPropagated,
            PipelineProperty::CardanoFieldNamesResolved,
            PipelineProperty::ConsistentRefIds,
        ]);

        executor.emit(pass, &expr);

        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::UniqueLetNames])
        );
        assert!(
            executor
                .properties
                .satisfies(&[PipelineProperty::ConsistentRefIds])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypeConstraintsSolved])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::TypesPropagated])
        );
        assert!(
            !executor
                .properties
                .satisfies(&[PipelineProperty::CardanoFieldNamesResolved])
        );
    }
}

#[test]
fn consistent_ref_id_contract_accepts_extract_heavy_constants_output() {
    use crate::pseudo::constructor::ConstructorShape;

    let x_id = VarId::new(9186);
    let expr = crate::decompile::extract_heavy_constants(PseudoExpr::BinOp {
        op: crate::pseudo::ast::BinaryOp::Eq,
        left: PBox::new(PseudoExpr::Var {
            name: "x".to_string(),
            id: Some(x_id),
        }),
        right: PBox::new(PseudoExpr::constr(
            ConstructorShape::unknown_data(0, 2),
            vec![
                PseudoExpr::ByteArray(vec![0xaa; 32]),
                PseudoExpr::constr(
                    ConstructorShape::unknown_data(0, 1),
                    vec![PseudoExpr::ByteArray(vec![0xbb; 32])],
                ),
            ],
        )),
    });

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::ExtractHeavyConstants.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_extract_complex_when_subjects_output() {
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};

    let xs_id = VarId::new(9191);
    let tmp_id = VarId::new(9192);
    let payload_id = VarId::new(9193);
    let expr = crate::decompile::extract_complex_when_subjects(PseudoExpr::Let {
        name: "xs".to_string(),
        id: Some(xs_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Lambda {
                    params: vec![Binder::new("tmp", tmp_id)],
                    body: PBox::new(PseudoExpr::Tuple(
                        vec![
                            PseudoExpr::Var {
                                name: "tmp".to_string(),
                                id: Some(tmp_id),
                            },
                            PseudoExpr::Bool(true),
                        ]
                        .into(),
                    )),
                }),
                args: vec![PseudoExpr::Var {
                    name: "xs".to_string(),
                    id: Some(xs_id),
                }]
                .into(),
            }),
            subject_name: Some(Binder::new("payload", payload_id)),
            clauses: vec![WhenClause::new(
                WhenPattern::Wildcard,
                PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::Var {
                            name: "payload".to_string(),
                            id: Some(payload_id),
                        },
                        PseudoExpr::Var {
                            name: "xs".to_string(),
                            id: Some(xs_id),
                        },
                    ]
                    .into(),
                ),
            )],
        }),
    });

    assert_eq!(
        PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
            &expr,
            PipelinePassId::ExtractComplexWhenSubjects.contract(),
            true,
        ),
        None,
    );
}

#[test]
fn consistent_ref_id_contract_accepts_collapse_eta_pair_selector_when_subjects_output() {
    use crate::pseudo::ast::{Binder, WhenClause, WhenPattern};

    let pair_src_id = VarId::new(9201);
    let selector_id = VarId::new(9202);
    let rest_id = VarId::new(9203);
    let pair_value_id = VarId::new(9204);
    let left_id = VarId::new(9205);
    let k_id = VarId::new(9206);
    let expr = crate::decompile::collapse_eta_pair_selector_when_subjects(PseudoExpr::Let {
        name: "pair_src".to_string(),
        id: Some(pair_src_id),
        value: PBox::new(PseudoExpr::int(1)),
        body: PBox::new(PseudoExpr::When {
            subject: PBox::new(PseudoExpr::Lambda {
                params: vec![
                    Binder::new("sel", selector_id),
                    Binder::new("rest", rest_id),
                ],
                body: PBox::new(PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::Var {
                        name: "sel".to_string(),
                        id: Some(selector_id),
                    }),
                    args: vec![
                        PseudoExpr::Var {
                            name: "pair_src".to_string(),
                            id: Some(pair_src_id),
                        },
                        PseudoExpr::Var {
                            name: "rest".to_string(),
                            id: Some(rest_id),
                        },
                    ]
                    .into(),
                }),
            }),
            subject_name: Some(Binder::new("pair_value", pair_value_id)),
            clauses: vec![WhenClause::new(
                WhenPattern::Pair(Binder::new("left", left_id), Binder::new("k", k_id)),
                PseudoExpr::Tuple(
                    vec![
                        PseudoExpr::Var {
                            name: "pair_value".to_string(),
                            id: Some(pair_value_id),
                        },
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::Var {
                                name: "k".to_string(),
                                id: Some(k_id),
                            }),
                            args: vec![PseudoExpr::Var {
                                name: "left".to_string(),
                                id: Some(left_id),
                            }]
                            .into(),
                        },
                        PseudoExpr::Var {
                            name: "pair_src".to_string(),
                            id: Some(pair_src_id),
                        },
                    ]
                    .into(),
                ),
            )],
        }),
    });

    for pass in [
        PipelinePassId::CollapseEtaPairSelectorWhenSubjects,
        PipelinePassId::CollapseEtaPairSelectorWhenSubjectsPostReadability,
    ] {
        assert_eq!(
            PipelineExecutor::<fn(&'static str, &PseudoExpr)>::consistent_ref_id_contract_violation(
                &expr,
                pass.contract(),
                true,
            ),
            None,
            "{} should preserve consistent ref ids",
            pass.label(),
        );
    }
}

#[test]
fn eliminate_dead_lets_drops_unused_pure_bindings() {
    let live_id = VarId::new(9201);
    let dead_id = VarId::new(9202);

    let dropped = crate::decompile::eliminate_dead_lets_pseudo(PseudoExpr::Let {
        name: "dead".to_string(),
        id: Some(dead_id),
        value: PBox::new(PseudoExpr::int(0)),
        body: PBox::new(PseudoExpr::int(1)),
    });
    assert!(
        matches!(dropped, PseudoExpr::Int(_)),
        "unused pure let should be dropped, got: {dropped:?}"
    );

    let kept = crate::decompile::eliminate_dead_lets_pseudo(PseudoExpr::Let {
        name: "live".to_string(),
        id: Some(live_id),
        value: PBox::new(PseudoExpr::int(2)),
        body: PBox::new(PseudoExpr::var_with_id("live", live_id)),
    });
    assert!(
        matches!(kept, PseudoExpr::Let { .. }),
        "used let should be kept, got: {kept:?}"
    );

    let bare = PseudoExpr::int(42);
    assert_eq!(
        crate::decompile::eliminate_dead_lets_pseudo(bare.clone()),
        bare,
        "expr without lets should be unchanged"
    );
}
