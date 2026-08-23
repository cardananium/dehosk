//! Nameless-pipeline tests — round-trip, end-to-end smoke, mint-site
//! populators.
//!
//! They exercise the nameless mini-pipeline on the synthetic smoke
//! hex and assert round-trip and non-growth invariants. Kept together
//! because they share the nameless-conversion helpers
//! (`run_nameless_round_trip`, `run_nameless_mini_pipeline`,
//! `run_nameless_post_pipeline_on_fixture`) and both node-count variants
//! (PseudoExpr and NamelessExpr).

#![cfg(test)]

use crate::decompile::decode_hex_to_program;
use crate::decompile::pipeline::run_pipeline_with_artifacts_opts;
use crate::decompile::tests::{MIR_V2_SMOKE_HEX, load_repo_hex_fixture};
use crate::pseudo::ast::PseudoExpr;
use crate::{DecompileOptions, ScriptVersion};

// =============================================================
// corpus round-trip property test
// =============================================================

#[allow(dead_code)] // overlay named-corpus gates
pub(crate) fn run_nameless_round_trip(fixture_name: &str, version: ScriptVersion) {
    let Some(hex) = load_repo_hex_fixture(fixture_name) else {
        return;
    };
    run_nameless_round_trip_hex(fixture_name, &hex, version);
}

pub(crate) fn run_nameless_round_trip_hex(label: &str, hex: &str, version: ScriptVersion) {
    use crate::pseudo::nameless::convert::{nameless_to_pseudo, pseudo_to_nameless};
    use crate::pseudo::nameless::invariants::validate_nameless_invariants;

    let program =
        decode_hex_to_program(hex).unwrap_or_else(|e| panic!("failed to decode {label}: {e:?}"));
    let mut opts = DecompileOptions::default();
    opts.script_version = Some(version);
    let pipeline_output = run_pipeline_with_artifacts_opts(&program, opts, |_, _| {}, false)
        .unwrap_or_else(|e| panic!("pipeline failed for {label}: {e:?}"));
    let pseudo = pipeline_output.expr;

    let (nameless, table) = pseudo_to_nameless(&pseudo);

    // Invariant: no free vars beyond entry-lambda parameters.
    let mut entry_params: std::collections::HashSet<crate::pseudo::var_id::VarId> =
        std::collections::HashSet::new();
    let mut current = &pseudo;
    loop {
        match current {
            PseudoExpr::Lambda { params, body } => {
                for p in params {
                    entry_params.insert(p.id);
                }
                current = body.as_ref();
            }
            PseudoExpr::Let { body, .. } => current = body.as_ref(),
            _ => break,
        }
    }
    // Free-var count is diagnostic, not asserted: the pipeline
    // still leaves hundreds of orphan vars, so the count is only
    // logged.
    let validation = validate_nameless_invariants(&nameless, &entry_params);
    if !validation.is_ok() {
        eprintln!(
            "[nameless baseline] fixture {label}: {} free vars",
            validation.free_vars.len()
        );
    }

    // Raise back. Render-string equality is not checked:
    // `prepare_for_render` mints fresh VarIds from a global
    // atomic counter, so two rendering passes on identical
    // input differ. That simplifier non-determinism is
    // orthogonal to the round-trip property, so node counts
    // are compared instead.
    let raised = nameless_to_pseudo(&nameless, &table);
    let pseudo_node_count = count_pseudo_nodes(&pseudo);
    let raised_node_count = count_pseudo_nodes(&raised);
    assert_eq!(
        pseudo_node_count, raised_node_count,
        "fixture {label}: round-trip node count mismatch ({pseudo_node_count} vs {raised_node_count})",
    );
}

fn count_pseudo_nodes(expr: &PseudoExpr) -> usize {
    let mut total = 1;
    match expr {
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
            total += count_pseudo_nodes(body);
        }
        PseudoExpr::Apply { function, args } => {
            total += count_pseudo_nodes(function);
            for a in args {
                total += count_pseudo_nodes(a);
            }
        }
        PseudoExpr::Let { value, body, .. } => {
            total += count_pseudo_nodes(value);
            total += count_pseudo_nodes(body);
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            total += count_pseudo_nodes(condition);
            total += count_pseudo_nodes(then_branch);
            total += count_pseudo_nodes(else_branch);
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            total += count_pseudo_nodes(subject);
            for c in clauses {
                if let Some(g) = &c.guard {
                    total += count_pseudo_nodes(g);
                }
                total += count_pseudo_nodes(&c.body);
            }
        }
        PseudoExpr::List { elements, tail } => {
            for e in elements {
                total += count_pseudo_nodes(e);
            }
            if let Some(t) = tail {
                total += count_pseudo_nodes(t);
            }
        }
        PseudoExpr::Tuple(items) => {
            for i in items {
                total += count_pseudo_nodes(i);
            }
        }
        PseudoExpr::Pair(a, b) => {
            total += count_pseudo_nodes(a);
            total += count_pseudo_nodes(b);
        }
        PseudoExpr::Constr { fields, .. } => {
            for f in fields {
                total += count_pseudo_nodes(f);
            }
        }
        PseudoExpr::FieldAccess { record, .. } => total += count_pseudo_nodes(record),
        PseudoExpr::IndexAccess { collection, .. } => total += count_pseudo_nodes(collection),
        PseudoExpr::BinOp { left, right, .. } => {
            total += count_pseudo_nodes(left);
            total += count_pseudo_nodes(right);
        }
        PseudoExpr::UnOp { operand, .. } => total += count_pseudo_nodes(operand),
        PseudoExpr::BuiltinCall { args, .. } => {
            for a in args {
                total += count_pseudo_nodes(a);
            }
        }
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => total += count_pseudo_nodes(inner),
        PseudoExpr::Trace { message, value } => {
            total += count_pseudo_nodes(message);
            total += count_pseudo_nodes(value);
        }
        _ => {}
    }
    total
}

#[test]
fn round_trip_mir_v2_smoke_hex() {
    run_nameless_round_trip_hex(
        "MIR_V2_SMOKE_HEX",
        MIR_V2_SMOKE_HEX,
        ScriptVersion::PlutusV2,
    );
}

// =============================================================
// end-to-end smoke — nameless mini-pipeline
// =============================================================
//
// Compose the leaf passes (inline_single_use →
// eliminate_dead_lets → slice_chain) on a fixture and
// assert:
//   1. The pipeline runs without panicking.
//   2. The output round-trips back to PseudoExpr cleanly.
//   3. Node count after the mini-pipeline is ≤ baseline node
//      count (passes shouldn't grow the tree).
//
// Production runs the guarded nameless post-pipeline after the
// core PseudoExpr pipeline; this standalone mini-pipeline is a
// narrower soundness gate on the leaf passes alone.

#[allow(dead_code)] // overlay named-corpus gates
pub(crate) fn run_nameless_mini_pipeline(fixture_name: &str, version: ScriptVersion) {
    use crate::decompile::dead_let_nameless::eliminate_dead_lets_nameless;
    use crate::decompile::inline::nameless::inline_single_use_nameless;
    use crate::decompile::slice_chain_nameless::inline_slice_chain_nameless;
    use crate::pseudo::nameless::convert::{nameless_to_pseudo, pseudo_to_nameless};

    let Some(hex) = load_repo_hex_fixture(fixture_name) else {
        return;
    };
    let program =
        decode_hex_to_program(&hex).unwrap_or_else(|e| panic!("decode {fixture_name}: {e:?}"));
    let mut opts = DecompileOptions::default();
    opts.script_version = Some(version);
    let pipeline_output = run_pipeline_with_artifacts_opts(&program, opts, |_, _| {}, false)
        .unwrap_or_else(|e| panic!("pipeline {fixture_name}: {e:?}"));
    let pseudo = pipeline_output.expr;

    let (nameless, table) = pseudo_to_nameless(&pseudo);
    let baseline_count = count_nameless_nodes_local(&nameless);

    // Slice-chain rewriting is metadata-driven; this standalone
    // mini-pipeline feeds it the table from the current
    // PseudoExpr snapshot to check it composes with the other
    // leaf passes.
    let after_inline = inline_single_use_nameless(nameless);
    let after_dce = eliminate_dead_lets_nameless(after_inline);
    let after_slice = inline_slice_chain_nameless(after_dce, &table);

    let final_count = count_nameless_nodes_local(&after_slice);
    assert!(
        final_count <= baseline_count,
        "fixture {fixture_name}: nameless mini-pipeline grew the tree from {baseline_count} to {final_count} nodes",
    );

    // Round-trip back to PseudoExpr should not panic.
    let _raised = nameless_to_pseudo(&after_slice, &table);

    eprintln!(
        "[nameless mini-pipeline] {fixture_name}: {baseline_count} → {final_count} nodes ({:.1}% reduction)",
        (1.0 - final_count as f64 / baseline_count as f64) * 100.0
    );
}

fn count_nameless_nodes_local(expr: &crate::pseudo::nameless::NamelessExpr) -> usize {
    use crate::pseudo::nameless::NamelessExpr as NE;
    let mut total = 1;
    match expr {
        NE::Lambda { body, .. } | NE::RecFn { body, .. } => {
            total += count_nameless_nodes_local(body)
        }
        NE::Apply { function, args } => {
            total += count_nameless_nodes_local(function);
            for a in args {
                total += count_nameless_nodes_local(a);
            }
        }
        NE::Let { value, body, .. } => {
            total += count_nameless_nodes_local(value);
            total += count_nameless_nodes_local(body);
        }
        NE::If {
            condition,
            then_branch,
            else_branch,
        } => {
            total += count_nameless_nodes_local(condition);
            total += count_nameless_nodes_local(then_branch);
            total += count_nameless_nodes_local(else_branch);
        }
        NE::When {
            subject, clauses, ..
        } => {
            total += count_nameless_nodes_local(subject);
            for c in clauses {
                if let Some(g) = &c.guard {
                    total += count_nameless_nodes_local(g);
                }
                total += count_nameless_nodes_local(&c.body);
            }
        }
        NE::List { elements, tail } => {
            for e in elements {
                total += count_nameless_nodes_local(e);
            }
            if let Some(t) = tail {
                total += count_nameless_nodes_local(t);
            }
        }
        NE::Tuple(items) => {
            for i in items {
                total += count_nameless_nodes_local(i);
            }
        }
        NE::Pair(a, b) => {
            total += count_nameless_nodes_local(a);
            total += count_nameless_nodes_local(b);
        }
        NE::Constr { fields, .. } => {
            for f in fields {
                total += count_nameless_nodes_local(f);
            }
        }
        NE::FieldAccess { record, .. } => total += count_nameless_nodes_local(record),
        NE::IndexAccess { collection, .. } => total += count_nameless_nodes_local(collection),
        NE::BinOp { left, right, .. } => {
            total += count_nameless_nodes_local(left);
            total += count_nameless_nodes_local(right);
        }
        NE::UnOp { operand, .. } => total += count_nameless_nodes_local(operand),
        NE::BuiltinCall { args, .. } => {
            for a in args {
                total += count_nameless_nodes_local(a);
            }
        }
        NE::Delay(inner) | NE::Force(inner) => total += count_nameless_nodes_local(inner),
        NE::Trace { message, value } => {
            total += count_nameless_nodes_local(message);
            total += count_nameless_nodes_local(value);
        }
        _ => {}
    }
    total
}

#[test]
fn wrap_run_nameless_post_pipeline_mir_v2_smoke_hex() {
    run_with_large_test_stack(|| {
        run_nameless_post_pipeline_on_fixture_hex(
            "MIR_V2_SMOKE_HEX",
            MIR_V2_SMOKE_HEX,
            ScriptVersion::PlutusV2,
        );
    });
}

#[allow(dead_code)] // overlay named-corpus gates
pub(crate) fn run_nameless_post_pipeline_on_fixture(fixture_name: &str) {
    let fixture_name = fixture_name.to_string();
    run_with_large_test_stack(move || {
        run_nameless_post_pipeline_on_fixture_inner(&fixture_name);
    });
}

pub(crate) fn run_with_large_test_stack<F>(f: F)
where
    F: FnOnce() + Send + 'static,
{
    let handle = std::thread::Builder::new()
        .name("wrap_large_stack".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn wrap_large_stack test thread");
    if let Err(payload) = handle.join() {
        std::panic::resume_unwind(payload);
    }
}

fn run_nameless_post_pipeline_on_fixture_inner(fixture_name: &str) {
    let Some(hex) = load_repo_hex_fixture(fixture_name) else {
        return;
    };
    run_nameless_post_pipeline_on_fixture_hex(fixture_name, &hex, ScriptVersion::PlutusV3);
}

pub(crate) fn run_nameless_post_pipeline_on_fixture_hex(
    label: &str,
    hex: &str,
    version: ScriptVersion,
) {
    let program = decode_hex_to_program(hex).unwrap_or_else(|e| panic!("decode {label}: {e:?}"));
    let mut opts = DecompileOptions::default();
    opts.script_version = Some(version);
    let pipeline_output = run_pipeline_with_artifacts_opts(&program, opts, |_, _| {}, false)
        .unwrap_or_else(|e| panic!("pipeline {label}: {e:?}"));
    let crate::decompile::pipeline::PipelineOutput {
        expr: pseudo,
        kind_annotations,
        nameless_guard_report,
        ..
    } = pipeline_output;
    assert!(
        nameless_guard_report.all_accepted(),
        "default nameless post-pipeline guards should be accepted on {label}, got: {nameless_guard_report:?}",
    );
    let baseline = pseudo_node_count(&pseudo);

    let (after, guard_report) =
        crate::decompile::nameless_post_pipeline::run_nameless_post_pipeline_with_annotations_and_guard_report(
            pseudo,
            &kind_annotations,
        );
    assert!(
        guard_report.all_accepted(),
        "nameless guards should be dormant on {label}, got: {guard_report:?}",
    );
    let after_count = pseudo_node_count(&after);
    assert!(
        after_count <= baseline,
        "nameless post-pipeline grew the tree on {label}: {baseline} → {after_count}",
    );
    eprintln!(
        "[nameless post-pipeline] {label}: {baseline} → {after_count} nodes ({:.1}% reduction)",
        (1.0 - after_count as f64 / baseline as f64) * 100.0
    );
}

fn pseudo_node_count(expr: &PseudoExpr) -> usize {
    let mut total = 1;
    match expr {
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
            total += pseudo_node_count(body);
        }
        PseudoExpr::Apply { function, args } => {
            total += pseudo_node_count(function);
            for a in args {
                total += pseudo_node_count(a);
            }
        }
        PseudoExpr::Let { value, body, .. } => {
            total += pseudo_node_count(value);
            total += pseudo_node_count(body);
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            total += pseudo_node_count(condition);
            total += pseudo_node_count(then_branch);
            total += pseudo_node_count(else_branch);
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            total += pseudo_node_count(subject);
            for c in clauses {
                total += pseudo_node_count(&c.body);
                if let Some(g) = &c.guard {
                    total += pseudo_node_count(g);
                }
            }
        }
        PseudoExpr::List { elements, tail } => {
            for e in elements {
                total += pseudo_node_count(e);
            }
            if let Some(t) = tail {
                total += pseudo_node_count(t);
            }
        }
        PseudoExpr::Tuple(items) => {
            for i in items {
                total += pseudo_node_count(i);
            }
        }
        PseudoExpr::Pair(a, b) => {
            total += pseudo_node_count(a);
            total += pseudo_node_count(b);
        }
        PseudoExpr::Constr { fields, .. } => {
            for f in fields {
                total += pseudo_node_count(f);
            }
        }
        PseudoExpr::FieldAccess { record, .. } => total += pseudo_node_count(record),
        PseudoExpr::IndexAccess { collection, .. } => total += pseudo_node_count(collection),
        PseudoExpr::BinOp { left, right, .. } => {
            total += pseudo_node_count(left);
            total += pseudo_node_count(right);
        }
        PseudoExpr::UnOp { operand, .. } => total += pseudo_node_count(operand),
        PseudoExpr::BuiltinCall { args, .. } => {
            for a in args {
                total += pseudo_node_count(a);
            }
        }
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
            total += pseudo_node_count(inner);
        }
        PseudoExpr::Trace { message, value } => {
            total += pseudo_node_count(message);
            total += pseudo_node_count(value);
        }
        _ => {}
    }
    total
}
