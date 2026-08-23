use std::collections::HashSet;

use super::super::postprocess::{context_field_type_from_display_name, seed_context_field_names};
use super::super::{Simplifier, SimplifyOutput, SimplifyState};
use crate::decompile::ScriptVersion;
use crate::decompile::mid::type_env::TypeEnvironment;
use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::var_id::OptionVarIdGet;

/// Names currently Let-bound anywhere in `expr`. Seeds
/// `Simplifier::global_used_names` at the start of each pass so collision
/// detection reflects the current binding landscape rather than a set
/// accumulated across every prior fixed-point iteration.
fn collect_let_binding_names(expr: &PseudoExpr) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut stack = vec![expr];
    while let Some(current) = stack.pop() {
        match current {
            PseudoExpr::Let {
                name, value, body, ..
            } => {
                names.insert(name.clone());
                stack.push(value.as_ref());
                stack.push(body.as_ref());
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                stack.push(body.as_ref());
            }
            PseudoExpr::Apply { function, args } => {
                stack.push(function.as_ref());
                for arg in args {
                    stack.push(arg);
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.push(condition.as_ref());
                stack.push(then_branch.as_ref());
                stack.push(else_branch.as_ref());
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                stack.push(subject.as_ref());
                for clause in clauses {
                    if let WhenPattern::Literal(lit) = &clause.pattern {
                        stack.push(lit);
                    }
                    if let Some(guard) = &clause.guard {
                        stack.push(guard);
                    }
                    stack.push(&clause.body);
                }
            }
            PseudoExpr::List { elements, tail } => {
                for element in elements {
                    stack.push(element);
                }
                if let Some(tail) = tail {
                    stack.push(tail.as_ref());
                }
            }
            PseudoExpr::Tuple(elements) => {
                for element in elements {
                    stack.push(element);
                }
            }
            PseudoExpr::Pair(left, right) => {
                stack.push(left.as_ref());
                stack.push(right.as_ref());
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields {
                    stack.push(field);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => stack.push(record.as_ref()),
            PseudoExpr::IndexAccess { collection, .. } => stack.push(collection.as_ref()),
            PseudoExpr::BinOp { left, right, .. } => {
                stack.push(left.as_ref());
                stack.push(right.as_ref());
            }
            PseudoExpr::UnOp { operand, .. } => stack.push(operand.as_ref()),
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    stack.push(arg);
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => stack.push(inner.as_ref()),
            PseudoExpr::Trace { message, value } => {
                stack.push(message.as_ref());
                stack.push(value.as_ref());
            }
            PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
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
    names
}

fn max_var_id_in_expr(expr: &PseudoExpr) -> u32 {
    let mut max_id = 0u32;
    let mut stack = vec![expr];
    while let Some(current) = stack.pop() {
        match current {
            PseudoExpr::Var { id, .. } | PseudoExpr::Let { id, .. } => {
                if let Some(vid) = id.get() {
                    max_id = max_id.max(vid.as_u32());
                }
            }
            _ => {}
        }
        match current {
            PseudoExpr::Let { value, body, .. } => {
                stack.push(value.as_ref());
                stack.push(body.as_ref());
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                stack.push(body.as_ref());
            }
            PseudoExpr::Apply { function, args } => {
                stack.push(function.as_ref());
                for arg in args {
                    stack.push(arg);
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.push(condition.as_ref());
                stack.push(then_branch.as_ref());
                stack.push(else_branch.as_ref());
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                stack.push(subject.as_ref());
                for clause in clauses {
                    if let WhenPattern::Literal(lit) = &clause.pattern {
                        stack.push(lit);
                    }
                    if let Some(guard) = &clause.guard {
                        stack.push(guard);
                    }
                    stack.push(&clause.body);
                }
            }
            PseudoExpr::List { elements, tail } => {
                for element in elements {
                    stack.push(element);
                }
                if let Some(tail) = tail {
                    stack.push(tail.as_ref());
                }
            }
            PseudoExpr::Tuple(elements) => {
                for element in elements {
                    stack.push(element);
                }
            }
            PseudoExpr::Pair(left, right) => {
                stack.push(left.as_ref());
                stack.push(right.as_ref());
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields {
                    stack.push(field);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => stack.push(record.as_ref()),
            PseudoExpr::IndexAccess { collection, .. } => stack.push(collection.as_ref()),
            PseudoExpr::BinOp { left, right, .. } => {
                stack.push(left.as_ref());
                stack.push(right.as_ref());
            }
            PseudoExpr::UnOp { operand, .. } => stack.push(operand.as_ref()),
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    stack.push(arg);
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => stack.push(inner.as_ref()),
            PseudoExpr::Trace { message, value } => {
                stack.push(message.as_ref());
                stack.push(value.as_ref());
            }
            PseudoExpr::Var { .. } => {}
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
    max_id
}

#[cfg(test)] // exercised only by the suite; production takes another entry point
/// Simplify an expression tree; discards the simplification context.
pub(crate) fn simplify(expr: PseudoExpr) -> PseudoExpr {
    simplify_with_options(expr, false)
}

#[cfg(test)] // exercised only by the suite; production takes another entry point
/// Simplify with explicit mode flags; discards the simplification context.
pub(crate) fn simplify_with_options(expr: PseudoExpr, safe_mode: bool) -> PseudoExpr {
    simplify_with_state(expr, None, safe_mode, None, &mut SimplifyState::default()).expr
}

#[cfg(test)] // exercised only by the suite; production takes another entry point
/// Simplify with persistent state carried across passes.
/// `state.booleans` accumulates boolean helper metadata across calls so
/// later passes can convert `force(and_fn(a, delay(b)))` -> `a && b`.
///
/// `env` is unused — the `refine_var_tipo_with_env` pre-pass that consumed
/// it is a no-op without inline `tipo` fields on `PseudoExpr` — but it
/// stays in the signature to keep call sites stable.
///
/// Returns the simplified expression plus the context data `run_pipeline`
/// needs for its post-processing steps.
pub(crate) fn simplify_with_state(
    expr: PseudoExpr,
    _env: Option<&TypeEnvironment>,
    safe_mode: bool,
    script_version: Option<ScriptVersion>,
    state: &mut SimplifyState,
) -> SimplifyOutput {
    simplify_with_state_opts(expr, _env, safe_mode, script_version, false, state)
}

/// `simplify_with_state` plus `use_varkind_recovery`, which lets
/// in-simplifier recovery passes (currently `single_field_collapse`)
/// dispatch by VarKind.
pub(crate) fn simplify_with_state_opts(
    expr: PseudoExpr,
    _env: Option<&TypeEnvironment>,
    safe_mode: bool,
    script_version: Option<ScriptVersion>,
    use_varkind_recovery: bool,
    state: &mut SimplifyState,
) -> SimplifyOutput {
    let mut simplifier = Simplifier::with_safe_mode(safe_mode);
    simplifier.use_varkind_recovery = use_varkind_recovery;
    seed_simplifier_from_state(&mut simplifier, &expr, script_version, state);

    let expr = simplifier.simplify(expr);

    harvest_simplifier_into_state(expr, simplifier, state)
}

fn seed_simplifier_from_state(
    simplifier: &mut Simplifier,
    expr: &PseudoExpr,
    script_version: Option<ScriptVersion>,
    state: &SimplifyState,
) {
    simplifier.script_version = script_version;
    simplifier.church_polarity = state.church_polarity;
    state.identity.seed_tracking(
        &mut simplifier.identity,
        max_var_id_in_expr(expr).saturating_add(1),
    );

    // Bidirectional carryover: seeded from persistent state and harvested
    // back after the pass.
    state.booleans.seed_tracking(&mut simplifier.booleans);
    state.recursion.seed_tracking(&mut simplifier.recursion);
    state.naming.seed_tracking(&mut simplifier.naming);
    // seed mint-site VarKind annotations so passes that
    // re-run on fixed-point iterations don't lose kind tags.
    state.var_kinds.seed_tracking(&mut simplifier.var_kinds);

    // Seed-only inputs: MIR/pipeline metadata used by this pass but not
    // discovered by simplification itself.
    state
        .constructors
        .seed_tracking(&mut simplifier.constructors);
    state.helpers.seed_tracking(&mut simplifier.helpers);

    // Seed `global_used_names` from the names currently Let-bound in the
    // input expression, not from a monotonic history set: a set of every
    // name ever assigned - including bindings since inlined out - drifts
    // deduped names like `int_1` to `int_2`, `int_3`, ... each iteration.
    simplifier.global_used_names = collect_let_binding_names(expr);

    // Output-only context tracking restarts from each pass's input expression:
    // top-level lambda params give the original names (e.g. "y_25") standing
    // for script_context/redeemer/datum, so field propagation can follow them.
    if let Some(version) = script_version {
        seed_context_field_names(expr, version, &mut simplifier.context.context_field_names);
        // Also seed well-known semantic names for subsequent passes where
        // params/vars have already been renamed.
        for name in &[
            "script_context",
            "tx_info",
            "purpose",
            "redeemer",
            "script_info",
            "datum",
        ] {
            simplifier
                .context
                .context_field_names
                .insert(name.to_string(), name.to_string());
        }
        // Seed types for well-known context variables so deeper field accesses
        // can be resolved even in later passes.
        for name in &[
            "script_context",
            "tx_info",
            "inputs",
            "reference_inputs",
            "outputs",
            "valid_range",
            "out_ref",
            "resolved",
            "address",
            "lower_bound",
            "upper_bound",
            "output_reference",
        ] {
            if let Some(var_type) = context_field_type_from_display_name(name, version) {
                simplifier
                    .context
                    .context_var_types
                    .insert(name.to_string(), var_type.display_name().to_string());
            }
        }
    }
}

fn harvest_simplifier_into_state(
    expr: PseudoExpr,
    simplifier: Simplifier,
    state: &mut SimplifyState,
) -> SimplifyOutput {
    // Output-only context maps are returned to post-processing but are not
    // persisted in `SimplifyState`.
    let context_field_names = simplifier.context.context_field_names;
    let context_var_types = simplifier.context.context_var_types;
    let context_field_names_by_id = simplifier.context.context_field_names_by_id;
    let context_var_types_by_id = simplifier.context.context_var_types_by_id;

    // Harvest bidirectional carryover. Seed-only state such as
    // `constr_unpack_subjects` and `preserved_helper_ids` is intentionally not
    // written back here.
    state.booleans.harvest_from_tracking(simplifier.booleans);
    state.recursion.harvest_from_tracking(simplifier.recursion);
    state.identity.harvest_from_tracking(simplifier.identity);
    state.naming.harvest_from_tracking(simplifier.naming);
    // `global_used_names` is deliberately NOT carried; it is reseeded from
    // the next pass's input to stay a snapshot of currently-bound names.
    // Propagate mint-site VarKind annotations out.
    state.var_kinds.harvest_from_tracking(simplifier.var_kinds);

    SimplifyOutput {
        expr,
        context_field_names,
        context_var_types,
        context_field_names_by_id,
        context_var_types_by_id,
    }
}
