//! V3 script-context type seeding.
//!
//! After [`harvest_final_type_table`](super::harvest::harvest_final_type_table)
//! has filled the table with solved declaration types and before
//! [`enrich_function_types`](super::enrich::enrich_function_types) runs its
//! fixed-point loop, this pass seeds known Cardano-context parameter
//! types; enrichment then propagates them through Apply chains and body
//! derivation.
//!
//! Seeds the validator-entry `script_context` param as
//! `Named("ScriptContext")`, and each `let X = script_context.<field>`
//! binder per CIP-0035 (`tx_info` → `TxInfo`, `redeemer` → `Redeemer`,
//! `script_info` → `ScriptInfo`). The Named types are display-only and
//! carry no field schemas: V3 field renaming lives in
//! `cardano_context_naming.rs`, purpose-aware rendering in
//! `validator_meta.rs`. Inner fields (`tx_info.inputs`, etc.) are named
//! by the cardano-context-naming pass, not by more seeding.
//!
//! Writes only where the existing entry is Unknown or absent; concrete
//! solver-derived types are never overwritten.

use std::rc::Rc;

use crate::decompile::final_type_table::FinalTypeTable;
use crate::pseudo::ast::{PseudoExpr, PseudoType};
use crate::pseudo::var_id::VarId;

pub(super) fn seed_cardano_context_types(expr: &PseudoExpr, table: &mut FinalTypeTable) {
    let ctx = Rc::new(PseudoType::Named("ScriptContext".to_string()));
    // Seed only the validator entry Lambda's params — a helper or
    // user-named binder spelled `script_context` is not touched.
    let mut script_context_ids: Vec<VarId> = Vec::new();
    if let Some(entry_params) = find_entry_lambda_params(expr) {
        for param in entry_params {
            if param.as_str() == "script_context" {
                seed_if_absent_or_unknown(table, param.id, &ctx);
                script_context_ids.push(param.id);
            }
        }
    }

    // V3 field-level seeding: each `let X = script_context.<field>`
    // binder gets the field's CIP-0035 type.
    if !script_context_ids.is_empty() {
        seed_v3_field_let_bindings(expr, table, &script_context_ids);
    }
}

/// Walk the AST and seed let-binder types from `script_context.<field>`
/// FieldAccess values. Targets the LET BINDER's VarId so enrichment
/// picks the seeded type up via `derive_body_type(Var(let_id))`.
fn seed_v3_field_let_bindings(
    expr: &PseudoExpr,
    table: &mut FinalTypeTable,
    script_context_ids: &[VarId],
) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                if let Some(binder_id) = id
                    && let PseudoExpr::FieldAccess { record, selector } = value.as_ref()
                    && let PseudoExpr::Var {
                        id: Some(record_id),
                        ..
                    } = record.as_ref()
                    && script_context_ids.contains(record_id)
                    && let Some(field_ty) = v3_field_type(selector.as_pretty_name())
                {
                    seed_if_absent_or_unknown(table, *binder_id, &field_ty);
                }
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                for arg in args.iter().rev() {
                    pending.push(arg);
                }
                pending.push(function);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for clause in clauses.iter().rev() {
                    pending.push(&clause.body);
                    if let Some(guard) = &clause.guard {
                        pending.push(guard);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => {
                pending.push(operand);
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push(f);
                }
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push(t);
                }
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Tuple(elements) => {
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::FieldAccess { record, .. } => {
                pending.push(record);
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                pending.push(collection);
            }
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                pending.push(inner);
            }
            _ => {}
        }
    }
}

/// Maps a V3 ScriptContext field name to its CIP-0035 type.
fn v3_field_type(field_name: &str) -> Option<Rc<PseudoType>> {
    match field_name {
        "tx_info" => Some(Rc::new(PseudoType::Named("TxInfo".to_string()))),
        "redeemer" => Some(Rc::new(PseudoType::Named("Redeemer".to_string()))),
        "script_info" => Some(Rc::new(PseudoType::Named("ScriptInfo".to_string()))),
        _ => None,
    }
}

/// Locate the validator-entry Lambda's params, mirroring
/// `rename_validator_params`:
///
/// - Bare `Lambda`/`RecFn` at top level → entry params.
/// - `let X = ...; ...; body`:
///   - body is `Lambda`/`RecFn`: that's the entry.
///   - body is `Var { id }` (Var-tail): the let-prefix whose `id`
///     matches and whose value is `Lambda`/`RecFn`.
///   - body is anything else (Unit-tail, Apply-tail, ...): the LAST
///     let-prefix whose value is `Lambda`/`RecFn`.
///
/// `None` if no shape matches; the seeder then skips, leaving the
/// table untouched.
fn find_entry_lambda_params(expr: &PseudoExpr) -> Option<&[crate::pseudo::ast::Binder]> {
    use crate::pseudo::ast::Binder;
    use crate::pseudo::var_id::VarId;

    // Collect all `(let_id, &Lambda/RecFn params)` prefixes on the
    // way down, plus the tail.
    let mut prefixes: Vec<(Option<VarId>, &[Binder])> = Vec::new();
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Lambda { params, .. } => return Some(params.as_slice()),
            PseudoExpr::RecFn { params, .. } => return Some(params.as_slice()),
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                if let Some(params) = match value.as_ref() {
                    PseudoExpr::Lambda { params, .. } => Some(params.as_slice()),
                    PseudoExpr::RecFn { params, .. } => Some(params.as_slice()),
                    _ => None,
                } {
                    prefixes.push((*id, params));
                }
                current = body;
            }
            // Var-tail: pick the matching prefix by id.
            PseudoExpr::Var { id: Some(vid), .. } => {
                for (let_id, params) in prefixes.iter().rev() {
                    if *let_id == Some(*vid) {
                        return Some(params);
                    }
                }
                // No matching prefix → fall through to last-prefix
                // rule below.
                break;
            }
            _ => break,
        }
    }
    // Unit-tail / Apply-tail / etc.: pick the LAST Lambda/RecFn
    // prefix walked.
    prefixes.last().map(|(_, params)| *params)
}

fn seed_if_absent_or_unknown(table: &mut FinalTypeTable, id: VarId, ty: &Rc<PseudoType>) {
    match table.type_of_var(id) {
        None => {
            table.bind_var(id, ty.clone());
        }
        Some(existing)
            if matches!(
                existing.as_ref(),
                // `Data` and `Unknown` are both the implicit
                // default (`resolve_type` suppresses them in
                // display), so overwriting with a Named
                // protocol type is safe and adds information.
                // The V3 entry context param usually arrives as
                // `Data`: the encoded UPLC carries it raw.
                PseudoType::Unknown | PseudoType::Data
            ) =>
        {
            table.bind_var(id, ty.clone());
        }
        _ => {
            // Concrete non-Data entry from the solver — don't overwrite.
        }
    }
}

#[cfg(test)]
mod tests;
