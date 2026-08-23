//! Monomorphic builtin arg-type seeding.
//!
//! For every `BuiltinCall { name, args }` whose `monomorphic_arg_types()`
//! is `Some(sig)`, each arg of the form `Var { id: Some(vid) }` at position
//! `i` gets its `vid` table entry refined to `sig[i]`: concrete wins over
//! Unknown / Data, and concrete is never demoted.
//!
//! Conservative scope: only monomorphic builtins — polymorphic ones
//! (`ListHead/Tail`, `IfThenElse`, `Trace`, ...) need type-variable
//! propagation — and only direct `Var` args; nested expressions are left
//! to the enrichment pass.
//!
//! Runs after
//! [`seed_cardano_context_types`](super::seed_cardano::seed_cardano_context_types)
//! and before `enrich_function_types`, so the enrichment fixed-point can
//! propagate the newly anchored types through Apply chains.

use std::rc::Rc;

use crate::decompile::final_type_table::FinalTypeTable;
use crate::pseudo::ast::{PseudoExpr, PseudoType};
use crate::pseudo::var_id::VarId;

pub(super) fn seed_builtin_arg_types(expr: &PseudoExpr, table: &mut FinalTypeTable) {
    walk(expr, table);
}

fn walk(expr: &PseudoExpr, table: &mut FinalTypeTable) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if let PseudoExpr::BuiltinCall { name, args } = expr
            && let Some(sig) = name.monomorphic_arg_types()
            && sig.len() == args.len()
        {
            for (i, arg) in args.iter().enumerate() {
                if let PseudoExpr::Var { id: Some(vid), .. } = arg {
                    seed_arg_type(table, *vid, &sig[i]);
                }
            }
        }

        let kids: Vec<&PseudoExpr> = match expr {
            PseudoExpr::Let { value, body, .. } => vec![value, body],
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => vec![body],
            PseudoExpr::Apply { function, args } => {
                let mut v = vec![function.as_ref()];
                v.extend(args.iter());
                v
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => vec![condition, then_branch, else_branch],
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                let mut v = vec![subject.as_ref()];
                for clause in clauses {
                    if let Some(guard) = &clause.guard {
                        v.push(guard);
                    }
                    v.push(&clause.body);
                }
                v
            }
            PseudoExpr::BinOp { left, right, .. } => vec![left, right],
            PseudoExpr::UnOp { operand, .. } => vec![operand],
            PseudoExpr::Constr { fields, .. } => fields.iter().collect(),
            PseudoExpr::BuiltinCall { args, .. } => args.iter().collect(),
            PseudoExpr::List { elements, tail } => {
                let mut v: Vec<&PseudoExpr> = elements.iter().collect();
                if let Some(t) = tail {
                    v.push(t);
                }
                v
            }
            PseudoExpr::Tuple(elements) => elements.iter().collect(),
            PseudoExpr::Pair(a, b) => vec![a, b],
            PseudoExpr::FieldAccess { record, .. } => vec![record],
            PseudoExpr::IndexAccess { collection, .. } => vec![collection],
            PseudoExpr::Trace { message, value } => vec![message, value],
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => vec![inner],
            _ => vec![],
        };
        pending.extend(kids.into_iter().rev());
    }
}

fn seed_arg_type(table: &mut FinalTypeTable, id: VarId, ty: &PseudoType) {
    match table.type_of_var(id) {
        None => {
            table.bind_var(id, Rc::new(ty.clone()));
        }
        Some(existing)
            if matches!(
                existing.as_ref(),
                // Same "implicit default" rule as seed_cardano: both
                // Unknown and Data are overwritable since `resolve_type`
                // display-suppresses them identically.
                PseudoType::Unknown | PseudoType::Data
            ) =>
        {
            table.bind_var(id, Rc::new(ty.clone()));
        }
        _ => {
            // Concrete non-Data type: never demote.
        }
    }
}

#[cfg(test)]
mod tests;
