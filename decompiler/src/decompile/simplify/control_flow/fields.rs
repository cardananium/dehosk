mod destructure;
mod direct_subject;
mod single_field_collapse;

use super::Simplifier;
use crate::decompile::helper::hoist::var_is_referenced_id_aware;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{PseudoExpr, PseudoType, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

impl Simplifier {
    pub(super) fn try_simplify_data_like_condition_if(
        &mut self,
        cond: &PseudoExpr,
        then_branch: &PseudoExpr,
        else_branch: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        // Convert `if var { A } else { B }` to
        // `when var is { Constr<1> -> A; _ -> B }` when the condition is a
        // Data-like constructor test rather than a real Bool.
        let PseudoExpr::Var { name, id } = cond else {
            return None;
        };

        let concrete_id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
        let uses_fields = Self::expr_accesses_fields_of(then_branch, name, concrete_id)
            || Self::expr_accesses_fields_of(else_branch, name, concrete_id);
        let branch_refs_var = var_is_referenced_id_aware(then_branch, concrete_id, name)
            || var_is_referenced_id_aware(else_branch, concrete_id, name);
        let is_data_typed = matches!(cond.type_resolution().as_deref(), Some(PseudoType::Data));

        if !(uses_fields || (is_data_typed && !branch_refs_var)) {
            return None;
        }

        Some(self.simplify_when(
            cond.clone(),
            None,
            vec![
                WhenClause {
                    pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                    guard: None,
                    body: then_branch.clone(),
                },
                WhenClause {
                    pattern: WhenPattern::Wildcard,
                    guard: None,
                    body: else_branch.clone(),
                },
            ],
        ))
    }

    /// Check if an expression accesses `.fields` on a specific variable.
    /// This proves the variable is a Data/constructor value, not a boolean.
    pub(super) fn expr_accesses_fields_of(
        expr: &PseudoExpr,
        var_name: &str,
        var_id: VarId,
    ) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(cur) = pending.pop() {
            match cur {
                PseudoExpr::FieldAccess {
                    record, selector, ..
                } => {
                    if selector.as_pretty_name() == "fields"
                        && let PseudoExpr::Var { name, id } = record.as_ref()
                        && crate::decompile::var_match::ref_matches_resolved_target(
                            name,
                            id.get(),
                            var_name,
                            var_id.get(),
                        )
                    {
                        return true;
                    }
                    pending.push(record);
                }
                PseudoExpr::IndexAccess { collection, .. } => {
                    pending.push(collection);
                }
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(body);
                    pending.push(value);
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
                PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                    pending.push(body);
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        pending.push(tail);
                    }
                    for element in elements.iter().rev() {
                        pending.push(element);
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for item in items.iter().rev() {
                        pending.push(item);
                    }
                }
                PseudoExpr::Pair(first, second) => {
                    pending.push(second);
                    pending.push(first);
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
                    }
                    pending.push(function);
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
                    }
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                PseudoExpr::UnOp { operand, .. } => {
                    pending.push(operand);
                }
                PseudoExpr::Constr { fields, .. } => {
                    for field in fields.iter().rev() {
                        pending.push(field);
                    }
                }
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                    pending.push(inner);
                }
                PseudoExpr::Trace { message, value } => {
                    pending.push(value);
                    pending.push(message);
                }
                _ => {}
            }
        }
        false
    }
}
