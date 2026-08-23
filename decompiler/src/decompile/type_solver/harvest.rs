use crate::decompile::final_type_table::FinalTypeTable;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::var_id::VarId;

use super::core::TypeSolver;
use super::pattern_binders;

/// Walk the final AST and record solved declaration types into a fresh
/// `FinalTypeTable`. The table comes back unfrozen so the caller can
/// run enrichment passes before freezing it.
pub(super) fn harvest_final_type_table(expr: &PseudoExpr, solver: &TypeSolver) -> FinalTypeTable {
    let mut table = FinalTypeTable::new();
    collect_declaration_types(expr, solver, &mut table);
    table
}

/// One pending step of [`collect_declaration_types`]'s explicit stack.
///
/// `record` calls are immediate side effects, not subtrees, so most of them
/// happen inline as a step is entered; only `When`'s subject-name binder —
/// recorded strictly AFTER the subject subtree and BEFORE the clauses — needs
/// a step of its own to land at the right point in the pop order.
enum Step<'a> {
    Visit(&'a PseudoExpr),
    RecordSubjectName(&'a Binder),
    EnterClause(&'a WhenClause),
}

/// Record each declaration `VarId`'s solved type into `table` when the
/// solver committed to a concrete `PseudoType`.
///
/// Declaration ids are distinct by construction, so the walk needs no
/// shadowing; reference `PseudoExpr::Var` nodes are skipped entirely.
fn collect_declaration_types(expr: &PseudoExpr, solver: &TypeSolver, table: &mut FinalTypeTable) {
    let record = |id: VarId, table: &mut FinalTypeTable| {
        if let Some(ty) = solver.solved_type_of_var(id) {
            table.bind_var(id, ty);
        }
    };

    let mut pending: Vec<Step<'_>> = vec![Step::Visit(expr)];
    while let Some(step) = pending.pop() {
        match step {
            Step::Visit(expr) => match expr {
                PseudoExpr::Let {
                    id, value, body, ..
                } => {
                    if let Some(vid) = *id {
                        record(vid, table);
                    }
                    pending.push(Step::Visit(body));
                    pending.push(Step::Visit(value));
                }
                PseudoExpr::Lambda { params, body } => {
                    for param in params {
                        record(param.id, table);
                    }
                    pending.push(Step::Visit(body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    record(name.id, table);
                    for param in params {
                        record(param.id, table);
                    }
                    pending.push(Step::Visit(body));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    for clause in clauses.iter().rev() {
                        pending.push(Step::EnterClause(clause));
                    }
                    if let Some(subject_name) = subject_name {
                        pending.push(Step::RecordSubjectName(subject_name));
                    }
                    pending.push(Step::Visit(subject));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(Step::Visit(else_branch));
                    pending.push(Step::Visit(then_branch));
                    pending.push(Step::Visit(condition));
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        pending.push(Step::Visit(arg));
                    }
                    pending.push(Step::Visit(function));
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(Step::Visit(right));
                    pending.push(Step::Visit(left));
                }
                PseudoExpr::UnOp { operand, .. } => {
                    pending.push(Step::Visit(operand));
                }
                PseudoExpr::Constr { fields, .. } => {
                    for field in fields.iter().rev() {
                        pending.push(Step::Visit(field));
                    }
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    for arg in args.iter().rev() {
                        pending.push(Step::Visit(arg));
                    }
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        pending.push(Step::Visit(t));
                    }
                    for element in elements.iter().rev() {
                        pending.push(Step::Visit(element));
                    }
                }
                PseudoExpr::Tuple(elements) => {
                    for element in elements.iter().rev() {
                        pending.push(Step::Visit(element));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    pending.push(Step::Visit(b));
                    pending.push(Step::Visit(a));
                }
                PseudoExpr::FieldAccess { record, .. } => {
                    pending.push(Step::Visit(record));
                }
                PseudoExpr::IndexAccess { collection, .. } => {
                    pending.push(Step::Visit(collection));
                }
                PseudoExpr::Trace { message, value } => {
                    pending.push(Step::Visit(value));
                    pending.push(Step::Visit(message));
                }
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                    pending.push(Step::Visit(inner));
                }
                PseudoExpr::Var { .. }
                | PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit => {}
                _ => {}
            },
            Step::RecordSubjectName(subject_name) => {
                record(subject_name.id, table);
            }
            Step::EnterClause(clause) => {
                for binder in pattern_binders(&clause.pattern) {
                    record(binder.id, table);
                }
                pending.push(Step::Visit(&clause.body));
                if let Some(guard) = &clause.guard {
                    pending.push(Step::Visit(guard));
                }
            }
        }
    }
}
