//! Optional-detection helpers used by `pretty.rs`.
//!
//! `collect_expect_sugar_positions` finds `when` nodes in statement
//!   position so the renderer can collapse single-branch patterns into
//!   `expect!` sugar.
//! `try_match_sorted_assoc_lookup_if` recognizes the sorted-assoc lookup
//!   if-chain and returns the projection the renderer emits as
//!   `if eq { ... } else if cutoff { None } else { ... }`.

use std::collections::HashSet;

use super::dispatch::is_display_option_none_candidate;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};

pub(in crate::decompile::render) fn collect_expect_sugar_positions(
    expr: &PseudoExpr,
) -> HashSet<usize> {
    enum Task<'a> {
        Enter(&'a PseudoExpr, bool),
    }

    fn push_children<'a>(
        stack: &mut Vec<Task<'a>>,
        nodes: impl IntoIterator<Item = &'a PseudoExpr>,
        in_statement: bool,
    ) {
        for node in nodes {
            stack.push(Task::Enter(node, in_statement));
        }
    }

    let mut positions = HashSet::new();
    let mut stack = vec![Task::Enter(expr, true)];

    while let Some(Task::Enter(node, in_statement)) = stack.pop() {
        if in_statement && matches!(node, PseudoExpr::When { .. }) {
            positions.insert(node as *const PseudoExpr as usize);
        }

        match node {
            PseudoExpr::Let { value, body, .. } => {
                stack.push(Task::Enter(body.as_ref(), true));
                stack.push(Task::Enter(value.as_ref(), false));
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                stack.push(Task::Enter(body.as_ref(), true));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.push(Task::Enter(else_branch.as_ref(), true));
                stack.push(Task::Enter(then_branch.as_ref(), true));
                stack.push(Task::Enter(condition.as_ref(), false));
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for clause in clauses.iter().rev() {
                    stack.push(Task::Enter(&clause.body, true));
                    if let Some(guard) = &clause.guard {
                        stack.push(Task::Enter(guard, false));
                    }
                }
                stack.push(Task::Enter(subject.as_ref(), false));
            }
            PseudoExpr::Apply { function, args } => {
                if let PseudoExpr::BuiltinCall {
                    name,
                    args: builtin_args,
                } = function.as_ref()
                    && *name == crate::BuiltinId::Seq
                    && builtin_args.is_empty()
                    && args.len() == 2
                {
                    // seq(a, b): both are statement positions.
                    stack.push(Task::Enter(&args[1], true));
                    stack.push(Task::Enter(&args[0], true));
                    continue;
                }

                for arg in args.iter().rev() {
                    stack.push(Task::Enter(arg, false));
                }
                stack.push(Task::Enter(function.as_ref(), false));
            }
            PseudoExpr::BuiltinCall { name, args } => {
                if *name == crate::BuiltinId::Seq && args.len() == 2 {
                    stack.push(Task::Enter(&args[1], true));
                    stack.push(Task::Enter(&args[0], true));
                    continue;
                }
                for arg in args.iter().rev() {
                    stack.push(Task::Enter(arg, false));
                }
            }
            PseudoExpr::Trace { message, value } => {
                stack.push(Task::Enter(value.as_ref(), true));
                stack.push(Task::Enter(message.as_ref(), false));
            }
            PseudoExpr::BinOp { op, left, right } => {
                // In && chains, operands are rendered as sequential statements,
                // so expect sugar is valid in both positions.
                let child_stmt = matches!(op, BinaryOp::And);
                stack.push(Task::Enter(right.as_ref(), child_stmt));
                stack.push(Task::Enter(left.as_ref(), child_stmt));
            }
            PseudoExpr::Pair(left, right) => {
                stack.push(Task::Enter(right.as_ref(), false));
                stack.push(Task::Enter(left.as_ref(), false));
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand)
            | PseudoExpr::FieldAccess {
                record: operand, ..
            }
            | PseudoExpr::IndexAccess {
                collection: operand,
                ..
            } => {
                stack.push(Task::Enter(operand.as_ref(), false));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    stack.push(Task::Enter(t.as_ref(), false));
                }
                push_children(&mut stack, elements.iter().rev(), false);
            }
            PseudoExpr::Tuple(elements) => {
                push_children(&mut stack, elements.iter().rev(), false);
            }
            PseudoExpr::Constr { fields, .. } => {
                push_children(&mut stack, fields.iter().rev(), false);
            }
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }

    positions
}

pub(in crate::decompile::render) struct SortedAssocLookupIf<'a> {
    pub(in crate::decompile::render) eq_condition: &'a PseudoExpr,
    pub(in crate::decompile::render) some_branch: &'a PseudoExpr,
    pub(in crate::decompile::render) cutoff_op: BinaryOp,
    pub(in crate::decompile::render) cutoff_left: &'a PseudoExpr,
    pub(in crate::decompile::render) cutoff_right: &'a PseudoExpr,
    pub(in crate::decompile::render) none_branch: &'a PseudoExpr,
    pub(in crate::decompile::render) final_else: &'a PseudoExpr,
}

pub(in crate::decompile::render) fn try_match_sorted_assoc_lookup_if<'a>(
    condition: &'a PseudoExpr,
    then_branch: &'a PseudoExpr,
    else_branch: &'a PseudoExpr,
) -> Option<SortedAssocLookupIf<'a>> {
    let (lt_op, left, right) = match condition {
        PseudoExpr::BinOp { op, left, right } => match op {
            BinaryOp::Lte => (BinaryOp::Lt, left.as_ref(), right.as_ref()),
            BinaryOp::Gte => (BinaryOp::Gt, left.as_ref(), right.as_ref()),
            _ => return None,
        },
        _ => return None,
    };

    let PseudoExpr::If {
        condition: inner_condition,
        then_branch: inner_then,
        else_branch: inner_else,
    } = then_branch
    else {
        return None;
    };

    if !is_display_option_none_candidate(inner_else.as_ref()) {
        return None;
    }

    let matches_eq = matches!(
        inner_condition.as_ref(),
        PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left: eq_left,
            right: eq_right,
        } if (eq_left.as_ref().structural_eq(left) && eq_right.as_ref().structural_eq(right))
            || (eq_left.as_ref().structural_eq(right) && eq_right.as_ref().structural_eq(left))
    );
    if !matches_eq {
        return None;
    }

    Some(SortedAssocLookupIf {
        eq_condition: inner_condition.as_ref(),
        some_branch: inner_then.as_ref(),
        cutoff_op: lt_op,
        cutoff_left: left,
        cutoff_right: right,
        none_branch: inner_else.as_ref(),
        final_else: else_branch,
    })
}
