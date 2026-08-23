//! Inline `let X = Y[k..]` slice-chain aliases over `NamelessExpr`.
//!
//! Driven by the [`VarKind::SliceTailAlias`] metadata the binding's
//! introducer records at mint time, not by string-matching
//! `List.tail` BuiltinCalls in the AST the way the `PseudoExpr`
//! version (`render_prep::inline_slice_chain_aliases`) does.
//!
//! For every `Var(id)` tagged a slice-tail alias, substitute a
//! `List.tail` chain on its `parent`; for `IndexAccess(Var(id), n)`,
//! substitute `IndexAccess(parent, depth + n)` directly. The pass
//! fires whenever the VarTable carries that metadata, whether from
//! mint-site annotations or `kind_inference`.

use super::dead_let_nameless::has_observable_effect;
use crate::pseudo::nameless::{NamelessClause, NamelessExpr, VarKind, VarTable};
use crate::pseudo::var_id::VarId;
use std::collections::HashSet;

/// Inline `let X = Y[k..]` slice-chain aliases when `X` carries
/// the [`VarKind::SliceTailAlias`] tag.
pub(crate) fn inline_slice_chain_nameless(expr: NamelessExpr, table: &VarTable) -> NamelessExpr {
    fold(expr, table)
}

/// Build `List.tail(List.tail(...List.tail(base)))` with `depth`
/// applications.
fn make_list_tail_chain(base: NamelessExpr, depth: usize) -> NamelessExpr {
    let mut result = base;
    for _ in 0..depth {
        result = NamelessExpr::Apply {
            function: Box::new(NamelessExpr::BuiltinCall {
                name: "List.tail".to_string().into(),
                args: vec![],
            }),
            args: vec![result],
        };
    }
    result
}

/// One step: `(parent, depth)` for `id`, without resolving
/// the rest of the alias chain.
fn slice_alias(id: VarId, table: &VarTable) -> Option<(VarId, usize)> {
    match table.get(id).map(|m| &m.kind)? {
        VarKind::SliceTailAlias { parent, depth } => Some((*parent, *depth)),
        _ => None,
    }
}

fn resolve_slice_alias(id: VarId, table: &VarTable) -> Option<(VarId, usize)> {
    let mut current = id;
    let mut total_depth = 0;
    let mut seen = HashSet::new();

    while let Some((parent, depth)) = slice_alias(current, table) {
        if !seen.insert(current) {
            return None;
        }
        total_depth += depth;
        current = parent;
    }

    if current == id {
        None
    } else {
        Some((current, total_depth))
    }
}

fn fold(expr: NamelessExpr, table: &VarTable) -> NamelessExpr {
    let mut in_scope = HashSet::new();
    fold_with_mode(expr, table, true, &mut in_scope)
}

/// Scope tracking: substituting `Var(id)` → `Var(parent)` leaks a
/// free variable when `parent` is not in scope at the substitution
/// site, and the production guard `RevertedNewFreeVarIds` then rolls
/// the whole pass back. `in_scope` records every binder VarId visible
/// at the current node; the Var-arm consults it before rewriting.
fn fold_with_mode(
    expr: NamelessExpr,
    table: &VarTable,
    rewrite_aliases: bool,
    in_scope: &mut HashSet<VarId>,
) -> NamelessExpr {
    match expr {
        NamelessExpr::Var(id) => {
            // Substitute a slice-tail alias with the `List.tail`
            // chain on its parent only while `parent` is in scope;
            // otherwise the rewrite leaks a free reference.
            if rewrite_aliases
                && let Some((parent, depth)) = resolve_slice_alias(id, table)
                && in_scope.contains(&parent)
            {
                return make_list_tail_chain(NamelessExpr::Var(parent), depth);
            }
            NamelessExpr::Var(id)
        }
        NamelessExpr::IndexAccess { collection, index } => {
            if rewrite_aliases
                && let NamelessExpr::Var(id) = collection.as_ref()
                && let Some((parent, depth)) = resolve_slice_alias(*id, table)
                && in_scope.contains(&parent)
            {
                return NamelessExpr::IndexAccess {
                    collection: Box::new(NamelessExpr::Var(parent)),
                    index: depth + index,
                };
            }
            NamelessExpr::IndexAccess {
                collection: Box::new(fold_with_mode(
                    *collection,
                    table,
                    rewrite_aliases,
                    in_scope,
                )),
                index,
            }
        }
        NamelessExpr::Lambda { params, body } => {
            let newly_added = with_scope_binders(in_scope, &params);
            let body = Box::new(fold_with_mode(*body, table, rewrite_aliases, in_scope));
            release_scope_binders(in_scope, &newly_added);
            NamelessExpr::Lambda { params, body }
        }
        NamelessExpr::RecFn { name, params, body } => {
            let mut newly_added = with_scope_binders(in_scope, &params);
            if in_scope.insert(name) {
                newly_added.push(name);
            }
            let body = Box::new(fold_with_mode(*body, table, rewrite_aliases, in_scope));
            release_scope_binders(in_scope, &newly_added);
            NamelessExpr::RecFn { name, params, body }
        }
        NamelessExpr::Apply { function, args } => NamelessExpr::Apply {
            function: Box::new(fold_with_mode(*function, table, rewrite_aliases, in_scope)),
            args: args
                .into_iter()
                .map(|a| fold_with_mode(a, table, rewrite_aliases, in_scope))
                .collect(),
        },
        NamelessExpr::Let {
            binder,
            value,
            body,
        } => {
            let is_slice_alias = rewrite_aliases && resolve_slice_alias(binder, table).is_some();
            let body_uses_binder = is_slice_alias && expr_contains_var(&body, binder);
            let preserve_observable_value =
                is_slice_alias && !body_uses_binder && has_observable_effect(&value);
            let binder_was_new = in_scope.insert(binder);
            let body = fold_with_mode(*body, table, rewrite_aliases, in_scope);
            if binder_was_new {
                in_scope.remove(&binder);
            }

            // If binder is a pure slice alias, drop the let entirely;
            // body refs to the binder are unfolded by the Var-arm above.
            // Keep observable alias values so this pass cannot undo
            // dead_let_nameless' strictness/effect preservation.
            if is_slice_alias && !preserve_observable_value && !expr_contains_var(&body, binder) {
                return body;
            }
            let value = fold_with_mode(
                *value,
                table,
                rewrite_aliases && !preserve_observable_value,
                in_scope,
            );
            NamelessExpr::Let {
                binder,
                value: Box::new(value),
                body: Box::new(body),
            }
        }
        NamelessExpr::If {
            condition,
            then_branch,
            else_branch,
        } => NamelessExpr::If {
            condition: Box::new(fold_with_mode(*condition, table, rewrite_aliases, in_scope)),
            then_branch: Box::new(fold_with_mode(
                *then_branch,
                table,
                rewrite_aliases,
                in_scope,
            )),
            else_branch: Box::new(fold_with_mode(
                *else_branch,
                table,
                rewrite_aliases,
                in_scope,
            )),
        },
        NamelessExpr::When {
            subject,
            subject_name,
            clauses,
        } => {
            let subject = Box::new(fold_with_mode(*subject, table, rewrite_aliases, in_scope));
            let subject_name_added = subject_name.filter(|sn| in_scope.insert(*sn)).map(|_| ());
            let clauses: Vec<_> = clauses
                .into_iter()
                .map(|c| fold_clause(c, table, rewrite_aliases, in_scope))
                .collect();
            if subject_name_added.is_some()
                && let Some(sn) = subject_name
            {
                in_scope.remove(&sn);
            }
            NamelessExpr::When {
                subject,
                subject_name,
                clauses,
            }
        }
        NamelessExpr::List { elements, tail } => NamelessExpr::List {
            elements: elements
                .into_iter()
                .map(|e| fold_with_mode(e, table, rewrite_aliases, in_scope))
                .collect(),
            tail: tail.map(|t| Box::new(fold_with_mode(*t, table, rewrite_aliases, in_scope))),
        },
        NamelessExpr::Tuple(items) => NamelessExpr::Tuple(
            items
                .into_iter()
                .map(|i| fold_with_mode(i, table, rewrite_aliases, in_scope))
                .collect(),
        ),
        NamelessExpr::Pair(a, b) => NamelessExpr::Pair(
            Box::new(fold_with_mode(*a, table, rewrite_aliases, in_scope)),
            Box::new(fold_with_mode(*b, table, rewrite_aliases, in_scope)),
        ),
        NamelessExpr::Constr {
            type_hint,
            tag,
            fields,
            shape,
        } => NamelessExpr::Constr {
            type_hint,
            tag,
            fields: fields
                .into_iter()
                .map(|f| fold_with_mode(f, table, rewrite_aliases, in_scope))
                .collect(),
            shape,
        },
        NamelessExpr::FieldAccess { record, selector } => NamelessExpr::FieldAccess {
            record: Box::new(fold_with_mode(*record, table, rewrite_aliases, in_scope)),
            selector,
        },
        NamelessExpr::BinOp { op, left, right } => NamelessExpr::BinOp {
            op,
            left: Box::new(fold_with_mode(*left, table, rewrite_aliases, in_scope)),
            right: Box::new(fold_with_mode(*right, table, rewrite_aliases, in_scope)),
        },
        NamelessExpr::UnOp { op, operand } => NamelessExpr::UnOp {
            op,
            operand: Box::new(fold_with_mode(*operand, table, rewrite_aliases, in_scope)),
        },
        NamelessExpr::BuiltinCall { name, args } => NamelessExpr::BuiltinCall {
            name,
            args: args
                .into_iter()
                .map(|a| fold_with_mode(a, table, rewrite_aliases, in_scope))
                .collect(),
        },
        NamelessExpr::Delay(inner) => NamelessExpr::Delay(Box::new(fold_with_mode(
            *inner,
            table,
            rewrite_aliases,
            in_scope,
        ))),
        NamelessExpr::Force(inner) => NamelessExpr::Force(Box::new(fold_with_mode(
            *inner,
            table,
            rewrite_aliases,
            in_scope,
        ))),
        NamelessExpr::Trace { message, value } => NamelessExpr::Trace {
            message: Box::new(fold_with_mode(*message, table, rewrite_aliases, in_scope)),
            value: Box::new(fold_with_mode(*value, table, rewrite_aliases, in_scope)),
        },
        other => other,
    }
}

fn with_scope_binders(in_scope: &mut HashSet<VarId>, binders: &[VarId]) -> Vec<VarId> {
    let mut newly_added = Vec::with_capacity(binders.len());
    for b in binders {
        if in_scope.insert(*b) {
            newly_added.push(*b);
        }
    }
    newly_added
}

fn release_scope_binders(in_scope: &mut HashSet<VarId>, binders: &[VarId]) {
    for b in binders {
        in_scope.remove(b);
    }
}

fn fold_clause(
    clause: NamelessClause,
    table: &VarTable,
    rewrite_aliases: bool,
    in_scope: &mut HashSet<VarId>,
) -> NamelessClause {
    let pattern_binders = collect_pattern_binders(&clause.pattern);
    let newly_added = with_scope_binders(in_scope, &pattern_binders);
    let guard = clause
        .guard
        .map(|g| fold_with_mode(g, table, rewrite_aliases, in_scope));
    let body = fold_with_mode(clause.body, table, rewrite_aliases, in_scope);
    release_scope_binders(in_scope, &newly_added);
    NamelessClause {
        pattern: clause.pattern,
        guard,
        body,
    }
}

fn collect_pattern_binders(pattern: &crate::pseudo::nameless::NamelessPattern) -> Vec<VarId> {
    use crate::pseudo::nameless::NamelessPattern;
    match pattern {
        NamelessPattern::Wildcard | NamelessPattern::Literal(_) => Vec::new(),
        NamelessPattern::Var(id) => vec![*id],
        NamelessPattern::Constructor { fields, .. } | NamelessPattern::Tuple(fields) => {
            fields.clone()
        }
        NamelessPattern::List { elements, tail } => {
            let mut out = elements.clone();
            if let Some(t) = tail {
                out.push(*t);
            }
            out
        }
        NamelessPattern::Pair(a, b) => vec![*a, *b],
    }
}

fn expr_contains_var(expr: &NamelessExpr, target: VarId) -> bool {
    let mut stack = vec![expr];

    while let Some(current) = stack.pop() {
        match current {
            NamelessExpr::Var(id) => {
                if *id == target {
                    return true;
                }
            }
            NamelessExpr::Lambda { body, .. } | NamelessExpr::RecFn { body, .. } => {
                stack.push(body);
            }
            NamelessExpr::Apply { function, args } => {
                stack.push(function);
                stack.extend(args);
            }
            NamelessExpr::Let { value, body, .. } => {
                stack.push(value);
                stack.push(body);
            }
            NamelessExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.push(condition);
                stack.push(then_branch);
                stack.push(else_branch);
            }
            NamelessExpr::When {
                subject, clauses, ..
            } => {
                stack.push(subject);
                for clause in clauses {
                    if let Some(guard) = &clause.guard {
                        stack.push(guard);
                    }
                    stack.push(&clause.body);
                }
            }
            NamelessExpr::List { elements, tail } => {
                stack.extend(elements);
                if let Some(tail) = tail {
                    stack.push(tail);
                }
            }
            NamelessExpr::Tuple(items) => stack.extend(items),
            NamelessExpr::Pair(left, right) => {
                stack.push(left);
                stack.push(right);
            }
            NamelessExpr::Constr { fields, .. } => {
                stack.extend(fields);
            }
            NamelessExpr::FieldAccess { record, .. } => stack.push(record),
            NamelessExpr::IndexAccess { collection, .. } => stack.push(collection),
            NamelessExpr::BinOp { left, right, .. } => {
                stack.push(left);
                stack.push(right);
            }
            NamelessExpr::UnOp { operand, .. } => stack.push(operand),
            NamelessExpr::BuiltinCall { args, .. } => {
                stack.extend(args);
            }
            NamelessExpr::Delay(inner) | NamelessExpr::Force(inner) => stack.push(inner),
            NamelessExpr::Trace { message, value } => {
                stack.push(message);
                stack.push(value);
            }
            NamelessExpr::Int(_)
            | NamelessExpr::ByteArray(_)
            | NamelessExpr::String(_)
            | NamelessExpr::Bool(_)
            | NamelessExpr::Unit
            | NamelessExpr::Error { .. }
            | NamelessExpr::Raw { .. }
            | NamelessExpr::Data(_)
            | NamelessExpr::HelperSymbol(_) => {}
        }
    }

    false
}

#[cfg(test)]
mod tests;
