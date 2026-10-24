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
use crate::pseudo::nameless::{
    NBox, NClauses, NamelessClause, NamelessExpr, NamelessPattern, VarKind, VarTable,
};
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
            function: NBox::new(NamelessExpr::BuiltinCall {
                name: "List.tail".to_string().into(),
                args: vec![].into(),
            }),
            args: vec![result].into(),
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

/// One pending step of [`fold_with_mode`]. `rewrite` is the alias-rewrite
/// mode a subtree folds in: it travels with the step, since a preserved
/// observable `let` value folds with rewriting off.
enum SliceStep {
    /// Fold this subtree.
    Visit { expr: NamelessExpr, rewrite: bool },
    /// The `let` body is folded and on top of `done`: take the binder out of
    /// scope, then drop the `let` or fold its value.
    LetAfterBody {
        binder: VarId,
        value: NamelessExpr,
        is_slice_alias: bool,
        preserve_observable_value: bool,
        binder_was_new: bool,
        rewrite: bool,
    },
    /// The `let` body and value are on `done`: reassemble the `Let`.
    LetBuild { binder: VarId },
    /// The `when` subject is folded: bring the subject name into scope, then
    /// fold the clauses in order.
    WhenClauses {
        subject_name: Option<VarId>,
        clauses: NClauses,
        rewrite: bool,
    },
    /// Bring a clause's pattern binders into scope, then fold its guard and
    /// body.
    Clause {
        clause: NamelessClause,
        rewrite: bool,
    },
    /// A clause's guard and body are on `done`: release its binders and
    /// reassemble it.
    ClauseDone {
        pattern: NamelessPattern,
        has_guard: bool,
        newly_added: Vec<VarId>,
    },
    /// The clauses and the subject are on their stacks: release the subject
    /// name and reassemble the `When`.
    WhenDone {
        subject_name: Option<VarId>,
        clause_count: usize,
        subject_name_added: bool,
    },
    /// Every other node: its folded children are on `done`; put them back
    /// into the shell they were taken out of, then release the binders the
    /// node brought into scope.
    Rebuild {
        shell: NamelessExpr,
        count: usize,
        release: Vec<VarId>,
    },
}

/// Scope tracking: substituting `Var(id)` → `Var(parent)` leaks a
/// free variable when `parent` is not in scope at the substitution
/// site, and the production guard `RevertedNewFreeVarIds` then rolls
/// the whole pass back. `in_scope` records every binder VarId visible
/// at the current node; the Var-arm consults it before rewriting.
///
/// Runs on a heap stack: nesting depth is script-controlled, and on
/// `wasm32` the engine's call stack cannot be grown to match. The steps
/// keep a recursive descent's order — a `let` body before its value, which
/// folds once the binder is out of scope again.
fn fold_with_mode(
    expr: NamelessExpr,
    table: &VarTable,
    rewrite_aliases: bool,
    in_scope: &mut HashSet<VarId>,
) -> NamelessExpr {
    let mut steps: Vec<SliceStep> = vec![SliceStep::Visit {
        expr,
        rewrite: rewrite_aliases,
    }];
    let mut done: Vec<NamelessExpr> = Vec::new();
    // LIFO like `done`: a clause's subtree (and any `when` nested in it)
    // completes before the next clause step runs.
    let mut clauses_done: Vec<NamelessClause> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            SliceStep::Visit { expr, rewrite } => {
                if rewrite && let Some(substituted) = substitute_alias_use(&expr, table, in_scope) {
                    done.push(substituted);
                    continue;
                }
                match expr {
                    NamelessExpr::Let {
                        binder,
                        value,
                        body,
                    } => {
                        let is_slice_alias =
                            rewrite && resolve_slice_alias(binder, table).is_some();
                        let body_uses_binder = is_slice_alias && expr_contains_var(&body, binder);
                        let preserve_observable_value =
                            is_slice_alias && !body_uses_binder && has_observable_effect(&value);
                        let binder_was_new = in_scope.insert(binder);
                        steps.push(SliceStep::LetAfterBody {
                            binder,
                            value: value.into_inner(),
                            is_slice_alias,
                            preserve_observable_value,
                            binder_was_new,
                            rewrite,
                        });
                        steps.push(SliceStep::Visit {
                            expr: body.into_inner(),
                            rewrite,
                        });
                    }
                    NamelessExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        steps.push(SliceStep::WhenClauses {
                            subject_name,
                            clauses,
                            rewrite,
                        });
                        steps.push(SliceStep::Visit {
                            expr: subject.into_inner(),
                            rewrite,
                        });
                    }
                    mut node => {
                        let release = match &node {
                            NamelessExpr::Lambda { params, .. } => {
                                with_scope_binders(in_scope, params)
                            }
                            NamelessExpr::RecFn { name, params, .. } => {
                                let mut newly_added = with_scope_binders(in_scope, params);
                                if in_scope.insert(*name) {
                                    newly_added.push(*name);
                                }
                                newly_added
                            }
                            _ => Vec::new(),
                        };
                        let kids: Vec<NamelessExpr> = node
                            .child_slots_mut()
                            .into_iter()
                            .map(|slot| std::mem::replace(slot, NamelessExpr::Unit))
                            .collect();
                        if kids.is_empty() {
                            // A leaf: nothing to fold, and it binds nothing.
                            done.push(node);
                            continue;
                        }
                        steps.push(SliceStep::Rebuild {
                            shell: node,
                            count: kids.len(),
                            release,
                        });
                        // Reversed so they pop — and so land on `done` — in order.
                        for kid in kids.into_iter().rev() {
                            steps.push(SliceStep::Visit { expr: kid, rewrite });
                        }
                    }
                }
            }
            SliceStep::LetAfterBody {
                binder,
                value,
                is_slice_alias,
                preserve_observable_value,
                binder_was_new,
                rewrite,
            } => {
                let body = done.pop().expect("let body");
                if binder_was_new {
                    in_scope.remove(&binder);
                }

                // If binder is a pure slice alias, drop the let entirely;
                // body refs to the binder are unfolded by the Var-arm above.
                // Keep observable alias values so this pass cannot undo
                // dead_let_nameless' strictness/effect preservation.
                let drop_let = is_slice_alias
                    && !preserve_observable_value
                    && !expr_contains_var(&body, binder);
                done.push(body);
                if !drop_let {
                    steps.push(SliceStep::LetBuild { binder });
                    steps.push(SliceStep::Visit {
                        expr: value,
                        rewrite: rewrite && !preserve_observable_value,
                    });
                }
            }
            SliceStep::LetBuild { binder } => {
                let value = done.pop().expect("let value");
                let body = done.pop().expect("let body");
                done.push(NamelessExpr::Let {
                    binder,
                    value: NBox::new(value),
                    body: NBox::new(body),
                });
            }
            SliceStep::WhenClauses {
                subject_name,
                clauses,
                rewrite,
            } => {
                let subject_name_added = subject_name.is_some_and(|sn| in_scope.insert(sn));
                steps.push(SliceStep::WhenDone {
                    subject_name,
                    clause_count: clauses.len(),
                    subject_name_added,
                });
                for clause in clauses.into_iter().rev() {
                    steps.push(SliceStep::Clause { clause, rewrite });
                }
            }
            SliceStep::Clause { clause, rewrite } => {
                let pattern_binders = collect_pattern_binders(&clause.pattern);
                let newly_added = with_scope_binders(in_scope, &pattern_binders);
                let NamelessClause {
                    pattern,
                    guard,
                    body,
                } = clause;
                steps.push(SliceStep::ClauseDone {
                    pattern,
                    has_guard: guard.is_some(),
                    newly_added,
                });
                steps.push(SliceStep::Visit {
                    expr: body,
                    rewrite,
                });
                if let Some(guard) = guard {
                    steps.push(SliceStep::Visit {
                        expr: guard,
                        rewrite,
                    });
                }
            }
            SliceStep::ClauseDone {
                pattern,
                has_guard,
                newly_added,
            } => {
                let body = done.pop().expect("clause body");
                let guard = has_guard.then(|| done.pop().expect("clause guard"));
                release_scope_binders(in_scope, &newly_added);
                clauses_done.push(NamelessClause {
                    pattern,
                    guard,
                    body,
                });
            }
            SliceStep::WhenDone {
                subject_name,
                clause_count,
                subject_name_added,
            } => {
                let at = clauses_done.len() - clause_count;
                let clauses = clauses_done.split_off(at);
                let subject = done.pop().expect("when subject");
                if subject_name_added && let Some(sn) = subject_name {
                    in_scope.remove(&sn);
                }
                done.push(NamelessExpr::When {
                    subject: NBox::new(subject),
                    subject_name,
                    clauses: clauses.into(),
                });
            }
            SliceStep::Rebuild {
                mut shell,
                count,
                release,
            } => {
                let at = done.len() - count;
                let kids = done.split_off(at);
                for (slot, kid) in shell.child_slots_mut().into_iter().zip(kids) {
                    *slot = kid;
                }
                release_scope_binders(in_scope, &release);
                done.push(shell);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the fold machine must leave one result");
    debug_assert!(clauses_done.is_empty(), "all clauses must be consumed");
    done.pop().expect("fold result")
}

/// The rewrite at an alias use, when `expr` is one: a slice-tail alias
/// `Var(id)` becomes the `List.tail` chain on its parent, and
/// `IndexAccess(Var(id), n)` indexes the parent at `depth + n` directly —
/// only while the parent is in scope; otherwise the rewrite leaks a free
/// reference.
fn substitute_alias_use(
    expr: &NamelessExpr,
    table: &VarTable,
    in_scope: &HashSet<VarId>,
) -> Option<NamelessExpr> {
    match expr {
        NamelessExpr::Var(id) => {
            let (parent, depth) = resolve_slice_alias(*id, table)?;
            in_scope
                .contains(&parent)
                .then(|| make_list_tail_chain(NamelessExpr::Var(parent), depth))
        }
        NamelessExpr::IndexAccess { collection, index } => {
            let NamelessExpr::Var(id) = collection.as_ref() else {
                return None;
            };
            let (parent, depth) = resolve_slice_alias(*id, table)?;
            in_scope
                .contains(&parent)
                .then(|| NamelessExpr::IndexAccess {
                    collection: NBox::new(NamelessExpr::Var(parent)),
                    index: depth + index,
                })
        }
        _ => None,
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

fn collect_pattern_binders(pattern: &NamelessPattern) -> Vec<VarId> {
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
