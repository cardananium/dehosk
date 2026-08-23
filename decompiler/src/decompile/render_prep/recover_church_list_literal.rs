//! Recover Church-encoded list literals from nested Cons chains.
//!
//! Source `[a, b, c]` lowers to `cons(a, cons(b, cons(c, nil)))` where
//! `cons` is `fn(h, t, _, k) { k(h, t) }` — a Church-pair-pack with the
//! Nil arm dead. That chain survives decompile as nested calls. This
//! pass finds let-bound helpers of that shape and rewrites any chain
//! of length ≥ 2 into a `PseudoExpr::List`, the terminator becoming
//! the optional list tail.
//!
//! The Church value is still a function (a closure of `head`/`tail`);
//! consumers apply `value(nil_arm, cons_arm)`. The rewrite is display
//! only — invert the compiler lowering so the reader sees `[a, b, c]`.
//!
//! Fail-closed:
//! - Helper `VarId` is bound to a Lambda of shape
//!   `fn(p_0, p_1, _, k) { k(p_0, p_1) }`.
//! - Chain depth ≥ 2 (skip trivial single-element).
//! - Every chain `head` is a pure value, so copying into the List
//!   does not change evaluation order.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

pub(super) fn recover_church_list_literals(expr: PseudoExpr) -> PseudoExpr {
    let mut church_cons_ids: HashSet<VarId> = HashSet::new();
    collect_church_cons_helpers(&expr, &mut church_cons_ids);
    if church_cons_ids.is_empty() {
        return expr;
    }
    rewrite_chains(expr, &church_cons_ids)
}

fn collect_church_cons_helpers(expr: &PseudoExpr, out: &mut HashSet<VarId>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                if let Some(binder_id) = id
                    && let PseudoExpr::Lambda {
                        params,
                        body: lam_body,
                    } = value.as_ref()
                    && is_church_cons_shape(params, lam_body)
                {
                    out.insert(*binder_id);
                }
                pending.push(body.as_ref());
                pending.push(value.as_ref());
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body.as_ref());
            }
            PseudoExpr::Apply { function, args } => {
                pending.extend(args.iter().rev());
                pending.push(function.as_ref());
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch.as_ref());
                pending.push(then_branch.as_ref());
                pending.push(condition.as_ref());
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                    if let Some(g) = &c.guard {
                        pending.push(g);
                    }
                }
                pending.push(subject.as_ref());
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right.as_ref());
                pending.push(left.as_ref());
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand.as_ref()),
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter().rev()),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter().rev()),
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push(t.as_ref());
                }
                pending.extend(elements.iter().rev());
            }
            PseudoExpr::Tuple(elements) => pending.extend(elements.iter().rev()),
            PseudoExpr::Pair(a, b) => {
                pending.push(b.as_ref());
                pending.push(a.as_ref());
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record.as_ref()),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection.as_ref()),
            PseudoExpr::Trace { message, value } => {
                pending.push(value.as_ref());
                pending.push(message.as_ref());
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner.as_ref()),
            _ => {}
        }
    }
}

/// Match `Lambda(p_0, p_1, _, k) -> Apply(Var(k), [Var(p_0), Var(p_1)])`
/// — the Church-Cons constructor; the third param (the "Nil arm" of
/// the Church-encoded sum) is dead.
fn is_church_cons_shape(params: &[Binder], body: &PseudoExpr) -> bool {
    if params.len() != 4 {
        return false;
    }
    let PseudoExpr::Apply { function, args } = body else {
        return false;
    };
    if args.len() != 2 {
        return false;
    }
    let last_param = &params[3];
    // Peel Force wrappers off the function head — `k` may be applied
    // as `Force(Var(k))` if it was a thunk-typed continuation in the
    // UPLC source. Matches the Force-aware chain detector below.
    let mut fn_inner = function.as_ref();
    loop {
        match fn_inner {
            PseudoExpr::Force(inner) => fn_inner = inner,
            _ => break,
        }
    }
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = fn_inner
    else {
        return false;
    };
    if *fn_id != last_param.id {
        return false;
    }
    let PseudoExpr::Var {
        id: Some(arg0_id), ..
    } = &args[0]
    else {
        return false;
    };
    let PseudoExpr::Var {
        id: Some(arg1_id), ..
    } = &args[1]
    else {
        return false;
    };
    *arg0_id == params[0].id && *arg1_id == params[1].id
}

struct ChainRewriter<'a> {
    cons_ids: &'a HashSet<VarId>,
}

impl ExprFolder for ChainRewriter<'_> {
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        if let Some((elements, tail)) = try_match_chain(expr, self.cons_ids)
            && elements.len() >= 2
        {
            let elements = elements.into_iter().map(|e| self.fold(e)).collect();
            let tail = tail.map(|t| PBox::new(self.fold(t.into_inner())));
            return FoldAction::Replace(PseudoExpr::List { elements, tail });
        }
        FoldAction::Walk
    }

    // Do not fold a `when` clause's pattern. Only `Literal` patterns carry a
    // sub-expression, and church-cons chains cannot occur there.
    fn fold_clause(&mut self, clause: WhenClause) -> WhenClause {
        let guard = clause.guard.map(|g| self.fold(g));
        let body = self.fold(clause.body);
        WhenClause {
            pattern: clause.pattern,
            guard,
            body,
        }
    }
}

fn rewrite_chains(expr: PseudoExpr, cons_ids: &HashSet<VarId>) -> PseudoExpr {
    ChainRewriter { cons_ids }.fold(expr)
}

/// Try to interpret `expr` as a Church-Cons chain, returning
/// `Some((elements, terminal))`; `terminal` is `None` when the chain
/// ends in a nil-shaped value (see `is_nil_terminator`) and the raw
/// tail expression otherwise.
///
/// Walks `Apply(Var(cons), [head, tail])` recursively on `tail`.
/// Each `head` must be a pure value, so that moving it from arg
/// position to list-element position is evaluation-safe.
fn try_match_chain(
    expr: &PseudoExpr,
    cons_ids: &HashSet<VarId>,
) -> Option<(Vec<PseudoExpr>, Option<PBox>)> {
    let mut elements = Vec::new();
    let mut current = expr;
    loop {
        let PseudoExpr::Apply { function, args } = current else {
            break;
        };
        if args.len() != 2 {
            break;
        }
        // Peel `Force(...)` wrappers off the function head:
        // force-thunked helpers arrive as `Apply { function:
        // Force(Var(helper)), args }`, and the renderer hides the
        // Force, so the cons-helper VarId match is on the inner Var.
        let mut fn_inner = function.as_ref();
        loop {
            match fn_inner {
                PseudoExpr::Force(inner) => fn_inner = inner,
                _ => break,
            }
        }
        let PseudoExpr::Var { id: Some(vid), .. } = fn_inner else {
            break;
        };
        if !cons_ids.contains(vid) {
            break;
        }
        if !super::purity::is_pure_value(&args[0]) {
            break;
        }
        elements.push(args[0].clone());
        current = &args[1];
    }
    if elements.is_empty() {
        return None;
    }
    let terminal: Option<PBox> = if is_nil_terminator(current) {
        None
    } else {
        Some(PBox::new(current.clone()))
    };
    Some((elements, terminal))
}

/// Crude nil-terminator heuristic: any nullary Constructor
/// (e.g., `Unknown_E_0_0`) is treated as the Nil terminator and
/// dropped from the rewritten list. Anything else becomes an
/// explicit tail (`[a, b | tail]` form).
fn is_nil_terminator(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Constr { fields, .. } if fields.is_empty()
    )
}

#[cfg(test)]
mod tests;
