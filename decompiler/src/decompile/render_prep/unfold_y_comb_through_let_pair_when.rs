//! Unfold `when Var(yc) is { Pair(a, b) → body }` where `yc` is
//! a let-bound canonical Y-combinator literal.
//!
//! The subject is a function value, not a real `Pair`: V1 scripts
//! use a Y-combinator literal as if it were a Scott-encoded pair,
//! so `App(YC, λself, x. body)` — the fixpoint
//! `rec fn self(x) { body }` — is folded by the
//! `App(subject, [Lambda(a, b, body)])` rewriter into
//! `When { Pair(a, b) → body }`.
//! `undo_pair_when_on_lambda_subject` reverts that collapse for
//! inline `Lambda`/`RecFn` subjects; this pass covers `Var`
//! subjects whose let-binding is the canonical Y-combinator
//! shape. Semantically `App(YC, λa, b. body)` is
//! `rec fn a(b) { body }`. The pass produces that form directly:
//! `a` becomes the `RecFn` self-name binder, `b` its parameter,
//! both keeping their VarIds, so `Var { id: a.id }` calls in
//! `body` resolve to the recursive call without substitution.
//!
//! The let value must match `fn(v) { rec fn s(x) { v(s, x) } }`
//! exactly up to alpha: one outer param, one inner self+param,
//! and a two-arg call in `(self, x)` order. Permutations or extra
//! wrappers are rejected. The `when` must be single-arm,
//! guard-less and un-aliased (no `subject_name`), with a
//! `Pair(a, b)` pattern or the equivalent
//! `WhenPattern::Constructor` carrying `KnownConstructor::Pair`
//! and two fields. The subject must be a `Var` whose `VarId` is
//! in the scanned YC-literal id set. Matching is by `VarId` only,
//! so shadowed names cannot mislead it.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

#[cfg(test)]
mod tests;

pub(super) fn unfold_y_comb_through_let_pair_when(expr: PseudoExpr) -> PseudoExpr {
    let mut yc_ids: HashSet<VarId> = HashSet::new();
    collect_yc_let_ids(&expr, &mut yc_ids);
    if yc_ids.is_empty() {
        return expr;
    }
    YCombPairWhenUnfolder { yc_ids: &yc_ids }.fold(expr)
}

/// Walk the tree, record any `let X = <Y-comb literal>` binder id.
fn collect_yc_let_ids(expr: &PseudoExpr, out: &mut HashSet<VarId>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            body,
            ..
        } = cur
        {
            if matches_y_comb_literal(value) {
                out.insert(*vid);
            }
            pending.push(body);
            pending.push(value);
            continue;
        }
        pending.extend(children(cur).into_iter().rev());
    }
}

/// Strict match of the canonical Y-combinator lambda shape
/// `fn(v) { rec fn self(x) { v(self, x) } }`. Argument order is
/// part of the shape: `(x, self)` is a different combinator.
fn matches_y_comb_literal(value: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = value else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let v_id = params[0].id;
    let PseudoExpr::RecFn {
        name,
        params: rec_params,
        body: rec_body,
    } = body.as_ref()
    else {
        return false;
    };
    if rec_params.len() != 1 {
        return false;
    }
    let self_id = name.id;
    let x_id = rec_params[0].id;
    let PseudoExpr::Apply { function, args } = rec_body.as_ref() else {
        return false;
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        return false;
    };
    if *fn_id != v_id || args.len() != 2 {
        return false;
    }
    let PseudoExpr::Var { id: Some(a0), .. } = &args[0] else {
        return false;
    };
    let PseudoExpr::Var { id: Some(a1), .. } = &args[1] else {
        return false;
    };
    *a0 == self_id && *a1 == x_id
}

struct YCombPairWhenUnfolder<'a> {
    yc_ids: &'a HashSet<VarId>,
}

impl ExprFolder for YCombPairWhenUnfolder<'_> {
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }

    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        if subject_name.is_none()
            && subject_is_y_comb_var(&subject, self.yc_ids)
            && let Some((a, b, body)) = try_extract_single_pair_clause(&clauses)
        {
            return PseudoExpr::RecFn {
                name: a.clone(),
                params: vec![b.clone()],
                body: PBox::new(body.clone()),
            };
        }
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses,
        }
    }
}

fn subject_is_y_comb_var(subject: &PseudoExpr, yc_ids: &HashSet<VarId>) -> bool {
    matches!(subject, PseudoExpr::Var { id: Some(vid), .. } if yc_ids.contains(vid))
}

fn try_extract_single_pair_clause(
    clauses: &[WhenClause],
) -> Option<(&Binder, &Binder, &PseudoExpr)> {
    if clauses.len() != 1 {
        return None;
    }
    let clause = &clauses[0];
    if clause.guard.is_some() {
        return None;
    }
    match &clause.pattern {
        WhenPattern::Pair(a, b) => Some((a, b, &clause.body)),
        WhenPattern::Constructor { shape, fields, .. }
            if shape.as_known() == Some(KnownConstructor::Pair) && fields.len() == 2 =>
        {
            Some((&fields[0], &fields[1], &clause.body))
        }
        _ => None,
    }
}

fn children(expr: &PseudoExpr) -> Vec<&PseudoExpr> {
    let mut out: Vec<&PseudoExpr> = Vec::new();
    match expr {
        PseudoExpr::Let { value, body, .. } => {
            out.push(value);
            out.push(body);
        }
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => out.push(body),
        PseudoExpr::Apply { function, args } => {
            out.push(function);
            out.extend(args.iter());
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            out.push(condition);
            out.push(then_branch);
            out.push(else_branch);
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            out.push(subject);
            for c in clauses {
                if let Some(g) = &c.guard {
                    out.push(g);
                }
                out.push(&c.body);
            }
        }
        PseudoExpr::Constr { fields, .. } => out.extend(fields.iter()),
        PseudoExpr::BuiltinCall { args, .. } => out.extend(args.iter()),
        PseudoExpr::List { elements, tail } => {
            out.extend(elements.iter());
            if let Some(t) = tail {
                out.push(t);
            }
        }
        PseudoExpr::Tuple(items) => out.extend(items.iter()),
        PseudoExpr::Pair(a, b) => {
            out.push(a);
            out.push(b);
        }
        PseudoExpr::FieldAccess { record, .. } => out.push(record),
        PseudoExpr::IndexAccess { collection, .. } => out.push(collection),
        PseudoExpr::BinOp { left, right, .. } => {
            out.push(left);
            out.push(right);
        }
        PseudoExpr::UnOp { operand, .. } => out.push(operand),
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => out.push(inner),
        PseudoExpr::Trace { message, value } => {
            out.push(message);
            out.push(value);
        }
        _ => {}
    }
    out
}
