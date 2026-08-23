//! Fold a boolean `if` whose one branch is a `Bool` literal into a
//! logical operator: `if c { body } else { False }` → `c && body`,
//! `if c { True } else { body }` → `c || body`.
//!
//! Both are exact short-circuit equivalences, but well-typed only
//! when `body: Bool`. The sibling branch being a `Bool` literal is
//! not sufficient — upstream church-bool decoding can leave one `if`
//! branch as a `Bool` literal while the other is a church-bool
//! sentinel: a zero-arity `Constr` (`Unknown_E_0_0`, the inlined
//! church_true) or a `Var` to such a const, optionally
//! trace-wrapped, which would fold to the non-compilable
//! `Bool && <ADT>`. Hence the `!is_church_sentinel(body)` gate;
//! genuine operands (`f(x)`, `x == y`, a plain Bool `Var`) still
//! fold, and a blocked fold leaves the source `if` intact.
//!
//! The both-literal identity cases (`if c { True } else { False }`
//! → `c`, etc.) belong to
//! `boolean_cleanup::simplify_if_bool_identity`; folding them to
//! `c && True` / `c || False` would regress. So `&&` fires only
//! when the then branch is not itself a `Bool` literal, and `||`
//! only when the else branch is not. The folded operand must be
//! expression-like, not a `When`/`If`/`Let` block — nested boolean
//! ifs still collapse to flat `&&`/`||` chains because they fold
//! bottom-up, so an inner `if` is already a `BinOp` when the outer
//! is checked.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

/// An operand that reads well inline after `&&`/`||` — anything that is NOT a
/// multi-line control-flow block (`When`/`If`/`Let`).
fn is_inline_operand(e: &PseudoExpr) -> bool {
    !matches!(
        e,
        PseudoExpr::When { .. } | PseudoExpr::If { .. } | PseudoExpr::Let { .. }
    )
}

/// A church-bool SENTINEL used as an `&&`/`||` operand — never a valid Bool.
/// Two shapes: a raw zero-arity `Constr` (`Unknown_E_0_0`), or a `Var` to a
/// top-level zero-arity-Constr const (`const e = Unknown_E_0_0`). Native
/// booleans are `PseudoExpr::Bool` (a distinct node) and genuine operands are
/// `Apply`/comparison/Bool-`Var`, so none of them match here.
fn is_church_sentinel(e: &PseudoExpr, church_const_ids: &HashSet<VarId>) -> bool {
    let mut current = e;
    loop {
        match current {
            PseudoExpr::Constr { fields, .. } if fields.is_empty() => return true,
            PseudoExpr::Var { id: Some(v), .. } => return church_const_ids.contains(v),
            // A trace-wrapped sentinel `trace @"m": e` is still the sentinel `e`.
            // The `&&` arm blocks all `Trace` anyway; this peel protects the `||`
            // arm, which does not, while leaving `trace: <bool>` sugar foldable.
            PseudoExpr::Trace { value, .. } => current = value,
            _ => return false,
        }
    }
}

/// Collect the `VarId`s of every binding whose value is a zero-arity `Constr`
/// (`const e = Unknown_E_0_0`) — the church-bool sentinel consts.
fn collect_church_const_ids(expr: &PseudoExpr, out: &mut HashSet<VarId>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(v), value, ..
        } = cur
            && matches!(value.as_ref(), PseudoExpr::Constr { fields, .. } if fields.is_empty())
        {
            out.insert(*v);
        }
        pending.extend(children(cur));
    }
}

pub(super) fn fold_if_to_logical(expr: PseudoExpr) -> PseudoExpr {
    let mut church_const_ids = HashSet::new();
    collect_church_const_ids(&expr, &mut church_const_ids);
    FoldIfToLogical {
        church_const_ids: &church_const_ids,
    }
    .fold(expr)
}

struct FoldIfToLogical<'a> {
    church_const_ids: &'a HashSet<VarId>,
}

impl ExprFolder for FoldIfToLogical<'_> {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    // Runs after `condition`/`then_branch`/`else_branch` are already
    // folded (bottom-up), same as the old post-order `map_children` call —
    // nested `if`s are already flat `&&`/`||` chains by the time an outer
    // `if` is examined here.
    fn post_if(
        &mut self,
        condition: PseudoExpr,
        then_branch: PseudoExpr,
        else_branch: PseudoExpr,
    ) -> PseudoExpr {
        // `if c { body } else { False }` → `c && body` (body a non-literal,
        // inline-renderable expression). NOT when `body` is a `Trace`: the display
        // `&& trace …: True` recognizer rewrites `c && (trace @"m": True)` to `!c?`,
        // dropping the message and inverting the truth value. (The `||` path below
        // is safe — its `Trace{False}` recognizer is message-gated.)
        if matches!(else_branch, PseudoExpr::Bool(false))
            && !matches!(then_branch, PseudoExpr::Bool(_))
            && !matches!(then_branch, PseudoExpr::Trace { .. })
            && is_inline_operand(&then_branch)
            // Don't fold when the THEN branch is a church-bool sentinel — that would
            // emit the non-compilable `c && e` (Bool && ADT). Genuine `c && f(x)` /
            // `c && (x == y)` operands still fold.
            && !is_church_sentinel(&then_branch, self.church_const_ids)
        {
            return PseudoExpr::BinOp {
                op: BinaryOp::And,
                left: PBox::new(condition),
                right: PBox::new(then_branch),
            };
        }
        // `if c { True } else { body }` → `c || body` (body a non-literal,
        // inline-renderable expression). Same church-sentinel exclusion as `&&`.
        if matches!(then_branch, PseudoExpr::Bool(true))
            && !matches!(else_branch, PseudoExpr::Bool(_))
            && is_inline_operand(&else_branch)
            && !is_church_sentinel(&else_branch, self.church_const_ids)
        {
            return PseudoExpr::BinOp {
                op: BinaryOp::Or,
                left: PBox::new(condition),
                right: PBox::new(else_branch),
            };
        }
        PseudoExpr::If {
            condition: PBox::new(condition),
            then_branch: PBox::new(then_branch),
            else_branch: PBox::new(else_branch),
        }
    }
}

#[cfg(test)]
mod tests;
