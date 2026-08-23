//! Collapse an over-applied divergent `fail` value: `a(x, y, z)` → `a` when
//! `a` provably diverges (a `fail`/`error`, or a const/let bound to one).
//!
//! PlutusTx emits shared fail-continuation arms where one common n-ary
//! continuation is applied uniformly across branches; in the fail branch the
//! continuation is a bare `fail`, so the arm renders as ill-typed
//! `a(True, …)` over `const a = fail @"PT1"`. A value that diverges when
//! forced discards its arguments, so `a(args)` denotes just `a`. The same
//! `a` already renders bare (`_ -> a`) at its wildcard-default sites;
//! collapsing here drops the ill-typed `fail(…)` surface and unifies the
//! two renderings.
//!
//! Mirrors the over-applied-literal collapse in `simplify/apply/mod.rs`:
//! the args are dropped only when none carries a strict failpoint, so a
//! real side-effecting argument is never erased (retention-biased). The
//! callee must be a *provably* divergent fail: a literal `Error`, a
//! `trace …: fail` wrapper around one, or a `Var` to a const/let bound
//! to such a value.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::decompile::simplify::Simplifier;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

pub(super) fn collapse_over_applied_fail(expr: PseudoExpr) -> PseudoExpr {
    let mut fail_ids = HashSet::new();
    collect_fail_bound_ids(&expr, &mut fail_ids);
    rewrite(expr, &fail_ids)
}

/// Whether `expr` provably diverges when forced: a literal `fail`/`error`, a
/// `trace …: <fail>` wrapper, or a `Var` to a known fail-bound binding.
fn is_divergent_fail(expr: &PseudoExpr, fail_ids: &HashSet<VarId>) -> bool {
    let mut expr = expr;
    loop {
        match expr {
            PseudoExpr::Error { .. } => return true,
            PseudoExpr::Trace { value, .. } => expr = value,
            PseudoExpr::Var { id: Some(v), .. } => return fail_ids.contains(v),
            _ => return false,
        }
    }
}

/// Collect the `VarId`s of `let`/const bindings whose value is a divergent
/// fail (so `Var` uses of them resolve as fail). Transitive aliases are picked
/// up because a `let b = a` where `a` is already known is itself a `Var`.
fn collect_fail_bound_ids(expr: &PseudoExpr, out: &mut HashSet<VarId>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(v), value, ..
        } = cur
            && is_divergent_fail(value, out)
        {
            out.insert(*v);
        }
        pending.extend(children(cur).into_iter().rev());
    }
}

// The match check must run on the RAW, not-yet-folded `function`/`args`.
// `is_divergent_fail` only recognises `Error`/`Trace`/`Var`, never `Apply`, so
// a nested `a(x, y)(z)` where the inner `Apply` collapses to `a` must not
// make the outer callee divergent: each node is checked once, pre-order,
// against its own immediate (unprocessed) shape. Folding bottom-up first
// and then testing the already-folded `function` would collapse that outer
// node into `a` too. The decision is made in `pre_expr` and stashed per
// open `Apply`; `post_apply` only applies it once children are folded.
fn rewrite(expr: PseudoExpr, fail_ids: &HashSet<VarId>) -> PseudoExpr {
    struct FailCollapser<'a> {
        fail_ids: &'a HashSet<VarId>,
        apply_matches: Vec<bool>,
    }

    impl ExprFolder for FailCollapser<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            if let PseudoExpr::Apply { function, args } = expr {
                let matched = is_divergent_fail(function, self.fail_ids)
                    && args
                        .iter()
                        .all(|a| !Simplifier::contains_strict_failpoint(a));
                self.apply_matches.push(matched);
            }
            FoldAction::Walk
        }

        fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
            let matched = self
                .apply_matches
                .pop()
                .expect("pre_expr pushes once for every Apply post_apply reconstructs");
            if matched {
                // The callee fails when forced; drop the (pure) args and keep the fail.
                return function;
            }
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
    }

    FailCollapser {
        fail_ids,
        apply_matches: Vec::new(),
    }
    .fold(expr)
}

#[cfg(test)]
mod tests;
