//! Backstop for orphan `Var("fix")` references.
//!
//! `fix_combinator::simplify_z_combinator` rewrites recognised
//! Y-combinator shapes into a special-marker
//! `Apply(Var("fix"), [captured])`. A downstream simplifier or inliner
//! that does not treat `Var("fix")` as a sentinel can strip the
//! wrapping `Apply`, leaving a bare `Var("fix")` with no `fix` binder
//! in scope — rendered as e.g. `when fix is { Pair(...) -> ... }`,
//! which is broken surface syntax (`fix` reads as a free variable).
//!
//! This pass renames every free `Var("fix")` to
//! `__fix_combinator_residue__`. That is still not valid surface syntax — no
//! such binder exists either — but the marker is unmistakable, so a
//! reader cannot mistake the residue for a real identifier.
//!
//! A free `Var("fix")` is one with `id: None` (the `compat_var("fix")`
//! marker, also minted by `PseudoExpr::fix_helper()`) or an `id` that
//! matches no `fix` binder in the expression. A bound `fix` (e.g. a
//! user-named local) is left alone.

use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;
use std::collections::HashSet;

const RESIDUE_NAME: &str = "__fix_combinator_residue__";

pub(super) fn flag_orphan_fix(expr: PseudoExpr) -> PseudoExpr {
    let bound_fix_ids = collect_bound_fix_ids(&expr);
    let mut renamer = Renamer { bound_fix_ids };
    renamer.fold(expr)
}

/// VarIds of every binder named `"fix"` anywhere in `expr`. A
/// `Var{name:"fix", id}` whose id is in this set is a real local
/// binder, not the sentinel.
fn collect_bound_fix_ids(expr: &PseudoExpr) -> HashSet<VarId> {
    use crate::pseudo::fold::ExprVisitor;
    struct Collector {
        ids: HashSet<VarId>,
    }
    impl ExprVisitor for Collector {
        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for p in params {
                if p.as_str() == "fix" {
                    self.ids.insert(p.id);
                }
            }
        }
        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            if name.as_str() == "fix" {
                self.ids.insert(name.id);
            }
            for p in params {
                if p.as_str() == "fix" {
                    self.ids.insert(p.id);
                }
            }
        }
        fn visit_let_value_post(&mut self, name: &str, id: &Option<VarId>, _value: &PseudoExpr) {
            if name == "fix"
                && let Some(id) = id
            {
                self.ids.insert(*id);
            }
        }
    }
    let mut c = Collector {
        ids: HashSet::new(),
    };
    c.walk(expr);
    c.ids
}

struct Renamer {
    bound_fix_ids: HashSet<VarId>,
}

impl ExprFolder for Renamer {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        if name == "fix" {
            let is_bound = id.map(|i| self.bound_fix_ids.contains(&i)).unwrap_or(false);
            if !is_bound {
                return PseudoExpr::Var {
                    name: RESIDUE_NAME.to_string(),
                    id: None,
                };
            }
        }
        PseudoExpr::Var { name, id }
    }

    // `HelperSymbol(Fix)` is the canonical form and is left alone:
    // this backstop only catches orphan `Var("fix")`. Flagging a
    // `HelperSymbol(Fix)` in a non-function-call position needs
    // parent-position awareness this folder lacks.
}

#[cfg(test)]
mod tests;
