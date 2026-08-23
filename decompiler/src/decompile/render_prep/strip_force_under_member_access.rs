//! Strip redundant `Force` / 0-arg `Apply` on a `Var` when the result
//! is immediately member-accessed (`FieldAccess` or `IndexAccess`).
//!
//! V1/PlutusTx emits Church-pair access via a Force intermediate
//! (`payload().snd`, `e5().0`). The `()` is the runtime `force` Plutus
//! needs because the Var's binding is type-erased. At render, the
//! `.snd`/`.fst`/`<num>` selector already forces materialization, so
//! the access is just `payload.snd`.
//!
//! Strip `Force(Var(p))` / `Apply{Var(p), []}` only when the enclosing
//! context is a member access and `p` is a pattern binder (Constructor
//! / List / Tuple / Pair / Var / subject_name — never `Delay`-typed;
//! they receive already-extracted payload) or a Lambda / RecFn
//! parameter (a caller can pass a Delay, but a member-access use
//! implies it must be materialized there).
//!
//! Let-bound `Var`s whose value is `Lambda` / `RecFn` are covered by
//! `fold_force_on_lambda_var`; this pass adds the scope-aware cases
//! that pass cannot see. `Force(Var)` anywhere else is left alone —
//! the semantics can differ when the Var binds a Delay.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

pub(super) fn strip_force_under_member_access(expr: PseudoExpr) -> PseudoExpr {
    Rewriter {
        in_scope: HashSet::new(),
    }
    .fold(expr)
}

/// `in_scope` only ever grows: every `VarId` here is a fresh binder unique
/// to the whole program, so a `Var` referencing one can only ever occur
/// inside that binder's real lexical scope — leaving a stale id in the set
/// after its scope closes can never cause a false match at a sibling. Same
/// "cumulative" reasoning `rename::Renamer::exit_let` relies on.
struct Rewriter {
    in_scope: HashSet<VarId>,
}

impl ExprFolder for Rewriter {
    fn post_field_access(&mut self, record: PseudoExpr, selector: FieldSelector) -> PseudoExpr {
        PseudoExpr::FieldAccess {
            record: PBox::new(strip_if_in_scope(record, &self.in_scope)),
            selector,
        }
    }

    fn post_index_access(&mut self, collection: PseudoExpr, index: usize) -> PseudoExpr {
        PseudoExpr::IndexAccess {
            collection: PBox::new(strip_if_in_scope(collection, &self.in_scope)),
            index,
        }
    }

    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        for p in params {
            self.in_scope.insert(p.id);
        }
        params.to_vec()
    }

    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        self.in_scope.insert(name.id);
        for p in params {
            self.in_scope.insert(p.id);
        }
        (name.clone(), params.to_vec())
    }

    fn enter_let(&mut self, name: &str, id: &Option<VarId>, _value: &PseudoExpr) -> String {
        if let Some(vid) = id {
            self.in_scope.insert(*vid);
        }
        name.to_string()
    }

    fn fold_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let subject = self.fold(subject);
        if let Some(sub_name) = &subject_name {
            self.in_scope.insert(sub_name.id);
        }
        let clauses = clauses.into_iter().map(|c| self.fold_clause(c)).collect();
        self.post_when(subject, subject_name, clauses)
    }

    fn fold_clause(&mut self, clause: WhenClause) -> WhenClause {
        self.in_scope.extend(clause.pattern.bound_ids());
        let guard = clause.guard.map(|g| self.fold(g));
        let body = self.fold(clause.body);
        WhenClause {
            pattern: clause.pattern,
            guard,
            body,
        }
    }
}

/// If `expr` is `Force(Var(p))` or `Apply{Var(p), []}` where p is in `in_scope`,
/// unwrap to `Var(p)`. Otherwise return as-is.
fn strip_if_in_scope(expr: PseudoExpr, in_scope: &HashSet<VarId>) -> PseudoExpr {
    match expr {
        PseudoExpr::Force(inner) => {
            if let PseudoExpr::Var { id: Some(vid), .. } = inner.as_ref()
                && in_scope.contains(vid)
            {
                inner.into_inner()
            } else {
                PseudoExpr::Force(inner)
            }
        }
        PseudoExpr::Apply { function, args } if args.is_empty() => {
            if let PseudoExpr::Var { id: Some(vid), .. } = function.as_ref()
                && in_scope.contains(vid)
            {
                function.into_inner()
            } else {
                PseudoExpr::Apply { function, args }
            }
        }
        other => other,
    }
}

#[cfg(test)]
mod tests;
