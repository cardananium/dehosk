//! Variable renaming utilities for simplification.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};
use crate::pseudo::walker::{FoldAction, Walker};

use super::Simplifier;
mod validator;

#[cfg(test)]
pub(crate) use validator::rename_validator_params;
pub(crate) use validator::{
    is_protected_validator_param_name, rename_validator_params_with_var_kinds,
    rename_validator_params_with_var_kinds_authoritative,
};

impl Simplifier {
    fn run_self_call_cleanup(
        expr: &PseudoExpr,
        fn_name: &str,
        mode: SelfCallCleanupMode,
    ) -> PseudoExpr {
        SelfCallCleanupFolder {
            fn_name,
            blocked_depth: 0,
            mode,
        }
        .fold(expr.clone())
    }

    /// Rename by name; with no `old_id`,
    /// `Var` sites match on name alone.
    pub(crate) fn rename_var(expr: &PseudoExpr, old_name: &str, new_name: &str) -> PseudoExpr {
        Self::rename_var_binding(expr, old_name, None, new_name)
    }

    /// Rename a specific lexical binding.
    ///
    /// `old_id`, when present, is authoritative for matching `Var` sites, but
    /// shadowing is judged by name alone: a lambda/recfn param, `let`, or
    /// when-pattern binder with `old_name` blocks the rename beneath it.
    pub(crate) fn rename_var_binding(
        expr: &PseudoExpr,
        old_name: &str,
        old_id: Option<VarId>,
        new_name: &str,
    ) -> PseudoExpr {
        RenameBindingFolder {
            old_name,
            old_id,
            new_name,
            new_id: None,
            blocked_depth: 0,
        }
        .fold(expr.clone())
    }

    /// Alias-substitution variant that also rewrites the `Var` id. Use for
    /// a substitution `x := y` (`let x = y in body` → `body[x := y]`): the
    /// body's `x`-refs must reference `y`'s binder id, or they are orphans
    /// against `y`'s binder — same name, different id.
    pub(crate) fn substitute_var_for_var(
        expr: &PseudoExpr,
        old_name: &str,
        old_id: Option<VarId>,
        new_name: &str,
        new_id: VarId,
    ) -> PseudoExpr {
        RenameBindingFolder {
            old_name,
            old_id,
            new_name,
            new_id: Some(new_id),
            blocked_depth: 0,
        }
        .fold(expr.clone())
    }

    /// Strip the self-argument from recursive calls inside a RecFn body.
    ///
    /// After Y-combinator decomposition, `f(f, a, b)` and
    /// `f(__y_comb_rec_fn, a, b)` calls remain even though the RecFn
    /// declaration no longer has a self-parameter.
    pub(crate) fn strip_rec_self_arg(expr: &PseudoExpr, fn_name: &str) -> PseudoExpr {
        Self::run_self_call_cleanup(expr, fn_name, SelfCallCleanupMode::StripRecSelfArg)
    }

    /// Strip thunked self-calls from a RecFn: convert `fn_name()` (0-arg call) to `fn_name`.
    ///
    /// In the thunked Y-combinator pattern `rec fn f(y) { callback(f(), y) }; f()`
    /// the 0-arg self-call `f()` is a thunk for `f` itself, and `rec fn` already
    /// provides the self-reference.
    pub(crate) fn strip_thunked_self_calls(expr: &PseudoExpr, fn_name: &str) -> PseudoExpr {
        Self::run_self_call_cleanup(expr, fn_name, SelfCallCleanupMode::StripThunkedSelfCall)
    }
}

#[derive(Clone, Copy)]
enum SelfCallCleanupMode {
    StripRecSelfArg,
    StripThunkedSelfCall,
}

struct SelfCallCleanupFolder<'a> {
    fn_name: &'a str,
    blocked_depth: usize,
    mode: SelfCallCleanupMode,
}

impl SelfCallCleanupFolder<'_> {
    fn rewrite_apply(&self, function: &PseudoExpr, args: &[PseudoExpr]) -> Option<PseudoExpr> {
        let PseudoExpr::Var { name, .. } = function else {
            return None;
        };

        if name != self.fn_name {
            return None;
        }

        match self.mode {
            SelfCallCleanupMode::StripRecSelfArg => {
                let first_arg = args.first()?;
                let PseudoExpr::Var { name: arg_name, .. } = first_arg else {
                    return None;
                };

                if arg_name == self.fn_name || arg_name == "__y_comb_rec_fn" {
                    Some(PseudoExpr::Apply {
                        function: PBox::new(function.clone()),
                        args: (args[1..].to_vec()).into(),
                    })
                } else {
                    None
                }
            }
            SelfCallCleanupMode::StripThunkedSelfCall => {
                if args.is_empty() {
                    Some(function.clone())
                } else {
                    None
                }
            }
        }
    }
}

struct RenameBindingFolder<'a> {
    old_name: &'a str,
    old_id: Option<VarId>,
    new_name: &'a str,
    /// When `Some`, matching `Var` refs take this id too, and
    /// a binder named `new_name` blocks traversal so the
    /// substitution cannot capture.
    new_id: Option<VarId>,
    blocked_depth: usize,
}

impl RenameBindingFolder<'_> {
    fn matches_binding(&self, name: &str, id: Option<VarId>) -> bool {
        // `.get()` maps a compat-placeholder id to `None`, so such a ref
        // falls back to name comparison. Comparing raw ids instead would
        // make `(Some(compat), Some(auth))` unequal and miss every
        // compat-id ref.
        crate::decompile::var_match::refs_match(name, id.get(), self.old_name, self.old_id)
    }

    fn blocks_rewrite(&self, name: &str) -> bool {
        name == self.old_name || self.new_id.is_some_and(|_| name == self.new_name)
    }

    fn fold_when_clause(
        &mut self,
        subject_name: Option<&Binder>,
        clause: WhenClause,
    ) -> WhenClause {
        let mut blocked =
            subject_name.is_some_and(|subject_name| self.blocks_rewrite(subject_name));
        if !blocked {
            blocked = Simplifier::pattern_bound_vars(&clause.pattern)
                .into_iter()
                .any(|bound| self.blocks_rewrite(bound.as_str()));
        }

        let pattern = self.fold_pattern(clause.pattern);
        let guard = clause
            .guard
            .map(|guard| if blocked { guard } else { self.fold(guard) });
        let body = if blocked {
            clause.body
        } else {
            self.fold(clause.body)
        };

        WhenClause {
            pattern,
            guard,
            body,
        }
    }

    fn rewrite_when(
        &mut self,
        subject: &PseudoExpr,
        subject_name: &Option<Binder>,
        clauses: &[WhenClause],
    ) -> PseudoExpr {
        let subject = self.fold(subject.clone());
        let clauses = clauses
            .iter()
            .cloned()
            .map(|clause| self.fold_when_clause(subject_name.as_ref(), clause))
            .collect();
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name: subject_name.clone(),
            clauses,
        }
    }
}

impl Walker for RenameBindingFolder<'_> {
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        if self.blocked_depth > 0 {
            return FoldAction::Replace(expr.clone());
        }

        match expr {
            PseudoExpr::Var { name, id } if self.matches_binding(name, *id) => {
                FoldAction::Replace(PseudoExpr::Var {
                    name: self.new_name.to_string(),
                    id: self.new_id.or(*id),
                })
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => FoldAction::Replace(self.rewrite_when(subject, subject_name, clauses)),
            _ => FoldAction::Walk,
        }
    }

    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        if params.iter().any(|param| self.blocks_rewrite(param)) {
            self.blocked_depth += 1;
        }
        params.to_vec()
    }

    fn exit_lambda(&mut self, params: &[Binder]) {
        if params.iter().any(|param| self.blocks_rewrite(param)) {
            self.blocked_depth -= 1;
        }
    }

    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        if self.blocks_rewrite(name) || params.iter().any(|param| self.blocks_rewrite(param)) {
            self.blocked_depth += 1;
        }
        (name.clone(), params.to_vec())
    }

    fn exit_recfn(&mut self, name: &Binder, params: &[Binder]) {
        if self.blocks_rewrite(name) || params.iter().any(|param| self.blocks_rewrite(param)) {
            self.blocked_depth -= 1;
        }
    }

    fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
        if self.blocks_rewrite(name) {
            self.blocked_depth += 1;
        }
        name.to_string()
    }

    fn exit_let(&mut self, name: &str) {
        if self.blocks_rewrite(name) {
            self.blocked_depth -= 1;
        }
    }
}

impl Walker for SelfCallCleanupFolder<'_> {
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        if self.blocked_depth > 0 {
            return FoldAction::Replace(expr.clone());
        }

        if let PseudoExpr::Apply { function, args } = expr
            && let Some(rewritten) = self.rewrite_apply(function, args)
        {
            return FoldAction::Replace(rewritten);
        }

        FoldAction::Walk
    }

    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        if params.iter().any(|p| p == self.fn_name) {
            self.blocked_depth += 1;
        }
        params.to_vec()
    }

    fn exit_lambda(&mut self, params: &[Binder]) {
        if params.iter().any(|p| p == self.fn_name) {
            self.blocked_depth -= 1;
        }
    }

    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        if name == self.fn_name || params.iter().any(|p| p == self.fn_name) {
            self.blocked_depth += 1;
        }
        (name.clone(), params.to_vec())
    }

    fn exit_recfn(&mut self, name: &Binder, params: &[Binder]) {
        if name == self.fn_name || params.iter().any(|p| p == self.fn_name) {
            self.blocked_depth -= 1;
        }
    }

    fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
        if name == self.fn_name {
            self.blocked_depth += 1;
        }
        name.to_string()
    }

    fn exit_let(&mut self, name: &str) {
        if name == self.fn_name {
            self.blocked_depth -= 1;
        }
    }
}

#[cfg(test)]
mod tests;
