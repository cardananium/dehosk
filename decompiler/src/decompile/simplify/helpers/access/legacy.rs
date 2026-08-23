// Legacy string-name access helpers kept for tests / fallback paths;
// production calls VarId-aware variants.
#![allow(dead_code)]

use crate::decompile::list_traversal::is_list_tail_of_var;
use crate::decompile::simplify::Simplifier;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::var_id::VarId;

fn is_head_of(expr: &PseudoExpr, subj_var_name: &str) -> bool {
    match expr {
        PseudoExpr::IndexAccess { collection, index } if *index == 0 => {
            matches!(
                collection.as_ref(),
                PseudoExpr::Var { name, .. } if name == subj_var_name
            )
        }
        PseudoExpr::FieldAccess {
            record, selector, ..
        } if selector.is_list_head() => {
            matches!(
                record.as_ref(),
                PseudoExpr::Var { name, .. } if name == subj_var_name
            )
        }
        _ => false,
    }
}

fn is_tail_of(expr: &PseudoExpr, subj_var_name: &str) -> bool {
    is_list_tail_of_var(expr, subj_var_name)
}

// The only between-child work is `shadowed` turning on across a binder and
// off again once that binder's scope is done. `pre_expr` reads it before the
// descent, so it must flip at the binder boundaries: `enter_let` fires after
// the value is folded and before the body; `enter_lambda`/`enter_recfn` fire
// before the body. Save-before / restore-after keeps the flag scoped without
// threading it through parameters.
fn replace_legacy_access(
    expr: PseudoExpr,
    subj_var_name: &str,
    replacement_name: &str,
    replacement_id: VarId,
    access_matches: fn(&PseudoExpr, &str) -> bool,
) -> PseudoExpr {
    use crate::pseudo::fold::{ExprFolder, FoldAction};

    struct LegacyAccessReplacer<'a> {
        subj_var_name: &'a str,
        replacement_name: &'a str,
        replacement_id: VarId,
        access_matches: fn(&PseudoExpr, &str) -> bool,
        shadowed: bool,
        // Saved `shadowed` to restore in the matching `exit_*` step.
        saved: Vec<bool>,
    }

    impl ExprFolder for LegacyAccessReplacer<'_> {
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            if !self.shadowed && (self.access_matches)(expr, self.subj_var_name) {
                FoldAction::Replace(PseudoExpr::Var {
                    name: self.replacement_name.to_string(),
                    id: Some(self.replacement_id),
                })
            } else {
                FoldAction::Walk
            }
        }

        fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
            self.saved.push(self.shadowed);
            self.shadowed = self.shadowed || params.iter().any(|p| p == self.subj_var_name);
            params.to_vec()
        }

        fn exit_lambda(&mut self, _params: &[Binder]) {
            self.shadowed = self.saved.pop().expect("lambda shadow");
        }

        fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
            self.saved.push(self.shadowed);
            self.shadowed = self.shadowed
                || name == self.subj_var_name
                || params.iter().any(|p| p == self.subj_var_name);
            (name.clone(), params.to_vec())
        }

        fn exit_recfn(&mut self, _name: &Binder, _params: &[Binder]) {
            self.shadowed = self.saved.pop().expect("recfn shadow");
        }

        fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
            self.saved.push(self.shadowed);
            self.shadowed = self.shadowed || name == self.subj_var_name;
            name.to_string()
        }

        fn exit_let(&mut self, _name: &str) {
            self.shadowed = self.saved.pop().expect("let shadow");
        }

        // Overridden only to leave `Literal` patterns alone: the default
        // `fold_clause` folds them. The rewrite shadows on no `when` binder
        // at all, so `shadowed` is untouched here.
        fn fold_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            let subject = self.fold(subject);
            let clauses = clauses
                .into_iter()
                .map(|c| WhenClause {
                    pattern: c.pattern,
                    guard: c.guard.map(|g| self.fold(g)),
                    body: self.fold(c.body),
                })
                .collect();
            self.post_when(subject, subject_name, clauses)
        }
    }

    LegacyAccessReplacer {
        subj_var_name,
        replacement_name,
        replacement_id,
        access_matches,
        shadowed: false,
        saved: Vec::new(),
    }
    .fold(expr)
}

impl Simplifier {
    /// Replace all `subj[0]` (IndexAccess with index 0 on Var matching subj_var_name)
    /// with `Var(replacement_name)`. Respects variable shadowing.
    pub(crate) fn replace_head_access(
        expr: PseudoExpr,
        subj_var_name: &str,
        replacement_name: &str,
        replacement_id: VarId,
    ) -> PseudoExpr {
        replace_legacy_access(
            expr,
            subj_var_name,
            replacement_name,
            replacement_id,
            is_head_of,
        )
    }

    /// Replace all `List.tail(subj)` (in both BuiltinCall and Apply forms)
    /// with `Var(replacement_name)`. Respects variable shadowing.
    pub(crate) fn replace_tail_access(
        expr: PseudoExpr,
        subj_var_name: &str,
        replacement_name: &str,
        replacement_id: VarId,
    ) -> PseudoExpr {
        replace_legacy_access(
            expr,
            subj_var_name,
            replacement_name,
            replacement_id,
            is_tail_of,
        )
    }
}
