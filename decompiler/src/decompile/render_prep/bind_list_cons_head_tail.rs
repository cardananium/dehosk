//! Bind `[head, ..tail]` in `when` cons-arms that still use wildcard
//! patterns plus `xs.head` / `xs[1..]` accessors.
//!
//! For a `[_, ..]` pattern, the head binder is `xs.head`
//! (`FieldAccess{ListHead}` on the subject) and the tail binder is
//! `xs[1..]` (`BuiltinCall(ListTail, [xs])`). Binding them in the
//! pattern and substituting the accessors changes nothing at runtime.
//!
//! After `rewrite_native_list_map`, which folds a whole recursive
//! `step` into `list.map`. This pass picks up the cons-arms that
//! survive it (a nil arm returning `church_true` rather than `[]`
//! makes the map recognizer bail) plus any one-off `when` over a list.
//!
//! Fail-closed: subject is a plain `Var` (so `xs.head` / `xs[1..]`
//! refer to it); cons pattern is exactly `[_, ..]`; a binder is
//! renamed only if it is a wildcard and its accessor is actually used
//! in the arm — otherwise left untouched, no spurious binders.

use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn bind_list_cons_head_tail(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_rewrite)
}

fn try_rewrite(expr: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = expr
    else {
        return expr;
    };
    // Only plain-`Var` subjects: `subj.head` / `subj[1..]` are references to it.
    let PseudoExpr::Var {
        id: Some(subj_id), ..
    } = subject.as_ref()
    else {
        return PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        };
    };
    let subj_id = *subj_id;
    let clauses = clauses
        .into_iter()
        .map(|c| rebind_clause(c, subj_id))
        .collect();
    PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    }
}

fn rebind_clause(clause: WhenClause, subj_id: VarId) -> WhenClause {
    // Match exactly `[_, ..]`: one element + a tail binder.
    let WhenPattern::List {
        elements,
        tail: Some(_),
    } = &clause.pattern
    else {
        return clause;
    };
    if elements.len() != 1 {
        return clause;
    }
    let WhenClause {
        pattern,
        guard,
        body,
    } = clause;
    let WhenPattern::List {
        mut elements,
        tail: Some(mut tail_binder),
    } = pattern
    else {
        unreachable!("matched `List{{ tail: Some }}` above");
    };

    // Substitute `subj.head` → the head binder and `subj[1..]` → the tail binder:
    // a WILDCARD binder is renamed to `head`/`tail`, a named one keeps its name,
    // so a body that re-slices `subj[1..]` (or re-accesses `subj.head`) instead
    // of using the bound binder is rewired to it. Binder ids are REUSED, never
    // minted: `fresh_binding()` advances a thread-local counter that VarId-derived
    // synthetic helper names depend on, and `prepare_for_render` runs twice per
    // decompile (DCE pre-render + real render), so a fresh id would perturb naming.
    let head_wild = elements[0].name == "_";
    let tail_wild = tail_binder.name == "_";
    let head_id = elements[0].id;
    let tail_id = tail_binder.id;
    let head_target = (
        if head_wild {
            "head".to_string()
        } else {
            elements[0].name.clone()
        },
        head_id,
    );
    let tail_target = (
        if tail_wild {
            "tail".to_string()
        } else {
            tail_binder.name.clone()
        },
        tail_id,
    );

    // `used_head`/`used_tail` record whether each binder's accessor was
    // actually referenced — accumulated across BOTH the body and the guard,
    // so one `Substituter` instance folds each in turn.
    let mut substituter = Substituter {
        subj_id,
        head_target: &head_target,
        tail_target: &tail_target,
        used_head: false,
        used_tail: false,
    };
    let body = substituter.fold(body);
    let guard = guard.map(|g| substituter.fold(g));

    // Rename a WILDCARD binder to `head`/`tail` only when its accessor was used
    // (a named binder is already correct and stays as-is).
    if substituter.used_head && head_wild {
        elements[0] = Binder::new("head", head_id);
    }
    if substituter.used_tail && tail_wild {
        tail_binder = Binder::new("tail", tail_id);
    }
    WhenClause {
        pattern: WhenPattern::List {
            elements,
            tail: Some(tail_binder),
        },
        guard,
        body,
    }
}

/// Replace `subj.head` → the head binder and `subj[1..]` (`ListTail(subj)`) →
/// the tail binder (each `(name, id)`). Bottom-up, so a nested `subj[2..]`
/// (`ListTail(ListTail(subj))`) folds its inner access to the tail binder and
/// renders as `tail[1..]`.
struct Substituter<'a> {
    subj_id: VarId,
    head_target: &'a (String, VarId),
    tail_target: &'a (String, VarId),
    /// Accumulated across every `fold` call this instance makes (body, then
    /// guard) — an accessor found in either counts as "used".
    used_head: bool,
    used_tail: bool,
}

impl ExprFolder for Substituter<'_> {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        // Do NOT descend into nested binding scopes. A nested `Lambda`/`RecFn`/`When`
        // may (re)bind `head`/`tail` — this pass renames cons-arms to
        // `[head, ..tail]` and `rewrite_native_list_map` names its `list.map`
        // parameter `head` — and the display layer resolves by name, so a
        // substituted ref (same name, other VarId) would be NAME-CAPTURED at
        // render. Leaving `subj.head` / `subj[1..]` untouched there is sound: they
        // stay valid accessors, and the usage tracker keeps the binder as `_` if
        // that was its only use. A `Let` is stopped only when it re-binds one of
        // the TARGET names (`let tail = …; subj[1..]` would let the inner
        // `let tail` capture the substituted `tail`); non-shadowing lets are still
        // descended into.
        if matches!(
            expr,
            PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } | PseudoExpr::When { .. }
        ) || matches!(
            expr,
            PseudoExpr::Let { name, .. } if name == &self.head_target.0 || name == &self.tail_target.0
        ) {
            return FoldAction::Replace(expr.clone());
        }
        FoldAction::Walk
    }

    fn post_field_access(&mut self, record: PseudoExpr, selector: FieldSelector) -> PseudoExpr {
        if matches!(selector, FieldSelector::ListHead) && is_var(&record, self.subj_id) {
            self.used_head = true;
            return PseudoExpr::var_with_id(&self.head_target.0, self.head_target.1);
        }
        PseudoExpr::field_access_typed(record, selector)
    }

    fn post_builtin_call(&mut self, name: BuiltinId, args: Vec<PseudoExpr>) -> PseudoExpr {
        if name == BuiltinId::ListTail && args.len() == 1 && is_var(&args[0], self.subj_id) {
            self.used_tail = true;
            return PseudoExpr::var_with_id(&self.tail_target.0, self.tail_target.1);
        }
        PseudoExpr::BuiltinCall {
            name,
            args: args.into(),
        }
    }

    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        // The partial-application spelling `(List.tail)(subj)` —
        // `Apply { function: BuiltinCall{ListTail, []}, args: [subj] }` — also
        // renders as `subj[1..]`, so match it too.
        if args.len() == 1
            && is_var(&args[0], self.subj_id)
            && matches!(
                &function,
                PseudoExpr::BuiltinCall { name, args: bargs }
                    if *name == BuiltinId::ListTail && bargs.is_empty()
            )
        {
            self.used_tail = true;
            return PseudoExpr::var_with_id(&self.tail_target.0, self.tail_target.1);
        }
        PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        }
    }
}

fn is_var(e: &PseudoExpr, id: VarId) -> bool {
    matches!(e, PseudoExpr::Var { id: Some(v), .. } if *v == id)
}

#[cfg(test)]
mod tests;
