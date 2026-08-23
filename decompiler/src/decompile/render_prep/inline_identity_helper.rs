//! Inline `let X = fn(p) { p } in body` identity helpers.
//!
//! A helper can survive simplification as a literal identity. Every
//! `c(arg)` callsite is then just `arg`. This pass inlines each
//! `Apply(Var(X), [arg])` as `arg` and drops the let — only when every
//! reference was consumed. Bare references or partial over-application
//! keep the let alive.
//!
//! Conservative on three axes:
//! - Shape: value is `Lambda { params: [p], body: Var(p) }` — exactly
//!   one param, body a Var to that param.
//! - Scope: call-site matching is id-first. Plain-name matching fires
//!   only when both the binder and the call carry `id: None` and no
//!   enclosing scope shadows the binder name.
//! - Drop safety: drop the let only when the inlined-call count equals
//!   the pre-walk total reference count.
//!
//! Multi-param identity (`fn(x, y) { x }` — K-combinator first
//! projection) is left alone: dropping the second arg's evaluation
//! could lose a side effect.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::{ExprFolder, ExprVisitor};
use crate::pseudo::var_id::VarId;

pub(super) fn inline_identity_helpers(expr: PseudoExpr) -> PseudoExpr {
    let mut inliner = Inliner {
        identity_ids: HashSet::new(),
    };
    inliner.fold(expr)
}

/// Bottom-up walker: on exiting a `Let` the body is already rewritten. If
/// the value is an identity lambda — or a bare `Var` alias resolving
/// (transitively) to one — inline every call to this binder in the body,
/// then drop the let *only if every reference was consumed*.
///
/// The alias case covers the `let r = map` indirection minted by
/// `eta_reduce_lambda_forwarder` (which collapses `fn(x) { map(x) }` to
/// `map`). `enter_let` registers identity-valued binders top-down: it runs
/// after the VALUE is folded and before the body, so an outer
/// `fn map(v) { v }` is registered before its body's `let r = map` is
/// reached, and registration is transitive through further `Var` aliases.
/// Membership is strictly by `VarId` — no name fallback, so a wrapped or
/// id-less alias is left untouched (fail-closed).
struct Inliner {
    identity_ids: HashSet<VarId>,
}

impl ExprFolder for Inliner {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn enter_let(&mut self, name: &str, id: &Option<VarId>, value: &PseudoExpr) -> String {
        if let Some(vid) = id {
            let is_identity_valued = is_identity_lambda(value)
                || matches!(
                    value,
                    PseudoExpr::Var { id: Some(t), .. } if self.identity_ids.contains(t)
                );
            if is_identity_valued {
                self.identity_ids.insert(*vid);
            }
        }
        name.to_string()
    }

    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let is_alias = matches!(
            &value,
            PseudoExpr::Var { id: Some(t), .. } if self.identity_ids.contains(t)
        );
        if is_identity_lambda(&value) || is_alias {
            // 1. Count refs to the binder anywhere in the body.
            let total_refs = count_refs(&body, id, &name);
            if total_refs == 0 {
                // Nothing to do; dead-let elimination drops the
                // let later.
                return PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                };
            }
            // 2. Rewrite single-arg call sites; count how many
            //    were actually consumed.
            let (rewritten_body, inlined_count) = inline_calls(body, id, &name);
            if inlined_count == total_refs {
                // Every reference was a `c(arg)` call; safe to
                // drop the let entirely.
                return rewritten_body;
            }
            // Some refs survived as bare uses / partial applies;
            // keep the let.
            return PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(rewritten_body),
            };
        }
        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }
}

/// `fn(p) { p }` — one param, body a `Var` referring to it.
fn is_identity_lambda(value: &PseudoExpr) -> bool {
    if let PseudoExpr::Lambda { params, body } = value
        && params.len() == 1
        && let PseudoExpr::Var { name: vn, id: vid } = body.as_ref()
    {
        return var_refers_to_binder(vn, vid, &params[0]);
    }
    false
}

pub(super) fn var_refers_to_binder(name: &str, id: &Option<VarId>, binder: &Binder) -> bool {
    if let Some(var_id) = id {
        return *var_id == binder.id;
    }
    name == binder.as_str()
}

/// Count every reference to a `(id, name)` pair across the expression.
/// Stops at scope boundaries that shadow `name`, so refs to an inner
/// `let name = ...` or `fn(name) { ... }` binder are not counted.
pub(super) fn count_refs(expr: &PseudoExpr, target_id: Option<VarId>, target_name: &str) -> usize {
    struct RefCounter<'a> {
        target_id: Option<VarId>,
        target_name: &'a str,
        count: usize,
        /// Count of enclosing scopes that shadow `target_name`. While
        /// non-zero, name-only matches are suppressed.
        shadow_depth: usize,
    }
    impl ExprVisitor for RefCounter<'_> {
        fn visit_var(&mut self, name: &str, id: &Option<VarId>) {
            if matches_binder(
                self.target_id,
                self.target_name,
                self.shadow_depth,
                name,
                id,
            ) {
                self.count += 1;
            }
        }
        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            if params.iter().any(|p| p.as_str() == self.target_name) {
                self.shadow_depth += 1;
            }
        }
        fn visit_lambda_post(&mut self, params: &[Binder]) {
            if params.iter().any(|p| p.as_str() == self.target_name) {
                self.shadow_depth -= 1;
            }
        }
        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            if name.as_str() == self.target_name
                || params.iter().any(|p| p.as_str() == self.target_name)
            {
                self.shadow_depth += 1;
            }
        }
        fn visit_recfn_post(&mut self, name: &Binder, params: &[Binder]) {
            if name.as_str() == self.target_name
                || params.iter().any(|p| p.as_str() == self.target_name)
            {
                self.shadow_depth -= 1;
            }
        }
        fn visit_let_pre(&mut self, name: &str) {
            if name == self.target_name {
                self.shadow_depth += 1;
            }
        }
        fn visit_let_post(&mut self, name: &str) {
            if name == self.target_name {
                self.shadow_depth -= 1;
            }
        }
        fn visit_when_clause_pre(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            if shadows_target(subject_name, &clause.pattern, self.target_name) {
                self.shadow_depth += 1;
            }
        }
        fn visit_when_clause_post(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            if shadows_target(subject_name, &clause.pattern, self.target_name) {
                self.shadow_depth -= 1;
            }
        }
    }
    let mut c = RefCounter {
        target_id,
        target_name,
        count: 0,
        shadow_depth: 0,
    };
    c.walk(expr);
    c.count
}

/// Replace every `Apply { function: Var(matches binder), args: [arg] }`
/// in `expr` with `arg`. Returns `(rewritten_expr, inlined_count)`.
/// Matching is id-first and shadow-aware, as in `count_refs`.
pub(super) fn inline_calls(
    expr: PseudoExpr,
    binder_id: Option<VarId>,
    binder_name: &str,
) -> (PseudoExpr, usize) {
    struct CallInliner<'a> {
        binder_id: Option<VarId>,
        binder_name: &'a str,
        inlined_count: usize,
        shadow_depth: usize,
    }
    impl ExprFolder for CallInliner<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
            if params.iter().any(|p| p.as_str() == self.binder_name) {
                self.shadow_depth += 1;
            }
            params.to_vec()
        }
        fn exit_lambda(&mut self, params: &[Binder]) {
            if params.iter().any(|p| p.as_str() == self.binder_name) {
                self.shadow_depth -= 1;
            }
        }
        fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
            if name.as_str() == self.binder_name
                || params.iter().any(|p| p.as_str() == self.binder_name)
            {
                self.shadow_depth += 1;
            }
            (name.clone(), params.to_vec())
        }
        fn exit_recfn(&mut self, name: &Binder, params: &[Binder]) {
            if name.as_str() == self.binder_name
                || params.iter().any(|p| p.as_str() == self.binder_name)
            {
                self.shadow_depth -= 1;
            }
        }
        fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
            if name == self.binder_name {
                self.shadow_depth += 1;
            }
            name.to_string()
        }
        fn exit_let(&mut self, name: &str) {
            if name == self.binder_name {
                self.shadow_depth -= 1;
            }
        }

        fn post_apply(&mut self, function: PseudoExpr, mut args: Vec<PseudoExpr>) -> PseudoExpr {
            if args.len() == 1
                && let PseudoExpr::Var { name, id } = &function
                && matches_binder(
                    self.binder_id,
                    self.binder_name,
                    self.shadow_depth,
                    name,
                    id,
                )
            {
                self.inlined_count += 1;
                return args.remove(0);
            }
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
    }
    let mut inliner = CallInliner {
        binder_id,
        binder_name,
        inlined_count: 0,
        shadow_depth: 0,
    };
    let rewritten = inliner.fold(expr);
    (rewritten, inliner.inlined_count)
}

/// Shared id-first scope-aware matcher. Strict id-match takes
/// precedence; name fallback only fires when both the binder and the
/// call carry `id: None` AND no enclosing scope has shadowed the name.
fn matches_binder(
    target_id: Option<VarId>,
    target_name: &str,
    shadow_depth: usize,
    var_name: &str,
    var_id: &Option<VarId>,
) -> bool {
    if let Some(target) = target_id {
        if let Some(other) = var_id {
            return *other == target;
        }
        // Binder has an id but ref is id-less. Don't match — could be
        // a name collision with an unrelated binder.
        return false;
    }
    // Binder has no id: fall back to a name match *only* outside
    // any shadowing scope and only when the ref is also id-less.
    if var_id.is_some() {
        return false;
    }
    shadow_depth == 0 && var_name == target_name
}

/// True when a when-clause shadows `target_name` — through its
/// optional `subject_name` binder or any pattern binder.
fn shadows_target(subject_name: Option<&Binder>, pattern: &WhenPattern, target_name: &str) -> bool {
    if let Some(sn) = subject_name
        && sn.as_str() == target_name
    {
        return true;
    }
    pattern_binders(pattern)
        .into_iter()
        .any(|b| b.as_str() == target_name)
}

fn pattern_binders(pattern: &WhenPattern) -> Vec<&Binder> {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields.iter().collect(),
        WhenPattern::List { elements, tail } => {
            let mut v: Vec<&Binder> = elements.iter().collect();
            if let Some(t) = tail {
                v.push(t);
            }
            v
        }
        WhenPattern::Tuple(items) => items.iter().collect(),
        WhenPattern::Pair(a, b) => vec![a, b],
        WhenPattern::Var(b) => vec![b],
        WhenPattern::Wildcard | WhenPattern::Literal(_) => vec![],
    }
}

#[cfg(test)]
mod tests;
