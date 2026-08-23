//! Inline single-use `let X = e` consumed by an
//! `expect Pattern = X` (rendered from `when X is { P -> body; _ ->
//! fail }`).
//!
//! The intermediate binder is dead weight when its only use is the
//! `expect` destructure. `expect P = X; body` renders from a
//! 2-clause `When { subject: Var(X), subject_name: None, clauses:
//! [P -> body; _ -> fail] }` (see
//! `pseudo/pretty_helpers/dispatch.rs: extract_expect_pattern`).
//! The rewrite substitutes `e` as the `When` subject and drops the
//! `Let`.
//!
//! `e` must not contain `X`. `X` must not appear free in any clause
//! body or guard — after the rewrite the outer `X` is unbound
//! there. The subject `Var` must carry `id: Some(id_X)` matching
//! the let, and `subject_name` must be `None`. The first clause's
//! pattern must not be `Wildcard`/`Var` (those are not `expect`);
//! optional trailing `_ -> fail` clauses are kept. Clauses are
//! copied unchanged; a pattern binder shadowing `X` inside its own
//! clause body is fine — those uses are the pattern's own binding.

use super::let_disambiguation::pattern_binds_name;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::{ExprFolder, ExprVisitor};
use crate::pseudo::var_id::VarId;

struct InlineExpectSubjects;

impl ExprFolder for InlineExpectSubjects {
    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        if let Some(when_subject) = try_inline_subject(&name, id, &value, &body) {
            return when_subject;
        }
        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }

    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }
}

pub(super) fn inline_expect_subjects(expr: PseudoExpr) -> PseudoExpr {
    InlineExpectSubjects.fold(expr)
}

/// If `body` is `When { subject: Var(name), ..., clauses: [<expect-form>] }`,
/// substitute `value` for the subject and return the new When; otherwise
/// return None.
fn try_inline_subject(
    name: &str,
    let_id: Option<VarId>,
    value: &PseudoExpr,
    body: &PseudoExpr,
) -> Option<PseudoExpr> {
    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = body
    else {
        return None;
    };
    // Subject of the When must be `Var(name, id_X)`.
    let subject_is_var_x = match subject.as_ref() {
        PseudoExpr::Var {
            name: sname,
            id: sid,
        } => sname == name && var_ids_match(*sid, let_id),
        _ => return None,
    };
    if !subject_is_var_x {
        return None;
    }
    // `subject_name` is the alias in `when X as Y is { ... }`. Bail
    // when it is `Some` and equals `name`: the alias then shadows
    // the binder, and clause bodies could be reading either one.
    if let Some(sn) = subject_name.as_ref()
        && sn.as_str() == name
    {
        return None;
    }
    // Clauses must form an expect-pattern (one non-fail clause
    // with a refutable pattern, all others fail), mirroring the
    // renderer's `extract_expect_pattern`.
    //
    // Multi-clause Whens are intentionally NOT inlined: pulling a
    // named binder (`let lookup_result = ...`) into an anonymous
    // When subject loses the name, so those keep the let-then-when
    // shape.
    let mut real_clause_count = 0usize;
    for clause in clauses {
        if clause.guard.is_some() {
            return None;
        }
        if is_fail_expr(&clause.body) {
            continue;
        }
        real_clause_count += 1;
        if matches!(&clause.pattern, WhenPattern::Wildcard | WhenPattern::Var(_)) {
            return None;
        }
    }
    if real_clause_count != 1 {
        return None;
    }
    // `name` must NOT appear free in `value` — otherwise inlining
    // changes scoping. (Lambdas/Let inside value can rebind `name`;
    // shadow-aware check.)
    if expr_contains_free_var(value, name) {
        return None;
    }
    // `name` must NOT appear free in any clause body or guard — after
    // the rewrite the outer `name` is unbound there.
    for clause in clauses {
        if pattern_binds_name(&clause.pattern, name) {
            // Pattern shadows the outer `name`; free uses of it in the
            // body are the pattern's own binding, so this clause is
            // safe.
            continue;
        }
        if expr_contains_free_var(&clause.body, name) {
            return None;
        }
        if let Some(g) = &clause.guard
            && expr_contains_free_var(g, name)
        {
            return None;
        }
    }
    // All preconditions OK — substitute.
    Some(PseudoExpr::When {
        subject: PBox::new(value.clone()),
        subject_name: subject_name.clone(),
        clauses: clauses.clone(),
    })
}

fn var_ids_match(a: Option<VarId>, b: Option<VarId>) -> bool {
    match (a, b) {
        (Some(x), Some(y)) => x == y,
        (None, None) => true,
        _ => false, // mismatch (one carries an id, the other doesn't): bail
    }
}

fn is_fail_expr(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Error { .. })
        || matches!(expr, PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::Error)
}

/// Scope-aware free-variable check; a binder that
/// shadows `target` blocks matches in its scope.
fn expr_contains_free_var(expr: &PseudoExpr, target: &str) -> bool {
    struct V<'a> {
        target: &'a str,
        blocked_depth: usize,
        found: bool,
    }
    impl ExprVisitor for V<'_> {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            if self.blocked_depth == 0 && name == self.target {
                self.found = true;
            }
        }
        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            if params.iter().any(|p| p == self.target) {
                self.blocked_depth += 1;
            }
        }
        fn visit_lambda_post(&mut self, params: &[Binder]) {
            if params.iter().any(|p| p == self.target) {
                self.blocked_depth -= 1;
            }
        }
        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            if name == self.target || params.iter().any(|p| p == self.target) {
                self.blocked_depth += 1;
            }
        }
        fn visit_recfn_post(&mut self, name: &Binder, params: &[Binder]) {
            if name == self.target || params.iter().any(|p| p == self.target) {
                self.blocked_depth -= 1;
            }
        }
        fn visit_let_value_post(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) {
            if name == self.target {
                self.blocked_depth += 1;
            }
        }
        fn visit_let_post(&mut self, name: &str) {
            if name == self.target {
                self.blocked_depth -= 1;
            }
        }
        fn visit_when_clause_pre(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            let binds = subject_name.is_some_and(|n| n == self.target)
                || pattern_binds_name(&clause.pattern, self.target);
            if binds {
                self.blocked_depth += 1;
            }
        }
        fn visit_when_clause_post(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            let binds = subject_name.is_some_and(|n| n == self.target)
                || pattern_binds_name(&clause.pattern, self.target);
            if binds {
                self.blocked_depth -= 1;
            }
        }
    }
    let mut v = V {
        target,
        blocked_depth: 0,
        found: false,
    };
    v.walk(expr);
    v.found
}

#[cfg(test)]
mod tests;
