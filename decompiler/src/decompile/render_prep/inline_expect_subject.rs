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

struct InlineExpectSubjects {
    /// References of each variable name in the tree, pattern literals
    /// included. A name referenced once is referenced only by the `when`
    /// subject being inlined, so the free-variable scans — a walk of the
    /// whole value and of every clause, at every `let` of a chain as deep
    /// as the script likes — have nothing to find. The fold moves nodes but
    /// never copies or drops them, and an inline removes exactly the subject
    /// reference, so the counts stay exact.
    references: std::collections::HashMap<String, usize>,
}

impl ExprFolder for InlineExpectSubjects {
    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let only_the_subject = self.references.get(&name).is_some_and(|n| *n <= 1);
        if can_inline_subject(&name, id, &value, &body, only_the_subject) {
            if let Some(n) = self.references.get_mut(&name) {
                *n -= 1;
            }
            let PseudoExpr::When {
                subject_name,
                clauses,
                ..
            } = body
            else {
                unreachable!("can_inline_subject checked the shape");
            };
            return PseudoExpr::When {
                subject: PBox::new(value),
                subject_name,
                clauses,
            };
        }
        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }

    // Folded flat, literal patterns left as they are — what this pass's
    // pattern hook always did — so a deep `when` costs no stack.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn machine_keeps_pattern_literals(&self) -> bool {
        true
    }
}

pub(super) fn inline_expect_subjects(expr: PseudoExpr) -> PseudoExpr {
    let mut references = std::collections::HashMap::new();
    let mut pending: Vec<&PseudoExpr> = vec![&expr];
    while let Some(node) = pending.pop() {
        if let PseudoExpr::Var { name, .. } = node {
            *references.entry(name.clone()).or_insert(0) += 1;
        }
        node.child_refs_into(&mut pending);
    }
    InlineExpectSubjects { references }.fold(expr)
}

/// Whether `body` is `When { subject: Var(name), ..., clauses: [<expect-form>] }`
/// whose subject `value` can take. `only_the_subject`: `name` is referenced
/// nowhere but that subject, so neither `value` nor a clause can mention it.
fn can_inline_subject(
    name: &str,
    let_id: Option<VarId>,
    value: &PseudoExpr,
    body: &PseudoExpr,
    only_the_subject: bool,
) -> bool {
    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = body
    else {
        return false;
    };
    // Subject of the When must be `Var(name, id_X)`.
    let subject_is_var_x = match subject.as_ref() {
        PseudoExpr::Var {
            name: sname,
            id: sid,
        } => sname == name && var_ids_match(*sid, let_id),
        _ => return false,
    };
    if !subject_is_var_x {
        return false;
    }
    // `subject_name` is the alias in `when X as Y is { ... }`. Bail
    // when it is `Some` and equals `name`: the alias then shadows
    // the binder, and clause bodies could be reading either one.
    if let Some(sn) = subject_name.as_ref()
        && sn.as_str() == name
    {
        return false;
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
            return false;
        }
        if is_fail_expr(&clause.body) {
            continue;
        }
        real_clause_count += 1;
        if matches!(&clause.pattern, WhenPattern::Wildcard | WhenPattern::Var(_)) {
            return false;
        }
    }
    if real_clause_count != 1 {
        return false;
    }
    // `name` must NOT appear free in `value` — otherwise inlining
    // changes scoping. (Lambdas/Let inside value can rebind `name`;
    // shadow-aware check.)
    if only_the_subject {
        return true;
    }
    if expr_contains_free_var(value, name) {
        return false;
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
            return false;
        }
        if let Some(g) = &clause.guard
            && expr_contains_free_var(g, name)
        {
            return false;
        }
    }
    true
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
