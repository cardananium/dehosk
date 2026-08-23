//! Hoist repeated Church-encoded Bool selector lambdas to top-level
//! named consts.
//!
//! After `church_bool_in_list_fold` rewrites Bool literals in Church
//! contexts to explicit lambdas (`fn(t, _) { t }` / `fn(_, f) { f }`),
//! the same shape recurs many times in one script. This pass hoists
//! each selector used ≥ 2 times to `church_true` / `church_false`.
//! A const for a single use is noise.
//!
//! Shape: a 2-param Lambda whose body is a `Var` of params[0]
//! (church-true) or params[1] (church-false). Param names are not
//! inspected. `church_bool_in_list_fold` mints fresh VarIds per emit,
//! so occurrences are alpha-equivalent rather than identical; matching
//! is by shape and every hit becomes one canonical Var.
//!
//! After `church_bool_in_list_fold` (the lambdas must already exist).
//! Before `promote_validator_entry_first`, so the hoisted const lands
//! in the top-level Let chain.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, children, plain_children, rebuild_plain, take};

pub(super) fn hoist_church_bool_selectors(expr: PseudoExpr) -> PseudoExpr {
    let mut true_count = 0usize;
    let mut false_count = 0usize;
    count_selectors(&expr, &mut true_count, &mut false_count);

    // Only hoist if 2+ occurrences (a const for 1 use is just noise).
    let mut hoist_true_id: Option<VarId> = None;
    let mut hoist_false_id: Option<VarId> = None;
    if true_count >= 2 {
        hoist_true_id = Some(VarId::fresh_binding());
    }
    if false_count >= 2 {
        hoist_false_id = Some(VarId::fresh_binding());
    }
    if hoist_true_id.is_none() && hoist_false_id.is_none() {
        return expr;
    }

    let rewritten = rewrite(expr, hoist_true_id, hoist_false_id);

    // Prepend the hoisted consts to the top-level Let chain.
    let mut body = rewritten;
    if let Some(false_id) = hoist_false_id {
        body = PseudoExpr::Let {
            name: "church_false".to_string(),
            id: Some(false_id),
            value: PBox::new(build_church_false_lambda()),
            body: PBox::new(body),
        };
    }
    if let Some(true_id) = hoist_true_id {
        body = PseudoExpr::Let {
            name: "church_true".to_string(),
            id: Some(true_id),
            value: PBox::new(build_church_true_lambda()),
            body: PBox::new(body),
        };
    }
    body
}

fn build_church_true_lambda() -> PseudoExpr {
    let t_id = VarId::fresh_binding();
    let dead_id = VarId::fresh_binding();
    PseudoExpr::Lambda {
        params: vec![Binder::new("t", t_id), Binder::new("_", dead_id)],
        body: PBox::new(PseudoExpr::var_with_id("t", t_id)),
    }
}

fn build_church_false_lambda() -> PseudoExpr {
    let dead_id = VarId::fresh_binding();
    let f_id = VarId::fresh_binding();
    PseudoExpr::Lambda {
        params: vec![Binder::new("_", dead_id), Binder::new("f", f_id)],
        body: PBox::new(PseudoExpr::var_with_id("f", f_id)),
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Selector {
    True,
    False,
}

/// A 2-param Lambda whose body is `Var(id)` bound to params[0]
/// (→ Church-True) or params[1] (→ Church-False); `None` otherwise.
fn match_selector(expr: &PseudoExpr) -> Option<Selector> {
    let PseudoExpr::Lambda { params, body } = expr else {
        return None;
    };
    if params.len() != 2 {
        return None;
    }
    let PseudoExpr::Var {
        id: Some(body_id), ..
    } = body.as_ref()
    else {
        return None;
    };
    if *body_id == params[0].var_id() {
        Some(Selector::True)
    } else if *body_id == params[1].var_id() {
        Some(Selector::False)
    } else {
        None
    }
}

fn count_selectors(expr: &PseudoExpr, true_count: &mut usize, false_count: &mut usize) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if let Some(sel) = match_selector(expr) {
            match sel {
                Selector::True => *true_count += 1,
                Selector::False => *false_count += 1,
            }
        }
        for child in children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// One pending step of [`rewrite`]'s explicit stack. The two hoist ids are
/// `Copy` constants for the whole walk, so no job needs to carry them.
enum SelStep {
    Enter(PseudoExpr),
    Post(SelPost),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum SelPost {
    Let {
        name: String,
        id: Option<VarId>,
    },
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    When {
        subject_name: Option<Binder>,
        /// Per clause: its pattern (never descended into) and whether it
        /// had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// TOP-DOWN: the selector test runs on a node BEFORE any
/// descent, and a hit returns a bare `Var` without visiting the Lambda's
/// children at all — so it is an `Enter` decision with no `Post` step.
/// A selector whose side was NOT hoisted falls through to the ordinary
/// rebuild. Everywhere else children are pushed in REVERSE so they pop in
/// source order, and are popped off `done` in that same order when the node
/// is rebuilt.
fn rewrite(
    expr: PseudoExpr,
    hoist_true_id: Option<VarId>,
    hoist_false_id: Option<VarId>,
) -> PseudoExpr {
    let mut steps: Vec<SelStep> = vec![SelStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            SelStep::Enter(expr) => {
                // Substitute matching Lambdas with Var refs to the hoisted consts.
                if let Some(sel) = match_selector(&expr) {
                    match (sel, hoist_true_id, hoist_false_id) {
                        (Selector::True, Some(id), _) => {
                            done.push(PseudoExpr::var_with_id("church_true", id));
                            continue;
                        }
                        (Selector::False, _, Some(id)) => {
                            done.push(PseudoExpr::var_with_id("church_false", id));
                            continue;
                        }
                        _ => {}
                    }
                }
                match expr {
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        steps.push(SelStep::Post(SelPost::Let { name, id }));
                        steps.push(SelStep::Enter(body.into_inner()));
                        steps.push(SelStep::Enter(value.into_inner()));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        steps.push(SelStep::Post(SelPost::Lambda { params }));
                        steps.push(SelStep::Enter(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        steps.push(SelStep::Post(SelPost::RecFn { name, params }));
                        steps.push(SelStep::Enter(body.into_inner()));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let mut clause_meta = Vec::with_capacity(clauses.len());
                        let mut clause_children = Vec::new();
                        for c in clauses {
                            clause_meta.push((c.pattern, c.guard.is_some()));
                            if let Some(g) = c.guard {
                                clause_children.push(g);
                            }
                            clause_children.push(c.body);
                        }
                        steps.push(SelStep::Post(SelPost::When {
                            subject_name,
                            clause_meta,
                        }));
                        for c in clause_children.into_iter().rev() {
                            steps.push(SelStep::Enter(c));
                        }
                        steps.push(SelStep::Enter(subject.into_inner()));
                    }
                    // Every remaining non-leaf kind rebuilt verbatim with each child
                    // rewritten, which is exactly `plain_children` / `rebuild_plain`;
                    // the leaves fall through `Err` untouched.
                    other => match plain_children(other) {
                        Ok((kind, children)) => {
                            steps.push(SelStep::Post(SelPost::Plain(kind)));
                            for c in children.into_iter().rev() {
                                steps.push(SelStep::Enter(c));
                            }
                        }
                        Err(leaf) => done.push(leaf),
                    },
                }
            }
            SelStep::Post(post) => {
                let rebuilt = match post {
                    SelPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    SelPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    SelPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    SelPost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = take(&mut done, total).into_iter();
                        let subject = parts.next().expect("when subject");
                        let clauses = clause_meta
                            .into_iter()
                            .map(|(pattern, has_guard)| WhenClause {
                                pattern,
                                guard: has_guard.then(|| parts.next().expect("when guard")),
                                body: parts.next().expect("when clause body"),
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    SelPost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

// Keeps the `HashSet` import from warning as unused.
#[allow(dead_code)]
fn _unused(_x: HashSet<VarId>) {}

#[cfg(test)]
mod tests;
