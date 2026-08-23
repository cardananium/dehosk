//! Replace inline Y-combinator-shaped `Lambda{[v], RecFn{[self, x],
//! Apply{Var(v), [Var(self), Var(x)]}}}` literals with a reference to
//! the top-level `y_combinator` const when one exists.
//!
//! Scripts emit many structurally-identical Y-combinator lambdas
//! inside the validator body. The top-level chain already defines the
//! canonical `const y_combinator = fn(v) { rec fn self(x) { v(self, x) } }`,
//! alpha-equivalent to every one of them.
//!
//! Inline Y-comb values become `Var(y_combinator)`; only the value
//! collapses to a one-line var ref. The let-binding itself stays,
//! because downstream `when match_subject_N is { Pair(...) -> ... }`
//! destructures reference its name.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

pub(super) fn cse_inline_y_comb(expr: PseudoExpr) -> PseudoExpr {
    let Some((yc_id, yc_name)) = find_top_level_y_comb(&expr) else {
        return expr;
    };
    rewrite(expr, yc_id, &yc_name, yc_id)
}

/// Walk the let chain, return the (VarId, name) of the first top-level
/// let whose value matches the Y-comb shape.
fn find_top_level_y_comb(expr: &PseudoExpr) -> Option<(VarId, String)> {
    let mut cur = expr;
    while let PseudoExpr::Let {
        name,
        id,
        value,
        body,
    } = cur
    {
        if let Some(vid) = id {
            if matches_y_comb(value) {
                return Some((*vid, name.clone()));
            }
        }
        cur = body;
    }
    None
}

/// Match `Lambda { [v], RecFn { name, [x], Apply { Var(v), [Var(name), Var(x)] } } }`.
/// Returns true iff alpha-equivalent to the canonical Y-comb shape.
fn matches_y_comb(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let v_id = params[0].id;
    let PseudoExpr::RecFn {
        name,
        params: rec_params,
        body: rec_body,
    } = body.as_ref()
    else {
        return false;
    };
    if rec_params.len() != 1 {
        return false;
    }
    let self_id = name.id;
    let x_id = rec_params[0].id;
    let PseudoExpr::Apply { function, args } = rec_body.as_ref() else {
        return false;
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        return false;
    };
    if *fn_id != v_id || args.len() != 2 {
        return false;
    }
    let PseudoExpr::Var {
        id: Some(arg0_id), ..
    } = &args[0]
    else {
        return false;
    };
    let PseudoExpr::Var {
        id: Some(arg1_id), ..
    } = &args[1]
    else {
        return false;
    };
    *arg0_id == self_id && *arg1_id == x_id
}

/// One pending step of [`rewrite`]'s explicit stack — same shape as the
/// sibling render-prep passes in `scope_recurse` (`fold_identity_aliases`
/// in particular): no scope of its own to thread, so a step carries no
/// environment; only `Let` gets its own arm (the Y-comb-value check),
/// everything else is a [`PlainPost`].
enum RewriteStep {
    Enter(PseudoExpr),
    Post(RewritePost),
}

enum RewritePost {
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
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(super::scope_recurse::PlainPost),
}

fn rewrite(expr: PseudoExpr, yc_id: VarId, yc_name: &str, canonical_id: VarId) -> PseudoExpr {
    use super::scope_recurse::{plain_children, rebuild_plain, take};

    let mut steps: Vec<RewriteStep> = vec![RewriteStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RewriteStep::Enter(expr) => match expr {
                // Inline Y-comb values become a Var ref; the canonical
                // binding's own value is left alone.
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(RewriteStep::Post(RewritePost::Let { name, id }));
                    steps.push(RewriteStep::Enter(body.into_inner()));
                    let is_canonical = id.is_some_and(|v| v == canonical_id);
                    if !is_canonical && matches_y_comb(&value) {
                        done.push(PseudoExpr::Var {
                            name: yc_name.to_string(),
                            id: Some(yc_id),
                        });
                    } else {
                        steps.push(RewriteStep::Enter(value.into_inner()));
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(RewriteStep::Post(RewritePost::Lambda { params }));
                    steps.push(RewriteStep::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(RewriteStep::Post(RewritePost::RecFn { name, params }));
                    steps.push(RewriteStep::Enter(body.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut bodies_and_guards = Vec::with_capacity(clauses.len());
                    for c in clauses {
                        clause_meta.push((c.pattern, c.guard.is_some()));
                        bodies_and_guards.push((c.guard, c.body));
                    }
                    steps.push(RewriteStep::Post(RewritePost::When {
                        subject_name,
                        clause_meta,
                    }));
                    for (guard, body) in bodies_and_guards.into_iter().rev() {
                        steps.push(RewriteStep::Enter(body));
                        if let Some(g) = guard {
                            steps.push(RewriteStep::Enter(g));
                        }
                    }
                    steps.push(RewriteStep::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RewriteStep::Post(RewritePost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(RewriteStep::Enter(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            RewriteStep::Post(post) => {
                let rebuilt = match post {
                    RewritePost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    RewritePost::Lambda { params } => {
                        let body = done.pop().expect("lambda body");
                        PseudoExpr::Lambda {
                            params,
                            body: PBox::new(body),
                        }
                    }
                    RewritePost::RecFn { name, params } => {
                        let body = done.pop().expect("recfn body");
                        PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(body),
                        }
                    }
                    RewritePost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total: usize = 1 + clause_meta
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
                    RewritePost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the rewrite machine must leave one result");
    done.pop().expect("rewrite result")
}
