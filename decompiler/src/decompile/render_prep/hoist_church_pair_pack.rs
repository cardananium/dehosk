//! Hoist inline 2-arg Church-pair-pack constructors to a named helper.
//!
//! The Plutus/UPLC Church-pair idiom is `fn(x) { x(a, b) }` — a
//! 1-arg Lambda whose body applies its parameter to a fixed pair
//! `(a, b)`; the consumer is a 2-arg callback receiving the packed
//! values. One validator block can build several such packs
//! inline. ≥ 2 occurrences hoist to a parameterized helper
//! `fn pair_pack(a, b) { fn(x) { x(a, b) } }`; the captured
//! `arg1`/`arg2` differ per site, so the helper takes them as
//! parameters and `pair_pack(a, b)` returns exactly the Lambda
//! value the inline form does.
//!
//! Exact match: `Lambda { params: [Binder("x_N", _)], body:
//! Apply { function: Var(x_N_id), args: [_, _] } }` — 1 outer
//! param, body an Apply on that param with exactly 2 args. Any
//! other inner arity is skipped. Both `args` must be
//! `super::purity::is_pure_value`. Inline they are evaluated only
//! when the consumer applies the lambda; after the hoist they are
//! evaluated eagerly at the `pair_pack(arg1, arg2)` call site, so
//! eager and lazy must be observationally identical — which holds
//! for pure values. Order relative to
//! `hoist_church_bool_selectors` is cosmetic: those selectors are
//! 2-param Lambdas and cannot match this pass's 1-param outer
//! shape either way.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, children, plain_children, rebuild_plain, take};

pub(super) fn hoist_church_pair_pack(expr: PseudoExpr) -> PseudoExpr {
    let mut count = 0usize;
    count_packs(&expr, &mut count);
    if count < 2 {
        return expr;
    }
    let helper_id = VarId::fresh_binding();
    let rewritten = rewrite(expr, helper_id);
    PseudoExpr::Let {
        name: "pair_pack".to_string(),
        id: Some(helper_id),
        value: PBox::new(build_pair_pack_helper()),
        body: PBox::new(rewritten),
    }
}

/// `Some((a, b))` if `expr` is the inline Church-pair-pack shape
/// `fn(x) { x(a, b) }` — a 1-param Lambda whose body applies that
/// param to exactly 2 args.
///
/// Both args MUST be pure values: the hoist moves them from the lazy
/// Lambda body to the eager `pair_pack` call site.
fn match_pack(expr: &PseudoExpr) -> Option<(&PseudoExpr, &PseudoExpr)> {
    let PseudoExpr::Lambda { params, body } = expr else {
        return None;
    };
    if params.len() != 1 {
        return None;
    }
    let outer_id = params[0].var_id();
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    // Peel any `Force(...)` wrappers off the function head: thunked-
    // consumer patterns surface as `Apply { function: Force(Var(x)),
    // args }`, and the identity of `x` sits on the inner Var.
    let mut fn_inner = function.as_ref();
    while let PseudoExpr::Force(inner) = fn_inner {
        fn_inner = inner;
    }
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = fn_inner
    else {
        return None;
    };
    if *fn_id != outer_id {
        return None;
    }
    if !super::purity::is_pure_value(&args[0]) || !super::purity::is_pure_value(&args[1]) {
        return None;
    }
    Some((&args[0], &args[1]))
}

fn build_pair_pack_helper() -> PseudoExpr {
    let a_id = VarId::fresh_binding();
    let b_id = VarId::fresh_binding();
    let x_id = VarId::fresh_binding();
    PseudoExpr::Lambda {
        params: vec![Binder::new("a", a_id), Binder::new("b", b_id)],
        body: PBox::new(PseudoExpr::Lambda {
            params: vec![Binder::new("x", x_id)],
            body: PBox::new(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id("x", x_id)),
                args: vec![
                    PseudoExpr::var_with_id("a", a_id),
                    PseudoExpr::var_with_id("b", b_id),
                ]
                .into(),
            }),
        }),
    }
}

fn count_packs(expr: &PseudoExpr, out: &mut usize) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if match_pack(expr).is_some() {
            *out += 1;
        }
        for child in children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// One pending step of [`rewrite`]'s explicit stack. `helper_id` is a
/// `Copy` constant for the whole walk, so no job needs to carry it.
enum PackStep {
    Enter(PseudoExpr),
    Post(PackPost),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum PackPost {
    /// A matched inline pack, whose two already-rewritten captured args
    /// become the `pair_pack(a, b)` call. The Lambda around them is gone —
    /// the walk does not descend into it; it descends into `a`
    /// and `b` directly.
    Pack,
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

/// TOP-DOWN: the pack test runs on a node BEFORE any
/// descent, and a hit replaces the node outright rather than rebuilding it —
/// so it is an `Enter` decision, not a `Post` one. Everywhere else children
/// are pushed in REVERSE so they pop in source order, and are popped off
/// `done` in that same order when the node is rebuilt.
fn rewrite(expr: PseudoExpr, helper_id: VarId) -> PseudoExpr {
    let mut steps: Vec<PackStep> = vec![PackStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            PackStep::Enter(expr) => {
                if let Some((a, b)) = match_pack(&expr) {
                    let a = a.clone();
                    let b = b.clone();
                    steps.push(PackStep::Post(PackPost::Pack));
                    steps.push(PackStep::Enter(b));
                    steps.push(PackStep::Enter(a));
                    continue;
                }
                match expr {
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        steps.push(PackStep::Post(PackPost::Let { name, id }));
                        steps.push(PackStep::Enter(body.into_inner()));
                        steps.push(PackStep::Enter(value.into_inner()));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        steps.push(PackStep::Post(PackPost::Lambda { params }));
                        steps.push(PackStep::Enter(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        steps.push(PackStep::Post(PackPost::RecFn { name, params }));
                        steps.push(PackStep::Enter(body.into_inner()));
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
                        steps.push(PackStep::Post(PackPost::When {
                            subject_name,
                            clause_meta,
                        }));
                        for c in clause_children.into_iter().rev() {
                            steps.push(PackStep::Enter(c));
                        }
                        steps.push(PackStep::Enter(subject.into_inner()));
                    }
                    // Every remaining non-leaf kind rebuilt verbatim with each child
                    // rewritten, which is exactly `plain_children` / `rebuild_plain`;
                    // the leaves fall through `Err` untouched.
                    other => match plain_children(other) {
                        Ok((kind, children)) => {
                            steps.push(PackStep::Post(PackPost::Plain(kind)));
                            for c in children.into_iter().rev() {
                                steps.push(PackStep::Enter(c));
                            }
                        }
                        Err(leaf) => done.push(leaf),
                    },
                }
            }
            PackStep::Post(post) => {
                let rebuilt = match post {
                    PackPost::Pack => {
                        let b = done.pop().expect("pack second arg");
                        let a = done.pop().expect("pack first arg");
                        PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::var_with_id("pair_pack", helper_id)),
                            args: vec![a, b].into(),
                        }
                    }
                    PackPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    PackPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    PackPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    PackPost::When {
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
                    PackPost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

#[cfg(test)]
mod tests;
