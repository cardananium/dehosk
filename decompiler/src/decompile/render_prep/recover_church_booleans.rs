//! Recover native `if`/`else` from the church-encoded Boolean residue
//! pattern.
//!
//! V1 scripts encode booleans as zero-arity Constr tags bound as
//! top-level consts. A comparison emits those tags and the
//! consumer decodes by matching against a singleton tag-1 type:
//! `let r = if x == y { e } else { b }; when r is { Unknown_S_NN_1
//! -> THEN; _ -> ELSE }`. Polarity: cond=true → `r = e` (tag 0) →
//! no match → ELSE; cond=false → `r = b` (tag 1) → match → THEN.
//! Rewrite to `if x == y { ELSE } else { THEN }`. The singleton
//! `Unknown_S_*` ADT decls the rewrite orphans are dropped by
//! stub-adt's reachability collector when it runs after this
//! pass.
//!
//! Strict shape: `Let { value: If { cond, then: known-tag, else:
//! known-tag }, body: When { subject: Var(let_id), clauses:
//! [Constr, Wildcard] } }`. Tags must differ between then-branch
//! and else-branch. The constructor clause's tag must equal one
//! of the branches' tags (else the `when` always falls to
//! wildcard — a separate constant-fold case, not handled here).
//! The constructor pattern must be zero-arity (no field binders)
//! so the THEN body can't depend on extracted fields.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain};

pub(super) fn recover_church_booleans(expr: PseudoExpr) -> PseudoExpr {
    let const_tags = collect_constr_tag_consts(&expr);
    if const_tags.is_empty() {
        return expr;
    }
    rewrite(expr, &const_tags)
}

/// Walk top-level lets, collect mappings from let-binder VarId → tag
/// for lets whose value is a zero-arity `Constr`.
fn collect_constr_tag_consts(expr: &PseudoExpr) -> HashMap<VarId, usize> {
    let mut map = HashMap::new();
    let mut cur = expr;
    while let PseudoExpr::Let {
        id, value, body, ..
    } = cur
    {
        if let (Some(vid), Some(tag)) = (id, constr_zero_arity_tag(value)) {
            map.insert(*vid, tag);
        }
        cur = body;
    }
    map
}

/// Returns the Constr tag if `expr` is a zero-arity `Constr`.
fn constr_zero_arity_tag(expr: &PseudoExpr) -> Option<usize> {
    if let PseudoExpr::Constr { tag, fields, .. } = expr
        && fields.is_empty()
    {
        return Some(*tag);
    }
    None
}

/// Resolve a tag from `expr` if it's either a zero-arity Constr or a
/// Var bound to one (looked up via `const_tags`).
fn resolve_bool_tag(expr: &PseudoExpr, const_tags: &HashMap<VarId, usize>) -> Option<usize> {
    let (inner, _trace) = peel_trace(expr);
    if let Some(tag) = constr_zero_arity_tag(inner) {
        return Some(tag);
    }
    if let PseudoExpr::Var { id: Some(vid), .. } = inner {
        return const_tags.get(vid).copied();
    }
    None
}

/// Peel leading `Trace` wrappers from `expr`, returning the inner
/// expression plus the `Trace` nodes in OUTERMOST-FIRST order so a
/// caller can re-attach them around a rewritten branch body: an
/// if-arm written `trace @"…": sentinel` must keep its trace for
/// the assertion behaviour to survive.
fn peel_trace(expr: &PseudoExpr) -> (&PseudoExpr, Vec<&PseudoExpr>) {
    let mut cur = expr;
    let mut traces: Vec<&PseudoExpr> = Vec::new();
    while let PseudoExpr::Trace { value, .. } = cur {
        traces.push(cur);
        cur = value.as_ref();
    }
    (cur, traces)
}

/// Rewrap `body` in the cloned `traces`, OUTERMOST-FIRST, restoring
/// the original trace order.
fn rewrap_traces(body: PseudoExpr, traces: Vec<&PseudoExpr>) -> PseudoExpr {
    let mut cur = body;
    for trace in traces.into_iter().rev() {
        if let PseudoExpr::Trace { message, .. } = trace {
            cur = PseudoExpr::Trace {
                message: message.clone(),
                value: PBox::new(cur),
            };
        }
    }
    cur
}

/// One pending step of [`rewrite`]'s explicit stack: enter a subtree (after
/// its own node-level rewrite fixpoint has run), or — once its queued
/// children are on `done` — reassemble it, carrying whatever isn't a child
/// (a `Let`/`Lambda`/`RecFn`/`When`'s non-child parts, or a `PlainPost` tag
/// for everything `plain_children`/`rebuild_plain` already know how to
/// split and rebuild).
enum RewriteStep {
    Enter(PseudoExpr),
    PostLet {
        name: String,
        id: Option<VarId>,
    },
    PostLambda {
        params: Vec<Binder>,
    },
    PostRecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    /// `patterns`/`has_guard` line up with the clauses, in source order —
    /// `done` gives back subject then, per clause, guard (if present) then
    /// body, so reassembly walks both from the tail.
    PostWhen {
        subject_name: Option<Binder>,
        patterns: Vec<WhenPattern>,
        has_guard: Vec<bool>,
    },
    PostPlain(PlainPost),
}

/// Applies the node-level rewrite rules at `expr` to a fixpoint. A
/// successful rewrite always produces an `If` or `When` root — never
/// another `Let` — so none of the three checks can match the result again.
fn rewrite_node_fixpoint(mut expr: PseudoExpr, const_tags: &HashMap<VarId, usize>) -> PseudoExpr {
    loop {
        if let Some(rewritten) = try_rewrite(&expr, const_tags) {
            expr = rewritten;
            continue;
        }
        if let Some(rewritten) = try_rewrite_via_option_when(&expr, const_tags) {
            expr = rewritten;
            continue;
        }
        if let Some(rewritten) = try_rewrite_via_generic_when(&expr, const_tags) {
            expr = rewritten;
            continue;
        }
        return expr;
    }
}

fn rewrite(expr: PseudoExpr, const_tags: &HashMap<VarId, usize>) -> PseudoExpr {
    let mut steps = vec![RewriteStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RewriteStep::Enter(expr) => match rewrite_node_fixpoint(expr, const_tags) {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(RewriteStep::PostLet { name, id });
                    steps.push(RewriteStep::Enter(body.into_inner()));
                    steps.push(RewriteStep::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(RewriteStep::PostLambda { params });
                    steps.push(RewriteStep::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(RewriteStep::PostRecFn { name, params });
                    steps.push(RewriteStep::Enter(body.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let patterns = clauses.iter().map(|c| c.pattern.clone()).collect();
                    let has_guard = clauses.iter().map(|c| c.guard.is_some()).collect();
                    steps.push(RewriteStep::PostWhen {
                        subject_name,
                        patterns,
                        has_guard,
                    });
                    for c in clauses.into_iter().rev() {
                        steps.push(RewriteStep::Enter(c.body));
                        if let Some(g) = c.guard {
                            steps.push(RewriteStep::Enter(g));
                        }
                    }
                    steps.push(RewriteStep::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RewriteStep::PostPlain(kind));
                        for c in children.into_iter().rev() {
                            steps.push(RewriteStep::Enter(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            RewriteStep::PostLet { name, id } => {
                let body = done.pop().expect("let body");
                let value = done.pop().expect("let value");
                done.push(PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                });
            }
            RewriteStep::PostLambda { params } => {
                let body = done.pop().expect("lambda body");
                done.push(PseudoExpr::Lambda {
                    params,
                    body: PBox::new(body),
                });
            }
            RewriteStep::PostRecFn { name, params } => {
                let body = done.pop().expect("recfn body");
                done.push(PseudoExpr::RecFn {
                    name,
                    params,
                    body: PBox::new(body),
                });
            }
            RewriteStep::PostWhen {
                subject_name,
                patterns,
                has_guard,
            } => {
                let mut clauses: Vec<WhenClause> = Vec::with_capacity(patterns.len());
                for (pattern, guarded) in patterns.into_iter().zip(has_guard).rev() {
                    let body = done.pop().expect("when clause body");
                    let guard = if guarded {
                        Some(done.pop().expect("when clause guard"))
                    } else {
                        None
                    };
                    clauses.push(WhenClause {
                        pattern,
                        guard,
                        body,
                    });
                }
                clauses.reverse();
                let subject = done.pop().expect("when subject");
                done.push(PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                });
            }
            RewriteStep::PostPlain(kind) => {
                let rebuilt = rebuild_plain(kind, &mut done);
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "the rewrite machine must leave one result");
    done.pop().expect("rewrite result")
}

/// Generalisation of `try_rewrite_via_option_when` accepting ANY
/// 2-arm when, not just Some/None. The outer When-on-let-id must
/// still match the `{ Constructor(tag, []) -> THEN; _ -> ELSE }`
/// church-bool eliminator shape; the INNER When (the let-value) may
/// have any pattern pair, provided both arm bodies resolve to
/// distinct known sentinel tags via `resolve_bool_tag` (which peels
/// Trace).
///
/// Catches V1 patterns like:
///
/// ```text
/// let X = when condition_ok is { Unknown_S_13_1 -> trace @"…": b; _ -> e }
/// when X is { Unknown_S_13_1 -> b; _ -> ELSE }
/// ```
///
/// Safety: arm bodies must NOT reference pattern-introduced binders.
/// `resolve_bool_tag` guarantees that — a sentinel is a bare
/// zero-arity Constr or a Var resolving to one, optionally under a
/// Trace, and none of those embed pattern binders.
fn try_rewrite_via_generic_when(
    expr: &PseudoExpr,
    const_tags: &HashMap<VarId, usize>,
) -> Option<PseudoExpr> {
    let PseudoExpr::Let {
        id: Some(let_id),
        value,
        body,
        ..
    } = expr
    else {
        return None;
    };
    // Value must be a 2-arm When with both arms resolving to known
    // sentinel tags.
    let PseudoExpr::When {
        subject: inner_subject,
        clauses: inner_clauses,
        subject_name,
    } = value.as_ref()
    else {
        return None;
    };
    if inner_clauses.len() != 2 {
        return None;
    }
    if inner_clauses[0].guard.is_some() || inner_clauses[1].guard.is_some() {
        return None;
    }
    let arm0_tag = resolve_bool_tag(&inner_clauses[0].body, const_tags)?;
    let arm1_tag = resolve_bool_tag(&inner_clauses[1].body, const_tags)?;
    if arm0_tag == arm1_tag {
        return None;
    }
    // Body must be `when Var(let_id) is { Constructor(tag, []) -> THEN; _ -> ELSE }`.
    let PseudoExpr::When {
        subject: outer_subject,
        clauses: outer_clauses,
        ..
    } = body.as_ref()
    else {
        return None;
    };
    let PseudoExpr::Var {
        id: Some(sub_id), ..
    } = outer_subject.as_ref()
    else {
        return None;
    };
    if *sub_id != *let_id || outer_clauses.len() != 2 {
        return None;
    }
    if outer_clauses[0].guard.is_some() || outer_clauses[1].guard.is_some() {
        return None;
    }
    let (constr_body, constr_tag, wild_body) =
        match (&outer_clauses[0].pattern, &outer_clauses[1].pattern) {
            (WhenPattern::Constructor { tag, fields, .. }, WhenPattern::Wildcard)
                if fields.is_empty() =>
            {
                (&outer_clauses[0].body, *tag, &outer_clauses[1].body)
            }
            (WhenPattern::Wildcard, WhenPattern::Constructor { tag, fields, .. })
                if fields.is_empty() =>
            {
                (&outer_clauses[1].body, *tag, &outer_clauses[0].body)
            }
            _ => return None,
        };
    // Polarity: replace each inner arm's body with the outer body
    // whose tag matches.
    let (new_arm0_body, new_arm1_body) = if constr_tag == arm0_tag {
        (constr_body.clone(), wild_body.clone())
    } else if constr_tag == arm1_tag {
        (wild_body.clone(), constr_body.clone())
    } else {
        return None;
    };
    // Preserve the inner traces around the new bodies in the same
    // polarity: arm0's original trace chain wraps `new_arm0_body`.
    let (_, arm0_traces) = peel_trace(&inner_clauses[0].body);
    let (_, arm1_traces) = peel_trace(&inner_clauses[1].body);
    let new_arm0_body = rewrap_traces(new_arm0_body, arm0_traces);
    let new_arm1_body = rewrap_traces(new_arm1_body, arm1_traces);
    let new_when = PseudoExpr::When {
        subject: inner_subject.clone(),
        subject_name: subject_name.clone(),
        clauses: vec![
            crate::pseudo::ast::WhenClause {
                pattern: inner_clauses[0].pattern.clone(),
                guard: None,
                body: new_arm0_body,
            },
            crate::pseudo::ast::WhenClause {
                pattern: inner_clauses[1].pattern.clone(),
                guard: None,
                body: new_arm1_body,
            },
        ],
    };
    Some(new_when)
}

/// Sibling of `try_rewrite` that recognises an `Option`-based
/// church-bool encoding:
///
/// ```text
/// let X = when Y is { Some(_) -> e; None -> b }
/// when X is { Unknown_S_NN_<tag> -> THEN; _ -> ELSE }
/// ```
///
/// Polarity dispatch is identical to the `If`-shape sibling: resolve
/// each Option arm's body to a known sentinel tag, then substitute
/// the outer When's THEN/ELSE bodies INTO the Some/None arms, whose
/// patterns are kept verbatim. Downstream
/// `fold_when_option_to_is_some` may further reduce to
/// `option.is_some(Y)` when the bodies are pure True/False.
///
/// Safety:
/// - The Option When and the outer When must each have exactly 2
///   clauses, the outer pair a zero-arity Constructor plus a Wildcard.
/// - The Option arms must resolve to distinct sentinel tags.
/// - Guards on either clause disqualify.
fn try_rewrite_via_option_when(
    expr: &PseudoExpr,
    const_tags: &HashMap<VarId, usize>,
) -> Option<PseudoExpr> {
    use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
    let PseudoExpr::Let {
        id: Some(let_id),
        value,
        body,
        ..
    } = expr
    else {
        return None;
    };
    // Value must be `when Y is { Some(_) -> SOME_BODY; None -> NONE_BODY }`.
    let PseudoExpr::When {
        subject: opt_subject,
        clauses: opt_clauses,
        ..
    } = value.as_ref()
    else {
        return None;
    };
    if opt_clauses.len() != 2 {
        return None;
    }
    if opt_clauses[0].guard.is_some() || opt_clauses[1].guard.is_some() {
        return None;
    }
    let (some_body, none_body) = match (&opt_clauses[0].pattern, &opt_clauses[1].pattern) {
        (
            WhenPattern::Constructor {
                shape: ConstructorShape::Known(KnownConstructor::Some),
                ..
            },
            WhenPattern::Constructor {
                shape: ConstructorShape::Known(KnownConstructor::None),
                ..
            },
        ) => (&opt_clauses[0].body, &opt_clauses[1].body),
        (
            WhenPattern::Constructor {
                shape: ConstructorShape::Known(KnownConstructor::None),
                ..
            },
            WhenPattern::Constructor {
                shape: ConstructorShape::Known(KnownConstructor::Some),
                ..
            },
        ) => (&opt_clauses[1].body, &opt_clauses[0].body),
        _ => return None,
    };
    let some_tag = resolve_bool_tag(some_body, const_tags)?;
    let none_tag = resolve_bool_tag(none_body, const_tags)?;
    if some_tag == none_tag {
        return None;
    }
    // Body must be `when Var(let_id) is { Constructor(tag, []) -> THEN; _ -> ELSE }`.
    let PseudoExpr::When {
        subject: outer_subject,
        clauses: outer_clauses,
        ..
    } = body.as_ref()
    else {
        return None;
    };
    let PseudoExpr::Var {
        id: Some(sub_id), ..
    } = outer_subject.as_ref()
    else {
        return None;
    };
    if *sub_id != *let_id || outer_clauses.len() != 2 {
        return None;
    }
    let (constr_body, constr_tag, wild_body) =
        match (&outer_clauses[0].pattern, &outer_clauses[1].pattern) {
            (WhenPattern::Constructor { tag, fields, .. }, WhenPattern::Wildcard)
                if fields.is_empty() =>
            {
                (&outer_clauses[0].body, *tag, &outer_clauses[1].body)
            }
            (WhenPattern::Wildcard, WhenPattern::Constructor { tag, fields, .. })
                if fields.is_empty() =>
            {
                (&outer_clauses[1].body, *tag, &outer_clauses[0].body)
            }
            _ => return None,
        };
    if outer_clauses[0].guard.is_some() || outer_clauses[1].guard.is_some() {
        return None;
    }
    // Polarity: constr_tag == some_tag → Some arm takes constr_body,
    // == none_tag → None arm does; wildcard body takes the other.
    let (new_some_body, new_none_body) = if constr_tag == some_tag {
        (constr_body.clone(), wild_body.clone())
    } else if constr_tag == none_tag {
        (wild_body.clone(), constr_body.clone())
    } else {
        return None;
    };
    // Rebuild the Option When with substituted bodies; patterns
    // and subject Var are re-used verbatim.
    let (orig_some_pattern, orig_none_pattern) = if matches!(
        opt_clauses[0].pattern,
        WhenPattern::Constructor {
            shape: ConstructorShape::Known(KnownConstructor::Some),
            ..
        }
    ) {
        (
            opt_clauses[0].pattern.clone(),
            opt_clauses[1].pattern.clone(),
        )
    } else {
        (
            opt_clauses[1].pattern.clone(),
            opt_clauses[0].pattern.clone(),
        )
    };
    let new_when = PseudoExpr::When {
        subject: opt_subject.clone(),
        subject_name: None,
        clauses: vec![
            crate::pseudo::ast::WhenClause {
                pattern: orig_some_pattern,
                guard: None,
                body: new_some_body,
            },
            crate::pseudo::ast::WhenClause {
                pattern: orig_none_pattern,
                guard: None,
                body: new_none_body,
            },
        ],
    };
    Some(new_when)
}

fn try_rewrite(expr: &PseudoExpr, const_tags: &HashMap<VarId, usize>) -> Option<PseudoExpr> {
    // Outer pattern: `Let { value: If { … }, body: When { … } }`.
    let PseudoExpr::Let {
        id: Some(let_id),
        value,
        body,
        ..
    } = expr
    else {
        return None;
    };
    let PseudoExpr::If {
        condition,
        then_branch,
        else_branch,
    } = value.as_ref()
    else {
        return None;
    };
    // Branches must each resolve to a known tag, and the tags must differ.
    // Peel `Trace` wrappers off the if-arms first: the assertion form
    // `if cond { trace @"msg": b } else { e }` needs its trace kept
    // around whichever output branch the polarity chooses.
    let (then_inner, then_traces) = peel_trace(then_branch);
    let (else_inner, else_traces) = peel_trace(else_branch);
    let then_tag = resolve_bool_tag(then_inner, const_tags)?;
    let else_tag = resolve_bool_tag(else_inner, const_tags)?;
    if then_tag == else_tag {
        return None;
    }
    // Body must be `when Var(let_id) is { Constr(matched_tag, []) -> _; _ -> _ }`.
    let PseudoExpr::When {
        subject, clauses, ..
    } = body.as_ref()
    else {
        return None;
    };
    let PseudoExpr::Var {
        id: Some(sub_id), ..
    } = subject.as_ref()
    else {
        return None;
    };
    if *sub_id != *let_id || clauses.len() != 2 {
        return None;
    }
    // One clause must be Constructor (zero-arity), the other Wildcard.
    let (constr_body, constr_tag, wild_body) = match (&clauses[0].pattern, &clauses[1].pattern) {
        (WhenPattern::Constructor { tag, fields, .. }, WhenPattern::Wildcard)
            if fields.is_empty() =>
        {
            (&clauses[0].body, *tag, &clauses[1].body)
        }
        (WhenPattern::Wildcard, WhenPattern::Constructor { tag, fields, .. })
            if fields.is_empty() =>
        {
            (&clauses[1].body, *tag, &clauses[0].body)
        }
        _ => return None,
    };
    // Guards on either clause disqualify; they would be lost.
    if clauses[0].guard.is_some() || clauses[1].guard.is_some() {
        return None;
    }
    // Polarity dispatch:
    //   constr_tag == then_tag → cond=true matches Constr → new_then = constr_body
    //   constr_tag == else_tag → cond=true falls to wildcard → new_then = wild_body
    //   else → the when always picks wildcard (constant-fold); not handled.
    let (new_then, new_else) = if constr_tag == then_tag {
        (constr_body.clone(), wild_body.clone())
    } else if constr_tag == else_tag {
        (wild_body.clone(), constr_body.clone())
    } else {
        return None;
    };
    // Re-wrap the polarity-chosen output branches with the
    // corresponding original if-arm's trace chain.
    let new_then = rewrap_traces(new_then, then_traces);
    let new_else = rewrap_traces(new_else, else_traces);
    Some(PseudoExpr::If {
        condition: PBox::new((**condition).clone()),
        then_branch: PBox::new(new_then),
        else_branch: PBox::new(new_else),
    })
}

#[cfg(test)]
mod tests;
