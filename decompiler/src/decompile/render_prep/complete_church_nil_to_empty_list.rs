//! Complete church-list decode in nil arms: `[] -> church_true` becomes
//! `[] -> []` when the sibling cons arm is already a native list producer.
//!
//! Scott-nil `λn. λc. n` is term-identical to church-true. The hoist
//! folds both into `const church_true`, so a half-decoded map helper
//! keeps the combinator name in the nil arm. The cons arm's native list
//! cell commits the `when` to a list reading; the nil value is that
//! list's Scott-nil, not a guessed boolean.
//!
//! All fail-closed:
//! - Provenance: the nil body is a `Var` of a `Let` named `church_true`
//!   whose value is `Bool(true)` or the K lambda. A literal `Bool(true)`
//!   is not rewritten — it could be a real boolean.
//! - Shape: two guard-free clauses, `[]` and `[x, ..tail]`, either AST
//!   encoding (`WhenPattern::List` or `Known(Nil|Cons)`).
//! - Cons-body witness: every value leaf is a `List` cell or `Error`,
//!   at least one real `List`, and no leaf is the identity rebuild
//!   `[h, ..t]` of the cons binders. That rejects the church-bool
//!   `all` predicate, an all-`Error` body, and a pass-through whose
//!   nil arm may be a boolean sentinel. The cons *pattern* alone is
//!   not a witness (`{ [] -> church_true; [_, ..] -> church_false }`).
//!
//! After `inline_constructor_helpers` and `cse_church_list_map_helpers`,
//! before the `drop_dead_pure_lets` re-run. Copy/const-propagation of
//! `church_true` must not run first — it would erase provenance and
//! print the lying `[] -> True`. Idempotent: the replacement is `[]`,
//! not a `Var`.

use std::collections::HashSet;

use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn complete_church_nil_to_empty_list(expr: PseudoExpr) -> PseudoExpr {
    let nil_ids = collect_church_true_ids(&expr);
    if nil_ids.is_empty() {
        return expr;
    }
    rewrite(expr, &nil_ids)
}

/// Collect the `VarId` of every `let church_true = …` whose value is
/// `Bool(true)` (post-decode) or the K lambda `fn(t, _) { t }` (pre-decode).
/// `fold::ExprVisitor` — unlike `scope_recurse::children` — also walks
/// `WhenPattern::Literal` payloads, so the collection is complete.
fn collect_church_true_ids(expr: &PseudoExpr) -> HashSet<VarId> {
    struct Collector {
        ids: HashSet<VarId>,
    }
    impl ExprVisitor for Collector {
        fn visit_let_value_post(&mut self, name: &str, id: &Option<VarId>, value: &PseudoExpr) {
            if name == "church_true"
                && let Some(vid) = id
                && is_church_true_value(value)
            {
                self.ids.insert(*vid);
            }
        }
    }
    let mut c = Collector {
        ids: HashSet::new(),
    };
    c.walk(expr);
    c.ids
}

/// The two value forms the `church_true` const takes: the decoded
/// `Bool(true)`, or the raw church-true / Scott-nil selector lambda
/// `fn(t, _) { t }` (strict VarId identity between param 0 and the body).
fn is_church_true_value(value: &PseudoExpr) -> bool {
    if matches!(value, PseudoExpr::Bool(true)) {
        return true;
    }
    if let PseudoExpr::Lambda { params, body } = value
        && params.len() == 2
        && let PseudoExpr::Var { id: Some(vid), .. } = body.as_ref()
        && *vid == params[0].id
    {
        return true;
    }
    false
}

/// BOTTOM-UP: `try_complete_nil_arm` runs on a node only after every child
/// has been rewritten, which is exactly where [`rewrite_bottom_up`] calls
/// back.
fn rewrite(expr: PseudoExpr, nil_ids: &HashSet<VarId>) -> PseudoExpr {
    rewrite_bottom_up(expr, |e| try_complete_nil_arm(e, nil_ids))
}

fn try_complete_nil_arm(expr: PseudoExpr, nil_ids: &HashSet<VarId>) -> PseudoExpr {
    let PseudoExpr::When {
        subject,
        subject_name,
        mut clauses,
    } = expr
    else {
        return expr;
    };

    if let Some((nil_idx, cons_idx)) = match_nil_cons_shape(&clauses)
        && is_church_true_ref(&clauses[nil_idx].body, nil_ids)
        && cons_body_commits_to_list(
            &clauses[cons_idx].body,
            &cons_pattern_binder_ids(&clauses[cons_idx].pattern),
        )
    {
        clauses[nil_idx].body = PseudoExpr::List {
            elements: vec![].into(),
            tail: None,
        };
    }

    PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    }
}

/// Shape gate: exactly two guard-free clauses, one `[]` and one
/// `[x, ..tail]` (either order). Returns `(nil_idx, cons_idx)`.
///
/// List patterns occur in TWO equivalent AST encodings — the dedicated
/// `WhenPattern::List`, and the list-ADT constructor form
/// `WhenPattern::Constructor { shape: Known(Nil | Cons), .. }`, which the
/// pretty printer renders identically. Both are accepted;
/// `ConstructorShape::Unknown` is rejected.
fn match_nil_cons_shape(clauses: &[WhenClause]) -> Option<(usize, usize)> {
    if clauses.len() != 2 || clauses.iter().any(|c| c.guard.is_some()) {
        return None;
    }
    let is_nil = |c: &WhenClause| match &c.pattern {
        WhenPattern::List {
            elements,
            tail: None,
        } => elements.is_empty(),
        WhenPattern::Constructor { shape, fields, .. } => {
            *shape == ConstructorShape::Known(KnownConstructor::Nil) && fields.is_empty()
        }
        _ => false,
    };
    let is_cons = |c: &WhenClause| match &c.pattern {
        WhenPattern::List {
            elements,
            tail: Some(_),
        } => elements.len() == 1,
        WhenPattern::Constructor { shape, fields, .. } => {
            *shape == ConstructorShape::Known(KnownConstructor::Cons) && fields.len() == 2
        }
        _ => false,
    };
    if is_nil(&clauses[0]) && is_cons(&clauses[1]) {
        return Some((0, 1));
    }
    if is_nil(&clauses[1]) && is_cons(&clauses[0]) {
        return Some((1, 0));
    }
    None
}

/// Provenance gate: the nil body is a `Var` whose id is a collected
/// `church_true` const. Matched by `VarId`, never by name.
fn is_church_true_ref(body: &PseudoExpr, nil_ids: &HashSet<VarId>) -> bool {
    matches!(body, PseudoExpr::Var { id: Some(vid), .. } if nil_ids.contains(vid))
}

/// The cons pattern's `(head, tail)` binder `VarId`s, used by the
/// identity-rebuild veto. Either encoding; missing ids stay `None`
/// (the veto then can't match — but an id-less binder also can't be
/// referenced by id, so the leaf comparison stays sound).
fn cons_pattern_binder_ids(pattern: &WhenPattern) -> (Option<VarId>, Option<VarId>) {
    match pattern {
        WhenPattern::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => (Some(elements[0].id), Some(tail.id)),
        WhenPattern::Constructor { fields, .. } if fields.len() == 2 => {
            (Some(fields[0].id), Some(fields[1].id))
        }
        _ => (None, None),
    }
}

/// All-tails witness: every value leaf of the cons body is a `List` cell
/// or `Error`, AND at least one leaf is a real `List` cell (an all-`Error`
/// body is a legitimate partial Bool predicate `{ [] -> True; [_, ..] ->
/// fail }` — its True must stay), AND no `List` leaf is the pure identity
/// rebuild `[h, ..t]` of the cons pattern's own binders (only a
/// TRANSFORMING rebuild is map-decode evidence). Descends statement-ish
/// wrappers only (`Let` body, both `If` branches, every `When` clause body,
/// `Trace` value); any other leaf — `Var`, `Apply` (incl. recursive
/// self-calls), `Bool`, builtin call, lambda, `Force`/`Delay` — vetoes.
fn cons_body_commits_to_list(
    body: &PseudoExpr,
    pattern_ids: &(Option<VarId>, Option<VarId>),
) -> bool {
    let mut saw_list_leaf = false;
    all_leaves_list_or_error(body, pattern_ids, &mut saw_list_leaf) && saw_list_leaf
}

fn all_leaves_list_or_error(
    body: &PseudoExpr,
    pattern_ids: &(Option<VarId>, Option<VarId>),
    saw_list_leaf: &mut bool,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![body];
    while let Some(body) = pending.pop() {
        match body {
            PseudoExpr::List { .. } => {
                if is_identity_rebuild(body, pattern_ids) {
                    return false;
                }
                *saw_list_leaf = true;
            }
            PseudoExpr::Error { .. } => {}
            PseudoExpr::Let { body, .. } => pending.push(body),
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
            }
            PseudoExpr::When { clauses, .. } => {
                if clauses.is_empty() {
                    return false;
                }
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                }
            }
            PseudoExpr::Trace { value, .. } => pending.push(value),
            _ => return false,
        }
    }
    true
}

/// `[h, ..t]` where `h`/`t` are exactly the cons pattern's own binders (by
/// `VarId`) — the pure identity pass-through. Such a `when` may be a
/// sentinel-returning shape whose nil arm is a genuine boolean, so it is
/// NOT decode evidence and vetoes the whole witness (fail-closed).
fn is_identity_rebuild(
    leaf: &PseudoExpr,
    (head_id, tail_id): &(Option<VarId>, Option<VarId>),
) -> bool {
    let PseudoExpr::List {
        elements,
        tail: Some(tail),
    } = leaf
    else {
        return false;
    };
    if elements.len() != 1 {
        return false;
    }
    let head_is_binder = matches!(
        (&elements[0], head_id),
        (PseudoExpr::Var { id: Some(vid), .. }, Some(hid)) if vid == hid
    );
    let tail_is_binder = matches!(
        (tail.as_ref(), tail_id),
        (PseudoExpr::Var { id: Some(vid), .. }, Some(tid)) if vid == tid
    );
    head_is_binder && tail_is_binder
}

#[cfg(test)]
mod tests;
