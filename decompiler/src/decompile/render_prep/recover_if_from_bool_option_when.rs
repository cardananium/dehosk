//! Recover a native `if` from an `Option`-named `when` whose subject
//! is provably a `Bool`.
//!
//! A `list.any`/`list.all`-style predicate result is left as a Bool,
//! but the consuming `when` is still rendered with church-decoded
//! `Some`/`None` labels. That is a tag-equivalent relabel of
//! `{ True -> .; False -> . }`: Bool `True` = `Constr<1>` = `None`'s
//! tag, and Bool `False` = `Constr<0>` = `Some`'s tag. The readable,
//! compilable form is a native `if`.
//!
//! The subject must be provably Bool: a `Var` bound (anywhere) to a
//! value with a definite Bool tail leaf (see [`bool_witness`]), or
//! such a value inline. An `Option` value can never carry such a
//! tail, so this cannot misfire on a genuine `Option`.
//!
//! Exactly two arms, both nullary — tag 1 and tag 0, either clause
//! order, no guards. A payload binder on either arm would imply a
//! real `Option` and aborts the rewrite, as does any further arm
//! except a trailing `_ -> fail`, which is dead once the match is a
//! Bool `if` and is dropped. Mapping: tag 1 (`True`, labelled
//! `None`) is the `if` then-branch; tag 0 (`False`, labelled
//! `Some`) is the else-branch.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::bool_witness::is_provably_bool;
use super::scope_recurse::children;

pub(super) fn recover_if_from_bool_option_when(expr: PseudoExpr) -> PseudoExpr {
    // A CSE-lifted `let ok = <bool>` proves a bare `Var` subject Bool; an
    // inline subject is proven Bool directly. So always walk — an empty
    // binder set is not "nothing to do".
    let mut bool_binders = HashSet::new();
    collect_bool_binders(&expr, &mut bool_binders);
    rewrite(expr, &bool_binders)
}

/// Collect every `let`-binder whose bound value is provably a `Bool` on
/// every path.
fn collect_bool_binders(expr: &PseudoExpr, out: &mut HashSet<VarId>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            ..
        } = current
            && is_provably_bool(value)
        {
            out.insert(*vid);
        }
        pending.extend(children(current));
    }
}

struct BoolOptionIfFolder<'a> {
    bool_binders: &'a HashSet<VarId>,
}

impl ExprFolder for BoolOptionIfFolder<'_> {
    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        // The subject is provably Bool either as a `Var` bound to a Bool
        // value (CSE-lifted), or as an inline expression with a definite
        // Bool tail — the common case, since the `let condition_ok = ...`
        // binding is only materialized by the pretty-printer.
        let subject_is_bool = match &subject {
            PseudoExpr::Var { id: Some(vid), .. } => self.bool_binders.contains(vid),
            other => is_provably_bool(other),
        };
        if subject_is_bool
            && let Some((then_branch, else_branch)) = match_bool_option_clauses(&clauses)
        {
            return PseudoExpr::If {
                condition: PBox::new(subject),
                then_branch: PBox::new(then_branch),
                else_branch: PBox::new(else_branch),
            };
        }
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses,
        }
    }

    // `map_children` never recursed into a `when` clause's literal
    // pattern expression (only subject/guard/body) — match that exactly
    // rather than the default's descent into `WhenPattern::Literal`.
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }
}

fn rewrite(expr: PseudoExpr, bool_binders: &HashSet<VarId>) -> PseudoExpr {
    BoolOptionIfFolder { bool_binders }.fold(expr)
}

/// Match the 2-arm `{ tag1 -> THEN; tag0 -> ELSE }` shape over a Bool
/// subject (either clause order, optional trailing `_ -> fail`). Both arms
/// are NULLARY: under the church/Option residue the printer may LABEL them
/// `None`(tag 1)/`Some(_)`(tag 0), but the AST patterns carry no field
/// binders — they are the Bool constructors `True`(tag 1)/`False`(tag 0).
///
/// Returns the cloned `(then_branch, else_branch)` bodies mapped to the
/// `if`'s polarity: tag 1 -> THEN, tag 0 -> ELSE.
///
/// Matches on (tag, arity), which is set on both `Known` and raw `Unknown`
/// constructor patterns — the Bool/Option naming for this `when` may not be
/// materialized until print time, so `shape.as_known()` is unreliable here.
fn match_bool_option_clauses(clauses: &[WhenClause]) -> Option<(PseudoExpr, PseudoExpr)> {
    let mut then_body: Option<&PseudoExpr> = None;
    let mut else_body: Option<&PseudoExpr> = None;
    let last = clauses.len().saturating_sub(1);

    for (idx, clause) in clauses.iter().enumerate() {
        if clause.guard.is_some() {
            return None;
        }
        match &clause.pattern {
            // tag 1 == `True`/`None` -> the `if` THEN branch.
            WhenPattern::Constructor { tag: 1, fields, .. } if fields.is_empty() => {
                if then_body.is_some() {
                    return None;
                }
                then_body = Some(&clause.body);
            }
            // tag 0 == `False`/`Some` -> the `if` ELSE branch. (Order of the
            // two tag arms is irrelevant — they are disjoint and exhaustive
            // over a Bool.)
            WhenPattern::Constructor { tag: 0, fields, .. } if fields.is_empty() => {
                if else_body.is_some() {
                    return None;
                }
                else_body = Some(&clause.body);
            }
            // A `_ -> fail` is dead once the match is a Bool `if` — but ONLY
            // as the LAST clause: a leading wildcard shadows the tag arms
            // (first-match-wins), so the original always `fail`s.
            WhenPattern::Wildcard
                if idx == last && matches!(&clause.body, PseudoExpr::Error { .. }) => {}
            _ => return None,
        }
    }

    match (then_body, else_body) {
        (Some(then), Some(els)) => Some((then.clone(), els.clone())),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
