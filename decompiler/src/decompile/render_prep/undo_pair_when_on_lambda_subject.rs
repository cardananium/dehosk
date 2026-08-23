//! Undo `when <Lambda/RecFn> is { Pair(a, b) → body }` at render time.
//!
//! The simplifier can collapse `Apply(<func>, [Lambda(a, b, body)])` into
//! `When { subject: <func>, clauses: [Pair(a, b) → body] }` because a
//! 2-param projection lambda looks like a Pair-destructure. That is
//! correct when the subject is a real Pair; for `Lambda` / `RecFn` /
//! `Force(Lambda)` (Y-combinator emits, Church constructors) the surface
//! is "pattern-match a function as a Pair", which is meaningless.
//!
//! Restore `Apply { function: subject, args: [Lambda { params: [a, b], body }] }`
//! for those subjects only.
//!
//! Narrow gates:
//! - One guard-less clause whose pattern is `Pair` (`WhenPattern::Pair`
//!   or a `Pair`-shaped `Constructor`).
//! - Subject is `Lambda`, `RecFn`, or `Force` of either. Pair-typed
//!   subjects, Vars, FieldAccess, Apply stay as `When` (idiomatic there).
//! - `subject_name` is None: a named subject is left as-is.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;
use crate::pseudo::fold::ExprFolder;

struct UndoPairWhenOnLambdaSubject;

impl ExprFolder for UndoPairWhenOnLambdaSubject {
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }

    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        if let Some((a, b, body)) = try_extract_single_pair_clause(&clauses)
            && subject_name.is_none()
            && is_function_subject(&subject)
        {
            let proj = PseudoExpr::Lambda {
                params: vec![a.clone(), b.clone()],
                body: PBox::new(body.clone()),
            };
            return PseudoExpr::Apply {
                function: PBox::new(subject),
                args: vec![proj].into(),
            };
        }
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses,
        }
    }
}

pub(super) fn undo_pair_when_on_lambda_subject(expr: PseudoExpr) -> PseudoExpr {
    UndoPairWhenOnLambdaSubject.fold(expr)
}

/// Returns `Some((a, b, body))` if `clauses` is a single
/// guard-less `Pair(a, b) -> body` clause.
fn try_extract_single_pair_clause(
    clauses: &[WhenClause],
) -> Option<(&Binder, &Binder, &PseudoExpr)> {
    if clauses.len() != 1 {
        return None;
    }
    let clause = &clauses[0];
    if clause.guard.is_some() {
        return None;
    }
    match &clause.pattern {
        WhenPattern::Pair(a, b) => Some((a, b, &clause.body)),
        // The simplifier may emit `WhenPattern::Constructor { shape:
        // Pair, fields: [a, b] }` for the same pattern; both render
        // as `Pair(a, b)` and need the same rewrite.
        WhenPattern::Constructor { shape, fields, .. }
            if shape.as_known() == Some(KnownConstructor::Pair) && fields.len() == 2 =>
        {
            Some((&fields[0], &fields[1], &clause.body))
        }
        _ => None,
    }
}

/// True when `expr` is a Lambda, RecFn, or `Force` of either —
/// the subjects for which `When { Pair(...) }` is pathological.
fn is_function_subject(expr: &PseudoExpr) -> bool {
    match expr {
        PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => true,
        PseudoExpr::Force(inner) => {
            matches!(
                inner.as_ref(),
                PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. }
            )
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests;
