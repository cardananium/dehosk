//! Collapse an empty `when X is { }` (zero clauses) into just `X`.
//!
//! An empty-clause `When` is a degenerate eliminator: with no arms it
//! performs no dispatch, so it is semantically just the evaluation of
//! its subject. It arises when the simplifier lowers a church/Scott
//! eliminator whose value turned out to be a diverging expression —
//! e.g. a fail-thunk placed where a church bool was expected, giving
//! `value_20 == value_19 && (when variant_24 is { })` where
//! `variant_24` is bound (via the constructor destructure) to
//! `fail @"PT2"`. That is both mystifying and not valid surface
//! syntax; collapsing to the subject preserves semantics (force the
//! subject, there are no arms to take) and reads as `… && variant_24`.
//!
//! Only fires when `clauses` is empty. The optional `subject_name`
//! binds the subject for use *inside* the clauses; with zero clauses
//! it is necessarily unused, so dropping it is sound.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::fold::ExprFolder;

pub(super) fn collapse_empty_when(expr: PseudoExpr) -> PseudoExpr {
    Collapser.fold(expr)
}

struct Collapser;

impl ExprFolder for Collapser {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        if clauses.is_empty() {
            // Zero arms → no dispatch → the `when` is just its subject.
            return subject;
        }
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses,
        }
    }
}

#[cfg(test)]
mod tests;
