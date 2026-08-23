//! Collapse `when X is { True → True; False → False; _ → fail }`
//! to just `X`.
//!
//! The shape comes from `expect Bool = x; x`: with no "expect
//! typename" surface syntax, that lowers to a Bool-discriminating
//! when whose arms each return their own matched constructor, with
//! `_ → fail` as the runtime type-assert.
//!
//! The match is exhaustive on True/False and each arm returns what
//! it matched, so the when is the identity on `X`. The `_ → fail`
//! arm is reachable only when `X` is not a Bool, so collapsing
//! drops that runtime type-assert.
//!
//! Conditions:
//!   - Subject must be a `Var` (so call sites can rely on
//!     evaluation order).
//!   - One nullary `Constructor(True)` arm and one nullary
//!     `Constructor(False)` arm, each returning its own
//!     constructor as `Constr` or as a `Bool` literal.
//!   - At most one `Wildcard` arm, and its body must be `fail`.
//!   - No guards on any arm.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;
use crate::pseudo::fold::ExprFolder;

struct Collapser;

impl ExprFolder for Collapser {
    fn fold_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let subject = self.fold(subject);
        let clauses: Vec<WhenClause> = clauses
            .into_iter()
            .map(|c| WhenClause {
                pattern: c.pattern,
                guard: c.guard.map(|g| self.fold(g)),
                body: self.fold(c.body),
            })
            .collect();
        self.post_when(subject, subject_name, clauses)
    }

    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        if is_bool_identity_when(&clauses) && matches!(subject, PseudoExpr::Var { .. }) {
            return subject;
        }
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses,
        }
    }
}

pub(super) fn collapse_bool_identity_when(expr: PseudoExpr) -> PseudoExpr {
    Collapser.fold(expr)
}

/// Returns true iff `clauses` form a Bool-identity match.
fn is_bool_identity_when(clauses: &[WhenClause]) -> bool {
    let mut saw_true = false;
    let mut saw_false = false;
    let mut saw_wildcard_fail = false;

    for clause in clauses {
        if clause.guard.is_some() {
            return false;
        }
        match &clause.pattern {
            WhenPattern::Constructor { shape, fields, .. }
                if fields.is_empty()
                    && matches!(
                        shape.as_known(),
                        Some(KnownConstructor::True | KnownConstructor::False)
                    ) =>
            {
                let Some(known) = shape.as_known() else {
                    return false;
                };
                if !arm_returns_matched_bool(&clause.body, known) {
                    return false;
                }
                match known {
                    KnownConstructor::True => {
                        if saw_true {
                            return false;
                        }
                        saw_true = true;
                    }
                    KnownConstructor::False => {
                        if saw_false {
                            return false;
                        }
                        saw_false = true;
                    }
                    _ => return false,
                }
            }
            WhenPattern::Wildcard => {
                if !matches!(&clause.body, PseudoExpr::Error { .. }) {
                    return false;
                }
                if saw_wildcard_fail {
                    return false;
                }
                saw_wildcard_fail = true;
            }
            _ => return false,
        }
    }

    saw_true && saw_false
}

/// True iff `body` is the same Bool constructor as `expected`,
/// in either the `Bool(true|false)` literal or `Constr` form.
fn arm_returns_matched_bool(body: &PseudoExpr, expected: KnownConstructor) -> bool {
    match (body, expected) {
        (PseudoExpr::Bool(true), KnownConstructor::True) => true,
        (PseudoExpr::Bool(false), KnownConstructor::False) => true,
        (
            PseudoExpr::Constr { shape, fields, .. },
            KnownConstructor::True | KnownConstructor::False,
        ) if fields.is_empty() => shape.as_known() == Some(expected),
        _ => false,
    }
}

#[cfg(test)]
mod tests;
