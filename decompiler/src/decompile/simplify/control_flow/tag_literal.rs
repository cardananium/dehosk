use super::Simplifier;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::OptionVarIdGet;
use num_traits::ToPrimitive;

impl Simplifier {
    pub(super) fn rewrite_tag_literal_when_subject(
        &self,
        subject: &PseudoExpr,
        clauses: &[WhenClause],
    ) -> Option<(PseudoExpr, Vec<WhenClause>)> {
        let subject = self.tag_literal_original_subject(subject)?;
        let clauses = Self::tag_literal_constructor_clauses(clauses)?;

        Some((subject, clauses))
    }

    fn tag_literal_original_subject(&self, subject: &PseudoExpr) -> Option<PseudoExpr> {
        // Convert `when x.tag is { 0 -> ...; 1 -> ... }` to
        // `when x is { Constr<0> -> ...; Constr<1> -> ... }`.
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = subject
            && selector.as_pretty_name() == "tag"
        {
            return Some((**record).clone());
        }

        // Also handle `when m is { 0 -> ...; 1 -> ... }` where m is tracked as x.tag.
        if let PseudoExpr::Var { name, id, .. } = subject {
            return self.tracked_var(&self.constructors.constr_tag_subjects, name, id.get());
        }

        None
    }

    fn tag_literal_constructor_clauses(clauses: &[WhenClause]) -> Option<Vec<WhenClause>> {
        let all_literal_or_wildcard = clauses.iter().all(|c| {
            matches!(
                &c.pattern,
                WhenPattern::Literal(PseudoExpr::Int(_)) | WhenPattern::Wildcard
            )
        });
        if !all_literal_or_wildcard {
            return None;
        }

        Some(
            clauses
                .iter()
                .filter_map(|c| match &c.pattern {
                    WhenPattern::Literal(PseudoExpr::Int(n)) => {
                        n.to_usize().map(|tag| WhenClause {
                            pattern: WhenPattern::constructor(
                                ConstructorShape::unknown_data(tag, 0),
                                vec![],
                            ),
                            guard: c.guard.clone(),
                            body: c.body.clone(),
                        })
                    }
                    _ => Some(c.clone()), // Wildcard stays.
                })
                .collect(),
        )
    }
}
