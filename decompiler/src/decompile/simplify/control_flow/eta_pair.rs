use super::Simplifier;
use crate::decompile::pair_patterns::pair_pattern_binders_with_ids;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};

impl Simplifier {
    pub(super) fn collapse_eta_pair_selector_when(
        &mut self,
        subject: &PseudoExpr,
        subject_name: &Option<Binder>,
        clauses: &[WhenClause],
    ) -> Option<PseudoExpr> {
        // Collapse one-clause eta-expanded Scott pair wrappers:
        // when fn(sel, x) { sel(a, x) } is { Pair(left, right) -> body }
        // -> body[left := a], wrapped in fn(right) { ... } when the
        // second binder is used. Removes the MIR/CPS artifact without
        // guessing constructor names or broader Scott semantics.
        let [clause] = clauses else {
            return None;
        };

        let first_field = Self::extract_eta_pair_selector_subject(subject)?;
        if clause.guard.is_some() {
            return None;
        }

        let (first_binder, second_binder) = pair_pattern_binders_with_ids(&clause.pattern)?;
        let mut body = clause.body.clone();

        if Self::is_binder_used(&body, &second_binder) {
            body = PseudoExpr::Lambda {
                params: vec![second_binder],
                body: PBox::new(body),
            };
        }

        if Self::is_binder_used(&body, &first_binder) {
            body = self.bind_binder_in_body(&first_binder, first_field, body);
        }

        if let Some(name) = subject_name.as_ref()
            && Self::is_binder_used(&body, name)
        {
            body = self.bind_binder_in_body(name, subject.clone(), body);
        }

        Some(self.simplify(body))
    }
}
