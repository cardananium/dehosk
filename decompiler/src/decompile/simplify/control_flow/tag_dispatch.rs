use super::Simplifier;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;

impl Simplifier {
    pub(super) fn try_simplify_expect_tag_comparison_if(
        &mut self,
        eq_tag_comparison: &Option<(PseudoExpr, usize)>,
        then_branch: &PseudoExpr,
        else_branch: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        // Before converting to ||/&&, check if condition is a tag comparison.
        // `if purpose.tag == N { True } else { fail }` should become
        // `when purpose is { Constr<N> -> True; _ -> fail }` -> `expect Purpose = ...`
        // rather than `purpose.tag == N || fail`.
        //
        // POLARITY INVARIANT: the `Constr<tag>` arm always receives the THEN
        // branch — `if (tag == N) { A } else { B }` runs A exactly when the tag
        // matches. The True/fail gate below only selects WHICH if shapes take
        // this expect-style path (vs the general ||/&& lowering); it must never
        // reorder the bodies. Swapping them inverts the accept set of every
        // must-NOT-match check `if (tag == N) { fail } else { True }`.
        let (subject, tag_value) = eq_tag_comparison.as_ref()?;
        if !((self.is_true(then_branch) && Self::is_fail(else_branch))
            || (Self::is_fail(then_branch) && self.is_true(else_branch)))
        {
            return None;
        }

        Some(self.simplify_when(
            subject.clone(),
            None,
            Self::tag_comparison_constructor_clauses(
                *tag_value,
                then_branch.clone(),
                else_branch.clone(),
            ),
        ))
    }

    pub(super) fn try_simplify_tag_comparison_if(
        &mut self,
        eq_tag_comparison: &Option<(PseudoExpr, usize)>,
        then_branch: &PseudoExpr,
        else_branch: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        // Convert `if x.tag == N` or `if m == N` (where m = x.tag) to
        // constructor when. This must run before boolean collapse rules so
        // `if z.tag == 0 { expr } else { False }` becomes
        // `when z is { Constr<0> -> expr; _ -> False }`.
        let (subject, tag_value) = eq_tag_comparison.as_ref()?;

        Some(self.simplify_when(
            subject.clone(),
            None,
            Self::tag_comparison_constructor_clauses(
                *tag_value,
                then_branch.clone(),
                else_branch.clone(),
            ),
        ))
    }

    fn tag_comparison_constructor_clauses(
        tag: usize,
        then_body: PseudoExpr,
        else_body: PseudoExpr,
    ) -> Vec<WhenClause> {
        vec![
            WhenClause::new(
                WhenPattern::constructor(ConstructorShape::unknown_data(tag, 0), vec![]),
                then_body,
            ),
            WhenClause::new(WhenPattern::Wildcard, else_body),
        ]
    }
}
