use super::Simplifier;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};

#[derive(Debug, Default, Clone, Copy)]
pub(super) struct WhenClauseShapeSummary {
    pub(super) has_guardless_wildcard_clause: bool,
    pub(super) has_guardless_wildcard_let_body: bool,
    pub(super) has_guardless_wildcard_if_body: bool,
    pub(super) has_guardless_nested_when_body: bool,
    pub(super) has_constructor_clause: bool,
    pub(super) has_empty_constructor_clause: bool,
    pub(super) has_unnamed_constructor_pattern: bool,
}

impl WhenClauseShapeSummary {
    pub(super) fn analyze(clauses: &[WhenClause]) -> Self {
        let mut summary = Self::default();
        for clause in clauses {
            if clause.guard.is_none() && matches!(clause.pattern, WhenPattern::Wildcard) {
                summary.has_guardless_wildcard_clause = true;
                summary.has_guardless_wildcard_let_body |=
                    matches!(clause.body, PseudoExpr::Let { .. });
                summary.has_guardless_wildcard_if_body |=
                    matches!(clause.body, PseudoExpr::If { .. });
            }
            if clause.guard.is_none() && matches!(clause.body, PseudoExpr::When { .. }) {
                summary.has_guardless_nested_when_body = true;
            }
            if let WhenPattern::Constructor {
                fields,
                shape: pattern_shape,
                ..
            } = &clause.pattern
            {
                summary.has_constructor_clause = true;
                if fields.is_empty() {
                    summary.has_empty_constructor_clause = true;
                }
                if !pattern_shape.is_known() {
                    summary.has_unnamed_constructor_pattern = true;
                }
            }
        }
        summary
    }
}

#[derive(Debug, Default, Clone, Copy)]
pub(super) struct WhenClauseOutcomeSummary<'a> {
    pub(super) all_bool_or_fail: bool,
    pub(super) true_body: Option<&'a PseudoExpr>,
    pub(super) false_body: Option<&'a PseudoExpr>,
    pub(super) first_non_fail_body: Option<&'a PseudoExpr>,
    pub(super) non_fail_count: usize,
    pub(super) all_non_fail_same: bool,
}

impl<'a> WhenClauseOutcomeSummary<'a> {
    fn body_is_fail(body: &PseudoExpr) -> bool {
        Simplifier::is_fail(body)
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct LateWhenClauseSummary<'a> {
    pub(super) shape: WhenClauseShapeSummary,
    pub(super) outcome: WhenClauseOutcomeSummary<'a>,
}

impl<'a> LateWhenClauseSummary<'a> {
    pub(super) fn analyze(clauses: &'a [WhenClause]) -> Self {
        let mut shape = WhenClauseShapeSummary::default();
        let mut outcome = WhenClauseOutcomeSummary {
            all_bool_or_fail: true,
            all_non_fail_same: true,
            ..WhenClauseOutcomeSummary::default()
        };

        for clause in clauses {
            if clause.guard.is_none() && matches!(clause.pattern, WhenPattern::Wildcard) {
                shape.has_guardless_wildcard_clause = true;
                shape.has_guardless_wildcard_let_body |=
                    matches!(clause.body, PseudoExpr::Let { .. });
                shape.has_guardless_wildcard_if_body |=
                    matches!(clause.body, PseudoExpr::If { .. });
            }
            if clause.guard.is_none() && matches!(clause.body, PseudoExpr::When { .. }) {
                shape.has_guardless_nested_when_body = true;
            }
            if let WhenPattern::Constructor {
                fields,
                shape: pattern_shape,
                ..
            } = &clause.pattern
            {
                shape.has_constructor_clause = true;
                if fields.is_empty() {
                    shape.has_empty_constructor_clause = true;
                }
                if !pattern_shape.is_known() {
                    shape.has_unnamed_constructor_pattern = true;
                }
            }

            if clause.guard.is_some() {
                outcome.all_bool_or_fail = false;
            }

            match &clause.pattern {
                WhenPattern::Constructor { shape, .. }
                    if shape.as_known() == Some(KnownConstructor::True) =>
                {
                    outcome.true_body = Some(&clause.body);
                }
                WhenPattern::Constructor { shape, .. }
                    if shape.as_known() == Some(KnownConstructor::False) =>
                {
                    outcome.false_body = Some(&clause.body);
                }
                // A witnessed data-tag church-bool arm carries a per-bool
                // `church_true` tag (Unknown, not CIP-Known): the arm whose tag
                // equals `church_true` is the True body, so the collapse is
                // per-bool and the program polarity flag never enters.
                WhenPattern::Constructor {
                    shape:
                        ConstructorShape::Unknown {
                            tag,
                            church_true: Some(ct),
                            ..
                        },
                    ..
                } => {
                    if tag == ct {
                        outcome.true_body = Some(&clause.body);
                    } else {
                        outcome.false_body = Some(&clause.body);
                    }
                }
                WhenPattern::Wildcard => {
                    if !WhenClauseOutcomeSummary::body_is_fail(&clause.body) {
                        outcome.all_bool_or_fail = false;
                    }
                }
                _ => {
                    outcome.all_bool_or_fail = false;
                }
            }

            if !WhenClauseOutcomeSummary::body_is_fail(&clause.body) {
                outcome.non_fail_count += 1;
                if let Some(first_body) = outcome.first_non_fail_body {
                    if !clause.body.structural_eq(first_body) {
                        outcome.all_non_fail_same = false;
                    }
                } else {
                    outcome.first_non_fail_body = Some(&clause.body);
                }
            }
        }

        Self { shape, outcome }
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct TwoClauseWildcardSummary<'a> {
    pub(super) first: &'a WhenClause,
    pub(super) second: &'a WhenClause,
    pub(super) first_is_empty_list_pattern: bool,
    pub(super) second_is_wildcard: bool,
    pub(super) both_guardless: bool,
    pub(super) first_bool: Option<bool>,
    pub(super) second_bool: Option<bool>,
    pub(super) first_is_voidish: bool,
    pub(super) second_is_voidish: bool,
    pub(super) first_is_fail_nomsg: bool,
    pub(super) second_is_fail_nomsg: bool,
}

impl<'a> TwoClauseWildcardSummary<'a> {
    pub(super) fn from_clauses(clauses: &'a [WhenClause]) -> Option<Self> {
        let [first, second] = clauses else {
            return None;
        };

        Some(Self {
            first,
            second,
            first_is_empty_list_pattern: matches!(
                &first.pattern,
                WhenPattern::List { elements, tail } if elements.is_empty() && tail.is_none()
            ),
            second_is_wildcard: matches!(second.pattern, WhenPattern::Wildcard),
            both_guardless: first.guard.is_none() && second.guard.is_none(),
            first_bool: match &first.body {
                PseudoExpr::Bool(value) => Some(*value),
                _ => None,
            },
            second_bool: match &second.body {
                PseudoExpr::Bool(value) => Some(*value),
                _ => None,
            },
            first_is_voidish: Simplifier::is_void(&first.body)
                || matches!(&first.body, PseudoExpr::Unit),
            second_is_voidish: Simplifier::is_void(&second.body)
                || matches!(&second.body, PseudoExpr::Unit),
            first_is_fail_nomsg: Simplifier::is_fail(&first.body)
                && !Simplifier::has_fail_message(&first.body),
            second_is_fail_nomsg: Simplifier::is_fail(&second.body)
                && !Simplifier::has_fail_message(&second.body),
        })
    }
}

#[derive(Debug, Default, Clone, Copy)]
pub(super) struct ScottClauseSummary {
    candidate_count: u8,
    candidate_has_fields: bool,
}

impl ScottClauseSummary {
    pub(super) fn observe(body: &PseudoExpr) -> Self {
        if Simplifier::is_fail(body) {
            return Self::default();
        }

        let maybe_scott = Simplifier::may_be_scott_constructor_value(body);
        let has_fields = Simplifier::may_have_scott_constructor_fields(body);
        Self {
            candidate_count: u8::from(maybe_scott),
            candidate_has_fields: has_fields,
        }
    }

    pub(super) fn add_assign(&mut self, other: Self) {
        self.candidate_count = self.candidate_count.saturating_add(other.candidate_count);
        self.candidate_has_fields |= other.candidate_has_fields;
    }

    pub(super) fn may_rewrite(self) -> bool {
        self.candidate_count >= 2 && self.candidate_has_fields
    }
}
