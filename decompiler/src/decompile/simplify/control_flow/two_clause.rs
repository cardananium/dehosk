use super::{Simplifier, summary::TwoClauseWildcardSummary};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};

impl Simplifier {
    pub(super) fn try_simplify_two_clause_wildcard_when(
        &mut self,
        subject: &PseudoExpr,
        subject_name: &Option<Binder>,
        clauses: &[WhenClause],
    ) -> Option<PseudoExpr> {
        // Pattern: when x is { [] -> Void _ -> fail } -> expect!(List.is_empty(x))
        let two_clause_summary = TwoClauseWildcardSummary::from_clauses(clauses)?;

        // Pattern: when xs is { [] -> True; _ -> False } -> List.is_empty(xs)
        // Pattern: when xs is { [] -> False; _ -> True } -> !List.is_empty(xs)
        let is_list_empty_bool_pattern = two_clause_summary.first_is_empty_list_pattern
            && two_clause_summary.second_is_wildcard
            && two_clause_summary.both_guardless;

        if is_list_empty_bool_pattern
            && let (Some(empty_val), Some(non_empty_val)) = (
                two_clause_summary.first_bool,
                two_clause_summary.second_bool,
            )
            && empty_val != non_empty_val
        {
            let empty_check = PseudoExpr::Apply {
                function: PBox::new(self.make_var("List.is_empty")),
                args: vec![subject.clone()].into(),
            };
            return Some(if empty_val {
                empty_check
            } else {
                PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand: PBox::new(empty_check),
                }
            });
        }

        // Check for [] -> Void/Unit, _ -> fail pattern.
        let is_empty_check = two_clause_summary.first_is_empty_list_pattern
            && two_clause_summary.first_is_voidish
            && two_clause_summary.second_is_wildcard
            && two_clause_summary.second_is_fail_nomsg;

        if is_empty_check {
            return Some(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::expect_helper()),
                args: vec![PseudoExpr::Apply {
                    function: PBox::new(self.make_var("List.is_empty")),
                    args: vec![subject.clone()].into(),
                }]
                .into(),
            });
        }

        // Check for [] -> fail, _ -> value pattern (expect list is NOT empty).
        let is_not_empty_check = two_clause_summary.first_is_empty_list_pattern
            && two_clause_summary.first_is_fail_nomsg
            && two_clause_summary.second_is_wildcard;

        if is_not_empty_check {
            return Some(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::expect_helper()),
                args: vec![
                    PseudoExpr::UnOp {
                        op: UnaryOp::Not,
                        operand: PBox::new(PseudoExpr::Apply {
                            function: PBox::new(self.make_var("List.is_empty")),
                            args: vec![subject.clone()].into(),
                        }),
                    },
                    two_clause_summary.second.body.clone(),
                ]
                .into(),
            });
        }

        let is_guard_expect_pattern =
            two_clause_summary.both_guardless && two_clause_summary.second_is_wildcard;

        // Generic pattern check:
        // When x is { P -> Void; _ -> fail } -> expect!(when x is { P -> True; _ -> False }, Void)
        if is_guard_expect_pattern
            && two_clause_summary.first_is_voidish
            && two_clause_summary.second_is_fail_nomsg
        {
            return Some(Self::expect_void(self.simplify_when(
                subject.clone(),
                subject_name.clone(),
                vec![
                    WhenClause::new(
                        two_clause_summary.first.pattern.clone(),
                        PseudoExpr::Bool(true),
                    ),
                    WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(false)),
                ],
            )));
        }

        // Mirrored generic pattern check:
        // When x is { P -> fail; _ -> Void } -> expect!(when x is { P -> False; _ -> True }, Void)
        if is_guard_expect_pattern
            && two_clause_summary.first_is_fail_nomsg
            && two_clause_summary.second_is_voidish
        {
            return Some(Self::expect_void(self.simplify_when(
                subject.clone(),
                subject_name.clone(),
                vec![
                    WhenClause::new(
                        two_clause_summary.first.pattern.clone(),
                        PseudoExpr::Bool(false),
                    ),
                    WhenClause::new(WhenPattern::Wildcard, PseudoExpr::Bool(true)),
                ],
            )));
        }

        None
    }
}
