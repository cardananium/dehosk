use super::Simplifier;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

impl Simplifier {
    pub(super) fn try_rewrite_when_return_binding(
        name: &str,
        var_id: Option<VarId>,
        value: &PseudoExpr,
        body: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        let PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } = value
        else {
            return None;
        };

        let non_fail: Vec<(usize, &WhenClause)> = clauses
            .iter()
            .enumerate()
            .filter(|(_, c)| !Self::is_fail(&c.body))
            .collect();
        if non_fail.len() != 1 {
            return None;
        }

        let (clause_idx, clause) = non_fail[0];
        let PseudoExpr::Var {
            name: return_var,
            id: Some(return_id),
            ..
        } = &clause.body
        else {
            return None;
        };

        let return_binder = Self::pattern_binder_named(&clause.pattern, return_var)?;
        let return_ids_match =
            crate::decompile::var_match::ids_compatible(return_id.get(), return_binder.id.get());
        let replacement_id = return_binder.var_id();
        let new_name = name.to_string();
        let guard_blockers = vec![return_var.clone(), new_name.clone()];
        let body_blockers = std::slice::from_ref(&new_name);
        let rewrite_would_capture = clause
            .guard
            .as_ref()
            .is_some_and(|guard| Self::has_binding_for_any(guard, &guard_blockers))
            || Self::has_binding_for_any(body, body_blockers);

        if !return_ids_match
            || rewrite_would_capture
            || matches!(&clause.pattern, WhenPattern::Wildcard | WhenPattern::Var(_))
        {
            return None;
        }

        let new_pattern = Self::rename_in_pattern(&clause.pattern, return_var, name);
        let rewritten_body = Self::substitute_var_for_var(body, name, var_id, name, replacement_id);
        let new_clauses: Vec<WhenClause> = clauses
            .iter()
            .enumerate()
            .map(|(i, c)| {
                if i == clause_idx {
                    WhenClause {
                        pattern: new_pattern.clone(),
                        guard: c.guard.as_ref().map(|guard| {
                            Self::substitute_var_for_var(
                                guard,
                                return_var,
                                Some(replacement_id),
                                name,
                                replacement_id,
                            )
                        }),
                        body: rewritten_body.clone(),
                    }
                } else {
                    c.clone()
                }
            })
            .collect();

        Some(PseudoExpr::When {
            subject: subject.clone(),
            subject_name: subject_name.clone(),
            clauses: new_clauses,
        })
    }
}
