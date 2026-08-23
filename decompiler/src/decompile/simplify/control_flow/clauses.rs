use super::Simplifier;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;
use std::collections::HashSet;

impl Simplifier {
    pub(super) fn pattern_binds_any_used_name(
        pattern: &WhenPattern,
        used_names: &HashSet<String>,
    ) -> bool {
        match pattern {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => fields
                .iter()
                .any(|field| field != "_" && used_names.contains(field.as_str())),
            WhenPattern::List { elements, tail } => {
                elements
                    .iter()
                    .any(|element| element != "_" && used_names.contains(element.as_str()))
                    || tail
                        .as_ref()
                        .is_some_and(|tail| tail != "_" && used_names.contains(tail.as_str()))
            }
            WhenPattern::Pair(first, second) => {
                (first != "_" && used_names.contains(first.as_str()))
                    || (second != "_" && used_names.contains(second.as_str()))
            }
            WhenPattern::Var(name) => name != "_" && used_names.contains(name.as_str()),
            WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
        }
    }

    /// Flatten nested when on the same subject.
    ///
    /// 1. Wildcard fallback: `_ -> when x is { ... }` merges the inner clauses.
    /// 2. Constructor body: `Constr<N>(fields) -> when x is { Constr<N>(c,d) -> body; ... }`
    ///    resolves the inner when at tag N, renaming its field vars to the outer binders.
    pub(super) fn flatten_nested_when(
        subject: &PseudoExpr,
        clauses: Vec<WhenClause>,
    ) -> Vec<WhenClause> {
        let mut result = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let WhenClause {
                pattern,
                guard,
                body,
            } = clause;

            if guard.is_some() {
                result.push(WhenClause {
                    pattern,
                    guard,
                    body,
                });
                continue;
            }

            // Check if clause body is a when on the same subject
            if let PseudoExpr::When {
                subject: inner_subject,
                subject_name: inner_subject_name,
                clauses: inner_clauses,
                ..
            } = body
            {
                if inner_subject.as_ref() == subject {
                    match pattern {
                        // Pattern 1: wildcard fallback -> merge inner clauses
                        WhenPattern::Wildcard => {
                            result.extend(inner_clauses);
                            continue;
                        }
                        // Pattern 2: constructor clause -> resolve inner when
                        WhenPattern::Constructor {
                            tag: outer_tag,
                            fields: outer_fields,
                            shape: outer_shape,
                            type_hint: outer_type_hint,
                        } => {
                            // Find matching constructor clause in inner when
                            let mut resolved = None;
                            for inner_c in &inner_clauses {
                                match &inner_c.pattern {
                                    WhenPattern::Constructor {
                                        tag: inner_tag,
                                        fields: inner_fields,
                                        ..
                                    } if *inner_tag == outer_tag && inner_c.guard.is_none() => {
                                        let can_rebind_all_inner_fields = inner_fields.len()
                                            <= outer_fields.len()
                                            && inner_fields.iter().zip(&outer_fields).all(
                                                |(inner_f, outer_f)| {
                                                    inner_f == "_" || outer_f != "_"
                                                },
                                            );
                                        if !can_rebind_all_inner_fields {
                                            continue;
                                        }
                                        // Same constructor: rename inner field vars to outer ones.
                                        // `substitute_var_for_var` retargets body refs to the outer
                                        // binder's VarId too; a name-only rename leaves inner-binder
                                        // ids orphaned against the outer pattern binders.
                                        let mut body = inner_c.body.clone();
                                        for (inner_f, outer_f) in
                                            inner_fields.iter().zip(&outer_fields)
                                        {
                                            if inner_f.as_str() != "_"
                                                && inner_f.as_str() != outer_f.as_str()
                                            {
                                                body = Self::substitute_var_for_var(
                                                    &body,
                                                    inner_f.as_str(),
                                                    inner_f.var_id().get(),
                                                    outer_f.as_str(),
                                                    outer_f.var_id(),
                                                );
                                            }
                                        }
                                        resolved = Some(body);
                                        break;
                                    }
                                    WhenPattern::Constructor { tag: inner_tag, .. }
                                        if *inner_tag != outer_tag =>
                                    {
                                        // Mismatching constructor, skip
                                        continue;
                                    }
                                    WhenPattern::Wildcard if inner_c.guard.is_none() => {
                                        // Wildcard catches everything
                                        resolved = Some(inner_c.body.clone());
                                        break;
                                    }
                                    _ => break, // guarded or complex: bail
                                }
                            }
                            if let Some(body) = resolved {
                                result.push(WhenClause {
                                    pattern: WhenPattern::Constructor {
                                        type_hint: outer_type_hint.clone(),
                                        tag: outer_tag,
                                        fields: outer_fields,
                                        shape: outer_shape,
                                    },
                                    guard: None,
                                    body,
                                });
                                continue;
                            }

                            result.push(WhenClause {
                                pattern: WhenPattern::Constructor {
                                    type_hint: outer_type_hint,
                                    tag: outer_tag,
                                    fields: outer_fields,
                                    shape: outer_shape,
                                },
                                guard: None,
                                body: PseudoExpr::When {
                                    subject: inner_subject,
                                    subject_name: inner_subject_name,
                                    clauses: inner_clauses,
                                },
                            });
                            continue;
                        }
                        other_pattern => {
                            result.push(WhenClause {
                                pattern: other_pattern,
                                guard: None,
                                body: PseudoExpr::When {
                                    subject: inner_subject,
                                    subject_name: inner_subject_name,
                                    clauses: inner_clauses,
                                },
                            });
                            continue;
                        }
                    }
                }

                result.push(WhenClause {
                    pattern,
                    guard: None,
                    body: PseudoExpr::When {
                        subject: inner_subject,
                        subject_name: inner_subject_name,
                        clauses: inner_clauses,
                    },
                });
                continue;
            }

            result.push(WhenClause {
                pattern,
                guard,
                body,
            });
        }
        result
    }

    /// Expand a wildcard branch of the form `_ -> if subject { A } else { B }`
    /// into `Constr<1> -> A` and `_ -> B` (True = tag 1, False = tag 0), so
    /// constructor dispatch is not displayed as a boolean `if` test.
    pub(super) fn expand_wildcard_if_to_clauses(
        mut clauses: Vec<WhenClause>,
        subject: &PseudoExpr,
        subject_name: &Option<Binder>,
    ) -> Vec<WhenClause> {
        // Find wildcard index
        let wildcard_idx = clauses
            .iter()
            .position(|c| matches!(c.pattern, WhenPattern::Wildcard) && c.guard.is_none());
        let Some(idx) = wildcard_idx else {
            return clauses;
        };

        // Check if the wildcard body is `if subject { then } else { else }`
        // where subject matches the when subject variable
        let is_subject_if = if let PseudoExpr::If { condition, .. } = &clauses[idx].body {
            match condition.as_ref() {
                PseudoExpr::Var { name, id, .. } => {
                    subject_name
                        .as_ref()
                        .is_some_and(|sn| Self::var_matches_binder(name, *id, sn))
                        || matches!(
                            subject,
                            PseudoExpr::Var { name: sname, id: sid, .. }
                                if Self::var_matches_direct_subject(name, *id, sname, sid.get())
                        )
                }
                _ => false,
            }
        } else {
            false
        };

        if !is_subject_if {
            return clauses;
        }

        // Extract the if branches
        let wildcard_clause = clauses.remove(idx);
        if let PseudoExpr::If {
            then_branch,
            else_branch,
            ..
        } = wildcard_clause.body
        {
            // In Plutus, IfThenElse on a constructor tests tag:
            // True (Constr<1>) -> then_branch, False (Constr<0>) -> else_branch
            clauses.push(WhenClause {
                pattern: WhenPattern::constructor(ConstructorShape::unknown_data(1, 0), vec![]),
                guard: None,
                body: then_branch.into_inner(),
            });
            // Use wildcard for the else case (Constr<0> and anything else)
            clauses.push(WhenClause {
                pattern: WhenPattern::Wildcard,
                guard: None,
                body: else_branch.into_inner(),
            });
        }

        clauses
    }

    fn var_matches_binder(name: &str, id: Option<VarId>, binder: &Binder) -> bool {
        crate::decompile::var_match::ref_matches_resolved_target(
            name,
            id,
            binder.as_str(),
            binder.id.get(),
        )
    }

    /// Deduplicate when clauses.
    ///
    /// Clauses whose body equals the wildcard clause's body are dropped — the
    /// wildcard already covers them. Guarded clauses are kept.
    pub(super) fn deduplicate_when_clauses(clauses: Vec<WhenClause>) -> Vec<WhenClause> {
        if clauses.len() <= 1 {
            return clauses;
        }
        // Find wildcard clause body
        if let Some(wildcard_idx) = clauses
            .iter()
            .position(|c| matches!(c.pattern, WhenPattern::Wildcard) && c.guard.is_none())
        {
            let mut before_and_wildcard = clauses;
            let after = before_and_wildcard.split_off(wildcard_idx + 1);
            let wildcard_clause = before_and_wildcard
                .pop()
                .expect("split_off after wildcard index leaves wildcard as last element");
            let (before_filtered, after_filtered) = {
                let wildcard_body = &wildcard_clause.body;
                (
                    before_and_wildcard
                        .into_iter()
                        .filter(|clause| clause.body != *wildcard_body || clause.guard.is_some())
                        .collect::<Vec<_>>(),
                    after
                        .into_iter()
                        .filter(|clause| clause.body != *wildcard_body || clause.guard.is_some())
                        .collect::<Vec<_>>(),
                )
            };

            let mut result = Vec::with_capacity(before_filtered.len() + after_filtered.len() + 1);
            result.extend(before_filtered);
            result.push(wildcard_clause);
            result.extend(after_filtered);
            return result;
        }

        clauses
    }
}
