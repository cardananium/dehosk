use super::Simplifier;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};

impl Simplifier {
    pub(super) fn collapse_constant_constructor_subject(
        &mut self,
        simplified_subject: &PseudoExpr,
        subject_name: &Option<Binder>,
        simplified_clauses: &[WhenClause],
    ) -> Option<PseudoExpr> {
        // when Constr<tag>(...) is { ... } -> the selected branch body, for
        // guardless Constructor/Wildcard/Var patterns. Bail if any subject
        // field contains an explicit Error: collapsing past an unused pattern
        // field (`_`) would drop its strict evaluation.
        let PseudoExpr::Constr {
            tag: subj_tag,
            fields: subj_fields,
            ..
        } = simplified_subject
        else {
            return None;
        };

        if subj_fields.iter().any(Self::contains_explicit_error) {
            return None;
        }

        let bind_subject_name =
            |this: &mut Self, body: PseudoExpr, subj: &PseudoExpr, subj_name: &Option<Binder>| {
                if let Some(name) = subj_name
                    && Self::is_binder_used(&body, name)
                {
                    return this.bind_binder_in_body(name, subj.clone(), body);
                }
                body
            };

        for clause in simplified_clauses {
            match &clause.pattern {
                WhenPattern::Constructor {
                    tag: pat_tag,
                    fields: pat_fields,
                    ..
                } => {
                    let matches = pat_tag == subj_tag
                        && (pat_fields.len() == subj_fields.len()
                            || (!self.safe_mode && pat_fields.len() < subj_fields.len()));
                    if !matches {
                        // Constructor mismatch means guard/body are unreachable for this subject.
                        continue;
                    }
                    if clause.guard.is_some() {
                        break;
                    }
                    let mut body = clause.body.clone();
                    let subject_name_is_used = subject_name
                        .as_ref()
                        .is_some_and(|name| Self::is_binder_used(&body, name));
                    for (field_binder, field_expr) in
                        pat_fields.iter().zip(subj_fields.iter()).rev()
                    {
                        if Self::is_binder_used(&body, field_binder) {
                            let field_value = if subject_name_is_used {
                                self.clone_with_fresh_ids(field_expr)
                            } else {
                                field_expr.clone()
                            };
                            body = self.bind_binder_in_body(field_binder, field_value, body);
                        }
                    }
                    return Some(bind_subject_name(
                        self,
                        body,
                        simplified_subject,
                        subject_name,
                    ));
                }
                WhenPattern::Wildcard => {
                    if clause.guard.is_some() {
                        break;
                    }
                    return Some(bind_subject_name(
                        self,
                        clause.body.clone(),
                        simplified_subject,
                        subject_name,
                    ));
                }
                WhenPattern::Var(var_name) => {
                    if clause.guard.is_some() {
                        break;
                    }
                    let mut body = clause.body.clone();
                    if Self::is_binder_used(&body, var_name) {
                        body = self.bind_binder_in_body(var_name, simplified_subject.clone(), body);
                    }
                    return Some(bind_subject_name(
                        self,
                        body,
                        simplified_subject,
                        subject_name,
                    ));
                }
                _ => {}
            }
        }

        None
    }
}
