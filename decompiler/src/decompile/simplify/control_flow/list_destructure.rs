use super::Simplifier;
use crate::decompile::list_traversal::list_tail_argument;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

impl Simplifier {
    pub(super) fn try_reconstruct_list_subject_if(
        &mut self,
        cond: &PseudoExpr,
        then_branch: &PseudoExpr,
        else_branch: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        // Reconstruct list matches before boolean collapse:
        // if xs { body(xs[0], xs[1..]) } else { empty_case }
        //   > when xs is { [] -> empty_case; [xs_h, ..xs_t] -> body(xs_h, xs_t) }
        //
        // Without this, `if cond { expr } else { False } -> cond && expr` turns
        // list recursion back into pseudo-boolean code like `list && rec(list[1..])`.
        let PseudoExpr::Var {
            name: cond_name,
            id,
            ..
        } = cond
        else {
            return None;
        };

        let cond_id = id.get();
        let then_uses_list_structure = {
            let (has_head, has_tail) =
                Self::list_access_usage_by_id(then_branch, cond_name, cond_id);
            has_head || has_tail
        };
        if !then_uses_list_structure {
            return None;
        }

        let else_uses_list_structure = {
            let (has_head, has_tail) =
                Self::list_access_usage_by_id(else_branch, cond_name, cond_id);
            has_head || has_tail
        };
        if else_uses_list_structure {
            return None;
        }

        Some(self.simplify_when(
            cond.clone(),
            None,
            vec![
                WhenClause::new(
                    WhenPattern::List {
                        elements: vec![],
                        tail: None,
                    },
                    else_branch.clone(),
                ),
                WhenClause::new(WhenPattern::Wildcard, then_branch.clone()),
            ],
        ))
    }

    fn is_list_tail_of_direct_subject(
        expr: &PseudoExpr,
        subject_name: &str,
        subject_id: Option<VarId>,
    ) -> bool {
        match list_tail_argument(expr) {
            Some(PseudoExpr::Var { name, id, .. }) => {
                Self::var_matches_direct_subject(name, *id, subject_name, subject_id)
            }
            _ => false,
        }
    }

    /// Convert wildcard clause with let-bound head/tail to a list pattern.
    ///
    /// ```text
    /// when xs is { [] -> empty; _ -> let h = xs[0]; let t = List.tail(xs); body }
    /// ```
    /// becomes:
    /// ```text
    /// when xs is { [] -> empty; [h, ..t] -> body }
    /// ```
    pub(super) fn destructure_list_head_tail(
        subject: &PseudoExpr,
        _subject_name: &Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> Vec<WhenClause> {
        let (subj_var_name, subj_var_id) = match subject {
            PseudoExpr::Var { name, id, .. } => (name.as_str(), id.get()),
            _ => return clauses,
        };

        clauses
            .into_iter()
            .map(|clause| {
                if !matches!(clause.pattern, WhenPattern::Wildcard) || clause.guard.is_some() {
                    return clause;
                }
                // Look for: let h = subj[0]; let t = List.tail(subj); body
                let mut body = &clause.body;
                let mut head_name: Option<Binder> = None;
                let mut tail_name: Option<Binder> = None;
                let mut inner_body = None;

                if let PseudoExpr::Let {
                    name: n1,
                    id: id1,
                    value: v1,
                    body: b1,
                    ..
                } = body
                {
                    // Check if v1 is subj[0] or subj.head
                    let first_is_head = match v1.as_ref() {
                        PseudoExpr::IndexAccess {
                            collection,
                            index: 0,
                        } => matches!(
                            collection.as_ref(),
                            PseudoExpr::Var { name, id, .. }
                                if Self::var_matches_direct_subject(name, *id, subj_var_name, subj_var_id)
                        ),
                        PseudoExpr::FieldAccess {
                            record, selector, ..
                        } if selector.is_list_head() => {
                            matches!(
                                record.as_ref(),
                                PseudoExpr::Var { name, id, .. }
                                    if Self::var_matches_direct_subject(name, *id, subj_var_name, subj_var_id)
                            )
                        }
                        _ => false,
                    };
                    if first_is_head {
                        head_name = Some(Binder::new(n1.clone(), id1.unwrap_or_else(VarId::fresh_compat_placeholder)));
                        body = b1.as_ref();
                    }
                    // Check if v1 is List.tail(subj) - either BuiltinCall or Apply form
                    if head_name.is_none() {
                        let is_tail = Self::is_list_tail_of_direct_subject(
                            v1.as_ref(),
                            subj_var_name,
                            subj_var_id,
                        );
                        if is_tail {
                            tail_name = Some(Binder::new(n1.clone(), id1.unwrap_or_else(VarId::fresh_compat_placeholder)));
                            body = b1.as_ref();
                        }
                    }

                    // Look for the second let
                    if let PseudoExpr::Let {
                        name: n2,
                        id: id2,
                        value: v2,
                        body: b2,
                        ..
                    } = body
                    {
                        if head_name.is_some() && tail_name.is_none() {
                            if Self::is_list_tail_of_direct_subject(
                                v2.as_ref(),
                                subj_var_name,
                                subj_var_id,
                            ) {
                                tail_name = Some(Binder::new(n2.clone(), id2.unwrap_or_else(VarId::fresh_compat_placeholder)));
                                inner_body = Some(b2.as_ref().clone());
                            }
                        } else if tail_name.is_some() && head_name.is_none() {
                            let second_is_head = match v2.as_ref() {
                                PseudoExpr::IndexAccess {
                                    collection,
                                    index: 0,
                                } => matches!(
                                    collection.as_ref(),
                                    PseudoExpr::Var { name, id, .. }
                                        if Self::var_matches_direct_subject(name, *id, subj_var_name, subj_var_id)
                                ),
                                PseudoExpr::FieldAccess {
                                    record, selector, ..
                                } if selector.is_list_head() => {
                                    matches!(
                                        record.as_ref(),
                                        PseudoExpr::Var { name, id, .. }
                                            if Self::var_matches_direct_subject(name, *id, subj_var_name, subj_var_id)
                                    )
                                }
                                _ => false,
                            };
                            if second_is_head {
                                head_name = Some(Binder::new(n2.clone(), id2.unwrap_or_else(VarId::fresh_compat_placeholder)));
                                inner_body = Some(b2.as_ref().clone());
                            }
                        }
                    }
                }

                if let (Some(h), Some(t), Some(ib)) = (head_name, tail_name, inner_body) {
                    WhenClause {
                        pattern: WhenPattern::List {
                            elements: vec![h],
                            tail: Some(t),
                        },
                        guard: None,
                        body: ib,
                    }
                } else {
                    clause
                }
            })
            .collect()
    }

    /// Convert wildcard clause with inline (not let-bound) head/tail accesses
    /// to a list pattern, binding fresh names for head and tail.
    pub(super) fn destructure_inline_list_head_tail(
        &mut self,
        subject: &PseudoExpr,
        subject_name: &Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> Vec<WhenClause> {
        let (subj_var_name, subj_var_id) = match subject {
            PseudoExpr::Var { name, id, .. } => (name.as_str(), id.get()),
            _ => match subject_name {
                Some(name) => (name.as_str(), name.id.get()),
                None => return clauses,
            },
        };

        clauses
            .into_iter()
            .map(|clause| {
                if !matches!(clause.pattern, WhenPattern::Wildcard) || clause.guard.is_some() {
                    return clause;
                }

                let (has_head, has_tail) =
                    Self::list_access_usage_by_id(&clause.body, subj_var_name, subj_var_id);

                if !has_head && !has_tail {
                    return clause;
                }

                let head_binder = self.fresh_synthetic_binder(&format!("{}_h", subj_var_name));
                let tail_binder = self.fresh_synthetic_binder(&format!("{}_t", subj_var_name));

                let mut new_body = clause.body;
                if has_head {
                    new_body = Self::replace_head_access_by_id(
                        new_body,
                        subj_var_name,
                        subj_var_id,
                        head_binder.as_str(),
                        head_binder.id,
                    );
                }
                if has_tail {
                    new_body = Self::replace_tail_access_by_id(
                        new_body,
                        subj_var_name,
                        subj_var_id,
                        tail_binder.as_str(),
                        tail_binder.id,
                    );
                }

                if has_head && has_tail {
                    WhenClause {
                        pattern: WhenPattern::List {
                            elements: vec![head_binder],
                            tail: Some(tail_binder),
                        },
                        guard: None,
                        body: new_body,
                    }
                } else if has_head {
                    WhenClause {
                        pattern: WhenPattern::List {
                            elements: vec![head_binder],
                            tail: Some(self.fresh_synthetic_binder("_")),
                        },
                        guard: None,
                        body: new_body,
                    }
                } else {
                    WhenClause {
                        pattern: WhenPattern::List {
                            elements: vec![self.fresh_synthetic_binder("_")],
                            tail: Some(tail_binder),
                        },
                        guard: None,
                        body: new_body,
                    }
                }
            })
            .collect()
    }
}
