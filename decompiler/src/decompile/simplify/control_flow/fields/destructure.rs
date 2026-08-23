use std::collections::{HashMap, HashSet};

use crate::decompile::simplify::Simplifier;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;

impl Simplifier {
    /// Convert field index accesses to named fields in when constructor patterns.
    ///
    /// Given:
    /// ```text
    /// when x is { Constr<N> -> ... fields_var[0] ... fields_var[1] ... }
    /// ```
    /// where `fields_var` is `x.fields`, convert to:
    /// ```text
    /// when x is { Constr<N>(field_0, field_1) -> ... field_0 ... field_1 ... }
    /// ```
    pub(in crate::decompile::simplify) fn destructure_when_fields(
        &mut self,
        subject: &PseudoExpr,
        _subject_name: &Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> Vec<WhenClause> {
        let (subj_var_name, subj_var_id) = match subject {
            PseudoExpr::Var { name, id, .. } => (name.as_str(), id.get()),
            _ => return clauses,
        };

        // Look up the fields binding: e.g., fv = x.fields
        let fields_var = self
            .constructors
            .fields_bindings
            .iter()
            .find(|(_, src)| {
                if let PseudoExpr::Var { name, id, .. } = src {
                    Self::var_matches_direct_subject(name, *id, subj_var_name, subj_var_id)
                } else {
                    false
                }
            })
            .map(|(k, _)| *k);

        let fv_id = fields_var;

        clauses
            .into_iter()
            .map(|clause| {
                if let WhenPattern::Constructor {
                    ref type_hint,
                    tag,
                    ref fields,
                    ref shape,
                } = clause.pattern
                {
                    if let Some(rewritten) = self.collapse_exact_single_field_subject_fields_clause(
                        &clause,
                        subj_var_name,
                        subj_var_id,
                    ) {
                        return rewritten;
                    }
                    if !fields.is_empty() {
                        return clause; // Already has fields
                    }
                    let mut index_counts = HashMap::new();
                    if let Some(guard) = &clause.guard {
                        Self::merge_index_access_counts(
                            &mut index_counts,
                            Self::collect_direct_subject_fields_index_access_counts(
                                guard,
                                subj_var_name,
                                subj_var_id,
                            ),
                        );
                    }
                    Self::merge_index_access_counts(
                        &mut index_counts,
                        Self::collect_direct_subject_fields_index_access_counts(
                            &clause.body,
                            subj_var_name,
                            subj_var_id,
                        ),
                    );
                    if let Some(fv_id) = fv_id {
                        if let Some(guard) = &clause.guard {
                            Self::merge_index_access_counts(
                                &mut index_counts,
                                Self::collect_index_access_counts(guard, "", Some(fv_id)),
                            );
                        }
                        Self::merge_index_access_counts(
                            &mut index_counts,
                            Self::collect_index_access_counts(&clause.body, "", Some(fv_id)),
                        );
                    }
                    if index_counts.is_empty() {
                        return clause;
                    }
                    let Some(max_index) = index_counts.keys().max().copied() else {
                        return clause;
                    };
                    let mut used_names = HashSet::new();
                    Self::collect_var_names(subject, &mut used_names);
                    if let Some(guard) = &clause.guard {
                        Self::collect_var_names(guard, &mut used_names);
                    }
                    Self::collect_var_names(&clause.body, &mut used_names);
                    used_names.insert(subj_var_name.to_string());
                    let field_binders: Vec<Binder> = (0..=max_index)
                        .map(|i| {
                            if index_counts.contains_key(&i) {
                                let field_name = self
                                    .fresh_name_for_scope(&mut used_names, format!("field_{}", i));
                                self.fresh_synthetic_binder(&field_name)
                            } else {
                                self.fresh_synthetic_binder("_")
                            }
                        })
                        .collect();
                    // Replace fv[N] with field_N in body
                    let mut new_guard = clause.guard.clone();
                    let mut new_body = clause.body.clone();
                    for &idx in index_counts.keys() {
                        let field_binder = &field_binders[idx];
                        if let Some(guard) = new_guard.take() {
                            let mut next_guard = Self::replace_direct_subject_fields_index_access(
                                guard,
                                subj_var_name,
                                subj_var_id,
                                idx,
                                &field_binder.name,
                                field_binder.id,
                            );
                            if let Some(fv_id) = fv_id {
                                next_guard = Self::replace_index_access(
                                    next_guard,
                                    "",
                                    Some(fv_id),
                                    idx,
                                    &field_binder.name,
                                    field_binder.id,
                                );
                            }
                            new_guard = Some(next_guard);
                        }
                        new_body = Self::replace_direct_subject_fields_index_access(
                            new_body,
                            subj_var_name,
                            subj_var_id,
                            idx,
                            &field_binder.name,
                            field_binder.id,
                        );
                        if let Some(fv_id) = fv_id {
                            new_body = Self::replace_index_access(
                                new_body,
                                "",
                                Some(fv_id),
                                idx,
                                &field_binder.name,
                                field_binder.id,
                            );
                        }
                    }
                    let type_hint = type_hint.clone();
                    // Pattern binders come from the simplifier's
                    // per-instance counter, not global
                    // `Binder::synthetic`: a global id could collide
                    // with one minted from the local counter in the
                    // same run, leaving two binders sharing an id.
                    let fields = field_binders;
                    let shape =
                        ConstructorShape::from_name_and_tag(shape.pretty_name(), tag, fields.len());
                    WhenClause {
                        pattern: WhenPattern::Constructor {
                            type_hint,
                            tag,
                            fields,
                            shape,
                        },
                        guard: new_guard,
                        body: new_body,
                    }
                } else {
                    clause
                }
            })
            .collect()
    }

    fn merge_index_access_counts(
        target: &mut HashMap<usize, usize>,
        counts: HashMap<usize, usize>,
    ) {
        for (index, count) in counts {
            *target.entry(index).or_default() += count;
        }
    }
}
