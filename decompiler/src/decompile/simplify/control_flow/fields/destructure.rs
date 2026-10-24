use std::collections::{HashMap, HashSet};

use crate::decompile::simplify::Simplifier;
use crate::decompile::simplify::step::Step;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

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
    ) -> Step<Vec<WhenClause>> {
        let (subj_var_name, subj_var_id) = match subject {
            PseudoExpr::Var { name, id, .. } => (name.as_str(), id.get()),
            _ => return Step::Done(clauses),
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

        let destructured = Vec::with_capacity(clauses.len());
        self.destructure_clause_fields_from(FieldsDestructure {
            subject: subject.clone(),
            subj_var_name: subj_var_name.to_string(),
            subj_var_id,
            fv_id,
            clauses: clauses.into_iter(),
            destructured,
        })
    }

    /// [`Self::destructure_when_fields`] run to its result, for the suites.
    #[cfg(test)]
    pub(in crate::decompile::simplify) fn destructure_when_fields_settled(
        &mut self,
        subject: &PseudoExpr,
        subject_name: &Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> Vec<WhenClause> {
        let step = self.destructure_when_fields(subject, subject_name, clauses);
        self.finish(step)
    }

    /// Destructure the remaining clauses in order. A constructor clause
    /// first tries the single-field collapse, which may have to simplify
    /// the collapsed body before it knows whether it applies; the loop
    /// then continues from the step's result.
    fn destructure_clause_fields_from(
        &mut self,
        mut state: FieldsDestructure,
    ) -> Step<Vec<WhenClause>> {
        while let Some(clause) = state.clauses.next() {
            if !matches!(clause.pattern, WhenPattern::Constructor { .. }) {
                state.destructured.push(clause);
                continue;
            }
            let collapsed = self.collapse_exact_single_field_subject_fields_clause(
                &clause,
                &state.subj_var_name,
                state.subj_var_id,
            );
            match collapsed {
                Step::Done(Some(rewritten)) => state.destructured.push(rewritten),
                Step::Done(None) => {
                    let destructured = self.destructure_clause_fields(&state, clause);
                    state.destructured.push(destructured);
                }
                pending => {
                    return pending.then(self, move |simplifier, collapsed| {
                        let destructured = match collapsed {
                            Some(rewritten) => rewritten,
                            None => simplifier.destructure_clause_fields(&state, clause),
                        };
                        state.destructured.push(destructured);
                        simplifier.destructure_clause_fields_from(state)
                    });
                }
            }
        }
        Step::Done(state.destructured)
    }

    /// Name the fields of one constructor clause that the single-field
    /// collapse left alone.
    fn destructure_clause_fields(
        &mut self,
        state: &FieldsDestructure,
        clause: WhenClause,
    ) -> WhenClause {
        let subject = &state.subject;
        let subj_var_name = state.subj_var_name.as_str();
        let subj_var_id = state.subj_var_id;
        let fv_id = state.fv_id;
        if let WhenPattern::Constructor {
            ref type_hint,
            tag,
            ref fields,
            ref shape,
        } = clause.pattern
        {
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
                        let field_name =
                            self.fresh_name_for_scope(&mut used_names, format!("field_{}", i));
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
            let shape = ConstructorShape::from_name_and_tag(shape.pretty_name(), tag, fields.len());
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

/// The clauses of a `when` whose constructor fields are being destructured,
/// with the direct subject they belong to.
struct FieldsDestructure {
    subject: PseudoExpr,
    subj_var_name: String,
    subj_var_id: Option<VarId>,
    /// The binding holding the subject's `fields`, when one is tracked.
    fv_id: Option<VarId>,
    clauses: std::vec::IntoIter<WhenClause>,
    destructured: Vec<WhenClause>,
}
