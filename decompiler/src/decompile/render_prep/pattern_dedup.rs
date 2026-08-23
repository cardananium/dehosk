use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::rename_var_use_by_id_in_expr;

#[cfg(test)]
pub(crate) fn debug_deduplicate_constr_pattern_binders(expr: PseudoExpr) -> PseudoExpr {
    deduplicate_constr_pattern_binders(expr)
}

// Deduplicate same-named binders in a single Constr pattern.
//
// Cardano-context naming can give a multi-field Constructor pattern the
// same schema-derived name in two field slots — `Constr<N>(map, _, _,
// map, …)` — which is invalid surface syntax: a pattern may not bind the same
// identifier twice.
//
// This pass renames earlier duplicates to `{name}_{idx}` where idx is
// the 0-based binder position. The rightmost occurrence keeps the
// original name, so body references resolve to it — the shadowing surface
// would apply at parse time.

pub(super) fn deduplicate_constr_pattern_binders(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    struct Dedup;

    impl ExprFolder for Dedup {
        fn fold_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<crate::pseudo::ast::WhenClause>,
        ) -> PseudoExpr {
            let subject = self.fold(subject);
            let clauses = clauses
                .into_iter()
                .map(|mut clause| {
                    let (pattern, renamed_binders) = dedup_pattern_fields(clause.pattern);
                    clause.pattern = pattern;
                    clause.body = self.fold(clause.body);
                    clause.guard = clause.guard.map(|g| self.fold(g));
                    for (id, new_name) in renamed_binders {
                        clause.body = rename_var_use_by_id_in_expr(&clause.body, id, &new_name);
                        clause.guard = clause
                            .guard
                            .map(|guard| rename_var_use_by_id_in_expr(&guard, id, &new_name));
                    }
                    clause
                })
                .collect();
            self.post_when(subject, subject_name, clauses)
        }
    }

    let mut folder = Dedup;
    folder.fold(expr)
}

fn dedup_pattern_fields(pattern: WhenPattern) -> (WhenPattern, Vec<(VarId, String)>) {
    match pattern {
        WhenPattern::Constructor {
            type_hint,
            tag,
            fields,
            shape,
        } => {
            // Only non-underscore binders matter for collision detection.
            let mut seen: HashMap<String, Vec<usize>> = HashMap::new();
            for (idx, b) in fields.iter().enumerate() {
                if b.as_str() != "_" {
                    seen.entry(b.to_string()).or_default().push(idx);
                }
            }
            let has_dup = seen.values().any(|idxs| idxs.len() > 1);
            if !has_dup {
                return (
                    WhenPattern::Constructor {
                        type_hint,
                        tag,
                        fields,
                        shape,
                    },
                    Vec::new(),
                );
            }
            // Rename all but the last occurrence of each duplicated name.
            let mut renamed_binders = Vec::new();
            let fields: Vec<Binder> = fields
                .into_iter()
                .enumerate()
                .map(|(idx, binder)| {
                    if binder.as_str() == "_" {
                        return binder;
                    }
                    let occurrences = seen.get(binder.as_str()).expect("seen populated above");
                    if occurrences.len() <= 1 {
                        return binder;
                    }
                    let is_last = occurrences.last().copied() == Some(idx);
                    if is_last {
                        binder
                    } else {
                        let new_name = format!("{}_{}", binder.as_str(), idx);
                        if binder.id.get().is_some() {
                            renamed_binders.push((binder.id, new_name.clone()));
                        }
                        Binder::new(&new_name, binder.var_id())
                    }
                })
                .collect();
            (
                WhenPattern::Constructor {
                    type_hint,
                    tag,
                    fields,
                    shape,
                },
                renamed_binders,
            )
        }
        other => (other, Vec::new()),
    }
}
