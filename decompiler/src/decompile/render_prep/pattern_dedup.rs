use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PBox, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

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
    /// One pending step of the walk: a job stack, because `when`s nest as
    /// deep as the script likes and on `wasm32` the call stack cannot grow
    /// to match.
    enum Step {
        Enter(PseudoExpr),
        Let {
            name: String,
            id: Option<VarId>,
        },
        Lambda {
            params: Vec<Binder>,
        },
        RecFn {
            name: Binder,
            params: Vec<Binder>,
        },
        /// The subject, then each clause's body and guard, are on `done`.
        When {
            subject_name: Option<Binder>,
            clause_meta: Vec<(WhenPattern, bool)>,
        },
        /// A clause renamed binders of its pattern: their uses in its body
        /// and guard take the new names, from this step to the matching
        /// `CloseClause`.
        OpenClause {
            renames: Vec<(VarId, String)>,
        },
        CloseClause {
            renames: usize,
        },
        Plain(PlainPost),
    }

    // Renamed pattern binders whose clauses are still being walked. A use
    // takes the name its OUTERMOST rename gives it — the order the renames
    // used to be applied in, inner clauses first and their parents after.
    let mut renamed: Vec<(VarId, String)> = Vec::new();
    let rename_of = |renamed: &[(VarId, String)], id: VarId| {
        renamed
            .iter()
            .find_map(|(vid, name)| (*vid == id).then(|| name.clone()))
    };

    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match expr {
                PseudoExpr::Var { name, id } => {
                    let name = id
                        .and_then(|id| rename_of(&renamed, id))
                        .unwrap_or(name);
                    done.push(PseudoExpr::Var { name, id });
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(Step::Let { name, id });
                    steps.push(Step::Enter(body.into_inner()));
                    steps.push(Step::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(Step::Lambda { params });
                    steps.push(Step::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(Step::RecFn { name, params });
                    steps.push(Step::Enter(body.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let subject_name = subject_name.map(|binder| match rename_of(&renamed, binder.id) {
                        Some(new_name) => binder.renamed(new_name),
                        None => binder,
                    });
                    // Each clause pops as: open its renames, its body, its
                    // guard, close its renames — so pushed in reverse.
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut clause_steps: Vec<Vec<Step>> = Vec::with_capacity(clauses.len());
                    for clause in clauses {
                        let (pattern, renamed_binders) = dedup_pattern_fields(clause.pattern);
                        clause_meta.push((pattern, clause.guard.is_some()));
                        let mut pending = vec![Step::CloseClause {
                            renames: renamed_binders.len(),
                        }];
                        if let Some(guard) = clause.guard {
                            pending.push(Step::Enter(guard));
                        }
                        pending.push(Step::Enter(clause.body));
                        pending.push(Step::OpenClause {
                            renames: renamed_binders,
                        });
                        clause_steps.push(pending);
                    }
                    steps.push(Step::When {
                        subject_name,
                        clause_meta,
                    });
                    for pending in clause_steps.into_iter().rev() {
                        steps.extend(pending);
                    }
                    steps.push(Step::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(Step::Plain(kind));
                        for child in children.into_iter().rev() {
                            steps.push(Step::Enter(child));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            Step::Let { name, id } => {
                let body = done.pop().expect("let body");
                let value = done.pop().expect("let value");
                done.push(PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                });
            }
            Step::Lambda { params } => {
                let body = done.pop().expect("lambda body");
                done.push(PseudoExpr::Lambda {
                    params,
                    body: PBox::new(body),
                });
            }
            Step::RecFn { name, params } => {
                let body = done.pop().expect("recfn body");
                done.push(PseudoExpr::RecFn {
                    name,
                    params,
                    body: PBox::new(body),
                });
            }
            Step::When {
                subject_name,
                clause_meta,
            } => {
                let total = 1 + clause_meta
                    .iter()
                    .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                    .sum::<usize>();
                let mut parts = take(&mut done, total).into_iter();
                let subject = parts.next().expect("when subject");
                let clauses = clause_meta
                    .into_iter()
                    .map(|(pattern, has_guard)| {
                        let body = parts.next().expect("when clause body");
                        let guard = has_guard.then(|| parts.next().expect("when guard"));
                        WhenClause {
                            pattern,
                            guard,
                            body,
                        }
                    })
                    .collect();
                done.push(PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                });
            }
            Step::OpenClause { renames } => renamed.extend(renames),
            Step::CloseClause { renames } => {
                renamed.truncate(renamed.len() - renames);
            }
            Step::Plain(kind) => {
                let rebuilt = rebuild_plain(kind, &mut done);
                done.push(rebuilt);
            }
        }
    }
    done.pop().expect("one result")
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
