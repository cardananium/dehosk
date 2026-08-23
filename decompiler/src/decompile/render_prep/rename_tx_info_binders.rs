//! Rename generic dehosk binders in a `when <subject> is { … }`
//! constructor pattern to the canonical Plutus field names.
//!
//! Synthetic names carry only a type hint (`items` for List, `map_*`
//! for Map, `variant` for a sum) — not the semantic identity
//! (`inputs`, `outputs`, `fee`, …). The subject's binder name picks the
//! schema and the pattern arity picks the variant: `tx_info` at arity
//! 10 / 12 / 16 is V1 / V2 / V3 TxInfo. Any other name/arity pair is
//! left alone — a script may bind a user-defined Constr under the same
//! name.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn rename_tx_info_binders(expr: PseudoExpr) -> PseudoExpr {
    rewrite(expr)
}

/// Canonical field names for a Plutus context type's
/// constructor pattern, keyed by the When-subject's binder name
/// and the constructor's arity. `None` for an unrecognized pair —
/// that pattern keeps its dehosk-generated names.
fn canonical_names_for_subject(
    subject_name: &str,
    arity: usize,
) -> Option<&'static [&'static str]> {
    match (subject_name, arity) {
        // V1/V2 ScriptContext: 2 fields (tx_info, purpose).
        ("script_context", 2) => Some(&["tx_info", "purpose"]),
        // V3 ScriptContext: 3 fields (tx_info, redeemer, script_info).
        ("script_context", 3) => Some(&["tx_info", "redeemer", "script_info"]),
        // V1/V2/V3 TxInfo: arity disambiguates the version.
        ("tx_info", a) => canonical_names_for_tx_info_arity(a),
        // Interval (valid_range) destructure: 2 fields.
        ("valid_range", 2) => Some(&["lower_bound", "upper_bound"]),
        // IntervalBound (lower_bound or upper_bound): 2 fields.
        ("lower_bound", 2) | ("upper_bound", 2) => Some(&["bound_type", "is_inclusive"]),
        _ => None,
    }
}

/// Canonical field names for the Plutus TxInfo
/// constructor at a given arity. Arity disambiguates V1 (10), V2
/// (12), V3 (16). Returns `None` for unknown arities.
pub(super) fn canonical_names_for_tx_info_arity(arity: usize) -> Option<&'static [&'static str]> {
    match arity {
        10 => Some(&[
            "inputs",
            "outputs",
            "fee",
            "mint",
            "certificates",
            "withdrawals",
            "valid_range",
            "signatories",
            "datums",
            "transaction_id",
        ]),
        12 => Some(&[
            "inputs",
            "reference_inputs",
            "outputs",
            "fee",
            "mint",
            "certificates",
            "withdrawals",
            "valid_range",
            "signatories",
            "redeemers",
            "datums",
            "transaction_id",
        ]),
        16 => Some(&[
            "inputs",
            "reference_inputs",
            "outputs",
            "fee",
            "mint",
            "certificates",
            "withdrawals",
            "valid_range",
            "signatories",
            "redeemers",
            "datums",
            "transaction_id",
            "votes",
            "proposal_procedures",
            "current_treasury_amount",
            "treasury_donation",
        ]),
        _ => None,
    }
}

/// One pending step of [`rewrite_top_down`]'s explicit stack.
enum Step {
    Enter(PseudoExpr),
    Post(Post),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum Post {
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
    When {
        subject_name: Option<Binder>,
        /// Per clause: its pattern (already settled by `f`, never
        /// descended into) and whether it had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Apply `f` to each node on the way DOWN, then rebuild that node from its
/// rewritten children.
fn rewrite_top_down(expr: PseudoExpr, mut f: impl FnMut(PseudoExpr) -> PseudoExpr) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match f(expr) {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(Step::Post(Post::Let { name, id }));
                    steps.push(Step::Enter(body.into_inner()));
                    steps.push(Step::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(Step::Post(Post::Lambda { params }));
                    steps.push(Step::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(Step::Post(Post::RecFn { name, params }));
                    steps.push(Step::Enter(body.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut clause_children = Vec::new();
                    for c in clauses {
                        clause_meta.push((c.pattern, c.guard.is_some()));
                        if let Some(g) = c.guard {
                            clause_children.push(g);
                        }
                        clause_children.push(c.body);
                    }
                    steps.push(Step::Post(Post::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(Step::Enter(c));
                    }
                    steps.push(Step::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(Step::Post(Post::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(Step::Enter(c));
                        }
                    }
                    // A leaf: `f` already ran on it and `map_children`
                    // returned it unchanged.
                    Err(leaf) => done.push(leaf),
                },
            },
            Step::Post(post) => {
                let rebuilt = match post {
                    Post::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    Post::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    Post::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    Post::When {
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
                            .map(|(pattern, has_guard)| WhenClause {
                                pattern,
                                guard: has_guard.then(|| parts.next().expect("when guard")),
                                body: parts.next().expect("when clause body"),
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    Post::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite_top_down must leave one result");
    done.pop().expect("rewrite_top_down result")
}

/// Settle every `when` in the tree: at each one, the subject's binder name
/// keys the canonical schema, the clause patterns are renamed, and the new
/// names are substituted through the clause guards/bodies before those are
/// walked.
///
/// The key is read from the subject BEFORE it is walked, which is what the
/// recursion did too — it read the key off `rewrite(subject)`, and `rewrite`
/// returns a `Var` untouched, so the two agree.
fn rewrite(expr: PseudoExpr) -> PseudoExpr {
    rewrite_top_down(expr, |expr| match expr {
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => {
            // The subject's binder name keys the canonical schema
            // — see `canonical_names_for_subject`.
            let subject_canonical_key = match subject.as_ref() {
                PseudoExpr::Var {
                    name, id: Some(_), ..
                } => Some(name.clone()),
                _ => None,
            };
            let clauses: Vec<WhenClause> = clauses
                .into_iter()
                .map(|c| {
                    if let Some(key) = subject_canonical_key.as_deref() {
                        settle_clause_with_canonical_names(c, key)
                    } else {
                        c
                    }
                })
                .collect();
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            }
        }
        other => other,
    })
}

/// Rename one clause's pattern binders to the canonical names and
/// substitute those names through its guard/body.
///
/// Does NOT walk the guard/body itself: [`rewrite_top_down`] descends into
/// them right after.
fn settle_clause_with_canonical_names(c: WhenClause, subject_name: &str) -> WhenClause {
    let WhenClause {
        pattern,
        guard,
        body,
    } = c;
    let (new_pattern, rename_map) = match pattern {
        WhenPattern::Constructor {
            type_hint,
            tag,
            fields,
            shape,
        } => {
            let canonical = match canonical_names_for_subject(subject_name, fields.len()) {
                Some(names) => names,
                None => {
                    return WhenClause {
                        pattern: WhenPattern::Constructor {
                            type_hint,
                            tag,
                            fields,
                            shape,
                        },
                        guard,
                        body,
                    };
                }
            };
            let mut rename_map: HashMap<VarId, &'static str> = HashMap::new();
            let new_fields: Vec<Binder> = fields
                .into_iter()
                .enumerate()
                .map(|(i, old)| {
                    let name = canonical[i];
                    // A binder already carrying the canonical name is
                    // left as-is — no rename entry, so the body walk
                    // skips it.
                    let old_name = old.to_string();
                    if old_name == name {
                        return old;
                    }
                    rename_map.insert(old.var_id(), name);
                    Binder::new(name, old.var_id())
                })
                .collect();
            (
                WhenPattern::Constructor {
                    type_hint,
                    tag,
                    fields: new_fields,
                    shape,
                },
                rename_map,
            )
        }
        other => (other, HashMap::new()),
    };
    if rename_map.is_empty() {
        return WhenClause {
            pattern: new_pattern,
            guard,
            body,
        };
    }
    WhenClause {
        pattern: new_pattern,
        guard: guard.map(|g| substitute_var_names(g, &rename_map)),
        body: substitute_var_names(body, &rename_map),
    }
}

/// Retarget every `Var` reference whose id is in `map` to the new display
/// name. Binders are untouched — the caller renamed those already.
/// Only rewrites leaves, so top-down and bottom-up coincide.
fn substitute_var_names(expr: PseudoExpr, map: &HashMap<VarId, &'static str>) -> PseudoExpr {
    rewrite_top_down(expr, |expr| match expr {
        PseudoExpr::Var {
            name,
            id: Some(vid),
        } => {
            if let Some(&new_name) = map.get(&vid) {
                PseudoExpr::Var {
                    name: new_name.to_string(),
                    id: Some(vid),
                }
            } else {
                PseudoExpr::Var {
                    name,
                    id: Some(vid),
                }
            }
        }
        other => other,
    })
}

#[cfg(test)]
mod tests;
