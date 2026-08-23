//! Collapse a redundant `when script_context is { K -> body }` wrap
//! inside an emitted validator block.
//!
//! `ScriptContext` is a single-variant Plutus constructor
//! (`Constr 0 [TxInfo, ScriptPurpose]` for V1/V2, single-variant
//! for V3), so the outer `when` is a tautology. The body reaches
//! `script_context` only by field access, which needs no pattern
//! match, so the wrapper drops and the productive clause's body
//! takes its place.
//!
//! Gated so it never fires on a legitimate sum-type `when`:
//!
//! 1. A `Let { name: "decompiled", .. }` binding a `Lambda` must
//!    exist (the `wrap_validator_entry_for_render` sentinel); only
//!    that lambda's `script_context` params qualify as subjects.
//! 2. The subject is a `Var` carrying one of those ids, and the
//!    `when` has no `subject_name` — an alias would dangle after
//!    collapse.
//! 3. The first clause is a `Constructor` with `tag == 0` (the one
//!    ScriptContext variant) and no fields; every later clause is a
//!    `Wildcard`. Clauses are order-sensitive, so a wildcard before
//!    the constructor arm would short-circuit; wildcards after it
//!    are unreachable.
//! 4. No clause has a guard.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;
use std::collections::HashSet;

pub(super) fn collapse_script_context_when(expr: PseudoExpr) -> PseudoExpr {
    // Collect the `script_context` param ids of every
    // `Let { name: "decompiled", value: Lambda }` — the only subjects
    // eligible to collapse.
    let sc_ids = collect_script_context_param_ids(&expr);
    if sc_ids.is_empty() {
        return expr;
    }
    let mut collapser = Collapser { sc_ids };
    collapser.fold(expr)
}

pub(super) fn collect_script_context_param_ids(expr: &PseudoExpr) -> HashSet<VarId> {
    let mut out = HashSet::new();
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Let {
                name, value, body, ..
            } => {
                if name == "decompiled"
                    && let PseudoExpr::Lambda { params, body: _ } = value.as_ref()
                {
                    for p in params {
                        if p.as_str() == "script_context" {
                            out.insert(p.id);
                        }
                    }
                }
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. } => pending.push(body),
            PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                    if let Some(g) = &c.guard {
                        pending.push(g);
                    }
                }
                pending.push(subject);
            }
            _ => {}
        }
    }
    out
}

struct Collapser {
    sc_ids: HashSet<VarId>,
}

impl ExprFolder for Collapser {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<crate::pseudo::ast::Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        // Gate 2: subject is a Var whose id is in sc_ids AND there's
        // no `when … as alias is` binding (alias would dangle).
        let subject_is_sc = match &subject {
            PseudoExpr::Var { id: Some(vid), .. } => self.sc_ids.contains(vid),
            _ => false,
        };
        if !subject_is_sc || subject_name.is_some() {
            return PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            };
        }
        // Gate 3: first clause `Constructor(tag=0, fields=[])`, all
        // later clauses `Wildcard`, none guarded. A wildcard before
        // the constructor would match first, hence the order gate.
        for c in &clauses {
            if c.guard.is_some() {
                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                };
            }
        }
        let Some(first) = clauses.first() else {
            return PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            };
        };
        let WhenPattern::Constructor { tag, fields, .. } = &first.pattern else {
            return PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            };
        };
        if *tag != 0 || !fields.is_empty() {
            return PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            };
        }
        for c in clauses.iter().skip(1) {
            if !matches!(&c.pattern, WhenPattern::Wildcard) {
                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                };
            }
        }
        // All gates passed — drop the wrapper, keep the first arm.
        let mut owned = clauses;
        owned.swap_remove(0).body
    }
}

#[cfg(test)]
mod tests;
