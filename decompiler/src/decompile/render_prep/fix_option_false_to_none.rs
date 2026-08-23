//! Re-label a `Bool(false)` that is actually `Option::None`.
//!
//! `None` and `False` share a nullary constructor encoding (Plutus
//! `Constr _ []`); under the reversed PlutusTx ordering they even
//! share tag 0, so a church/constructor decoder can decode an
//! `Option::None` to a `Bool(false)` literal. Matched later as an
//! `Option`, the output is type-incoherent.
//!
//! For `Let { id, value, body }` where `id` is matched somewhere in
//! `body` against a `Some`/`None` pattern — structural proof that
//! the binding is an `Option` — rewrite every `Bool(false)` in the
//! tail positions of `value` to `None`, unless `value` has a
//! definite Bool tail leaf. The downstream match is the evidence
//! rather than an inferred type: the same `False`/`None` ambiguity
//! poisons inference (a `False` arm can push a binding's inferred
//! type to `Option<Option<_>>`), so the inferred `Option` would be
//! circular. A `Some`/`None` pattern cannot apply to a genuine
//! `Bool`.
//!
//! Only `Bool(false)` in tail/result position of the bound value is
//! touched (an `if`/`when`/`let` result, not an operand). A genuine
//! `Bool` can never sit in the tail of an `Option`-typed
//! expression. `Bool(true)` is left alone: `True`/`Some` would need
//! a payload to reconcile. The Bool-tail veto also blocks a Bool
//! predicate consumed by a church-decoded `{None; Some(_)}` when —
//! a tag-equivalent relabel of `{True; False}` — which would flip
//! tag 0 → 1 and invert the surrounding logic.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;
use crate::pseudo::var_id::VarId;

use super::bool_witness::has_definite_bool_tail_leaf;
use super::scope_recurse::{children, rewrite_bottom_up};

pub(super) fn fix_option_false_to_none(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_rewrite)
}

fn try_rewrite(expr: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::Let {
        name,
        id,
        value,
        body,
    } = expr
    else {
        return expr;
    };
    // The `Some`/`None` match is necessary but not sufficient evidence:
    // a Bool predicate result (a `list.any` predicate, say) consumed by
    // a church-decoded `when {None -> .; Some(_) -> .}` — a tag-equivalent
    // RELABEL of `{True -> .; False -> .}` — trips the same witness, and
    // rewriting its `False` to `None` flips tag 0 -> 1, INVERTING the
    // surrounding logic. So also require that the bound value carries no
    // definite Bool tail leaf.
    let matched = id.is_some_and(|vid| binding_matched_as_option(&body, vid));
    let value = if matched && !has_definite_bool_tail_leaf(&value) {
        PBox::new(rewrite_tail_false_to_none(value.into_inner()))
    } else {
        value
    };
    PseudoExpr::Let {
        name,
        id,
        value,
        body,
    }
}

/// True when `vid` is the subject of a `When` somewhere in `expr` that
/// matches it against a `Some`/`None` constructor pattern.
fn binding_matched_as_option(expr: &PseudoExpr, vid: VarId) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = current
            && matches!(subject.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == vid)
            && clauses.iter().any(|c| pattern_is_option(&c.pattern))
        {
            return true;
        }
        pending.extend(children(current));
    }
    false
}

fn pattern_is_option(pattern: &WhenPattern) -> bool {
    matches!(
        pattern,
        WhenPattern::Constructor { shape, .. }
            if matches!(
                shape.as_known(),
                Some(KnownConstructor::Some | KnownConstructor::None)
            )
    )
}

/// Replace `Bool(false)` with `None` in the tail/result positions of
/// `expr` only — recursing through `if`/`when`/`let` results, never
/// into operands or sub-values.
fn rewrite_tail_false_to_none(expr: PseudoExpr) -> PseudoExpr {
    enum Frame {
        If {
            condition: PBox,
        },
        When {
            subject: PBox,
            subject_name: Option<crate::pseudo::ast::Binder>,
            pattern_guards: Vec<(WhenPattern, Option<PseudoExpr>)>,
        },
        Let {
            name: String,
            id: Option<VarId>,
            value: PBox,
        },
        // `trace msg: value` evaluates to `value`, so the value is the
        // tail; the message is not.
        Trace {
            message: PBox,
        },
    }

    enum Step {
        Enter(PseudoExpr),
        Post(Frame),
    }

    let mut steps = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(PseudoExpr::Bool(false)) => {
                done.push(PseudoExpr::constr_known(KnownConstructor::None, vec![]));
            }
            Step::Enter(PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            }) => {
                steps.push(Step::Post(Frame::If { condition }));
                steps.push(Step::Enter(else_branch.into_inner()));
                steps.push(Step::Enter(then_branch.into_inner()));
            }
            Step::Enter(PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            }) => {
                let mut pattern_guards = Vec::with_capacity(clauses.len());
                let mut bodies = Vec::with_capacity(clauses.len());
                for c in clauses {
                    pattern_guards.push((c.pattern, c.guard));
                    bodies.push(c.body);
                }
                steps.push(Step::Post(Frame::When {
                    subject,
                    subject_name,
                    pattern_guards,
                }));
                for body in bodies.into_iter().rev() {
                    steps.push(Step::Enter(body));
                }
            }
            Step::Enter(PseudoExpr::Let {
                name,
                id,
                value,
                body,
            }) => {
                steps.push(Step::Post(Frame::Let { name, id, value }));
                steps.push(Step::Enter(body.into_inner()));
            }
            Step::Enter(PseudoExpr::Trace { message, value }) => {
                steps.push(Step::Post(Frame::Trace { message }));
                steps.push(Step::Enter(value.into_inner()));
            }
            Step::Enter(other) => done.push(other),

            Step::Post(Frame::If { condition }) => {
                let else_branch = done.pop().expect("rewrite_tail_false_to_none: if else");
                let then_branch = done.pop().expect("rewrite_tail_false_to_none: if then");
                done.push(PseudoExpr::If {
                    condition,
                    then_branch: PBox::new(then_branch),
                    else_branch: PBox::new(else_branch),
                });
            }
            Step::Post(Frame::When {
                subject,
                subject_name,
                pattern_guards,
            }) => {
                let at = done.len() - pattern_guards.len();
                let bodies = done.split_off(at);
                let clauses = pattern_guards
                    .into_iter()
                    .zip(bodies)
                    .map(|((pattern, guard), body)| WhenClause {
                        pattern,
                        guard,
                        body,
                    })
                    .collect();
                done.push(PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                });
            }
            Step::Post(Frame::Let { name, id, value }) => {
                let body = done.pop().expect("rewrite_tail_false_to_none: let body");
                done.push(PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body: PBox::new(body),
                });
            }
            Step::Post(Frame::Trace { message }) => {
                let value = done.pop().expect("rewrite_tail_false_to_none: trace value");
                done.push(PseudoExpr::Trace {
                    message,
                    value: PBox::new(value),
                });
            }
        }
    }

    done.pop()
        .expect("rewrite_tail_false_to_none: machine must leave one result")
}

#[cfg(test)]
mod tests;
