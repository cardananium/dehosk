//! Unify the field-arity of each unresolved stub constructor across
//! all of its destructuring sites.
//!
//! A Scott-encoded constructor the decompiler can't name is emitted
//! as a synthetic `Unknown_S_<ord>_<tag>` whose arity is captured at
//! collection time from the `when`/`expect` pattern — often nullary.
//! `inline_pattern_field_access::expand_pattern_for_overflow_accesses`
//! then grows each pattern site independently, so the same constructor
//! is destructured at different arities. A constructor has one fixed
//! arity, so that neither parses nor type-checks.
//!
//! Per `(type_hint, tag)` of an unresolved `ConstructorShape::Unknown`,
//! take the max field-arity over every `when`/`expect` pattern, then
//! pad every shorter pattern of that pair with `_` binders and bump
//! the pattern's shape arity to match. The matching declaration arity
//! is reconciled separately by [`super::stub_adt::reconcile_declared_arities`],
//! which reads the padded patterns back out of the rendered AST.
//!
//! Only `Unknown`-shape constructors carrying a `type_hint` are
//! touched: `Known(_)` constructors have a fixed prelude arity that
//! must not change. `_` binders introduce no referenceable name, so
//! the padded fields render as ignored.

use std::collections::HashMap;

use crate::decompile::blueprint_registry::TypeHintId;
use crate::pseudo::ast::{Binder, PBox, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

use super::scope_recurse::children;

pub(super) fn unify_constructor_pattern_arity(expr: PseudoExpr) -> PseudoExpr {
    let mut max: HashMap<(TypeHintId, usize), usize> = HashMap::new();
    collect_max_arity(&expr, &mut max);
    if max.is_empty() {
        return expr;
    }
    pad(expr, &max)
}

/// Record, per `(type_hint, tag)`, the maximum field count of any
/// unresolved-constructor `when`/`expect` pattern.
fn collect_max_arity(expr: &PseudoExpr, max: &mut HashMap<(TypeHintId, usize), usize>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::When { clauses, .. } = cur {
            for clause in clauses {
                record_pattern(&clause.pattern, max);
            }
        }
        // Fold in value-position constructions too: a `Constr` value isn't
        // paddable, so its field count sets the floor the patterns must be
        // padded up to, keeping value, patterns and declaration uniform.
        if let PseudoExpr::Constr {
            type_hint: Some(hint),
            tag,
            fields,
            shape,
        } = cur
            && matches!(shape, ConstructorShape::Unknown { .. })
        {
            let entry = max.entry((hint.clone(), *tag)).or_insert(0);
            *entry = (*entry).max(fields.len());
        }
        for child in children(cur).into_iter().rev() {
            pending.push(child);
        }
    }
}

fn record_pattern(pattern: &WhenPattern, max: &mut HashMap<(TypeHintId, usize), usize>) {
    if let WhenPattern::Constructor {
        type_hint: Some(hint),
        tag,
        fields,
        shape,
    } = pattern
        && matches!(shape, ConstructorShape::Unknown { .. })
    {
        let entry = max.entry((hint.clone(), *tag)).or_insert(0);
        *entry = (*entry).max(fields.len());
    }
}

/// Pad every short constructor pattern in `expr`.
///
/// A job stack, because `when`s nest as deep as the script likes and on
/// `wasm32` the call stack cannot grow to match. `pad_pattern` allocates
/// fresh `VarId`s in call order (`VarId::fresh_binding`), and a `when`'s
/// clauses — each pattern, then its guard and body — are padded before its
/// subject, so the walk keeps exactly that order.
fn pad(expr: PseudoExpr, max: &HashMap<(TypeHintId, usize), usize>) -> PseudoExpr {
    enum Step {
        Enter(PseudoExpr),
        /// Pad a clause's pattern, now that the clauses before it are done.
        Pattern(WhenPattern),
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
        /// The clauses' guards and bodies, then the subject, are on `done`;
        /// the padded patterns are on `patterns`.
        When {
            subject_name: Option<Binder>,
            guards: Vec<bool>,
        },
        Plain(PlainPost),
    }

    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();
    let mut patterns: Vec<WhenPattern> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match expr {
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
                    let guards = clauses.iter().map(|c| c.guard.is_some()).collect();
                    steps.push(Step::When {
                        subject_name,
                        guards,
                    });
                    // Popped in order: each clause's pattern, guard and body,
                    // then the subject.
                    steps.push(Step::Enter(subject.into_inner()));
                    for clause in clauses.into_iter().rev() {
                        steps.push(Step::Enter(clause.body));
                        if let Some(guard) = clause.guard {
                            steps.push(Step::Enter(guard));
                        }
                        steps.push(Step::Pattern(clause.pattern));
                    }
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
            Step::Pattern(pattern) => patterns.push(pad_pattern(pattern, max)),
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
                guards,
            } => {
                let subject = done.pop().expect("when subject");
                let parts = guards.iter().map(|g| usize::from(*g) + 1).sum();
                let mut parts = take(&mut done, parts).into_iter();
                let padded = patterns.split_off(patterns.len() - guards.len());
                let clauses = padded
                    .into_iter()
                    .zip(guards)
                    .map(|(pattern, has_guard)| {
                        let guard = has_guard.then(|| parts.next().expect("when guard"));
                        let body = parts.next().expect("when clause body");
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
            Step::Plain(kind) => {
                let rebuilt = rebuild_plain(kind, &mut done);
                done.push(rebuilt);
            }
        }
    }
    done.pop().expect("one result")
}

fn pad_pattern(pattern: WhenPattern, max: &HashMap<(TypeHintId, usize), usize>) -> WhenPattern {
    if let WhenPattern::Constructor {
        type_hint: Some(hint),
        tag,
        mut fields,
        shape,
    } = pattern
    {
        if let ConstructorShape::Unknown { tag: shape_tag, .. } = shape
            && let Some(&target) = max.get(&(hint.clone(), tag))
            && fields.len() < target
        {
            while fields.len() < target {
                fields.push(Binder::new("_", VarId::fresh_binding()));
            }
            return WhenPattern::Constructor {
                type_hint: Some(hint),
                tag,
                shape: ConstructorShape::unknown_data(shape_tag, fields.len()),
                fields,
            };
        }
        return WhenPattern::Constructor {
            type_hint: Some(hint),
            tag,
            fields,
            shape,
        };
    }
    pattern
}
