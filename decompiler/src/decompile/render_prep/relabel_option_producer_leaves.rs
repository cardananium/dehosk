//! Witness-gated producer-side completion of the option-like recovery.
//!
//! Option machinery names consumers from a producer's raw `Constr<0>(x)` /
//! `Constr<1>` leaves (`option_cps` synthesizes `when helper(…) is {
//! Some(p); None }`) but never relabels the producer. For every fn binder
//! whose result is witnessed as Option — some `when`/`expect` matches a
//! call of it against a native `Known(Some)`/`Known(None)` pattern —
//! relabel the raw Option-shaped return leaves: `Constr { tag: 0, fields:
//! [x], shape: Unknown }` → `Some(x)`; `Constr { tag: 1, fields: [],
//! shape: Unknown }` → `None`; a leaf `Var` whose unique binding is a raw
//! `Constr<1>` nullary (the CSE-hoisted `const d` alias) → `None` at the
//! occurrence only — the const itself and its other (church-bool) use
//! sites are not. Tag-faithful by the standard Plutus convention (`Some =
//! Constr 0 [x]`, `None = Constr 1 []` — `constructor/mod.rs`), matching
//! the consumer naming so the two sides cannot diverge.
//!
//! The witness is required: a fn with Option-shaped leaves but no native
//! Option consumer is never touched, so a genuine `Data` sum that shares
//! the shape stays raw. Fn identity and the alias hop are VarId-keyed;
//! only ids bound exactly once program-wide participate (collision → skip).
//! Leaves are reached through If / When tails / Let bodies / Trace values,
//! descending into leaf-position `Lambda`/`RecFn` bodies (curried producers
//! return that closure). Non-Option leaves stay — partial relabel is sound,
//! each replacement individually tag-faithful. Idempotent: relabeled leaves
//! are `Known` shapes the rewrite no longer matches; the `Var` hop fires
//! only while the alias leaf is still a `Var`. Runs after
//! `unfold_y_comb_helper_apply`, so half-Z-seated producers have already
//! unfolded into direct `rec fn` bodies whose leaves are visible.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn relabel_option_producer_leaves(expr: PseudoExpr) -> PseudoExpr {
    if !super::drop_dead_pure_lets::contains_decompiled_marker(&expr) {
        return expr;
    }
    let bindings = collect_unique_bindings(&expr);
    let witnessed = collect_option_witnessed_fns(&expr, &bindings);
    if witnessed.is_empty() {
        return expr;
    }
    let none_aliases: HashSet<VarId> = bindings
        .iter()
        .filter(|(_, value)| is_raw_none(value))
        .map(|(id, _)| *id)
        .collect();
    rewrite(expr, &witnessed, &none_aliases)
}

fn is_raw_none(e: &PseudoExpr) -> bool {
    matches!(
        e,
        PseudoExpr::Constr {
            tag: 1,
            fields,
            shape: ConstructorShape::Unknown { .. },
            ..
        } if fields.is_empty()
    )
}

fn is_raw_some(e: &PseudoExpr) -> bool {
    matches!(
        e,
        PseudoExpr::Constr {
            tag: 0,
            fields,
            shape: ConstructorShape::Unknown { .. },
            ..
        } if fields.len() == 1
    )
}

/// Every `Let` binder id bound exactly once program-wide, mapped to its
/// value. Multiply-bound ids (VarId collisions) are dropped entirely.
fn collect_unique_bindings(expr: &PseudoExpr) -> HashMap<VarId, PseudoExpr> {
    struct Scan {
        values: HashMap<VarId, PseudoExpr>,
        counts: HashMap<VarId, usize>,
    }
    impl ExprVisitor for Scan {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, value: &PseudoExpr) {
            if let Some(vid) = id {
                *self.counts.entry(*vid).or_insert(0) += 1;
                self.values.insert(*vid, value.clone());
            }
        }
        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for p in params {
                *self.counts.entry(p.var_id()).or_insert(0) += 1;
            }
        }
        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            *self.counts.entry(name.var_id()).or_insert(0) += 1;
            for p in params {
                *self.counts.entry(p.var_id()).or_insert(0) += 1;
            }
        }
        fn visit_when_clause_pre(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            if let Some(b) = subject_name {
                *self.counts.entry(b.var_id()).or_insert(0) += 1;
            }
            for id in clause.pattern.bound_ids() {
                *self.counts.entry(id).or_insert(0) += 1;
            }
        }
    }
    let mut scan = Scan {
        values: HashMap::new(),
        counts: HashMap::new(),
    };
    scan.walk(expr);
    scan.values
        .into_iter()
        .filter(|(id, _)| scan.counts.get(id) == Some(&1))
        .collect()
}

/// Fn binder ids whose CALL RESULT is matched somewhere against a
/// native `Known(Some)`/`Known(None)` pattern. The subject's Apply
/// spine is peeled to its head `Var` (curried producers are called
/// with extra args).
fn collect_option_witnessed_fns(
    expr: &PseudoExpr,
    bindings: &HashMap<VarId, PseudoExpr>,
) -> HashSet<VarId> {
    // Peel curried `Apply` layers. Only one child (`function`) is descended
    // into, so this is a pointer loop.
    fn apply_head_var(expr: &PseudoExpr) -> Option<VarId> {
        let mut current = expr;
        loop {
            match current {
                PseudoExpr::Apply { function, .. } => match function.as_ref() {
                    PseudoExpr::Var { id: Some(vid), .. } => return Some(*vid),
                    inner @ PseudoExpr::Apply { .. } => current = inner,
                    _ => return None,
                },
                _ => return None,
            }
        }
    }
    struct Scan<'a> {
        bindings: &'a HashMap<VarId, PseudoExpr>,
        witnessed: HashSet<VarId>,
        current_subject_head: Vec<Option<VarId>>,
    }
    impl ExprVisitor for Scan<'_> {
        fn visit_when_clause_pre(&mut self, _subject_name: Option<&Binder>, clause: &WhenClause) {
            let Some(Some(head)) = self.current_subject_head.last() else {
                return;
            };
            let native_option_pattern = matches!(
                &clause.pattern,
                crate::pseudo::ast::WhenPattern::Constructor {
                    shape: ConstructorShape::Known(KnownConstructor::Some | KnownConstructor::None),
                    ..
                }
            );
            if native_option_pattern {
                self.witnessed.insert(*head);
            }
        }
    }
    // `ExprVisitor` has no subject hook carrying the clause context, so
    // recurse manually, tracking the subject head at each `When`.
    fn walk(expr: &PseudoExpr, scan: &mut Scan<'_>) {
        let mut pending = vec![expr];
        while let Some(cur) = pending.pop() {
            if let PseudoExpr::When {
                subject, clauses, ..
            } = cur
            {
                let head = apply_head_var(subject).filter(|h| scan.bindings.contains_key(h));
                scan.current_subject_head.push(head);
                for clause in clauses {
                    scan.visit_when_clause_pre(None, clause);
                }
                scan.current_subject_head.pop();
            }
            for child in super::scope_recurse::children(cur).into_iter().rev() {
                pending.push(child);
            }
        }
    }
    let mut scan = Scan {
        bindings,
        witnessed: HashSet::new(),
        current_subject_head: Vec::new(),
    };
    walk(expr, &mut scan);
    scan.witnessed
}

/// Rewrite pass: at each `let F = <fn>` where `F` is a witnessed Option
/// producer, relabel that fn value's RETURN LEAVES before descending.
///
/// The `Let` value's leaf relabel runs on the `Visit` arm, before descending
/// into the two children.
fn rewrite(
    expr: PseudoExpr,
    witnessed: &HashSet<VarId>,
    none_aliases: &HashSet<VarId>,
) -> PseudoExpr {
    let mut steps: Vec<RwStep> = vec![RwStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RwStep::Visit(expr) => match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    let value = if id.is_some_and(|vid| witnessed.contains(&vid)) {
                        relabel_leaves(value.into_inner(), none_aliases)
                    } else {
                        value.into_inner()
                    };
                    steps.push(RwStep::Post(RwPost::Let { name, id }));
                    steps.push(RwStep::Visit(body.into_inner()));
                    steps.push(RwStep::Visit(value));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(RwStep::Post(RwPost::Lambda { params }));
                    steps.push(RwStep::Visit(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(RwStep::Post(RwPost::RecFn { name, params }));
                    steps.push(RwStep::Visit(body.into_inner()));
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
                    steps.push(RwStep::Post(RwPost::When {
                        subject_name,
                        clause_meta,
                    }));
                    // Reversed so they pop in source order.
                    for c in clause_children.into_iter().rev() {
                        steps.push(RwStep::Visit(c));
                    }
                    steps.push(RwStep::Visit(subject.into_inner()));
                }
                // `map_children`'s remaining (non-binding) variants.
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RwStep::Post(RwPost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(RwStep::Visit(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            RwStep::Post(post) => {
                let rebuilt = match post {
                    RwPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    RwPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    RwPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    RwPost::When {
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
                    RwPost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

/// A job on [`rewrite`]'s stack.
enum RwStep {
    Visit(PseudoExpr),
    Post(RwPost),
}

enum RwPost {
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
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Relabel the Option-shaped RETURN LEAVES of a witnessed fn value.
///
/// Only LEAF positions are descended into, so each `Post` variant carries the
/// non-leaf parts of its node (a `let` value, an `if` condition, a `when`
/// subject and its clause guards, a `trace` message) verbatim rather than
/// rebuilding them from `done`.
fn relabel_leaves(expr: PseudoExpr, none_aliases: &HashSet<VarId>) -> PseudoExpr {
    let mut steps: Vec<LeafStep> = vec![LeafStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            LeafStep::Visit(expr) => match expr {
                e if is_raw_some(&e) => {
                    let PseudoExpr::Constr { fields, .. } = e else {
                        unreachable!("shape checked");
                    };
                    done.push(PseudoExpr::constr_known(
                        KnownConstructor::Some,
                        fields.into_vec(),
                    ))
                }
                e if is_raw_none(&e) => {
                    done.push(PseudoExpr::constr_known(KnownConstructor::None, Vec::new()))
                }
                PseudoExpr::Var { name, id } => {
                    if id.is_some_and(|vid| none_aliases.contains(&vid)) {
                        done.push(PseudoExpr::constr_known(KnownConstructor::None, Vec::new()))
                    } else {
                        done.push(PseudoExpr::Var { name, id })
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(LeafStep::Post(LeafPost::Lambda { params }));
                    steps.push(LeafStep::Visit(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(LeafStep::Post(LeafPost::RecFn { name, params }));
                    steps.push(LeafStep::Visit(body.into_inner()));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(LeafStep::Post(LeafPost::Let { name, id, value }));
                    steps.push(LeafStep::Visit(body.into_inner()));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(LeafStep::Post(LeafPost::If { condition }));
                    // Reversed so they pop in source order.
                    steps.push(LeafStep::Visit(else_branch.into_inner()));
                    steps.push(LeafStep::Visit(then_branch.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut bodies = Vec::with_capacity(clauses.len());
                    for c in clauses {
                        clause_meta.push((c.pattern, c.guard));
                        bodies.push(c.body);
                    }
                    steps.push(LeafStep::Post(LeafPost::When {
                        subject,
                        subject_name,
                        clause_meta,
                    }));
                    for b in bodies.into_iter().rev() {
                        steps.push(LeafStep::Visit(b));
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(LeafStep::Post(LeafPost::Trace { message }));
                    steps.push(LeafStep::Visit(value.into_inner()));
                }
                other => done.push(other),
            },
            LeafStep::Post(post) => {
                let rebuilt = match post {
                    LeafPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    LeafPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    LeafPost::Let { name, id, value } => PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body: PBox::new(done.pop().expect("let body")),
                    },
                    LeafPost::If { condition } => {
                        let else_branch = done.pop().expect("if else");
                        let then_branch = done.pop().expect("if then");
                        PseudoExpr::If {
                            condition,
                            then_branch: PBox::new(then_branch),
                            else_branch: PBox::new(else_branch),
                        }
                    }
                    LeafPost::When {
                        subject,
                        subject_name,
                        clause_meta,
                    } => {
                        let mut parts = take(&mut done, clause_meta.len()).into_iter();
                        PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses: clause_meta
                                .into_iter()
                                .map(|(pattern, guard)| WhenClause {
                                    pattern,
                                    guard,
                                    body: parts.next().expect("when clause body"),
                                })
                                .collect(),
                        }
                    }
                    LeafPost::Trace { message } => PseudoExpr::Trace {
                        message,
                        value: PBox::new(done.pop().expect("trace value")),
                    },
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "relabel_leaves must leave one result");
    done.pop().expect("relabel_leaves result")
}

/// A job on [`relabel_leaves`]'s stack.
enum LeafStep {
    Visit(PseudoExpr),
    Post(LeafPost),
}

enum LeafPost {
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    /// The `let` VALUE is not a leaf position — carried through untouched.
    Let {
        name: String,
        id: Option<VarId>,
        value: PBox,
    },
    /// Same for an `if` CONDITION.
    If {
        condition: PBox,
    },
    /// Same for a `when` SUBJECT and each clause GUARD.
    When {
        subject: PBox,
        subject_name: Option<Binder>,
        clause_meta: Vec<(WhenPattern, Option<PseudoExpr>)>,
    },
    /// Same for a `trace` MESSAGE.
    Trace {
        message: PBox,
    },
}

#[cfg(test)]
mod tests;
