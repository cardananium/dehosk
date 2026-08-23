//! Shared scope-recursive scaffolding for render-prep passes and the ADT
//! disambiguator. [`run_with_scope_fn`] drives the two hoist passes
//! (`hoist_entry_param_chain_calls`, `hoist_pure_multi_arg_calls`) from
//! the `let decompiled = ENTRY_LAMBDA in body` envelope: entry-Lambda
//! params seed the stable set, and each nested Lambda/RecFn/When-clause
//! scope adds its binders before the per-scope closure runs.
//!
//! Also exported: identity-let alias fold (`let X = Var(Y); body` →
//! `body[X→Y]`) and the tree-walking helpers (`children`, `map_children`,
//! `substitute_var`).

use crate::pseudo::ast::PBox;
use std::collections::HashSet;
use std::rc::Rc;

use crate::builtins::BuiltinId;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::type_hint::TypeHintId;
use crate::pseudo::var_id::VarId;

/// Finds the `decompiled` let, peels its entry-Lambda chain, then runs
/// [`process_scope_recursive`] over the entry body.
///
/// `extra_stable_seeds` adds to the initial stable set (e.g. top-level helper
/// let ids).
pub(super) fn run_with_scope_fn<F>(
    expr: PseudoExpr,
    extra_stable_seeds: impl Fn(&[(String, Option<VarId>, PseudoExpr)]) -> Vec<VarId>,
    scope_fn: F,
) -> PseudoExpr
where
    F: Fn(PseudoExpr, &HashSet<VarId>) -> PseudoExpr,
{
    let (top_lets, terminal) = peel_top_lets(expr);
    let decompiled_idx = top_lets
        .iter()
        .position(|(name, _, _)| name == "decompiled");
    let Some(decompiled_idx) = decompiled_idx else {
        return reassemble_top(top_lets, terminal);
    };
    let mut top_lets = top_lets;
    let (name, id, entry_value) = top_lets.remove(decompiled_idx);

    let (entry_lambdas, entry_body, entry_param_ids) = peel_entry_lambdas(entry_value);
    if entry_param_ids.is_empty() {
        let restored = reassemble_lambdas(entry_lambdas, entry_body);
        top_lets.insert(decompiled_idx, (name, id, restored));
        return reassemble_top(top_lets, terminal);
    }

    let mut initial_stable: HashSet<VarId> = entry_param_ids;
    for vid in extra_stable_seeds(&top_lets) {
        initial_stable.insert(vid);
    }

    let processed_body = process_scope_recursive(entry_body, initial_stable, &scope_fn);

    let restored = reassemble_lambdas(entry_lambdas, processed_body);
    top_lets.insert(decompiled_idx, (name, id, restored));
    reassemble_top(top_lets, terminal)
}

/// Run `scope_fn` on `body` with `stable`, then descend into inner scopes
/// (Lambda/RecFn/When-clause bodies) and process each with the inner
/// scope's augmented stable set.
///
/// The entry point of [`descend_inner_scopes`]'s job-stack machine; the
/// "run `scope_fn` here, then descend" pair is [`ScopeStep::Scope`] inside
/// it, so a nested scope costs a job, not a stack frame.
pub(super) fn process_scope_recursive<F>(
    body: PseudoExpr,
    stable: HashSet<VarId>,
    scope_fn: &F,
) -> PseudoExpr
where
    F: Fn(PseudoExpr, &HashSet<VarId>) -> PseudoExpr,
{
    let body = scope_fn(body, &stable);
    descend_inner_scopes(body, &stable, scope_fn)
}

/// A job on [`descend_inner_scopes`]'s stack. The stable set travels WITH the node
/// (`Rc`, so a scope's augmented set is shared by its whole subtree) rather than as a
/// call argument. `Scope` and `WhenClauses` are the points run between two child walks;
/// they stay separate steps.
enum ScopeStep {
    Enter(PseudoExpr, Rc<HashSet<VarId>>),
    /// What `process_scope_recursive` did: apply `scope_fn` with this
    /// scope's stable set, THEN descend into the result. `scope_fn` mints
    /// binder ids, so it must fire here and not one child earlier or later.
    Scope(PseudoExpr, Rc<HashSet<VarId>>),
    /// Ran after the `When` subject, before the first clause: each clause
    /// extends the outer set with its pattern binders (and the subject
    /// name) before its guard/body descend.
    WhenClauses {
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
        outer: Rc<HashSet<VarId>>,
    },
    Post(ScopePost),
}

enum ScopePost {
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
        /// Per clause: its pattern (never descended into) and whether it
        /// had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

fn descend_inner_scopes<F>(
    expr: PseudoExpr,
    outer_stable: &HashSet<VarId>,
    scope_fn: &F,
) -> PseudoExpr
where
    F: Fn(PseudoExpr, &HashSet<VarId>) -> PseudoExpr,
{
    let mut steps = vec![ScopeStep::Enter(expr, Rc::new(outer_stable.clone()))];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            // `process_scope_recursive(expr, stable, scope_fn)`, unrolled.
            ScopeStep::Scope(expr, stable) => {
                let expr = scope_fn(expr, &stable);
                steps.push(ScopeStep::Enter(expr, stable));
            }
            ScopeStep::Enter(expr, stable) => match expr {
                PseudoExpr::Lambda { params, body } => {
                    let mut inner = (*stable).clone();
                    for p in &params {
                        inner.insert(p.id);
                    }
                    steps.push(ScopeStep::Post(ScopePost::Lambda { params }));
                    steps.push(ScopeStep::Scope(body.into_inner(), Rc::new(inner)));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let mut inner = (*stable).clone();
                    inner.insert(name.id);
                    for p in &params {
                        inner.insert(p.id);
                    }
                    steps.push(ScopeStep::Post(ScopePost::RecFn { name, params }));
                    steps.push(ScopeStep::Scope(body.into_inner(), Rc::new(inner)));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    steps.push(ScopeStep::WhenClauses {
                        subject_name,
                        clauses,
                        outer: Rc::clone(&stable),
                    });
                    steps.push(ScopeStep::Enter(subject.into_inner(), stable));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    let mut inner = (*stable).clone();
                    if let Some(vid) = id {
                        inner.insert(vid);
                    }
                    steps.push(ScopeStep::Post(ScopePost::Let { name, id }));
                    steps.push(ScopeStep::Enter(body.into_inner(), Rc::new(inner)));
                    steps.push(ScopeStep::Enter(value.into_inner(), stable));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(ScopeStep::Post(ScopePost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(ScopeStep::Enter(c, Rc::clone(&stable)));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            ScopeStep::WhenClauses {
                subject_name,
                clauses,
                outer,
            } => {
                let mut clause_meta = Vec::with_capacity(clauses.len());
                // Built in source order, then drained onto `steps` in
                // reverse so the jobs pop in source order.
                let mut jobs: Vec<ScopeStep> = Vec::new();
                for c in clauses {
                    let mut inner = (*outer).clone();
                    inner.extend(c.pattern.bound_ids());
                    if let Some(sub_name) = &subject_name {
                        inner.insert(sub_name.id);
                    }
                    let inner = Rc::new(inner);
                    clause_meta.push((c.pattern, c.guard.is_some()));
                    if let Some(g) = c.guard {
                        jobs.push(ScopeStep::Enter(g, Rc::clone(&inner)));
                    }
                    jobs.push(ScopeStep::Scope(c.body, inner));
                }
                steps.push(ScopeStep::Post(ScopePost::When {
                    subject_name,
                    clause_meta,
                }));
                while let Some(job) = jobs.pop() {
                    steps.push(job);
                }
            }
            ScopeStep::Post(post) => {
                let rebuilt = match post {
                    ScopePost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    ScopePost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    ScopePost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    ScopePost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = take(&mut done, total).into_iter();
                        let subject = parts.next().expect("when subject");
                        let new_clauses = clause_meta
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
                            clauses: new_clauses,
                        }
                    }
                    ScopePost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "descend_inner_scopes must leave one result");
    done.pop().expect("descend_inner_scopes result")
}

pub(super) fn peel_top_lets(
    expr: PseudoExpr,
) -> (Vec<(String, Option<VarId>, PseudoExpr)>, PseudoExpr) {
    let mut lets = Vec::new();
    let mut cur = expr;
    while let PseudoExpr::Let {
        name,
        id,
        value,
        body,
    } = cur
    {
        lets.push((name, id, value.into_inner()));
        cur = body.into_inner();
    }
    (lets, cur)
}

pub(super) fn peel_entry_lambdas(
    expr: PseudoExpr,
) -> (Vec<Vec<Binder>>, PseudoExpr, HashSet<VarId>) {
    let mut chains = Vec::new();
    let mut ids = HashSet::new();
    let mut cur = expr;
    while let PseudoExpr::Lambda { params, body } = cur {
        for p in &params {
            ids.insert(p.id);
        }
        chains.push(params);
        cur = body.into_inner();
    }
    (chains, cur, ids)
}

pub(super) fn reassemble_lambdas(lambdas: Vec<Vec<Binder>>, body: PseudoExpr) -> PseudoExpr {
    let mut cur = body;
    for params in lambdas.into_iter().rev() {
        cur = PseudoExpr::Lambda {
            params,
            body: PBox::new(cur),
        };
    }
    cur
}

pub(super) fn reassemble_top(
    top_lets: Vec<(String, Option<VarId>, PseudoExpr)>,
    terminal: PseudoExpr,
) -> PseudoExpr {
    let mut cur = terminal;
    for (name, id, value) in top_lets.into_iter().rev() {
        cur = PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(cur),
        };
    }
    cur
}

fn settle_identity_alias(mut expr: PseudoExpr) -> PseudoExpr {
    loop {
        let PseudoExpr::Let {
            id: Some(let_id),
            value,
            body,
            ..
        } = &expr
        else {
            break;
        };
        let PseudoExpr::Var {
            id: Some(target_id),
            name: target_name,
        } = value.as_ref()
        else {
            break;
        };
        let (let_id, target_id, target_name) = (*let_id, *target_id, target_name.clone());
        expr = substitute_var(body.as_ref().clone(), let_id, target_id, &target_name);
    }
    expr
}

/// One pending step of [`fold_identity_aliases`]'s explicit stack — same
/// shape/reasoning as [`ScopeStep`], but this pass has no scope of its own
/// to thread (`map_children` recurses into every child with the same rule),
/// so a step carries no environment.
enum AliasStep {
    Enter(PseudoExpr),
    Post(AliasPost),
}

enum AliasPost {
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

pub(super) fn fold_identity_aliases(expr: PseudoExpr) -> PseudoExpr {
    let mut steps = vec![AliasStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            AliasStep::Enter(expr) => {
                // Settle any alias chain rooted here before deciding how (or
                // whether) to descend into children.
                match settle_identity_alias(expr) {
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        steps.push(AliasStep::Post(AliasPost::Let { name, id }));
                        steps.push(AliasStep::Enter(body.into_inner()));
                        steps.push(AliasStep::Enter(value.into_inner()));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        steps.push(AliasStep::Post(AliasPost::Lambda { params }));
                        steps.push(AliasStep::Enter(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        steps.push(AliasStep::Post(AliasPost::RecFn { name, params }));
                        steps.push(AliasStep::Enter(body.into_inner()));
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
                        steps.push(AliasStep::Post(AliasPost::When {
                            subject_name,
                            clause_meta,
                        }));
                        for c in clause_children.into_iter().rev() {
                            steps.push(AliasStep::Enter(c));
                        }
                        steps.push(AliasStep::Enter(subject.into_inner()));
                    }
                    other => match plain_children(other) {
                        Ok((kind, children)) => {
                            steps.push(AliasStep::Post(AliasPost::Plain(kind)));
                            for c in children.into_iter().rev() {
                                steps.push(AliasStep::Enter(c));
                            }
                        }
                        Err(leaf) => done.push(leaf),
                    },
                }
            }
            AliasStep::Post(post) => {
                let rebuilt = match post {
                    AliasPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    AliasPost::Lambda { params } => {
                        let body = done.pop().expect("lambda body");
                        PseudoExpr::Lambda {
                            params,
                            body: PBox::new(body),
                        }
                    }
                    AliasPost::RecFn { name, params } => {
                        let body = done.pop().expect("recfn body");
                        PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(body),
                        }
                    }
                    AliasPost::When {
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
                    AliasPost::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "fold_identity_aliases must leave one result");
    done.pop().expect("fold_identity_aliases result")
}

/// Substitutes every `Var` bound to `from_id` with `to_id`/`to_name` — a
/// blind rename with no shadow-awareness (callers only ever pass a
/// synthetic id that can't collide with a real binder).
pub(super) fn substitute_var(
    expr: PseudoExpr,
    from_id: VarId,
    to_id: VarId,
    to_name: &str,
) -> PseudoExpr {
    struct Substitute<'a> {
        from_id: VarId,
        to_id: VarId,
        to_name: &'a str,
    }

    impl ExprFolder for Substitute<'_> {
        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            if id == Some(self.from_id) {
                PseudoExpr::Var {
                    name: self.to_name.to_string(),
                    id: Some(self.to_id),
                }
            } else {
                PseudoExpr::Var { name, id }
            }
        }

        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            pattern
        }
    }

    Substitute {
        from_id,
        to_id,
        to_name,
    }
    .fold(expr)
}

pub(super) enum PlainPost {
    Apply {
        argc: usize,
    },
    If,
    BinOp {
        op: BinaryOp,
    },
    UnOp {
        op: UnaryOp,
    },
    Constr {
        tag: usize,
        shape: ConstructorShape,
        type_hint: Option<TypeHintId>,
        count: usize,
    },
    BuiltinCall {
        name: BuiltinId,
        argc: usize,
    },
    List {
        count: usize,
        has_tail: bool,
    },
    Tuple {
        count: usize,
    },
    Pair,
    FieldAccess {
        selector: FieldSelector,
    },
    IndexAccess {
        index: usize,
    },
    Trace,
    Delay,
    Force,
}

/// Splits a "plain" node into its reassembly tag and its children in
/// source-evaluation order (the order `map_children` applies `f` in), for a
/// walk to push in reverse and later rebuild via [`rebuild_plain`]. `Err`
/// for anything not plain — the caller's own match already special-cased
/// Let/Lambda/RecFn/When, so this only needs to reject the leaves, which get
/// pushed onto `done` unchanged (matching `map_children`'s `other => other`).
pub(super) fn plain_children(expr: PseudoExpr) -> Result<(PlainPost, Vec<PseudoExpr>), PseudoExpr> {
    Ok(match expr {
        PseudoExpr::Apply { function, args } => {
            let argc = args.len();
            let mut children = vec![function.into_inner()];
            children.extend(args);
            (PlainPost::Apply { argc }, children)
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => (
            PlainPost::If,
            vec![
                condition.into_inner(),
                then_branch.into_inner(),
                else_branch.into_inner(),
            ],
        ),
        PseudoExpr::BinOp { op, left, right } => (
            PlainPost::BinOp { op },
            vec![left.into_inner(), right.into_inner()],
        ),
        PseudoExpr::UnOp { op, operand } => (PlainPost::UnOp { op }, vec![operand.into_inner()]),
        PseudoExpr::Constr {
            tag,
            shape,
            fields,
            type_hint,
        } => {
            let count = fields.len();
            (
                PlainPost::Constr {
                    tag,
                    shape,
                    type_hint,
                    count,
                },
                fields.into_vec(),
            )
        }
        PseudoExpr::BuiltinCall { name, args } => {
            let argc = args.len();
            (PlainPost::BuiltinCall { name, argc }, args.into_vec())
        }
        PseudoExpr::List { elements, tail } => {
            let count = elements.len();
            let has_tail = tail.is_some();
            let mut children = elements;
            if let Some(t) = tail {
                children.push(t.into_inner());
            }
            (PlainPost::List { count, has_tail }, children.into_vec())
        }
        PseudoExpr::Tuple(elements) => {
            let count = elements.len();
            (PlainPost::Tuple { count }, elements.into_vec())
        }
        PseudoExpr::Pair(a, b) => (PlainPost::Pair, vec![a.into_inner(), b.into_inner()]),
        PseudoExpr::FieldAccess { record, selector } => (
            PlainPost::FieldAccess { selector },
            vec![record.into_inner()],
        ),
        PseudoExpr::IndexAccess { collection, index } => (
            PlainPost::IndexAccess { index },
            vec![collection.into_inner()],
        ),
        PseudoExpr::Trace { message, value } => (
            PlainPost::Trace,
            vec![message.into_inner(), value.into_inner()],
        ),
        PseudoExpr::Delay(inner) => (PlainPost::Delay, vec![inner.into_inner()]),
        PseudoExpr::Force(inner) => (PlainPost::Force, vec![inner.into_inner()]),
        other => return Err(other),
    })
}

/// Takes the last `n` items off `done` — the children of the node currently
/// being reassembled, left there in source order by the walk.
pub(super) fn take(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
    let at = done.len() - n;
    done.split_off(at)
}

/// Rebuilds a plain node from its already-folded children on `done`,
/// mirroring `map_children`'s reconstruction for the same node kind exactly.
pub(super) fn rebuild_plain(kind: PlainPost, done: &mut Vec<PseudoExpr>) -> PseudoExpr {
    match kind {
        PlainPost::Apply { argc } => {
            let args = take(done, argc);
            let function = done.pop().expect("apply function");
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
        PlainPost::If => {
            let mut parts = take(done, 3).into_iter();
            let condition = parts.next().expect("if condition");
            let then_branch = parts.next().expect("if then");
            let else_branch = parts.next().expect("if else");
            PseudoExpr::If {
                condition: PBox::new(condition),
                then_branch: PBox::new(then_branch),
                else_branch: PBox::new(else_branch),
            }
        }
        PlainPost::BinOp { op } => {
            let right = done.pop().expect("binop right");
            let left = done.pop().expect("binop left");
            PseudoExpr::BinOp {
                op,
                left: PBox::new(left),
                right: PBox::new(right),
            }
        }
        PlainPost::UnOp { op } => {
            let operand = done.pop().expect("unop operand");
            PseudoExpr::UnOp {
                op,
                operand: PBox::new(operand),
            }
        }
        PlainPost::Constr {
            tag,
            shape,
            type_hint,
            count,
        } => {
            let fields = take(done, count);
            PseudoExpr::Constr {
                tag,
                shape,
                fields: fields.into(),
                type_hint,
            }
        }
        PlainPost::BuiltinCall { name, argc } => {
            let args = take(done, argc);
            PseudoExpr::BuiltinCall {
                name,
                args: args.into(),
            }
        }
        PlainPost::List { count, has_tail } => {
            let tail = if has_tail {
                Some(PBox::new(done.pop().expect("list tail")))
            } else {
                None
            };
            let elements = take(done, count);
            PseudoExpr::List {
                elements: elements.into(),
                tail,
            }
        }
        PlainPost::Tuple { count } => PseudoExpr::Tuple((take(done, count)).into()),
        PlainPost::Pair => {
            let second = done.pop().expect("pair second");
            let first = done.pop().expect("pair first");
            PseudoExpr::Pair(PBox::new(first), PBox::new(second))
        }
        PlainPost::FieldAccess { selector } => {
            let record = done.pop().expect("field access record");
            PseudoExpr::FieldAccess {
                record: PBox::new(record),
                selector,
            }
        }
        PlainPost::IndexAccess { index } => {
            let collection = done.pop().expect("index access collection");
            PseudoExpr::IndexAccess {
                collection: PBox::new(collection),
                index,
            }
        }
        PlainPost::Trace => {
            let value = done.pop().expect("trace value");
            let message = done.pop().expect("trace message");
            PseudoExpr::Trace {
                message: PBox::new(message),
                value: PBox::new(value),
            }
        }
        PlainPost::Delay => PseudoExpr::Delay(PBox::new(done.pop().expect("delay inner"))),
        PlainPost::Force => PseudoExpr::Force(PBox::new(done.pop().expect("force inner"))),
    }
}

pub(crate) fn children(expr: &PseudoExpr) -> Vec<&PseudoExpr> {
    let mut out = Vec::new();
    match expr {
        PseudoExpr::Let { value, body, .. } => {
            out.push(value.as_ref());
            out.push(body.as_ref());
        }
        PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
            out.push(body.as_ref());
        }
        PseudoExpr::Apply { function, args } => {
            out.push(function.as_ref());
            for a in args {
                out.push(a);
            }
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            out.push(condition.as_ref());
            out.push(then_branch.as_ref());
            out.push(else_branch.as_ref());
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            out.push(subject.as_ref());
            for c in clauses {
                if let Some(g) = &c.guard {
                    out.push(g);
                }
                out.push(&c.body);
            }
        }
        PseudoExpr::BinOp { left, right, .. } => {
            out.push(left.as_ref());
            out.push(right.as_ref());
        }
        PseudoExpr::UnOp { operand, .. } => out.push(operand.as_ref()),
        PseudoExpr::Constr { fields, .. } => {
            for f in fields {
                out.push(f);
            }
        }
        PseudoExpr::BuiltinCall { args, .. } => {
            for a in args {
                out.push(a);
            }
        }
        PseudoExpr::List { elements, tail } => {
            for e in elements {
                out.push(e);
            }
            if let Some(t) = tail {
                out.push(t.as_ref());
            }
        }
        PseudoExpr::Tuple(elements) => {
            for e in elements {
                out.push(e);
            }
        }
        PseudoExpr::Pair(a, b) => {
            out.push(a.as_ref());
            out.push(b.as_ref());
        }
        PseudoExpr::FieldAccess { record, .. } => out.push(record.as_ref()),
        PseudoExpr::IndexAccess { collection, .. } => out.push(collection.as_ref()),
        PseudoExpr::Trace { message, value } => {
            out.push(message.as_ref());
            out.push(value.as_ref());
        }
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => out.push(inner.as_ref()),
        _ => {}
    }
    out
}

/// Rebuild `expr` with `f` applied to each immediate child expression.
///
/// `FnMut`, not `Fn`: a pass that carries scope state (`let_disambiguation`)
/// or accumulates notes (`decode_church_to_native`) needs `&mut` access
/// from inside the closure, and forcing `Fn` had pushed both of those into
/// interior mutability or a hand-rolled task stack. Every `Fn` caller is
/// still accepted.
pub(crate) fn map_children<F: FnMut(PseudoExpr) -> PseudoExpr>(
    expr: PseudoExpr,
    mut f: F,
) -> PseudoExpr {
    match expr {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => PseudoExpr::Let {
            name,
            id,
            value: PBox::new(f(value.into_inner())),
            body: PBox::new(f(body.into_inner())),
        },
        PseudoExpr::Lambda { params, body } => PseudoExpr::Lambda {
            params,
            body: PBox::new(f(body.into_inner())),
        },
        PseudoExpr::RecFn { name, params, body } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(f(body.into_inner())),
        },
        PseudoExpr::Apply { function, args } => PseudoExpr::Apply {
            function: PBox::new(f(function.into_inner())),
            args: args.into_iter().map(&mut f).collect(),
        },
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => PseudoExpr::If {
            condition: PBox::new(f(condition.into_inner())),
            then_branch: PBox::new(f(then_branch.into_inner())),
            else_branch: PBox::new(f(else_branch.into_inner())),
        },
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => PseudoExpr::When {
            subject: PBox::new(f(subject.into_inner())),
            subject_name,
            clauses: clauses
                .into_iter()
                .map(|c| WhenClause {
                    pattern: c.pattern,
                    guard: c.guard.map(&mut f),
                    body: f(c.body),
                })
                .collect(),
        },
        PseudoExpr::BinOp { op, left, right } => PseudoExpr::BinOp {
            op,
            left: PBox::new(f(left.into_inner())),
            right: PBox::new(f(right.into_inner())),
        },
        PseudoExpr::UnOp { op, operand } => PseudoExpr::UnOp {
            op,
            operand: PBox::new(f(operand.into_inner())),
        },
        PseudoExpr::Constr {
            tag,
            shape,
            fields,
            type_hint,
        } => PseudoExpr::Constr {
            tag,
            shape,
            fields: fields.into_iter().map(&mut f).collect(),
            type_hint,
        },
        PseudoExpr::BuiltinCall { name, args } => PseudoExpr::BuiltinCall {
            name,
            args: args.into_iter().map(&mut f).collect(),
        },
        PseudoExpr::List { elements, tail } => PseudoExpr::List {
            elements: elements.into_iter().map(&mut f).collect(),
            tail: tail.map(|t| PBox::new(f(t.into_inner()))),
        },
        PseudoExpr::Tuple(elements) => {
            PseudoExpr::Tuple(elements.into_iter().map(&mut f).collect())
        }
        PseudoExpr::Pair(a, b) => {
            PseudoExpr::Pair(PBox::new(f(a.into_inner())), PBox::new(f(b.into_inner())))
        }
        PseudoExpr::FieldAccess { record, selector } => PseudoExpr::FieldAccess {
            record: PBox::new(f(record.into_inner())),
            selector,
        },
        PseudoExpr::IndexAccess { collection, index } => PseudoExpr::IndexAccess {
            collection: PBox::new(f(collection.into_inner())),
            index,
        },
        PseudoExpr::Trace { message, value } => PseudoExpr::Trace {
            message: PBox::new(f(message.into_inner())),
            value: PBox::new(f(value.into_inner())),
        },
        PseudoExpr::Delay(inner) => PseudoExpr::Delay(PBox::new(f(inner.into_inner()))),
        PseudoExpr::Force(inner) => PseudoExpr::Force(PBox::new(f(inner.into_inner()))),
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Shared bottom-up rewrite
//
// `map_children(expr, f)` where `f` is the walk itself is the most common
// shape in this directory, and it costs one call frame per level of nesting.
// Depth here is script-controlled, and on `wasm32` the engine's call stack
// cannot be grown from the page, so that shape caps the whole decompiler.
//
// `rewrite_bottom_up(expr, f)` is the same traversal as a job stack: children
// are rewritten first, then `f` runs on the rebuilt node.
// ---------------------------------------------------------------------------

enum BottomUpStep {
    Enter(PseudoExpr),
    Post(BottomUpKind),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum BottomUpKind {
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
        /// Per clause: its pattern (never descended into, exactly as
        /// `map_children` leaves it) and whether it had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Rebuild each node from its already-rewritten children, then hand it to
/// `f`.
pub(super) fn rewrite_bottom_up(
    expr: PseudoExpr,
    mut f: impl FnMut(PseudoExpr) -> PseudoExpr,
) -> PseudoExpr {
    let mut steps: Vec<BottomUpStep> = vec![BottomUpStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            BottomUpStep::Enter(expr) => match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(BottomUpStep::Post(BottomUpKind::Let { name, id }));
                    steps.push(BottomUpStep::Enter(body.into_inner()));
                    steps.push(BottomUpStep::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(BottomUpStep::Post(BottomUpKind::Lambda { params }));
                    steps.push(BottomUpStep::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(BottomUpStep::Post(BottomUpKind::RecFn { name, params }));
                    steps.push(BottomUpStep::Enter(body.into_inner()));
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
                    steps.push(BottomUpStep::Post(BottomUpKind::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(BottomUpStep::Enter(c));
                    }
                    steps.push(BottomUpStep::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(BottomUpStep::Post(BottomUpKind::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(BottomUpStep::Enter(c));
                        }
                    }
                    // `map_children` returns a leaf unchanged, and the
                    // node's own logic still ran on it.
                    Err(leaf) => done.push(f(leaf)),
                },
            },
            BottomUpStep::Post(post) => {
                let rebuilt = match post {
                    BottomUpKind::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    BottomUpKind::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    BottomUpKind::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    BottomUpKind::When {
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
                    BottomUpKind::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(f(rebuilt));
            }
        }
    }

    done.pop()
        .expect("rewrite_bottom_up leaves exactly one result")
}

/// Top-down rewrite with pruning: `f` runs on a node *before* its children,
/// and returning `Some` replaces the subtree without descending into it.
///
/// Same constraint as [`rewrite_bottom_up`]: script-controlled depth on a
/// `wasm32` engine stack that cannot grow.
pub(super) fn rewrite_top_down_pruning(
    expr: PseudoExpr,
    mut f: impl FnMut(&PseudoExpr) -> Option<PseudoExpr>,
) -> PseudoExpr {
    let mut steps: Vec<BottomUpStep> = vec![BottomUpStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            BottomUpStep::Enter(expr) => {
                // A hit replaces the subtree, so it is never descended into.
                if let Some(replacement) = f(&expr) {
                    done.push(replacement);
                    continue;
                }
                match expr {
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        steps.push(BottomUpStep::Post(BottomUpKind::Let { name, id }));
                        steps.push(BottomUpStep::Enter(body.into_inner()));
                        steps.push(BottomUpStep::Enter(value.into_inner()));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        steps.push(BottomUpStep::Post(BottomUpKind::Lambda { params }));
                        steps.push(BottomUpStep::Enter(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        steps.push(BottomUpStep::Post(BottomUpKind::RecFn { name, params }));
                        steps.push(BottomUpStep::Enter(body.into_inner()));
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
                        steps.push(BottomUpStep::Post(BottomUpKind::When {
                            subject_name,
                            clause_meta,
                        }));
                        for c in clause_children.into_iter().rev() {
                            steps.push(BottomUpStep::Enter(c));
                        }
                        steps.push(BottomUpStep::Enter(subject.into_inner()));
                    }
                    other => match plain_children(other) {
                        Ok((kind, children)) => {
                            steps.push(BottomUpStep::Post(BottomUpKind::Plain(kind)));
                            for c in children.into_iter().rev() {
                                steps.push(BottomUpStep::Enter(c));
                            }
                        }
                        // `map_children` returns a leaf unchanged, and the
                        // node's own logic still ran on it.
                        Err(leaf) => done.push(leaf),
                    },
                }
            }
            BottomUpStep::Post(post) => {
                let rebuilt = match post {
                    BottomUpKind::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    BottomUpKind::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    BottomUpKind::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    BottomUpKind::When {
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
                    BottomUpKind::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    done.pop()
        .expect("rewrite_bottom_up leaves exactly one result")
}
