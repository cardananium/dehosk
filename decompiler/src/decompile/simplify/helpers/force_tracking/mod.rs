use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::type_hint::TypeHintId;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

use super::Simplifier;

#[derive(Clone, Copy)]
struct ForceUseTarget<'a> {
    name: &'a str,
    id: Option<VarId>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct ForceUseState {
    exact_active: bool,
    fallback_active: bool,
}

impl ForceUseState {
    fn active() -> Self {
        Self {
            exact_active: true,
            fallback_active: true,
        }
    }
}

impl Simplifier {
    fn force_ref_matches_target(
        name: &str,
        id: Option<VarId>,
        target: &ForceUseTarget<'_>,
        state: ForceUseState,
    ) -> bool {
        match (target.id, id.get()) {
            (Some(target_id), Some(candidate_id)) => {
                state.exact_active && target_id == candidate_id
            }
            _ => state.fallback_active && name == target.name,
        }
    }

    fn shadow_force_target_for_binders<'a, I>(
        index: usize,
        target: &ForceUseTarget<'_>,
        binders: I,
        states: &mut [ForceUseState],
        shadowed: &mut Vec<(usize, ForceUseState)>,
    ) where
        I: IntoIterator<Item = (&'a str, Option<VarId>)>,
    {
        let current = states[index];
        let next = Self::force_state_after_binders(target, binders, current);

        if next != current {
            shadowed.push((index, current));
            states[index] = next;
        }
    }

    fn force_state_after_binders<'a, I>(
        target: &ForceUseTarget<'_>,
        binders: I,
        state: ForceUseState,
    ) -> ForceUseState
    where
        I: IntoIterator<Item = (&'a str, Option<VarId>)>,
    {
        let mut next = state;

        for (binder_name, binder_id) in binders {
            if next.exact_active
                && crate::decompile::var_match::ids_match_strict(target.id, binder_id.get())
            {
                next.exact_active = false;
            }
            if next.fallback_active && binder_name == target.name {
                next.fallback_active = false;
            }
        }

        next
    }

    fn when_force_binders<'a>(
        subject_name: Option<&'a Binder>,
        pattern: &'a WhenPattern,
    ) -> Vec<(&'a str, Option<VarId>)> {
        fn collect_pattern_binders<'a>(
            pattern: &'a WhenPattern,
            binders: &mut Vec<(&'a str, Option<VarId>)>,
        ) {
            match pattern {
                WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                    binders.extend(fields.iter().map(|field| (field.as_str(), Some(field.id))));
                }
                WhenPattern::List { elements, tail } => {
                    binders.extend(
                        elements
                            .iter()
                            .map(|element| (element.as_str(), Some(element.id))),
                    );
                    if let Some(tail) = tail {
                        binders.push((tail.as_str(), Some(tail.id)));
                    }
                }
                WhenPattern::Pair(left, right) => {
                    binders.push((left.as_str(), Some(left.id)));
                    binders.push((right.as_str(), Some(right.id)));
                }
                WhenPattern::Var(binder) => {
                    binders.push((binder.as_str(), Some(binder.id)));
                }
                WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
            }
        }

        let mut binders = Vec::new();
        if let Some(subject_name) = subject_name {
            binders.push((subject_name.as_str(), Some(subject_name.id)));
        }
        collect_pattern_binders(pattern, &mut binders);
        binders
    }

    /// Count occurrences of `Force(Var(param_name))` in an expression.
    /// Respects shadowing by Lambda/Let/RecFn params.
    pub(crate) fn count_force_of_var(expr: &PseudoExpr, param: &str) -> usize {
        let mut total = 0usize;
        let mut stack: Vec<&PseudoExpr> = vec![expr];
        while let Some(expr) = stack.pop() {
            match expr {
                PseudoExpr::Force(inner) => {
                    if matches!(inner.as_ref(), PseudoExpr::Var { name, .. } if name == param) {
                        total += 1;
                    } else {
                        stack.push(inner);
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    if !params.iter().any(|p| p == param) {
                        stack.push(body);
                    }
                }
                PseudoExpr::Let {
                    name, value, body, ..
                } => {
                    stack.push(value);
                    if name != param {
                        stack.push(body);
                    }
                }
                PseudoExpr::RecFn { name, params, body } => {
                    if name != param && !params.iter().any(|p| p == param) {
                        stack.push(body);
                    }
                }
                PseudoExpr::Apply { function, args } => {
                    stack.push(function);
                    stack.extend(args.iter());
                }
                PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                    stack.push(left);
                    stack.push(right);
                }
                PseudoExpr::UnOp { operand, .. }
                | PseudoExpr::FieldAccess {
                    record: operand, ..
                }
                | PseudoExpr::IndexAccess {
                    collection: operand,
                    ..
                }
                | PseudoExpr::Delay(operand) => {
                    stack.push(operand);
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.push(condition);
                    stack.push(then_branch);
                    stack.push(else_branch);
                }
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    stack.push(subject);
                    for c in clauses {
                        stack.push(&c.body);
                        if let Some(guard) = &c.guard {
                            stack.push(guard);
                        }
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    stack.push(message);
                    stack.push(value);
                }
                PseudoExpr::Constr { fields, .. }
                | PseudoExpr::BuiltinCall { args: fields, .. } => {
                    stack.extend(fields.iter());
                }
                PseudoExpr::List { elements, tail } => {
                    stack.extend(elements.iter());
                    if let Some(t) = tail {
                        stack.push(t);
                    }
                }
                PseudoExpr::Tuple(elements) => {
                    stack.extend(elements.iter());
                }
                _ => {}
            }
        }
        total
    }

    /// One pending step of the shadowed force-count walk.
    fn count_force_of_bindings_impl(
        expr: &PseudoExpr,
        targets: &[ForceUseTarget<'_>],
        states: &mut [ForceUseState],
        counts: &mut [usize],
    ) {
        enum Step<'e> {
            Visit(&'e PseudoExpr),
            /// A `let`: its VALUE is walked with the outer state, its body
            /// with `name` shadowed.
            EnterLetBody {
                name: &'e str,
                id: Option<VarId>,
                body: &'e PseudoExpr,
            },
            /// A `when` clause: its binders are shadowed for guard+body only.
            EnterClause {
                subject_name: Option<&'e Binder>,
                clause: &'e WhenClause,
            },
            /// Undo exactly the shadowing one scope step applied.
            Restore(Vec<(usize, ForceUseState)>),
        }

        let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(expr) => {
                    if let PseudoExpr::Force(inner) = expr
                        && let PseudoExpr::Var { name, id, .. } = inner.as_ref()
                    {
                        for (index, target) in targets.iter().enumerate() {
                            if Self::force_ref_matches_target(name, *id, target, states[index]) {
                                counts[index] += 1;
                            }
                        }
                    }

                    match expr {
                        PseudoExpr::Lambda { params, body } => {
                            let mut shadowed = Vec::new();
                            for (index, target) in targets.iter().enumerate() {
                                Self::shadow_force_target_for_binders(
                                    index,
                                    target,
                                    params.iter().map(|param| (param.as_str(), Some(param.id))),
                                    states,
                                    &mut shadowed,
                                );
                            }
                            steps.push(Step::Restore(shadowed));
                            steps.push(Step::Visit(body));
                        }
                        PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body,
                        } => {
                            steps.push(Step::EnterLetBody {
                                name,
                                id: *id,
                                body,
                            });
                            steps.push(Step::Visit(value));
                        }
                        PseudoExpr::RecFn { name, params, body } => {
                            let mut shadowed = Vec::new();
                            for (index, target) in targets.iter().enumerate() {
                                Self::shadow_force_target_for_binders(
                                    index,
                                    target,
                                    std::iter::once((name.as_str(), Some(name.id))).chain(
                                        params.iter().map(|param| (param.as_str(), Some(param.id))),
                                    ),
                                    states,
                                    &mut shadowed,
                                );
                            }
                            steps.push(Step::Restore(shadowed));
                            steps.push(Step::Visit(body));
                        }
                        PseudoExpr::Apply { function, args } => {
                            for arg in args.iter().rev() {
                                steps.push(Step::Visit(arg));
                            }
                            steps.push(Step::Visit(function));
                        }
                        PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                            steps.push(Step::Visit(right));
                            steps.push(Step::Visit(left));
                        }
                        PseudoExpr::UnOp { operand, .. }
                        | PseudoExpr::FieldAccess {
                            record: operand, ..
                        }
                        | PseudoExpr::IndexAccess {
                            collection: operand,
                            ..
                        }
                        | PseudoExpr::Delay(operand)
                        | PseudoExpr::Force(operand) => {
                            steps.push(Step::Visit(operand));
                        }
                        PseudoExpr::If {
                            condition,
                            then_branch,
                            else_branch,
                        } => {
                            steps.push(Step::Visit(else_branch));
                            steps.push(Step::Visit(then_branch));
                            steps.push(Step::Visit(condition));
                        }
                        PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses,
                        } => {
                            for clause in clauses.iter().rev() {
                                steps.push(Step::EnterClause {
                                    subject_name: subject_name.as_ref(),
                                    clause,
                                });
                            }
                            steps.push(Step::Visit(subject));
                        }
                        PseudoExpr::BuiltinCall { args, .. }
                        | PseudoExpr::Constr { fields: args, .. } => {
                            for arg in args.iter().rev() {
                                steps.push(Step::Visit(arg));
                            }
                        }
                        PseudoExpr::Trace { message, value } => {
                            steps.push(Step::Visit(value));
                            steps.push(Step::Visit(message));
                        }
                        PseudoExpr::List { elements, tail } => {
                            if let Some(tail) = tail {
                                steps.push(Step::Visit(tail));
                            }
                            for element in elements.iter().rev() {
                                steps.push(Step::Visit(element));
                            }
                        }
                        PseudoExpr::Tuple(elements) => {
                            for element in elements.iter().rev() {
                                steps.push(Step::Visit(element));
                            }
                        }
                        PseudoExpr::Var { .. }
                        | PseudoExpr::Int(_)
                        | PseudoExpr::ByteArray(_)
                        | PseudoExpr::String(_)
                        | PseudoExpr::Bool(_)
                        | PseudoExpr::Unit
                        | PseudoExpr::Error { .. }
                        | PseudoExpr::Raw { .. }
                        | PseudoExpr::Data(_)
                        | PseudoExpr::HelperSymbol(_) => {}
                    }
                }
                Step::EnterLetBody { name, id, body } => {
                    let mut shadowed = Vec::new();
                    for (index, target) in targets.iter().enumerate() {
                        Self::shadow_force_target_for_binders(
                            index,
                            target,
                            std::iter::once((name, id)),
                            states,
                            &mut shadowed,
                        );
                    }
                    steps.push(Step::Restore(shadowed));
                    steps.push(Step::Visit(body));
                }
                Step::EnterClause {
                    subject_name,
                    clause,
                } => {
                    let binders = Self::when_force_binders(subject_name, &clause.pattern);
                    let mut shadowed = Vec::new();
                    for (index, target) in targets.iter().enumerate() {
                        Self::shadow_force_target_for_binders(
                            index,
                            target,
                            binders.iter().copied(),
                            states,
                            &mut shadowed,
                        );
                    }
                    steps.push(Step::Restore(shadowed));
                    steps.push(Step::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        steps.push(Step::Visit(guard));
                    }
                }
                Step::Restore(shadowed) => {
                    for (index, state) in shadowed {
                        states[index] = state;
                    }
                }
            }
        }
    }

    pub(crate) fn count_force_of_bindings(expr: &PseudoExpr, binders: &[Binder]) -> Vec<usize> {
        let targets: Vec<_> = binders
            .iter()
            .map(|binder| ForceUseTarget {
                name: binder.as_str(),
                id: binder.id.get(),
            })
            .collect();
        let mut states = vec![ForceUseState::active(); targets.len()];
        let mut counts = vec![0; targets.len()];
        Self::count_force_of_bindings_impl(expr, &targets, &mut states, &mut counts);
        counts
    }

    pub(crate) fn replace_force_of_var_with_id(
        expr: PseudoExpr,
        param: &str,
        param_id: Option<VarId>,
        alias: &str,
        replacement_id: VarId,
    ) -> PseudoExpr {
        Self::replace_force_of_var_impl(
            expr,
            param,
            param_id,
            alias,
            replacement_id,
            ForceUseState::active(),
        )
    }

    fn emitted_force_replacement_id(
        alias: &str,
        param: &str,
        forced_var_id: Option<VarId>,
        replacement_id: VarId,
    ) -> VarId {
        if alias == param {
            forced_var_id.unwrap_or(replacement_id)
        } else {
            replacement_id
        }
    }

    /// Rewrite every in-scope `Force(<param>)` into `Var(alias)`.
    fn replace_force_of_var_impl(
        expr: PseudoExpr,
        param: &str,
        param_id: Option<VarId>,
        alias: &str,
        replacement_id: VarId,
        state: ForceUseState,
    ) -> PseudoExpr {
        enum Step {
            /// Rewrite this subtree under its own force-use state.
            Enter(PseudoExpr, ForceUseState),
            Force,
            Lambda {
                params: Vec<Binder>,
            },
            Let {
                name: String,
                id: Option<VarId>,
            },
            RecFn {
                name: Binder,
                params: Vec<Binder>,
            },
            Apply {
                argc: usize,
            },
            BinOp {
                op: BinaryOp,
            },
            UnOp {
                op: UnaryOp,
            },
            If,
            When {
                subject_name: Option<Binder>,
                clause_shapes: Vec<(WhenPattern, bool)>,
            },
            Delay,
            Trace,
            FieldAccess {
                selector: FieldSelector,
            },
            IndexAccess {
                index: usize,
            },
            Constr {
                type_hint: Option<TypeHintId>,
                tag: usize,
                shape: ConstructorShape,
                count: usize,
            },
            List {
                count: usize,
                has_tail: bool,
            },
            BuiltinCall {
                name: BuiltinId,
                argc: usize,
            },
            Pair,
            Tuple {
                count: usize,
            },
        }

        let target = ForceUseTarget {
            name: param,
            id: param_id,
        };

        let mut stack = vec![Step::Enter(expr, state)];
        let mut done: Vec<PseudoExpr> = Vec::new();

        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(expr, state) => match expr {
                    PseudoExpr::Force(inner) => {
                        if let PseudoExpr::Var { name, id, .. } = inner.as_ref()
                            && Self::force_ref_matches_target(name, *id, &target, state)
                        {
                            done.push(PseudoExpr::Var {
                                name: alias.to_string(),
                                id: Some(Self::emitted_force_replacement_id(
                                    alias,
                                    param,
                                    id.get(),
                                    replacement_id,
                                )),
                            });
                            continue;
                        }
                        stack.push(Step::Force);
                        stack.push(Step::Enter(inner.into_inner(), state));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let body_state = Self::force_state_after_binders(
                            &target,
                            params.iter().map(|param| (param.as_str(), Some(param.id))),
                            state,
                        );
                        stack.push(Step::Lambda { params });
                        stack.push(Step::Enter(body.into_inner(), body_state));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        let body_state = Self::force_state_after_binders(
                            &target,
                            std::iter::once((name.as_str(), id)),
                            state,
                        );
                        stack.push(Step::Let { name, id });
                        stack.push(Step::Enter(body.into_inner(), body_state));
                        stack.push(Step::Enter(value.into_inner(), state));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let body_state = Self::force_state_after_binders(
                            &target,
                            std::iter::once((name.as_str(), Some(name.id)))
                                .chain(params.iter().map(|param| (param.as_str(), Some(param.id)))),
                            state,
                        );
                        stack.push(Step::RecFn { name, params });
                        stack.push(Step::Enter(body.into_inner(), body_state));
                    }
                    PseudoExpr::Apply { function, args } => {
                        stack.push(Step::Apply { argc: args.len() });
                        for a in args.into_iter().rev() {
                            stack.push(Step::Enter(a, state));
                        }
                        stack.push(Step::Enter(function.into_inner(), state));
                    }
                    PseudoExpr::BinOp { op, left, right } => {
                        stack.push(Step::BinOp { op });
                        stack.push(Step::Enter(right.into_inner(), state));
                        stack.push(Step::Enter(left.into_inner(), state));
                    }
                    PseudoExpr::UnOp { op, operand } => {
                        stack.push(Step::UnOp { op });
                        stack.push(Step::Enter(operand.into_inner(), state));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        stack.push(Step::If);
                        stack.push(Step::Enter(else_branch.into_inner(), state));
                        stack.push(Step::Enter(then_branch.into_inner(), state));
                        stack.push(Step::Enter(condition.into_inner(), state));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let mut clause_shapes = Vec::with_capacity(clauses.len());
                        let mut clause_exprs = Vec::with_capacity(clauses.len());
                        for c in clauses {
                            let clause_state = {
                                let binders =
                                    Self::when_force_binders(subject_name.as_ref(), &c.pattern);
                                Self::force_state_after_binders(
                                    &target,
                                    binders.iter().copied(),
                                    state,
                                )
                            };
                            clause_shapes.push((c.pattern, c.guard.is_some()));
                            clause_exprs.push((c.guard, c.body, clause_state));
                        }
                        stack.push(Step::When {
                            subject_name,
                            clause_shapes,
                        });
                        for (guard, body, clause_state) in clause_exprs.into_iter().rev() {
                            stack.push(Step::Enter(body, clause_state));
                            if let Some(g) = guard {
                                stack.push(Step::Enter(g, clause_state));
                            }
                        }
                        stack.push(Step::Enter(subject.into_inner(), state));
                    }
                    PseudoExpr::Delay(inner) => {
                        stack.push(Step::Delay);
                        stack.push(Step::Enter(inner.into_inner(), state));
                    }
                    PseudoExpr::Trace { message, value } => {
                        stack.push(Step::Trace);
                        stack.push(Step::Enter(value.into_inner(), state));
                        stack.push(Step::Enter(message.into_inner(), state));
                    }
                    PseudoExpr::FieldAccess {
                        record, selector, ..
                    } => {
                        stack.push(Step::FieldAccess { selector });
                        stack.push(Step::Enter(record.into_inner(), state));
                    }
                    PseudoExpr::IndexAccess { collection, index } => {
                        stack.push(Step::IndexAccess { index });
                        stack.push(Step::Enter(collection.into_inner(), state));
                    }
                    PseudoExpr::Constr {
                        type_hint,
                        tag,
                        fields,
                        shape,
                    } => {
                        stack.push(Step::Constr {
                            type_hint,
                            tag,
                            shape,
                            count: fields.len(),
                        });
                        for f in fields.into_iter().rev() {
                            stack.push(Step::Enter(f, state));
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        stack.push(Step::List {
                            count: elements.len(),
                            has_tail: tail.is_some(),
                        });
                        if let Some(t) = tail {
                            stack.push(Step::Enter(t.into_inner(), state));
                        }
                        for e in elements.into_iter().rev() {
                            stack.push(Step::Enter(e, state));
                        }
                    }
                    PseudoExpr::BuiltinCall { name, args } => {
                        stack.push(Step::BuiltinCall {
                            name,
                            argc: args.len(),
                        });
                        for a in args.into_iter().rev() {
                            stack.push(Step::Enter(a, state));
                        }
                    }
                    PseudoExpr::Pair(a, b) => {
                        stack.push(Step::Pair);
                        stack.push(Step::Enter(b.into_inner(), state));
                        stack.push(Step::Enter(a.into_inner(), state));
                    }
                    PseudoExpr::Tuple(elements) => {
                        stack.push(Step::Tuple {
                            count: elements.len(),
                        });
                        for e in elements.into_iter().rev() {
                            stack.push(Step::Enter(e, state));
                        }
                    }
                    other => done.push(other),
                },
                Step::Force => {
                    let inner = done.pop().expect("force inner");
                    done.push(PseudoExpr::Force(PBox::new(inner)));
                }
                Step::Lambda { params } => {
                    let body = done.pop().expect("lambda body");
                    done.push(PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    });
                }
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
                Step::RecFn { name, params } => {
                    let body = done.pop().expect("recfn body");
                    done.push(PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(body),
                    });
                }
                Step::Apply { argc } => {
                    let args = done.split_off(done.len() - argc);
                    let function = done.pop().expect("apply function");
                    done.push(PseudoExpr::Apply {
                        function: PBox::new(function),
                        args: args.into(),
                    });
                }
                Step::BinOp { op } => {
                    let right = done.pop().expect("binop right");
                    let left = done.pop().expect("binop left");
                    done.push(PseudoExpr::BinOp {
                        op,
                        left: PBox::new(left),
                        right: PBox::new(right),
                    });
                }
                Step::UnOp { op } => {
                    let operand = done.pop().expect("unop operand");
                    done.push(PseudoExpr::UnOp {
                        op,
                        operand: PBox::new(operand),
                    });
                }
                Step::If => {
                    let else_branch = done.pop().expect("if else");
                    let then_branch = done.pop().expect("if then");
                    let condition = done.pop().expect("if condition");
                    done.push(PseudoExpr::If {
                        condition: PBox::new(condition),
                        then_branch: PBox::new(then_branch),
                        else_branch: PBox::new(else_branch),
                    });
                }
                Step::When {
                    subject_name,
                    clause_shapes,
                } => {
                    let total: usize = 1 + clause_shapes
                        .iter()
                        .map(|(_, has_guard)| if *has_guard { 2 } else { 1 })
                        .sum::<usize>();
                    let mut items = done.split_off(done.len() - total).into_iter();
                    let subject = items.next().expect("when subject");
                    let mut clauses = Vec::with_capacity(clause_shapes.len());
                    for (pattern, has_guard) in clause_shapes {
                        let guard = if has_guard {
                            Some(items.next().expect("clause guard"))
                        } else {
                            None
                        };
                        let body = items.next().expect("clause body");
                        clauses.push(WhenClause {
                            pattern,
                            guard,
                            body,
                        });
                    }
                    done.push(PseudoExpr::When {
                        subject: PBox::new(subject),
                        subject_name,
                        clauses,
                    });
                }
                Step::Delay => {
                    let inner = done.pop().expect("delay inner");
                    done.push(PseudoExpr::Delay(PBox::new(inner)));
                }
                Step::Trace => {
                    let value = done.pop().expect("trace value");
                    let message = done.pop().expect("trace message");
                    done.push(PseudoExpr::Trace {
                        message: PBox::new(message),
                        value: PBox::new(value),
                    });
                }
                Step::FieldAccess { selector } => {
                    let record = done.pop().expect("field access record");
                    done.push(PseudoExpr::field_access_typed(record, selector));
                }
                Step::IndexAccess { index } => {
                    let collection = done.pop().expect("index access collection");
                    done.push(PseudoExpr::IndexAccess {
                        collection: PBox::new(collection),
                        index,
                    });
                }
                Step::Constr {
                    type_hint,
                    tag,
                    shape,
                    count,
                } => {
                    let fields = done.split_off(done.len() - count);
                    done.push(PseudoExpr::Constr {
                        type_hint,
                        tag,
                        fields: fields.into(),
                        shape,
                    });
                }
                Step::List { count, has_tail } => {
                    let mut items = done.split_off(done.len() - (count + usize::from(has_tail)));
                    let tail = if has_tail {
                        Some(PBox::new(items.pop().expect("list tail")))
                    } else {
                        None
                    };
                    done.push(PseudoExpr::List {
                        elements: items.into(),
                        tail,
                    });
                }
                Step::BuiltinCall { name, argc } => {
                    let args = done.split_off(done.len() - argc);
                    done.push(PseudoExpr::BuiltinCall {
                        name,
                        args: args.into(),
                    });
                }
                Step::Pair => {
                    let b = done.pop().expect("pair second");
                    let a = done.pop().expect("pair first");
                    done.push(PseudoExpr::Pair(PBox::new(a), PBox::new(b)));
                }
                Step::Tuple { count } => {
                    let elements = done.split_off(done.len() - count);
                    done.push(PseudoExpr::Tuple(elements.into()));
                }
            }
        }

        done.pop().expect("replace_force_of_var root")
    }
}

#[cfg(test)]
mod tests;
