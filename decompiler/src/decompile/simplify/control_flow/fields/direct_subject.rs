use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::builtins::BuiltinId;
use crate::decompile::simplify::Simplifier;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::type_hint::TypeHintId;
use crate::pseudo::var_id::VarId;

impl Simplifier {
    pub(in crate::decompile::simplify::control_flow) fn direct_subject_fields_matches(
        expr: &PseudoExpr,
        subject_name: &str,
        subject_id: Option<VarId>,
    ) -> bool {
        matches!(
            expr,
            PseudoExpr::FieldAccess { record, selector, .. }
                if selector.as_pretty_name() == "fields"
                    && matches!(
                        record.as_ref(),
                        PseudoExpr::Var { name, id, .. }
                            if Self::var_matches_direct_subject(name, *id, subject_name, subject_id)
                    )
        )
    }

    pub(in crate::decompile::simplify::control_flow) fn var_matches_direct_subject(
        name: &str,
        id: Option<VarId>,
        subject_name: &str,
        subject_id: Option<VarId>,
    ) -> bool {
        crate::decompile::var_match::ref_matches_resolved_target(name, id, subject_name, subject_id)
    }

    pub(in crate::decompile::simplify::control_flow) fn binder_shadows_direct_subject(
        binder: &Binder,
        subject_name: &str,
        subject_id: Option<VarId>,
    ) -> bool {
        crate::decompile::var_match::ref_matches_resolved_target(
            binder.as_str(),
            binder.id.get(),
            subject_name,
            subject_id,
        )
    }

    pub(in crate::decompile::simplify::control_flow) fn let_shadows_direct_subject(
        name: &str,
        id: Option<VarId>,
        subject_name: &str,
        subject_id: Option<VarId>,
    ) -> bool {
        crate::decompile::var_match::ref_matches_resolved_target(name, id, subject_name, subject_id)
    }

    pub(in crate::decompile::simplify::control_flow) fn pattern_shadows_direct_subject(
        pattern: &WhenPattern,
        subject_name: &str,
        subject_id: Option<VarId>,
    ) -> bool {
        match pattern {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => fields
                .iter()
                .any(|field| Self::binder_shadows_direct_subject(field, subject_name, subject_id)),
            WhenPattern::List { elements, tail } => {
                elements.iter().any(|element| {
                    Self::binder_shadows_direct_subject(element, subject_name, subject_id)
                }) || tail.as_ref().is_some_and(|tail| {
                    Self::binder_shadows_direct_subject(tail, subject_name, subject_id)
                })
            }
            WhenPattern::Pair(first, second) => {
                Self::binder_shadows_direct_subject(first, subject_name, subject_id)
                    || Self::binder_shadows_direct_subject(second, subject_name, subject_id)
            }
            WhenPattern::Var(name) => {
                Self::binder_shadows_direct_subject(name, subject_name, subject_id)
            }
            WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
        }
    }

    pub(in crate::decompile::simplify::control_flow) fn direct_subject_fields_index_access_matches(
        expr: &PseudoExpr,
        subject_name: &str,
        subject_id: Option<VarId>,
    ) -> bool {
        matches!(
            expr,
            PseudoExpr::IndexAccess { collection, .. }
                if Self::direct_subject_fields_matches(collection, subject_name, subject_id)
        )
    }

    pub(in crate::decompile::simplify::control_flow) fn collect_direct_subject_fields_index_access_counts(
        expr: &PseudoExpr,
        subject_name: &str,
        subject_id: Option<VarId>,
    ) -> HashMap<usize, usize> {
        let mut counts = HashMap::new();
        let mut stack = vec![(expr, false)];

        while let Some((current, shadowed)) = stack.pop() {
            if !shadowed
                && let PseudoExpr::IndexAccess { index, .. } = current
                && Self::direct_subject_fields_index_access_matches(
                    current,
                    subject_name,
                    subject_id,
                )
            {
                *counts.entry(*index).or_default() += 1;
            }

            match current {
                PseudoExpr::Lambda { params, body } => {
                    let shadows_subject = params.iter().any(|param| {
                        Self::binder_shadows_direct_subject(param, subject_name, subject_id)
                    });
                    stack.push((body, shadowed || shadows_subject));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let shadows_subject =
                        Self::binder_shadows_direct_subject(name, subject_name, subject_id)
                            || params.iter().any(|param| {
                                Self::binder_shadows_direct_subject(param, subject_name, subject_id)
                            });
                    stack.push((body, shadowed || shadows_subject));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    stack.push((
                        body,
                        shadowed
                            || Self::let_shadows_direct_subject(
                                name,
                                *id,
                                subject_name,
                                subject_id,
                            ),
                    ));
                    stack.push((value, shadowed));
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        stack.push((arg, shadowed));
                    }
                    stack.push((function, shadowed));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    stack.push((else_branch, shadowed));
                    stack.push((then_branch, shadowed));
                    stack.push((condition, shadowed));
                }
                PseudoExpr::When {
                    subject,
                    subject_name: when_subject_name,
                    clauses,
                } => {
                    let when_subject_shadows = when_subject_name.as_ref().is_some_and(|name| {
                        Self::binder_shadows_direct_subject(name, subject_name, subject_id)
                    });
                    for clause in clauses.iter().rev() {
                        let clause_shadowed = shadowed
                            || when_subject_shadows
                            || Self::pattern_shadows_direct_subject(
                                &clause.pattern,
                                subject_name,
                                subject_id,
                            );
                        stack.push((&clause.body, clause_shadowed));
                        if let Some(guard) = &clause.guard {
                            stack.push((guard, clause_shadowed));
                        }
                    }
                    stack.push((subject, shadowed));
                }
                PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                    stack.push((right, shadowed));
                    stack.push((left, shadowed));
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
                    stack.push((operand, shadowed));
                }
                PseudoExpr::BuiltinCall { args, .. } | PseudoExpr::Constr { fields: args, .. } => {
                    for arg in args.iter().rev() {
                        stack.push((arg, shadowed));
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    stack.push((value, shadowed));
                    stack.push((message, shadowed));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        stack.push((tail, shadowed));
                    }
                    for element in elements.iter().rev() {
                        stack.push((element, shadowed));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for item in items.iter().rev() {
                        stack.push((item, shadowed));
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

        counts
    }

    /// Rewrite every unshadowed `subject.fields[target_index]` into a
    /// reference to `replacement_name`, top-down.
    pub(in crate::decompile::simplify::control_flow) fn replace_direct_subject_fields_index_access(
        expr: PseudoExpr,
        subject_name: &str,
        subject_id: Option<VarId>,
        target_index: usize,
        replacement_name: &str,
        replacement_id: VarId,
    ) -> PseudoExpr {
        /// Take the last `n` results: this node's children, in source order.
        fn take(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
            let at = done.len() - n;
            done.split_off(at)
        }

        let mut steps: Vec<ReplaceStep> = vec![ReplaceStep::Visit(expr, false)];
        let mut done: Vec<PseudoExpr> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                // Children are pushed in REVERSE so they pop — and so land on
                // `done` — in source order.
                ReplaceStep::Visit(expr, shadowed) => {
                    if !shadowed
                        && let PseudoExpr::IndexAccess { index, .. } = &expr
                        && *index == target_index
                        && Self::direct_subject_fields_index_access_matches(
                            &expr,
                            subject_name,
                            subject_id,
                        )
                    {
                        done.push(PseudoExpr::Var {
                            name: replacement_name.to_string(),
                            id: Some(replacement_id),
                        });
                        continue;
                    }

                    match expr {
                        PseudoExpr::Lambda { params, body } => {
                            let shadows_subject = params.iter().any(|param| {
                                Self::binder_shadows_direct_subject(param, subject_name, subject_id)
                            });
                            let shadowed = shadowed || shadows_subject;
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::Lambda { params }));
                            steps.push(ReplaceStep::Visit(body.into_inner(), shadowed));
                        }
                        PseudoExpr::RecFn { name, params, body } => {
                            let shadows_subject = Self::binder_shadows_direct_subject(
                                &name,
                                subject_name,
                                subject_id,
                            ) || params.iter().any(|param| {
                                Self::binder_shadows_direct_subject(param, subject_name, subject_id)
                            });
                            let shadowed = shadowed || shadows_subject;
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::RecFn { name, params }));
                            steps.push(ReplaceStep::Visit(body.into_inner(), shadowed));
                        }
                        PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body,
                        } => {
                            // The binding shadows the subject for the BODY only;
                            // the value is still walked under the outer flag.
                            let body_shadowed = shadowed
                                || Self::let_shadows_direct_subject(
                                    &name,
                                    id,
                                    subject_name,
                                    subject_id,
                                );
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::Let { name, id }));
                            steps.push(ReplaceStep::Visit(body.into_inner(), body_shadowed));
                            steps.push(ReplaceStep::Visit(value.into_inner(), shadowed));
                        }
                        PseudoExpr::Apply { function, args } => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::Apply {
                                argc: args.len(),
                            }));
                            for arg in args.into_iter().rev() {
                                steps.push(ReplaceStep::Visit(arg, shadowed));
                            }
                            steps.push(ReplaceStep::Visit(function.into_inner(), shadowed));
                        }
                        PseudoExpr::If {
                            condition,
                            then_branch,
                            else_branch,
                        } => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::If));
                            steps.push(ReplaceStep::Visit(else_branch.into_inner(), shadowed));
                            steps.push(ReplaceStep::Visit(then_branch.into_inner(), shadowed));
                            steps.push(ReplaceStep::Visit(condition.into_inner(), shadowed));
                        }
                        PseudoExpr::When {
                            subject,
                            subject_name: when_subject_name,
                            clauses,
                        } => {
                            let when_subject_shadows =
                                when_subject_name.as_ref().is_some_and(|name| {
                                    Self::binder_shadows_direct_subject(
                                        name,
                                        subject_name,
                                        subject_id,
                                    )
                                });
                            // Split each clause into the pattern (never walked)
                            // and its expression positions, guard before body.
                            let mut shells: Vec<ReplaceClause> = Vec::with_capacity(clauses.len());
                            let mut clause_children: Vec<(PseudoExpr, bool)> = Vec::new();
                            for clause in clauses {
                                let clause_shadowed = shadowed
                                    || when_subject_shadows
                                    || Self::pattern_shadows_direct_subject(
                                        &clause.pattern,
                                        subject_name,
                                        subject_id,
                                    );
                                shells.push(ReplaceClause {
                                    has_guard: clause.guard.is_some(),
                                    pattern: clause.pattern,
                                });
                                if let Some(guard) = clause.guard {
                                    clause_children.push((guard, clause_shadowed));
                                }
                                clause_children.push((clause.body, clause_shadowed));
                            }
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::When {
                                subject_name: when_subject_name,
                                clauses: shells,
                            }));
                            for (child, clause_shadowed) in clause_children.into_iter().rev() {
                                steps.push(ReplaceStep::Visit(child, clause_shadowed));
                            }
                            steps.push(ReplaceStep::Visit(subject.into_inner(), shadowed));
                        }
                        PseudoExpr::List { elements, tail } => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::List {
                                count: elements.len(),
                                has_tail: tail.is_some(),
                            }));
                            if let Some(tail) = tail {
                                steps.push(ReplaceStep::Visit(tail.into_inner(), shadowed));
                            }
                            for element in elements.into_iter().rev() {
                                steps.push(ReplaceStep::Visit(element, shadowed));
                            }
                        }
                        PseudoExpr::Pair(left, right) => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::Pair));
                            steps.push(ReplaceStep::Visit(right.into_inner(), shadowed));
                            steps.push(ReplaceStep::Visit(left.into_inner(), shadowed));
                        }
                        PseudoExpr::Tuple(items) => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::Tuple {
                                count: items.len(),
                            }));
                            for item in items.into_iter().rev() {
                                steps.push(ReplaceStep::Visit(item, shadowed));
                            }
                        }
                        PseudoExpr::FieldAccess {
                            record, selector, ..
                        } => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::FieldAccess { selector }));
                            steps.push(ReplaceStep::Visit(record.into_inner(), shadowed));
                        }
                        PseudoExpr::IndexAccess { collection, index } => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::IndexAccess { index }));
                            steps.push(ReplaceStep::Visit(collection.into_inner(), shadowed));
                        }
                        PseudoExpr::BinOp { op, left, right } => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::BinOp { op }));
                            steps.push(ReplaceStep::Visit(right.into_inner(), shadowed));
                            steps.push(ReplaceStep::Visit(left.into_inner(), shadowed));
                        }
                        PseudoExpr::UnOp { op, operand } => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::UnOp { op }));
                            steps.push(ReplaceStep::Visit(operand.into_inner(), shadowed));
                        }
                        PseudoExpr::BuiltinCall { name, args } => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::BuiltinCall {
                                name,
                                argc: args.len(),
                            }));
                            for arg in args.into_iter().rev() {
                                steps.push(ReplaceStep::Visit(arg, shadowed));
                            }
                        }
                        PseudoExpr::Constr {
                            type_hint,
                            tag,
                            fields,
                            shape,
                        } => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::Constr {
                                type_hint,
                                tag,
                                count: fields.len(),
                                shape,
                            }));
                            for field in fields.into_iter().rev() {
                                steps.push(ReplaceStep::Visit(field, shadowed));
                            }
                        }
                        PseudoExpr::Delay(inner) => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::Delay));
                            steps.push(ReplaceStep::Visit(inner.into_inner(), shadowed));
                        }
                        PseudoExpr::Force(inner) => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::Force));
                            steps.push(ReplaceStep::Visit(inner.into_inner(), shadowed));
                        }
                        PseudoExpr::Trace { message, value } => {
                            steps.push(ReplaceStep::Rebuild(ReplaceNode::Trace));
                            steps.push(ReplaceStep::Visit(value.into_inner(), shadowed));
                            steps.push(ReplaceStep::Visit(message.into_inner(), shadowed));
                        }
                        other => done.push(other),
                    }
                }
                ReplaceStep::Rebuild(node) => {
                    let rebuilt = match node {
                        ReplaceNode::Lambda { params } => PseudoExpr::Lambda {
                            params,
                            body: PBox::new(done.pop().expect("lambda body")),
                        },
                        ReplaceNode::RecFn { name, params } => PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(done.pop().expect("recfn body")),
                        },
                        ReplaceNode::Let { name, id } => {
                            let new_body = done.pop().expect("let body");
                            let new_value = done.pop().expect("let value");
                            PseudoExpr::Let {
                                name,
                                id,
                                value: PBox::new(new_value),
                                body: PBox::new(new_body),
                            }
                        }
                        ReplaceNode::Apply { argc } => {
                            let args = take(&mut done, argc);
                            PseudoExpr::Apply {
                                function: PBox::new(done.pop().expect("apply function")),
                                args: args.into(),
                            }
                        }
                        ReplaceNode::If => {
                            let else_branch = done.pop().expect("if else");
                            let then_branch = done.pop().expect("if then");
                            let condition = done.pop().expect("if condition");
                            PseudoExpr::If {
                                condition: PBox::new(condition),
                                then_branch: PBox::new(then_branch),
                                else_branch: PBox::new(else_branch),
                            }
                        }
                        ReplaceNode::When {
                            subject_name: when_subject_name,
                            clauses,
                        } => {
                            let count: usize = clauses
                                .iter()
                                .map(|shell| 1 + usize::from(shell.has_guard))
                                .sum();
                            let mut parts = take(&mut done, count).into_iter();
                            let subject = done.pop().expect("when subject");
                            PseudoExpr::When {
                                subject: PBox::new(subject),
                                subject_name: when_subject_name,
                                clauses: clauses
                                    .into_iter()
                                    .map(|shell| WhenClause {
                                        pattern: shell.pattern,
                                        guard: shell
                                            .has_guard
                                            .then(|| parts.next().expect("when clause guard")),
                                        body: parts.next().expect("when clause body"),
                                    })
                                    .collect(),
                            }
                        }
                        ReplaceNode::List { count, has_tail } => {
                            let tail = if has_tail {
                                Some(PBox::new(done.pop().expect("list tail")))
                            } else {
                                None
                            };
                            PseudoExpr::List {
                                elements: (take(&mut done, count)).into(),
                                tail,
                            }
                        }
                        ReplaceNode::Pair => {
                            let right = done.pop().expect("pair second");
                            let left = done.pop().expect("pair first");
                            PseudoExpr::Pair(PBox::new(left), PBox::new(right))
                        }
                        ReplaceNode::Tuple { count } => {
                            PseudoExpr::Tuple((take(&mut done, count)).into())
                        }
                        ReplaceNode::FieldAccess { selector } => PseudoExpr::field_access_typed(
                            done.pop().expect("field access record"),
                            selector,
                        ),
                        ReplaceNode::IndexAccess { index } => PseudoExpr::IndexAccess {
                            collection: PBox::new(done.pop().expect("index access collection")),
                            index,
                        },
                        ReplaceNode::BinOp { op } => {
                            let right = done.pop().expect("binop right");
                            let left = done.pop().expect("binop left");
                            PseudoExpr::BinOp {
                                op,
                                left: PBox::new(left),
                                right: PBox::new(right),
                            }
                        }
                        ReplaceNode::UnOp { op } => PseudoExpr::UnOp {
                            op,
                            operand: PBox::new(done.pop().expect("unop operand")),
                        },
                        ReplaceNode::BuiltinCall { name, argc } => PseudoExpr::BuiltinCall {
                            name,
                            args: (take(&mut done, argc)).into(),
                        },
                        ReplaceNode::Constr {
                            type_hint,
                            tag,
                            count,
                            shape,
                        } => PseudoExpr::Constr {
                            type_hint,
                            tag,
                            fields: (take(&mut done, count)).into(),
                            shape,
                        },
                        ReplaceNode::Delay => {
                            PseudoExpr::Delay(PBox::new(done.pop().expect("delay inner")))
                        }
                        ReplaceNode::Force => {
                            PseudoExpr::Force(PBox::new(done.pop().expect("force inner")))
                        }
                        ReplaceNode::Trace => {
                            let value = done.pop().expect("trace value");
                            let message = done.pop().expect("trace message");
                            PseudoExpr::Trace {
                                message: PBox::new(message),
                                value: PBox::new(value),
                            }
                        }
                    };
                    done.push(rebuilt);
                }
            }
        }

        debug_assert_eq!(done.len(), 1, "the rewrite machine must leave one result");
        done.pop().expect("rewrite result")
    }
}

/// One pending step of [`Simplifier::replace_direct_subject_fields_index_access`].
enum ReplaceStep {
    /// Rewrite this node under `shadowed`, then queue its children.
    Visit(PseudoExpr, bool),
    /// Its children are on the result stack: reassemble the node.
    Rebuild(ReplaceNode),
}

enum ReplaceNode {
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    Let {
        name: String,
        id: Option<VarId>,
    },
    Apply {
        argc: usize,
    },
    If,
    When {
        subject_name: Option<Binder>,
        clauses: Vec<ReplaceClause>,
    },
    List {
        count: usize,
        has_tail: bool,
    },
    Pair,
    Tuple {
        count: usize,
    },
    FieldAccess {
        selector: FieldSelector,
    },
    IndexAccess {
        index: usize,
    },
    BinOp {
        op: BinaryOp,
    },
    UnOp {
        op: UnaryOp,
    },
    BuiltinCall {
        name: BuiltinId,
        argc: usize,
    },
    Constr {
        type_hint: Option<TypeHintId>,
        tag: usize,
        count: usize,
        shape: ConstructorShape,
    },
    Delay,
    Force,
    Trace,
}

struct ReplaceClause {
    pattern: WhenPattern,
    has_guard: bool,
}
