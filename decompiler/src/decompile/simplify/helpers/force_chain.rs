use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::type_hint::TypeHintId;
use crate::pseudo::var_id::VarId;

use super::Simplifier;

impl Simplifier {
    pub(crate) fn replace_forced_var(
        &mut self,
        expr: PseudoExpr,
        var_name: &str,
        var_id: Option<VarId>,
        replacement: &PseudoExpr,
        force_depth: u8,
    ) -> PseudoExpr {
        fn matches_force_chain(
            expr: &PseudoExpr,
            var_name: &str,
            var_id: Option<VarId>,
            depth: u8,
        ) -> bool {
            let mut current = expr;
            let mut depth = depth;
            while depth > 0 {
                let PseudoExpr::Force(inner) = current else {
                    return false;
                };
                current = inner;
                depth -= 1;
            }
            matches!(
                current,
                PseudoExpr::Var { name, id, .. }
                    if Simplifier::ref_matches_var_id(name, *id, var_name, var_id)
            )
        }

        fn go(
            expr: PseudoExpr,
            var_name: &str,
            var_id: Option<VarId>,
            replacement: &PseudoExpr,
            force_depth: u8,
            shadowed: bool,
            counter: &mut u32,
        ) -> PseudoExpr {
            enum Step {
                Enter(PseudoExpr, bool),
                Lambda {
                    params: Vec<Binder>,
                },
                RecFn {
                    name: Binder,
                    params: Vec<Binder>,
                },
                Apply {
                    argc: usize,
                },
                Let {
                    name: String,
                    id: Option<VarId>,
                },
                If,
                When {
                    subject_name: Option<Binder>,
                    /// Per clause: its untouched pattern, and whether a
                    /// guard result sits in front of the body result.
                    clauses: Vec<(WhenPattern, bool)>,
                },
                BinOp {
                    op: BinaryOp,
                },
                UnOp {
                    op: UnaryOp,
                },
                List {
                    count: usize,
                    has_tail: bool,
                },
                Pair,
                Tuple {
                    count: usize,
                },
                BuiltinCall {
                    name: BuiltinId,
                    argc: usize,
                },
                Constr {
                    type_hint: Option<TypeHintId>,
                    tag: usize,
                    shape: ConstructorShape,
                    count: usize,
                },
                FieldAccess {
                    selector: FieldSelector,
                },
                IndexAccess {
                    index: usize,
                },
                Trace,
                Force,
                Delay,
            }

            let mut stack = vec![Step::Enter(expr, shadowed)];
            let mut done: Vec<PseudoExpr> = Vec::new();

            while let Some(step) = stack.pop() {
                match step {
                    Step::Enter(expr, shadowed) => {
                        if !shadowed && matches_force_chain(&expr, var_name, var_id, force_depth) {
                            // Hygienic clone: raw `.clone()` would duplicate
                            // internal binder ids across copies, violating the
                            // one-binder-per-id invariant and stranding refs
                            // across clones.
                            done.push(
                                crate::decompile::simplify::clone_hygiene::clone_with_fresh_binder_ids(
                                    replacement,
                                    || {
                                        let id = crate::pseudo::var_id::VarId::from_raw(*counter);
                                        *counter = counter.saturating_add(1);
                                        id
                                    },
                                ),
                            );
                            continue;
                        }

                        match expr {
                            PseudoExpr::Lambda { params, body } => {
                                let body_shadowed = shadowed
                                    || params.iter().any(|p| {
                                        Simplifier::binder_matches_var_id(p, var_name, var_id)
                                    });
                                stack.push(Step::Lambda { params });
                                stack.push(Step::Enter(body.into_inner(), body_shadowed));
                            }
                            PseudoExpr::RecFn { name, params, body } => {
                                let body_shadowed = shadowed
                                    || Simplifier::binder_matches_var_id(&name, var_name, var_id)
                                    || params.iter().any(|p| {
                                        Simplifier::binder_matches_var_id(p, var_name, var_id)
                                    });
                                stack.push(Step::RecFn { name, params });
                                stack.push(Step::Enter(body.into_inner(), body_shadowed));
                            }
                            PseudoExpr::Apply { function, args } => {
                                stack.push(Step::Apply { argc: args.len() });
                                for a in args.into_iter().rev() {
                                    stack.push(Step::Enter(a, shadowed));
                                }
                                stack.push(Step::Enter(function.into_inner(), shadowed));
                            }
                            PseudoExpr::Let {
                                name,
                                id,
                                value,
                                body,
                            } => {
                                // The binding comes into scope BETWEEN the
                                // two children: the value is walked under the
                                // ambient flag, the body under this one.
                                let body_shadowed = shadowed
                                    || Simplifier::ref_matches_var_id(&name, id, var_name, var_id);
                                stack.push(Step::Let { name, id });
                                stack.push(Step::Enter(body.into_inner(), body_shadowed));
                                stack.push(Step::Enter(value.into_inner(), shadowed));
                            }
                            PseudoExpr::If {
                                condition,
                                then_branch,
                                else_branch,
                            } => {
                                stack.push(Step::If);
                                stack.push(Step::Enter(else_branch.into_inner(), shadowed));
                                stack.push(Step::Enter(then_branch.into_inner(), shadowed));
                                stack.push(Step::Enter(condition.into_inner(), shadowed));
                            }
                            PseudoExpr::When {
                                subject,
                                subject_name,
                                clauses,
                            } => {
                                let when_shadowed = shadowed
                                    || subject_name.as_ref().is_some_and(|n| {
                                        Simplifier::binder_matches_var_id(n, var_name, var_id)
                                    });
                                let mut shells = Vec::with_capacity(clauses.len());
                                let mut children = Vec::with_capacity(clauses.len());
                                for c in clauses {
                                    let clause_shadowed = when_shadowed
                                        || Simplifier::pattern_binds_var_id(
                                            &c.pattern, var_name, var_id,
                                        );
                                    shells.push((c.pattern, c.guard.is_some()));
                                    children.push((c.guard, c.body, clause_shadowed));
                                }
                                stack.push(Step::When {
                                    subject_name,
                                    clauses: shells,
                                });
                                for (guard, body, clause_shadowed) in children.into_iter().rev() {
                                    stack.push(Step::Enter(body, clause_shadowed));
                                    if let Some(g) = guard {
                                        stack.push(Step::Enter(g, clause_shadowed));
                                    }
                                }
                                stack.push(Step::Enter(subject.into_inner(), shadowed));
                            }
                            PseudoExpr::BinOp { op, left, right } => {
                                stack.push(Step::BinOp { op });
                                stack.push(Step::Enter(right.into_inner(), shadowed));
                                stack.push(Step::Enter(left.into_inner(), shadowed));
                            }
                            PseudoExpr::UnOp { op, operand } => {
                                stack.push(Step::UnOp { op });
                                stack.push(Step::Enter(operand.into_inner(), shadowed));
                            }
                            PseudoExpr::List { elements, tail } => {
                                stack.push(Step::List {
                                    count: elements.len(),
                                    has_tail: tail.is_some(),
                                });
                                if let Some(t) = tail {
                                    stack.push(Step::Enter(t.into_inner(), shadowed));
                                }
                                for e in elements.into_iter().rev() {
                                    stack.push(Step::Enter(e, shadowed));
                                }
                            }
                            PseudoExpr::Pair(fst, snd) => {
                                stack.push(Step::Pair);
                                stack.push(Step::Enter(snd.into_inner(), shadowed));
                                stack.push(Step::Enter(fst.into_inner(), shadowed));
                            }
                            PseudoExpr::Tuple(elements) => {
                                stack.push(Step::Tuple {
                                    count: elements.len(),
                                });
                                for e in elements.into_iter().rev() {
                                    stack.push(Step::Enter(e, shadowed));
                                }
                            }
                            PseudoExpr::BuiltinCall { name, args } => {
                                stack.push(Step::BuiltinCall {
                                    name,
                                    argc: args.len(),
                                });
                                for a in args.into_iter().rev() {
                                    stack.push(Step::Enter(a, shadowed));
                                }
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
                                    stack.push(Step::Enter(f, shadowed));
                                }
                            }
                            PseudoExpr::FieldAccess {
                                record, selector, ..
                            } => {
                                stack.push(Step::FieldAccess { selector });
                                stack.push(Step::Enter(record.into_inner(), shadowed));
                            }
                            PseudoExpr::IndexAccess { collection, index } => {
                                stack.push(Step::IndexAccess { index });
                                stack.push(Step::Enter(collection.into_inner(), shadowed));
                            }
                            PseudoExpr::Trace { message, value } => {
                                stack.push(Step::Trace);
                                stack.push(Step::Enter(value.into_inner(), shadowed));
                                stack.push(Step::Enter(message.into_inner(), shadowed));
                            }
                            PseudoExpr::Force(inner) => {
                                stack.push(Step::Force);
                                stack.push(Step::Enter(inner.into_inner(), shadowed));
                            }
                            PseudoExpr::Delay(inner) => {
                                stack.push(Step::Delay);
                                stack.push(Step::Enter(inner.into_inner(), shadowed));
                            }
                            other => done.push(other),
                        }
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
                    Step::Apply { argc } => {
                        let args = done.split_off(done.len() - argc);
                        let function = done.pop().expect("apply function");
                        done.push(PseudoExpr::Apply {
                            function: PBox::new(function),
                            args: args.into(),
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
                        clauses,
                    } => {
                        let total = 1 + clauses
                            .iter()
                            .map(|(_, has_guard)| 1 + usize::from(*has_guard))
                            .sum::<usize>();
                        let mut results = done.split_off(done.len() - total).into_iter();
                        let subject = results.next().expect("when subject");
                        let clauses = clauses
                            .into_iter()
                            .map(|(pattern, has_guard)| {
                                let guard = if has_guard {
                                    Some(results.next().expect("when guard"))
                                } else {
                                    None
                                };
                                let body = results.next().expect("when body");
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
                    Step::List { count, has_tail } => {
                        let tail = has_tail.then(|| PBox::new(done.pop().expect("list tail")));
                        let elements = done.split_off(done.len() - count);
                        done.push(PseudoExpr::List {
                            elements: elements.into(),
                            tail,
                        });
                    }
                    Step::Pair => {
                        let snd = done.pop().expect("pair snd");
                        let fst = done.pop().expect("pair fst");
                        done.push(PseudoExpr::Pair(PBox::new(fst), PBox::new(snd)));
                    }
                    Step::Tuple { count } => {
                        let elements = done.split_off(done.len() - count);
                        done.push(PseudoExpr::Tuple(elements.into()));
                    }
                    Step::BuiltinCall { name, argc } => {
                        let args = done.split_off(done.len() - argc);
                        done.push(PseudoExpr::BuiltinCall {
                            name,
                            args: args.into(),
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
                    Step::Trace => {
                        let value = done.pop().expect("trace value");
                        let message = done.pop().expect("trace message");
                        done.push(PseudoExpr::Trace {
                            message: PBox::new(message),
                            value: PBox::new(value),
                        });
                    }
                    Step::Force => {
                        let inner = done.pop().expect("force inner");
                        done.push(PseudoExpr::Force(PBox::new(inner)));
                    }
                    Step::Delay => {
                        let inner = done.pop().expect("delay inner");
                        done.push(PseudoExpr::Delay(PBox::new(inner)));
                    }
                }
            }

            done.pop().expect("force-chain rewrite result")
        }

        go(
            expr,
            var_name,
            var_id,
            replacement,
            force_depth,
            false,
            &mut self.identity.next_synthetic_var_id,
        )
    }

    /// Count exact occurrences of force^depth(var) with lexical shadowing awareness.
    #[cfg(test)]
    pub(crate) fn count_force_chain_uses(expr: &PseudoExpr, var_name: &str, depth: u8) -> usize {
        fn matches_force_chain(expr: &PseudoExpr, var_name: &str, depth: u8) -> bool {
            let mut current = expr;
            let mut depth = depth;
            while depth > 0 {
                let PseudoExpr::Force(inner) = current else {
                    return false;
                };
                current = inner;
                depth -= 1;
            }
            matches!(current, PseudoExpr::Var { name, .. } if name == var_name)
        }

        fn go(expr: &PseudoExpr, var_name: &str, depth: u8, shadowed: bool) -> usize {
            let mut pending: Vec<(&PseudoExpr, bool)> = vec![(expr, shadowed)];
            let mut total = 0usize;
            while let Some((current, shadowed)) = pending.pop() {
                total += usize::from(!shadowed && matches_force_chain(current, var_name, depth));
                match current {
                    PseudoExpr::Lambda { params, body } => {
                        let body_shadowed = shadowed || params.iter().any(|p| p == var_name);
                        pending.push((body, body_shadowed));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let body_shadowed =
                            shadowed || name == var_name || params.iter().any(|p| p == var_name);
                        pending.push((body, body_shadowed));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for a in args.iter().rev() {
                            pending.push((a, shadowed));
                        }
                        pending.push((function, shadowed));
                    }
                    PseudoExpr::Let {
                        name, value, body, ..
                    } => {
                        pending.push((body, shadowed || name == var_name));
                        pending.push((value, shadowed));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        pending.push((else_branch, shadowed));
                        pending.push((then_branch, shadowed));
                        pending.push((condition, shadowed));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let when_shadowed =
                            shadowed || subject_name.as_ref().is_some_and(|n| n == var_name);
                        for clause in clauses.iter().rev() {
                            let clause_shadowed = when_shadowed
                                || Simplifier::pattern_binds_var(&clause.pattern, var_name);
                            pending.push((&clause.body, clause_shadowed));
                            if let Some(guard) = &clause.guard {
                                pending.push((guard, clause_shadowed));
                            }
                        }
                        pending.push((subject, shadowed));
                    }
                    PseudoExpr::BinOp { left, right, .. } => {
                        pending.push((right, shadowed));
                        pending.push((left, shadowed));
                    }
                    PseudoExpr::UnOp { operand, .. } => pending.push((operand, shadowed)),
                    PseudoExpr::List { elements, tail } => {
                        if let Some(t) = tail {
                            pending.push((t, shadowed));
                        }
                        for e in elements.iter().rev() {
                            pending.push((e, shadowed));
                        }
                    }
                    PseudoExpr::Pair(first, second) => {
                        pending.push((second, shadowed));
                        pending.push((first, shadowed));
                    }
                    PseudoExpr::Tuple(elements) => {
                        for e in elements.iter().rev() {
                            pending.push((e, shadowed));
                        }
                    }
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for a in args.iter().rev() {
                            pending.push((a, shadowed));
                        }
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for f in fields.iter().rev() {
                            pending.push((f, shadowed));
                        }
                    }
                    PseudoExpr::FieldAccess { record, .. } => pending.push((record, shadowed)),
                    PseudoExpr::IndexAccess { collection, .. } => {
                        pending.push((collection, shadowed));
                    }
                    PseudoExpr::Trace { message, value } => {
                        pending.push((value, shadowed));
                        pending.push((message, shadowed));
                    }
                    PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => {
                        pending.push((inner, shadowed));
                    }
                    _ => {}
                }
            }
            total
        }

        go(expr, var_name, depth, false)
    }

    /// VarId-aware variant of [`count_force_chain_uses`].
    ///
    /// At each `Var` leaf, uses VarId comparison when both sides have one,
    /// otherwise falls back to string name. Shadowing uses the same strategy
    /// so same-name foreign binders do not mask the target binding.
    pub(crate) fn count_force_chain_uses_by_id(
        expr: &PseudoExpr,
        var_name: &str,
        var_id: Option<VarId>,
        depth: u8,
    ) -> usize {
        fn matches_force_chain_by_id(
            expr: &PseudoExpr,
            var_name: &str,
            var_id: Option<VarId>,
            depth: u8,
        ) -> bool {
            let mut current = expr;
            let mut depth = depth;
            while depth > 0 {
                let PseudoExpr::Force(inner) = current else {
                    return false;
                };
                current = inner;
                depth -= 1;
            }
            if let PseudoExpr::Var { name, id, .. } = current {
                return Simplifier::ref_matches_var_id(name, *id, var_name, var_id);
            }
            false
        }

        fn go(
            expr: &PseudoExpr,
            var_name: &str,
            var_id: Option<VarId>,
            depth: u8,
            shadowed: bool,
        ) -> usize {
            let mut pending: Vec<(&PseudoExpr, bool)> = vec![(expr, shadowed)];
            let mut total = 0usize;
            while let Some((current, shadowed)) = pending.pop() {
                total += usize::from(
                    !shadowed && matches_force_chain_by_id(current, var_name, var_id, depth),
                );
                match current {
                    PseudoExpr::Lambda { params, body } => {
                        let body_shadowed = shadowed
                            || params
                                .iter()
                                .any(|p| Simplifier::binder_matches_var_id(p, var_name, var_id));
                        pending.push((body, body_shadowed));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let body_shadowed = shadowed
                            || Simplifier::binder_matches_var_id(name, var_name, var_id)
                            || params
                                .iter()
                                .any(|p| Simplifier::binder_matches_var_id(p, var_name, var_id));
                        pending.push((body, body_shadowed));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for a in args.iter().rev() {
                            pending.push((a, shadowed));
                        }
                        pending.push((function, shadowed));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                        ..
                    } => {
                        let let_shadows =
                            Simplifier::ref_matches_var_id(name, *id, var_name, var_id);
                        pending.push((body, shadowed || let_shadows));
                        pending.push((value, shadowed));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        pending.push((else_branch, shadowed));
                        pending.push((then_branch, shadowed));
                        pending.push((condition, shadowed));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let when_shadowed = shadowed
                            || subject_name.as_ref().is_some_and(|n| {
                                Simplifier::binder_matches_var_id(n, var_name, var_id)
                            });
                        for clause in clauses.iter().rev() {
                            let clause_shadowed = when_shadowed
                                || Simplifier::pattern_binds_var_id(
                                    &clause.pattern,
                                    var_name,
                                    var_id,
                                );
                            pending.push((&clause.body, clause_shadowed));
                            if let Some(guard) = &clause.guard {
                                pending.push((guard, clause_shadowed));
                            }
                        }
                        pending.push((subject, shadowed));
                    }
                    PseudoExpr::BinOp { left, right, .. } => {
                        pending.push((right, shadowed));
                        pending.push((left, shadowed));
                    }
                    PseudoExpr::UnOp { operand, .. } => pending.push((operand, shadowed)),
                    PseudoExpr::List { elements, tail } => {
                        if let Some(t) = tail {
                            pending.push((t, shadowed));
                        }
                        for e in elements.iter().rev() {
                            pending.push((e, shadowed));
                        }
                    }
                    PseudoExpr::Pair(first, second) => {
                        pending.push((second, shadowed));
                        pending.push((first, shadowed));
                    }
                    PseudoExpr::Tuple(elements) => {
                        for e in elements.iter().rev() {
                            pending.push((e, shadowed));
                        }
                    }
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for a in args.iter().rev() {
                            pending.push((a, shadowed));
                        }
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for f in fields.iter().rev() {
                            pending.push((f, shadowed));
                        }
                    }
                    PseudoExpr::FieldAccess { record, .. } => pending.push((record, shadowed)),
                    PseudoExpr::IndexAccess { collection, .. } => {
                        pending.push((collection, shadowed));
                    }
                    PseudoExpr::Trace { message, value } => {
                        pending.push((value, shadowed));
                        pending.push((message, shadowed));
                    }
                    PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => {
                        pending.push((inner, shadowed));
                    }
                    _ => {}
                }
            }
            total
        }

        go(expr, var_name, var_id, depth, false)
    }

    pub(crate) fn max_force_chain_depth_by_id(
        expr: &PseudoExpr,
        var_name: &str,
        var_id: Option<VarId>,
    ) -> u8 {
        fn chain_depth(expr: &PseudoExpr, var_name: &str, var_id: Option<VarId>) -> Option<u8> {
            let mut depth: u8 = 0;
            let mut current = expr;
            while let PseudoExpr::Force(inner) = current {
                depth = depth.saturating_add(1);
                current = inner.as_ref();
            }
            if depth > 0
                && matches!(
                    current,
                    PseudoExpr::Var { name, id, .. }
                        if Simplifier::ref_matches_var_id(name, *id, var_name, var_id)
                )
            {
                Some(depth)
            } else {
                None
            }
        }

        fn go(expr: &PseudoExpr, var_name: &str, var_id: Option<VarId>, shadowed: bool) -> u8 {
            let mut pending: Vec<(&PseudoExpr, bool)> = vec![(expr, shadowed)];
            let mut max_depth: u8 = 0;
            while let Some((current, shadowed)) = pending.pop() {
                if !shadowed {
                    max_depth = max_depth.max(chain_depth(current, var_name, var_id).unwrap_or(0));
                }
                match current {
                    PseudoExpr::Lambda { params, body } => {
                        let body_shadowed = shadowed
                            || params
                                .iter()
                                .any(|p| Simplifier::binder_matches_var_id(p, var_name, var_id));
                        pending.push((body, body_shadowed));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let body_shadowed = shadowed
                            || Simplifier::binder_matches_var_id(name, var_name, var_id)
                            || params
                                .iter()
                                .any(|p| Simplifier::binder_matches_var_id(p, var_name, var_id));
                        pending.push((body, body_shadowed));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for a in args.iter().rev() {
                            pending.push((a, shadowed));
                        }
                        pending.push((function, shadowed));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                        ..
                    } => {
                        pending.push((
                            body,
                            shadowed || Simplifier::ref_matches_var_id(name, *id, var_name, var_id),
                        ));
                        pending.push((value, shadowed));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        pending.push((else_branch, shadowed));
                        pending.push((then_branch, shadowed));
                        pending.push((condition, shadowed));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let when_shadowed = shadowed
                            || subject_name.as_ref().is_some_and(|n| {
                                Simplifier::binder_matches_var_id(n, var_name, var_id)
                            });
                        for clause in clauses.iter().rev() {
                            let clause_shadowed = when_shadowed
                                || Simplifier::pattern_binds_var_id(
                                    &clause.pattern,
                                    var_name,
                                    var_id,
                                );
                            pending.push((&clause.body, clause_shadowed));
                            if let Some(guard) = &clause.guard {
                                pending.push((guard, clause_shadowed));
                            }
                        }
                        pending.push((subject, shadowed));
                    }
                    PseudoExpr::BinOp { left, right, .. } => {
                        pending.push((right, shadowed));
                        pending.push((left, shadowed));
                    }
                    PseudoExpr::UnOp { operand, .. } => pending.push((operand, shadowed)),
                    PseudoExpr::List { elements, tail } => {
                        if let Some(t) = tail {
                            pending.push((t, shadowed));
                        }
                        for e in elements.iter().rev() {
                            pending.push((e, shadowed));
                        }
                    }
                    PseudoExpr::Pair(first, second) => {
                        pending.push((second, shadowed));
                        pending.push((first, shadowed));
                    }
                    PseudoExpr::Tuple(elements) => {
                        for e in elements.iter().rev() {
                            pending.push((e, shadowed));
                        }
                    }
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for a in args.iter().rev() {
                            pending.push((a, shadowed));
                        }
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for f in fields.iter().rev() {
                            pending.push((f, shadowed));
                        }
                    }
                    PseudoExpr::FieldAccess { record, .. } => pending.push((record, shadowed)),
                    PseudoExpr::IndexAccess { collection, .. } => {
                        pending.push((collection, shadowed));
                    }
                    PseudoExpr::Trace { message, value } => {
                        pending.push((value, shadowed));
                        pending.push((message, shadowed));
                    }
                    PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => {
                        pending.push((inner, shadowed));
                    }
                    _ => {}
                }
            }
            max_depth
        }

        go(expr, var_name, var_id, false)
    }
}
