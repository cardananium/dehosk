use std::rc::Rc;

use crate::pseudo::ast::{Binder, PseudoExpr, PseudoType, WhenClause, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;
use crate::pseudo::var_id::VarId;

use super::core::{BindingKey, LexicalEnv, TypeExpr, TypeSolver, TypeVarId};
use super::{expr_type_var, let_binding_key, pattern_binders};

/// Second constraint generation pass. With forward constraints from types
/// and usage in place, propagate backward from fields to containers.
///
/// Example: if `let x: ByteArray = Data.to_bytes(field_0)` and `field_0`
/// came from `Ok(field_0)` on a `Result<?, ?>`, the Ok side is ByteArray.
///
/// Walks an explicit stack: the tree's depth is the script's nesting, which
/// the script chooses. Each node's own work runs when it is visited and its
/// children follow in source order, with the lexical scope pushed and popped
/// around exactly the children a binder covers.
pub(super) fn generate_backward_constraints(
    expr: &PseudoExpr,
    solver: &mut TypeSolver,
    env: &mut LexicalEnv,
) {
    enum Step<'a> {
        Visit(&'a PseudoExpr),
        /// One `when` clause: its binder scope and pattern constraints, then
        /// its body, then the next clause.
        Clause {
            clauses: &'a [WhenClause],
            index: usize,
            subject_name: Option<&'a Binder>,
            subject_tv: TypeVarId,
        },
        /// A `Let`'s binding, entered between its value and its body.
        PushLet {
            name: &'a str,
            id: Option<VarId>,
        },
        /// The matching `env.pop`s, after the scoped child.
        PopEnv(usize),
    }

    let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];
    while let Some(step) = steps.pop() {
        let expr = match step {
            Step::Visit(expr) => expr,
            Step::PushLet { name, id } => {
                env.push(name.to_string(), let_binding_key(id));
                continue;
            }
            Step::PopEnv(count) => {
                for _ in 0..count {
                    env.pop();
                }
                continue;
            }
            Step::Clause {
                clauses,
                index,
                subject_name,
                subject_tv,
            } => {
                let clause = &clauses[index];
                if let Some(subject_name) = subject_name {
                    env.push(subject_name.to_string(), BindingKey::VarId(subject_name.id));
                }
                let binders = pattern_binders(&clause.pattern);
                for binder in &binders {
                    env.push(binder.name.clone(), BindingKey::VarId(binder.id));
                }
                propagate_pattern_to_subject(&clause.pattern, subject_tv, solver, env);

                // Pushed in reverse of the order they run: the body, the
                // clause's `env.pop`s, then the next clause.
                if index + 1 < clauses.len() {
                    steps.push(Step::Clause {
                        clauses,
                        index: index + 1,
                        subject_name,
                        subject_tv,
                    });
                }
                steps.push(Step::PopEnv(
                    binders.len() + usize::from(subject_name.is_some()),
                ));
                steps.push(Step::Visit(&clause.body));
                continue;
            }
        };

        // Children are pushed in REVERSE so they are walked in order.
        match expr {
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                let subject_tv = expr_type_var(subject, solver, env);

                if let Some(subject_name) = subject_name {
                    let subject_name_tv = solver.var_for_var_id(subject_name.id);
                    solver.constrain_eq(subject_name_tv, subject_tv);
                }

                // The subject is walked after every clause.
                steps.push(Step::Visit(subject));
                if !clauses.is_empty() {
                    steps.push(Step::Clause {
                        clauses: clauses.as_slice(),
                        index: 0,
                        subject_name: subject_name.as_ref(),
                        subject_tv,
                    });
                }
            }

            PseudoExpr::Let {
                name,
                id,
                value,
                body,
                ..
            } => {
                steps.push(Step::PopEnv(1));
                steps.push(Step::Visit(body));
                steps.push(Step::PushLet { name, id: *id });
                steps.push(Step::Visit(value));
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
            PseudoExpr::Apply { function, args } => {
                steps.extend(args.iter().rev().map(Step::Visit));
                steps.push(Step::Visit(function));
            }
            PseudoExpr::Lambda { body, params, .. } => {
                for param in params {
                    env.push(param.to_string(), BindingKey::VarId(param.id));
                }
                steps.push(Step::PopEnv(params.len()));
                steps.push(Step::Visit(body));
            }
            PseudoExpr::RecFn { name, params, body } => {
                env.push(name.to_string(), BindingKey::VarId(name.id));
                for param in params {
                    env.push(param.to_string(), BindingKey::VarId(param.id));
                }
                steps.push(Step::PopEnv(params.len() + 1));
                steps.push(Step::Visit(body));
            }
            PseudoExpr::Constr { fields, .. } => {
                steps.extend(fields.iter().rev().map(Step::Visit));
            }
            PseudoExpr::BinOp { left, right, .. } => {
                steps.push(Step::Visit(right));
                steps.push(Step::Visit(left));
            }
            PseudoExpr::UnOp { operand, .. } => {
                steps.push(Step::Visit(operand));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    steps.push(Step::Visit(t));
                }
                steps.extend(elements.iter().rev().map(Step::Visit));
            }
            PseudoExpr::Tuple(elements) => {
                steps.extend(elements.iter().rev().map(Step::Visit));
            }
            PseudoExpr::Pair(a, b) => {
                steps.push(Step::Visit(b));
                steps.push(Step::Visit(a));
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                steps.extend(args.iter().rev().map(Step::Visit));
            }
            PseudoExpr::FieldAccess {
                record, selector, ..
            } => {
                let record_tv = expr_type_var(record, solver, env);
                match selector.as_pretty_name() {
                    "fields" | "tag" => {
                        solver.constrain_known(record_tv, PseudoType::Data);
                    }
                    "fst" | "snd" | "first" | "second" | "1st" | "2nd" => {
                        solver.constrain_known(
                            record_tv,
                            PseudoType::Pair(
                                Rc::new(PseudoType::Unknown),
                                Rc::new(PseudoType::Unknown),
                            ),
                        );
                    }
                    "head" | "tail" => {
                        solver.constrain_known(
                            record_tv,
                            PseudoType::List(Rc::new(PseudoType::Unknown)),
                        );
                    }
                    _ => {}
                }
                steps.push(Step::Visit(record));
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                steps.push(Step::Visit(collection));
            }
            PseudoExpr::Trace { message, value } => {
                steps.push(Step::Visit(value));
                steps.push(Step::Visit(message));
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                steps.push(Step::Visit(inner));
            }
            _ => {}
        }
    }
}

/// One clause's pattern evidence, pushed back onto the `when` subject.
fn propagate_pattern_to_subject(
    pattern: &WhenPattern,
    subject_tv: TypeVarId,
    solver: &mut TypeSolver,
    env: &LexicalEnv,
) {
    match pattern {
        WhenPattern::Constructor { shape, fields, .. } => {
            // After solve pass 1, field vars may have known types.
            // Propagate back to subject.
            match shape.as_known() {
                Some(KnownConstructor::Some) => {
                    let field_tv =
                        solver.resolve_binding_in_env(fields[0].as_str(), Some(fields[0].id), env);
                    let resolved = solver.find(field_tv);
                    if let TypeExpr::Known(t) = resolved
                        && *t.as_ref() != PseudoType::Unknown
                    {
                        solver
                            .constrain(subject_tv, TypeExpr::Known(Rc::new(PseudoType::Option(t))));
                    }
                }
                Some(KnownConstructor::Ok) => {
                    let field_tv =
                        solver.resolve_binding_in_env(fields[0].as_str(), Some(fields[0].id), env);
                    let resolved = solver.find(field_tv);
                    if let TypeExpr::Known(t) = resolved
                        && *t.as_ref() != PseudoType::Unknown
                    {
                        // Merge with existing Result type.
                        let subj_res = solver.find(subject_tv);
                        let err_side = if let TypeExpr::Known(st) = &subj_res {
                            if let PseudoType::Result(_, err) = st.as_ref() {
                                err.clone()
                            } else {
                                Rc::new(PseudoType::Unknown)
                            }
                        } else {
                            Rc::new(PseudoType::Unknown)
                        };
                        solver.constrain(
                            subject_tv,
                            TypeExpr::Known(Rc::new(PseudoType::Result(t, err_side))),
                        );
                    }
                }
                Some(KnownConstructor::Error) => {
                    let field_tv =
                        solver.resolve_binding_in_env(fields[0].as_str(), Some(fields[0].id), env);
                    let resolved = solver.find(field_tv);
                    if let TypeExpr::Known(t) = resolved
                        && *t.as_ref() != PseudoType::Unknown
                    {
                        let subj_res = solver.find(subject_tv);
                        let ok_side = if let TypeExpr::Known(st) = &subj_res {
                            if let PseudoType::Result(ok, _) = st.as_ref() {
                                ok.clone()
                            } else {
                                Rc::new(PseudoType::Unknown)
                            }
                        } else {
                            Rc::new(PseudoType::Unknown)
                        };
                        solver.constrain(
                            subject_tv,
                            TypeExpr::Known(Rc::new(PseudoType::Result(ok_side, t))),
                        );
                    }
                }
                Some(
                    KnownConstructor::True
                    | KnownConstructor::False
                    | KnownConstructor::None
                    | KnownConstructor::Pair
                    | KnownConstructor::Nil
                    | KnownConstructor::Cons
                    | KnownConstructor::Less
                    | KnownConstructor::Equal
                    | KnownConstructor::Greater,
                )
                | None => {}
                // Cardano-purpose variants - no `PseudoType` rep.
                Some(_) => {}
            }
        }
        WhenPattern::Pair(a, b) => {
            let a_tv = solver.resolve_binding_in_env(a, Some(a.id), env);
            let b_tv = solver.resolve_binding_in_env(b, Some(b.id), env);
            let a_res = solver.find(a_tv);
            let b_res = solver.find(b_tv);
            let a_type = match a_res {
                TypeExpr::Known(t) => t,
                _ => Rc::new(PseudoType::Unknown),
            };
            let b_type = match b_res {
                TypeExpr::Known(t) => t,
                _ => Rc::new(PseudoType::Unknown),
            };
            if *a_type.as_ref() != PseudoType::Unknown || *b_type.as_ref() != PseudoType::Unknown {
                solver.constrain(
                    subject_tv,
                    TypeExpr::Known(Rc::new(PseudoType::Pair(a_type, b_type))),
                );
            }
        }
        _ => {}
    }
}
