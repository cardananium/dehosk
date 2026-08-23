use std::rc::Rc;

use crate::pseudo::ast::{PseudoExpr, PseudoType, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;

use super::core::{BindingKey, LexicalEnv, TypeExpr, TypeSolver};
use super::{child_path, expr_type_var, let_binding_key, pattern_binders};

/// Second constraint generation pass. With forward constraints from types
/// and usage in place, propagate backward from fields to containers.
///
/// Example: if `let x: ByteArray = Data.to_bytes(field_0)` and `field_0`
/// came from `Ok(field_0)` on a `Result<?, ?>`, the Ok side is ByteArray.
pub(super) fn generate_backward_constraints(
    expr: &PseudoExpr,
    solver: &mut TypeSolver,
    env: &mut LexicalEnv,
    path: &[u32],
) {
    match expr {
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => {
            let subject_tv = expr_type_var(subject, solver, env, &child_path(path, 0));

            if let Some(subject_name) = subject_name {
                let subject_name_tv = solver.var_for_var_id(subject_name.id);
                solver.constrain_eq(subject_name_tv, subject_tv);
            }

            let mut child_index = 1;
            for clause in clauses.iter() {
                if let Some(subject_name) = subject_name {
                    env.push(subject_name.to_string(), BindingKey::VarId(subject_name.id));
                }
                let binders = pattern_binders(&clause.pattern);
                for binder in &binders {
                    env.push(binder.name.clone(), BindingKey::VarId(binder.id));
                }
                match &clause.pattern {
                    WhenPattern::Constructor { shape, fields, .. } => {
                        // After solve pass 1, field vars may have known types.
                        // Propagate back to subject.
                        match shape.as_known() {
                            Some(KnownConstructor::Some) => {
                                let field_tv = solver.resolve_binding_in_env(
                                    fields[0].as_str(),
                                    Some(fields[0].id),
                                    env,
                                );
                                let resolved = solver.find(field_tv);
                                if let TypeExpr::Known(t) = resolved
                                    && *t.as_ref() != PseudoType::Unknown
                                {
                                    solver.constrain(
                                        subject_tv,
                                        TypeExpr::Known(Rc::new(PseudoType::Option(t))),
                                    );
                                }
                            }
                            Some(KnownConstructor::Ok) => {
                                let field_tv = solver.resolve_binding_in_env(
                                    fields[0].as_str(),
                                    Some(fields[0].id),
                                    env,
                                );
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
                                let field_tv = solver.resolve_binding_in_env(
                                    fields[0].as_str(),
                                    Some(fields[0].id),
                                    env,
                                );
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
                        if *a_type.as_ref() != PseudoType::Unknown
                            || *b_type.as_ref() != PseudoType::Unknown
                        {
                            solver.constrain(
                                subject_tv,
                                TypeExpr::Known(Rc::new(PseudoType::Pair(a_type, b_type))),
                            );
                        }
                    }
                    _ => {}
                }
                if matches!(&clause.pattern, WhenPattern::Literal(_)) {
                    child_index += 1;
                }
                if clause.guard.is_some() {
                    child_index += 1;
                }
                generate_backward_constraints(
                    &clause.body,
                    solver,
                    env,
                    &child_path(path, child_index),
                );
                child_index += 1;
                for _ in &binders {
                    env.pop();
                }
                if subject_name.is_some() {
                    env.pop();
                }
            }
            generate_backward_constraints(subject, solver, env, &child_path(path, 0));
        }

        // Recurse into all children.
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
            ..
        } => {
            generate_backward_constraints(value, solver, env, &child_path(path, 0));
            env.push(name.clone(), let_binding_key(*id));
            generate_backward_constraints(body, solver, env, &child_path(path, 1));
            env.pop();
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            generate_backward_constraints(condition, solver, env, &child_path(path, 0));
            generate_backward_constraints(then_branch, solver, env, &child_path(path, 1));
            generate_backward_constraints(else_branch, solver, env, &child_path(path, 2));
        }
        PseudoExpr::Apply { function, args } => {
            generate_backward_constraints(function, solver, env, &child_path(path, 0));
            for (index, arg) in args.iter().enumerate() {
                generate_backward_constraints(
                    arg,
                    solver,
                    env,
                    &child_path(path, index as u32 + 1),
                );
            }
        }
        PseudoExpr::Lambda { body, params, .. } => {
            for param in params {
                env.push(param.to_string(), BindingKey::VarId(param.id));
            }
            generate_backward_constraints(body, solver, env, &child_path(path, 0));
            for _ in params {
                env.pop();
            }
        }
        PseudoExpr::RecFn { name, params, body } => {
            env.push(name.to_string(), BindingKey::VarId(name.id));
            for param in params {
                env.push(param.to_string(), BindingKey::VarId(param.id));
            }
            generate_backward_constraints(body, solver, env, &child_path(path, 0));
            for _ in 0..=params.len() {
                env.pop();
            }
        }
        PseudoExpr::Constr { fields, .. } => {
            for (index, field) in fields.iter().enumerate() {
                generate_backward_constraints(field, solver, env, &child_path(path, index as u32));
            }
        }
        PseudoExpr::BinOp { left, right, .. } => {
            generate_backward_constraints(left, solver, env, &child_path(path, 0));
            generate_backward_constraints(right, solver, env, &child_path(path, 1));
        }
        PseudoExpr::UnOp { operand, .. } => {
            generate_backward_constraints(operand, solver, env, &child_path(path, 0));
        }
        PseudoExpr::List { elements, tail } => {
            for (index, element) in elements.iter().enumerate() {
                generate_backward_constraints(
                    element,
                    solver,
                    env,
                    &child_path(path, index as u32),
                );
            }
            if let Some(t) = tail {
                generate_backward_constraints(
                    t,
                    solver,
                    env,
                    &child_path(path, elements.len() as u32),
                );
            }
        }
        PseudoExpr::Tuple(elements) => {
            for (index, element) in elements.iter().enumerate() {
                generate_backward_constraints(
                    element,
                    solver,
                    env,
                    &child_path(path, index as u32),
                );
            }
        }
        PseudoExpr::Pair(a, b) => {
            generate_backward_constraints(a, solver, env, &child_path(path, 0));
            generate_backward_constraints(b, solver, env, &child_path(path, 1));
        }
        PseudoExpr::BuiltinCall { args, .. } => {
            for (index, arg) in args.iter().enumerate() {
                generate_backward_constraints(arg, solver, env, &child_path(path, index as u32));
            }
        }
        PseudoExpr::FieldAccess {
            record, selector, ..
        } => {
            let record_tv = expr_type_var(record, solver, env, &child_path(path, 0));
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
                    solver
                        .constrain_known(record_tv, PseudoType::List(Rc::new(PseudoType::Unknown)));
                }
                _ => {}
            }
            generate_backward_constraints(record, solver, env, &child_path(path, 0));
        }
        PseudoExpr::IndexAccess { collection, .. } => {
            generate_backward_constraints(collection, solver, env, &child_path(path, 0));
        }
        PseudoExpr::Trace { message, value } => {
            generate_backward_constraints(message, solver, env, &child_path(path, 0));
            generate_backward_constraints(value, solver, env, &child_path(path, 1));
        }
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
            generate_backward_constraints(inner, solver, env, &child_path(path, 0));
        }
        _ => {}
    }
}
