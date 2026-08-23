use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::LiftedLet;

pub(crate) fn var_is_referenced(expr: &PseudoExpr, var_name: &str) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        let kids: Vec<&PseudoExpr> = match expr {
            PseudoExpr::Var { name, .. } => {
                if name == var_name {
                    return true;
                }
                vec![]
            }
            PseudoExpr::Let {
                name, value, body, ..
            } => {
                if name != var_name {
                    vec![value, body]
                } else {
                    vec![value]
                }
            }
            PseudoExpr::Lambda { params, body } => {
                if params.iter().any(|p| p == var_name) {
                    vec![]
                } else {
                    vec![body]
                }
            }
            PseudoExpr::RecFn {
                name, params, body, ..
            } => {
                if name == var_name || params.iter().any(|p| p == var_name) {
                    vec![]
                } else {
                    vec![body]
                }
            }
            PseudoExpr::Apply { function, args } => {
                let mut v = vec![function.as_ref()];
                v.extend(args.iter());
                v
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => vec![condition, then_branch, else_branch],
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                let mut v = vec![subject.as_ref()];
                for c in clauses {
                    if !pattern_binds_var(&c.pattern, var_name) {
                        v.push(&c.body);
                    }
                }
                v
            }
            PseudoExpr::BinOp { left, right, .. } => vec![left, right],
            PseudoExpr::UnOp { operand, .. } => vec![operand],
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => vec![inner],
            PseudoExpr::Trace { message, value } => vec![message, value],
            PseudoExpr::List { elements, tail } => {
                let mut v: Vec<&PseudoExpr> = elements.iter().collect();
                if let Some(t) = tail {
                    v.push(t);
                }
                v
            }
            PseudoExpr::Tuple(elements) => elements.iter().collect(),
            PseudoExpr::Pair(a, b) => vec![a, b],
            PseudoExpr::Constr { fields, .. } => fields.iter().collect(),
            PseudoExpr::FieldAccess { record, .. } => vec![record],
            PseudoExpr::IndexAccess { collection, .. } => vec![collection],
            PseudoExpr::BuiltinCall { args, .. } => args.iter().collect(),
            _ => vec![],
        };
        pending.extend(kids.into_iter().rev());
    }
    false
}

pub(crate) fn pattern_binds_var(pattern: &WhenPattern, var_name: &str) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields.iter().any(|f| f == var_name),
        WhenPattern::List { elements, tail } => {
            elements.iter().any(|e| e == var_name) || tail.as_ref().is_some_and(|t| t == var_name)
        }
        WhenPattern::Tuple(fields) => fields.iter().any(|f| f == var_name),
        WhenPattern::Pair(a, b) => a == var_name || b == var_name,
        WhenPattern::Var(v) => v == var_name,
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}

#[derive(Debug, Clone)]
pub(crate) struct BindingTarget {
    pub(crate) name: String,
    pub(crate) id: VarId,
}

impl From<&LiftedLet> for BindingTarget {
    fn from(binding: &LiftedLet) -> Self {
        Self {
            name: binding.name.clone(),
            id: binding
                .id
                .get()
                .unwrap_or_else(VarId::fresh_compat_placeholder),
        }
    }
}

impl From<&Binder> for BindingTarget {
    fn from(binder: &Binder) -> Self {
        Self {
            name: binder.name.clone(),
            id: binder.id,
        }
    }
}

pub(super) fn binder_shadows_name_fallback(
    name: &str,
    id: VarId,
    target_name: &str,
    target_id: VarId,
) -> bool {
    id != target_id && name == target_name
}

pub(super) fn pattern_shadows_name_fallback(
    pattern: &WhenPattern,
    target_name: &str,
    target_id: VarId,
) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields.iter().any(|field| {
            binder_shadows_name_fallback(field.as_str(), field.id, target_name, target_id)
        }),
        WhenPattern::List { elements, tail } => {
            elements.iter().any(|element| {
                binder_shadows_name_fallback(element.as_str(), element.id, target_name, target_id)
            }) || tail.as_ref().is_some_and(|tail| {
                binder_shadows_name_fallback(tail.as_str(), tail.id, target_name, target_id)
            })
        }
        WhenPattern::Tuple(fields) => fields.iter().any(|field| {
            binder_shadows_name_fallback(field.as_str(), field.id, target_name, target_id)
        }),
        WhenPattern::Pair(a, b) => {
            binder_shadows_name_fallback(a.as_str(), a.id, target_name, target_id)
                || binder_shadows_name_fallback(b.as_str(), b.id, target_name, target_id)
        }
        WhenPattern::Var(v) => {
            binder_shadows_name_fallback(v.as_str(), v.id, target_name, target_id)
        }
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}

pub(super) fn expr_has_shadowing_binder(
    expr: &PseudoExpr,
    target_name: &str,
    target_id: VarId,
) -> bool {
    let mut stack = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                if binder_shadows_name_fallback(
                    name,
                    id.unwrap_or_else(VarId::fresh_compat_placeholder),
                    target_name,
                    target_id,
                ) {
                    return true;
                }
                stack.push(body);
                stack.push(value);
            }
            PseudoExpr::Lambda { params, body } => {
                if params.iter().any(|param| {
                    binder_shadows_name_fallback(param.as_str(), param.id, target_name, target_id)
                }) {
                    return true;
                }
                stack.push(body);
            }
            PseudoExpr::RecFn { name, params, body } => {
                if binder_shadows_name_fallback(name.as_str(), name.id, target_name, target_id)
                    || params.iter().any(|param| {
                        binder_shadows_name_fallback(
                            param.as_str(),
                            param.id,
                            target_name,
                            target_id,
                        )
                    })
                {
                    return true;
                }
                stack.push(body);
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                if subject_name.as_ref().is_some_and(|subject_name| {
                    binder_shadows_name_fallback(
                        subject_name.as_str(),
                        subject_name.id,
                        target_name,
                        target_id,
                    )
                }) {
                    return true;
                }
                for clause in clauses.iter().rev() {
                    if pattern_shadows_name_fallback(&clause.pattern, target_name, target_id) {
                        return true;
                    }
                    stack.push(&clause.body);
                    if let Some(guard) = &clause.guard {
                        stack.push(guard);
                    }
                    if let WhenPattern::Literal(lit) = &clause.pattern {
                        stack.push(lit);
                    }
                }
                stack.push(subject);
            }
            PseudoExpr::Apply { function, args } => {
                for arg in args.iter().rev() {
                    stack.push(arg);
                }
                stack.push(function);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.push(else_branch);
                stack.push(then_branch);
                stack.push(condition);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                stack.push(right);
                stack.push(left);
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => {
                stack.push(operand);
            }
            PseudoExpr::Trace { message, value } => {
                stack.push(value);
                stack.push(message);
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(tail) = tail {
                    stack.push(tail);
                }
                for element in elements.iter().rev() {
                    stack.push(element);
                }
            }
            PseudoExpr::Tuple(elements) => {
                for element in elements.iter().rev() {
                    stack.push(element);
                }
            }
            PseudoExpr::Pair(a, b) => {
                stack.push(b);
                stack.push(a);
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields.iter().rev() {
                    stack.push(field);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => {
                stack.push(record);
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                stack.push(collection);
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args.iter().rev() {
                    stack.push(arg);
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
    false
}

pub(super) fn rename_target_var_display_name(
    expr: PseudoExpr,
    target_name: &str,
    target_id: VarId,
    new_name: &str,
) -> PseudoExpr {
    rename_target_var_display_name_with_shadow(expr, target_name, target_id, new_name, false)
}

fn rename_target_var_display_name_with_shadow(
    expr: PseudoExpr,
    target_name: &str,
    target_id: VarId,
    new_name: &str,
    fallback_shadowed: bool,
) -> PseudoExpr {
    fn var_matches(
        name: &str,
        id: Option<VarId>,
        target_name: &str,
        target_id: VarId,
        shadowed: bool,
    ) -> bool {
        id == Some(target_id)
            || (!shadowed && target_id.get().is_none() && id.get().is_none() && name == target_name)
    }

    fn go(
        expr: PseudoExpr,
        target_name: &str,
        target_id: VarId,
        new_name: &str,
        fallback_shadowed: bool,
    ) -> PseudoExpr {
        match expr {
            PseudoExpr::Var { name, id } => {
                let rename = var_matches(&name, id, target_name, target_id, fallback_shadowed);
                PseudoExpr::Var {
                    name: if rename { new_name.to_string() } else { name },
                    id,
                }
            }
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                let value = go(
                    value.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                );
                let body_shadowed = fallback_shadowed
                    || binder_shadows_name_fallback(
                        &name,
                        id.unwrap_or_else(VarId::fresh_compat_placeholder),
                        target_name,
                        target_id,
                    );
                let body = go(
                    body.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    body_shadowed,
                );
                PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                }
            }
            PseudoExpr::Lambda { params, body } => {
                let body_shadowed = fallback_shadowed
                    || params.iter().any(|param| {
                        binder_shadows_name_fallback(
                            param.as_str(),
                            param.id,
                            target_name,
                            target_id,
                        )
                    });
                PseudoExpr::Lambda {
                    params,
                    body: PBox::new(go(
                        body.into_inner(),
                        target_name,
                        target_id,
                        new_name,
                        body_shadowed,
                    )),
                }
            }
            PseudoExpr::RecFn { name, params, body } => {
                let body_shadowed = fallback_shadowed
                    || binder_shadows_name_fallback(name.as_str(), name.id, target_name, target_id)
                    || params.iter().any(|param| {
                        binder_shadows_name_fallback(
                            param.as_str(),
                            param.id,
                            target_name,
                            target_id,
                        )
                    });
                PseudoExpr::RecFn {
                    name,
                    params,
                    body: PBox::new(go(
                        body.into_inner(),
                        target_name,
                        target_id,
                        new_name,
                        body_shadowed,
                    )),
                }
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                let subject = PBox::new(go(
                    subject.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                ));
                let clauses = clauses
                    .into_iter()
                    .map(|clause| {
                        let pattern = rename_pattern_literal_display_name(
                            clause.pattern,
                            target_name,
                            target_id,
                            new_name,
                            fallback_shadowed,
                        );
                        let clause_shadowed = fallback_shadowed
                            || subject_name.as_ref().is_some_and(|subject_name| {
                                binder_shadows_name_fallback(
                                    subject_name.as_str(),
                                    subject_name.id,
                                    target_name,
                                    target_id,
                                )
                            })
                            || pattern_shadows_name_fallback(&pattern, target_name, target_id);
                        WhenClause {
                            pattern,
                            guard: clause.guard.map(|guard| {
                                go(guard, target_name, target_id, new_name, clause_shadowed)
                            }),
                            body: go(
                                clause.body,
                                target_name,
                                target_id,
                                new_name,
                                clause_shadowed,
                            ),
                        }
                    })
                    .collect();
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                }
            }
            PseudoExpr::Apply { function, args } => PseudoExpr::Apply {
                function: PBox::new(go(
                    function.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
                args: args
                    .into_iter()
                    .map(|arg| go(arg, target_name, target_id, new_name, fallback_shadowed))
                    .collect(),
            },
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => PseudoExpr::If {
                condition: PBox::new(go(
                    condition.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
                then_branch: PBox::new(go(
                    then_branch.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
                else_branch: PBox::new(go(
                    else_branch.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
            },
            PseudoExpr::BinOp { op, left, right } => PseudoExpr::BinOp {
                op,
                left: PBox::new(go(
                    left.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
                right: PBox::new(go(
                    right.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
            },
            PseudoExpr::UnOp { op, operand } => PseudoExpr::UnOp {
                op,
                operand: PBox::new(go(
                    operand.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
            },
            PseudoExpr::BuiltinCall { name, args } => PseudoExpr::BuiltinCall {
                name,
                args: args
                    .into_iter()
                    .map(|arg| go(arg, target_name, target_id, new_name, fallback_shadowed))
                    .collect(),
            },
            PseudoExpr::Delay(inner) => PseudoExpr::Delay(PBox::new(go(
                inner.into_inner(),
                target_name,
                target_id,
                new_name,
                fallback_shadowed,
            ))),
            PseudoExpr::Force(inner) => PseudoExpr::Force(PBox::new(go(
                inner.into_inner(),
                target_name,
                target_id,
                new_name,
                fallback_shadowed,
            ))),
            PseudoExpr::Trace { message, value } => PseudoExpr::Trace {
                message: PBox::new(go(
                    message.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
                value: PBox::new(go(
                    value.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
            },
            PseudoExpr::List { elements, tail } => PseudoExpr::List {
                elements: elements
                    .into_iter()
                    .map(|element| go(element, target_name, target_id, new_name, fallback_shadowed))
                    .collect(),
                tail: tail.map(|tail| {
                    PBox::new(go(
                        tail.into_inner(),
                        target_name,
                        target_id,
                        new_name,
                        fallback_shadowed,
                    ))
                }),
            },
            PseudoExpr::Tuple(elements) => PseudoExpr::Tuple(
                elements
                    .into_iter()
                    .map(|element| go(element, target_name, target_id, new_name, fallback_shadowed))
                    .collect(),
            ),
            PseudoExpr::Pair(a, b) => PseudoExpr::Pair(
                PBox::new(go(
                    a.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
                PBox::new(go(
                    b.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
            ),
            PseudoExpr::Constr {
                type_hint,
                tag,
                fields,
                shape,
            } => PseudoExpr::Constr {
                type_hint,
                tag,
                fields: fields
                    .into_iter()
                    .map(|field| go(field, target_name, target_id, new_name, fallback_shadowed))
                    .collect(),
                shape,
            },
            PseudoExpr::FieldAccess { record, selector } => PseudoExpr::FieldAccess {
                record: PBox::new(go(
                    record.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
                selector,
            },
            PseudoExpr::IndexAccess { collection, index } => PseudoExpr::IndexAccess {
                collection: PBox::new(go(
                    collection.into_inner(),
                    target_name,
                    target_id,
                    new_name,
                    fallback_shadowed,
                )),
                index,
            },
            other @ (PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_)) => other,
        }
    }

    go(expr, target_name, target_id, new_name, fallback_shadowed)
}

fn rename_pattern_literal_display_name(
    pattern: WhenPattern,
    target_name: &str,
    target_id: VarId,
    new_name: &str,
    fallback_shadowed: bool,
) -> WhenPattern {
    match pattern {
        WhenPattern::Literal(expr) => {
            WhenPattern::Literal(rename_target_var_display_name_with_shadow(
                expr,
                target_name,
                target_id,
                new_name,
                fallback_shadowed,
            ))
        }
        other => other,
    }
}

pub(crate) fn var_is_referenced_id_aware(
    expr: &PseudoExpr,
    target_id: VarId,
    target_name: &str,
) -> bool {
    let mut stack = vec![(expr, false)];

    while let Some((current, fallback_shadowed)) = stack.pop() {
        match current {
            PseudoExpr::Var { name, id, .. } => {
                if *id == Some(target_id)
                    || (!fallback_shadowed && id.get().is_none() && name == target_name)
                {
                    return true;
                }
            }
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
                ..
            } => {
                stack.push((value.as_ref(), fallback_shadowed));
                let body_shadowed = fallback_shadowed
                    || binder_shadows_name_fallback(
                        name,
                        id.unwrap_or_else(VarId::fresh_compat_placeholder),
                        target_name,
                        target_id,
                    );
                stack.push((body.as_ref(), body_shadowed));
            }
            PseudoExpr::Lambda { params, body } => {
                let body_shadowed = fallback_shadowed
                    || params.iter().any(|param| {
                        binder_shadows_name_fallback(
                            param.as_str(),
                            param.id,
                            target_name,
                            target_id,
                        )
                    });
                stack.push((body.as_ref(), body_shadowed));
            }
            PseudoExpr::RecFn { name, params, body } => {
                let body_shadowed = fallback_shadowed
                    || binder_shadows_name_fallback(name.as_str(), name.id, target_name, target_id)
                    || params.iter().any(|param| {
                        binder_shadows_name_fallback(
                            param.as_str(),
                            param.id,
                            target_name,
                            target_id,
                        )
                    });
                stack.push((body.as_ref(), body_shadowed));
            }
            PseudoExpr::Apply { function, args } => {
                stack.push((function.as_ref(), fallback_shadowed));
                for arg in args {
                    stack.push((arg, fallback_shadowed));
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.push((condition.as_ref(), fallback_shadowed));
                stack.push((then_branch.as_ref(), fallback_shadowed));
                stack.push((else_branch.as_ref(), fallback_shadowed));
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                stack.push((subject.as_ref(), fallback_shadowed));
                for clause in clauses {
                    let clause_shadowed = fallback_shadowed
                        || subject_name.as_ref().is_some_and(|subject_name| {
                            binder_shadows_name_fallback(
                                subject_name.as_str(),
                                subject_name.id,
                                target_name,
                                target_id,
                            )
                        })
                        || pattern_shadows_name_fallback(&clause.pattern, target_name, target_id);
                    if let Some(guard) = &clause.guard {
                        stack.push((guard, clause_shadowed));
                    }
                    stack.push((&clause.body, clause_shadowed));
                    if let WhenPattern::Literal(lit) = &clause.pattern {
                        stack.push((lit, fallback_shadowed));
                    }
                }
            }
            PseudoExpr::BinOp { left, right, .. } => {
                stack.push((left.as_ref(), fallback_shadowed));
                stack.push((right.as_ref(), fallback_shadowed));
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Force(operand)
            | PseudoExpr::Delay(operand) => stack.push((operand.as_ref(), fallback_shadowed)),
            PseudoExpr::Trace { message, value } => {
                stack.push((message.as_ref(), fallback_shadowed));
                stack.push((value.as_ref(), fallback_shadowed));
            }
            PseudoExpr::List { elements, tail } => {
                for element in elements {
                    stack.push((element, fallback_shadowed));
                }
                if let Some(tail) = tail {
                    stack.push((tail.as_ref(), fallback_shadowed));
                }
            }
            PseudoExpr::Tuple(elements) => {
                for element in elements {
                    stack.push((element, fallback_shadowed));
                }
            }
            PseudoExpr::Pair(a, b) => {
                stack.push((a.as_ref(), fallback_shadowed));
                stack.push((b.as_ref(), fallback_shadowed));
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields {
                    stack.push((field, fallback_shadowed));
                }
            }
            PseudoExpr::FieldAccess { record, .. } => {
                stack.push((record.as_ref(), fallback_shadowed));
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                stack.push((collection.as_ref(), fallback_shadowed));
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    stack.push((arg, fallback_shadowed));
                }
            }
            PseudoExpr::Int(_)
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

    false
}
