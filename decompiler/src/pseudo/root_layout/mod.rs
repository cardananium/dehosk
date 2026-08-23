use std::collections::HashSet;

use super::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use super::var_id::VarId;

pub(crate) enum RootHelper<'a> {
    RecFn {
        let_expr: &'a PseudoExpr,
        expr: &'a PseudoExpr,
    },
    Lambda {
        let_expr: &'a PseudoExpr,
        expr: &'a PseudoExpr,
        name: &'a str,
        var_id: VarId,

        params: &'a [Binder],
        body: &'a PseudoExpr,
    },
}

pub(crate) struct RootLambdaWithHelpers<'a> {
    pub(crate) lambda_expr: &'a PseudoExpr,
    pub(crate) params: &'a [Binder],
    pub(crate) body: &'a PseudoExpr,
    pub(crate) helpers: Vec<RootHelper<'a>>,
}

pub(crate) struct RootParameter<'a> {
    pub(crate) let_expr: &'a PseudoExpr,
    pub(crate) name: &'a str,
    pub(crate) var_id: VarId,
    pub(crate) value: &'a PseudoExpr,
}

pub(crate) struct RootParametrizedScript<'a> {
    pub(crate) parameters: Vec<RootParameter<'a>>,
    pub(crate) main: RootLambdaWithHelpers<'a>,
}

pub(crate) enum RootRenderLayout<'a> {
    Plain(&'a PseudoExpr),
    LambdaWithHelpers(RootLambdaWithHelpers<'a>),
    Parametrized(RootParametrizedScript<'a>),
}

pub(crate) fn prepare_root_render_layout<'a>(expr: &'a PseudoExpr) -> RootRenderLayout<'a> {
    let (parameters, after_params) = collect_applied_parameters(expr);
    if !parameters.is_empty()
        && let Some(main) =
            collect_root_helper_chain_before_lambda(after_params).or_else(|| match after_params {
                PseudoExpr::Lambda { params, body } => {
                    let (helpers, stripped_body) = collect_root_lambda_body_helpers(body, params);
                    Some(RootLambdaWithHelpers {
                        lambda_expr: after_params,
                        params,
                        body: stripped_body,
                        helpers,
                    })
                }
                _ => None,
            })
    {
        return RootRenderLayout::Parametrized(RootParametrizedScript { parameters, main });
    }

    if let Some(layout) = collect_root_helper_chain_before_lambda(expr) {
        return RootRenderLayout::LambdaWithHelpers(layout);
    }

    match expr {
        PseudoExpr::Lambda { params, body } => {
            let (helpers, stripped_body) = collect_root_lambda_body_helpers(body, params);
            if helpers.is_empty() {
                RootRenderLayout::Plain(expr)
            } else {
                RootRenderLayout::LambdaWithHelpers(RootLambdaWithHelpers {
                    lambda_expr: expr,
                    params,
                    body: stripped_body,
                    helpers,
                })
            }
        }
        _ => RootRenderLayout::Plain(expr),
    }
}

fn is_applied_parameter_value(expr: &PseudoExpr) -> bool {
    // The original is an AND over every element/field/item (`.all()`,
    // `&&`, `is_none_or`), not an existential search: this worklist mirrors
    // that by returning `false` the instant it meets a node that fails the
    // leaf check, and otherwise keeps expanding — the AND is pure, so
    // evaluation order doesn't change the answer.
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(tail) = tail.as_deref() {
                    pending.push(tail);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items.iter()),
            PseudoExpr::Pair(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            _ => return false,
        }
    }
    true
}

fn collect_applied_parameters<'a>(
    mut expr: &'a PseudoExpr,
) -> (Vec<RootParameter<'a>>, &'a PseudoExpr) {
    let mut parameters = Vec::new();
    while let PseudoExpr::Let {
        name,
        id,
        value,
        body,
    } = expr
    {
        if !is_applied_parameter_value(value.as_ref()) {
            break;
        }
        parameters.push(RootParameter {
            let_expr: expr,
            name,
            var_id: id.unwrap_or_else(VarId::fresh_compat_placeholder),
            value: value.as_ref(),
        });
        expr = body.as_ref();
    }
    (parameters, expr)
}

fn collect_root_helper_chain_before_lambda<'a>(
    mut expr: &'a PseudoExpr,
) -> Option<RootLambdaWithHelpers<'a>> {
    let mut helpers = Vec::new();

    while let PseudoExpr::Let {
        name,
        id,
        value,
        body,
        ..
    } = expr
    {
        match value.as_ref() {
            PseudoExpr::RecFn { name: fn_name, .. } if fn_name == name => {
                helpers.push(RootHelper::RecFn {
                    let_expr: expr,
                    expr: value.as_ref(),
                });
                expr = body.as_ref();
            }
            PseudoExpr::Lambda {
                params,
                body: lambda_body,
            } if !uses_var_as_control_subject(
                body.as_ref(),
                id.unwrap_or_else(VarId::fresh_compat_placeholder),
                name,
            ) =>
            {
                helpers.push(RootHelper::Lambda {
                    let_expr: expr,
                    expr: value.as_ref(),
                    name,
                    var_id: id.unwrap_or_else(VarId::fresh_compat_placeholder),
                    params,
                    body: lambda_body.as_ref(),
                });
                expr = body.as_ref();
            }
            _ => break,
        }
    }

    if helpers.is_empty() {
        return None;
    }

    match expr {
        PseudoExpr::Lambda { params, body } => {
            let (body_helpers, stripped_body) = collect_root_lambda_body_helpers(body, params);
            helpers.extend(body_helpers);
            Some(RootLambdaWithHelpers {
                lambda_expr: expr,
                params,
                body: stripped_body,
                helpers,
            })
        }
        _ => None,
    }
}

fn helper_value_free_vars(expr: &PseudoExpr) -> HashSet<VarId> {
    /// One pending step of the scoped, read-only free-variable walk below.
    enum Step<'a> {
        Visit(&'a PseudoExpr),
        EnterLambdaBody {
            params: &'a [Binder],
            body: &'a PseudoExpr,
        },
        EnterRecFnBody {
            name: &'a Binder,
            params: &'a [Binder],
            body: &'a PseudoExpr,
        },
        /// A `let`'s bound id comes into scope BETWEEN its value (walked
        /// already, outside any new binding) and its body.
        EnterLetBody {
            id: Option<VarId>,
            body: &'a PseudoExpr,
        },
        EnterClause {
            subject_name: Option<&'a Binder>,
            clause: &'a WhenClause,
        },
        /// Remove exactly the ids a scope ADDED — never ones it shadowed,
        /// which some enclosing scope already bound and must survive.
        Unbind(Vec<VarId>),
    }

    let mut bound: HashSet<VarId> = HashSet::new();
    let mut free: HashSet<VarId> = HashSet::new();
    let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];

    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(expr) => match expr {
                PseudoExpr::Var { id, .. } => {
                    if let Some(v) = *id
                        && !bound.contains(&v)
                    {
                        free.insert(v);
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(Step::EnterLambdaBody { params, body });
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(Step::EnterRecFnBody { name, params, body });
                }
                PseudoExpr::Let {
                    id, value, body, ..
                } => {
                    steps.push(Step::EnterLetBody { id: *id, body });
                    steps.push(Step::Visit(value));
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        steps.push(Step::Visit(arg));
                    }
                    steps.push(Step::Visit(function));
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
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail.as_deref() {
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
                PseudoExpr::Pair(left, right) | PseudoExpr::BinOp { left, right, .. } => {
                    steps.push(Step::Visit(right));
                    steps.push(Step::Visit(left));
                }
                PseudoExpr::Constr { fields, .. }
                | PseudoExpr::BuiltinCall { args: fields, .. } => {
                    for field in fields.iter().rev() {
                        steps.push(Step::Visit(field));
                    }
                }
                PseudoExpr::FieldAccess { record, .. }
                | PseudoExpr::Delay(record)
                | PseudoExpr::Force(record) => steps.push(Step::Visit(record)),
                PseudoExpr::IndexAccess { collection, .. } => steps.push(Step::Visit(collection)),
                PseudoExpr::UnOp {
                    operand: record, ..
                } => steps.push(Step::Visit(record)),
                PseudoExpr::Trace { message, value } => {
                    steps.push(Step::Visit(value));
                    steps.push(Step::Visit(message));
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
            },
            Step::EnterLambdaBody { params, body } => {
                let added: Vec<VarId> = params
                    .iter()
                    .map(|param| param.id)
                    .filter(|id| bound.insert(*id))
                    .collect();
                steps.push(Step::Unbind(added));
                steps.push(Step::Visit(body));
            }
            Step::EnterRecFnBody { name, params, body } => {
                let mut added = Vec::new();
                if bound.insert(name.id) {
                    added.push(name.id);
                }
                added.extend(
                    params
                        .iter()
                        .map(|param| param.id)
                        .filter(|id| bound.insert(*id)),
                );
                steps.push(Step::Unbind(added));
                steps.push(Step::Visit(body));
            }
            Step::EnterLetBody { id, body } => {
                let inserted = id.map(|v| bound.insert(v)).unwrap_or(false);
                let added = if inserted {
                    id.into_iter().collect()
                } else {
                    Vec::new()
                };
                steps.push(Step::Unbind(added));
                steps.push(Step::Visit(body));
            }
            Step::EnterClause {
                subject_name,
                clause,
            } => {
                let mut added = Vec::new();
                if let Some(subject_name) = subject_name
                    && bound.insert(subject_name.id)
                {
                    added.push(subject_name.id);
                }
                match &clause.pattern {
                    WhenPattern::Constructor { fields, .. } => added.extend(
                        fields
                            .iter()
                            .map(|field| field.id)
                            .filter(|id| bound.insert(*id)),
                    ),
                    WhenPattern::List { elements, tail } => {
                        added.extend(
                            elements
                                .iter()
                                .map(|element| element.id)
                                .filter(|id| bound.insert(*id)),
                        );
                        if let Some(tail) = tail
                            && bound.insert(tail.id)
                        {
                            added.push(tail.id);
                        }
                    }
                    WhenPattern::Tuple(fields) => added.extend(
                        fields
                            .iter()
                            .map(|field| field.id)
                            .filter(|id| bound.insert(*id)),
                    ),
                    WhenPattern::Pair(a, b) => {
                        if bound.insert(a.id) {
                            added.push(a.id);
                        }
                        if bound.insert(b.id) {
                            added.push(b.id);
                        }
                    }
                    WhenPattern::Var(v) => {
                        if bound.insert(v.id) {
                            added.push(v.id);
                        }
                    }
                    WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
                }
                steps.push(Step::Unbind(added));
                steps.push(Step::Visit(&clause.body));
                if let Some(guard) = &clause.guard {
                    steps.push(Step::Visit(guard));
                }
            }
            Step::Unbind(added) => {
                for id in added {
                    bound.remove(&id);
                }
            }
        }
    }

    free
}

fn collect_root_lambda_body_helpers<'a>(
    mut body: &'a PseudoExpr,
    lambda_params: &'a [Binder],
) -> (Vec<RootHelper<'a>>, &'a PseudoExpr) {
    let mut helpers = Vec::new();
    let lambda_param_ids: HashSet<VarId> = lambda_params.iter().map(|param| param.id).collect();

    loop {
        let PseudoExpr::Let {
            name,
            id,
            value,
            body: next_body,
            ..
        } = body
        else {
            break;
        };

        let free = helper_value_free_vars(value.as_ref());
        let captures_lambda_param = free
            .iter()
            .any(|free_id| lambda_param_ids.contains(free_id));
        match value.as_ref() {
            PseudoExpr::RecFn { name: fn_name, .. }
                if fn_name == name && !captures_lambda_param =>
            {
                helpers.push(RootHelper::RecFn {
                    let_expr: body,
                    expr: value.as_ref(),
                });
                body = next_body.as_ref();
            }
            PseudoExpr::Lambda {
                params,
                body: lambda_body,
            } if !uses_var_as_control_subject(
                next_body.as_ref(),
                id.unwrap_or_else(VarId::fresh_compat_placeholder),
                name,
            ) && !captures_lambda_param =>
            {
                helpers.push(RootHelper::Lambda {
                    let_expr: body,
                    expr: value.as_ref(),
                    name,
                    var_id: id.unwrap_or_else(VarId::fresh_compat_placeholder),
                    params,
                    body: lambda_body.as_ref(),
                });
                body = next_body.as_ref();
            }
            _ => break,
        }
    }

    (helpers, body)
}

fn matches_var_or_forced_var(expr: &PseudoExpr, target: VarId, target_name: &str) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Var { id, name, .. } => {
                if *id == Some(target) || name == target_name {
                    return true;
                }
            }
            PseudoExpr::Force(inner) => pending.push(inner.as_ref()),
            _ => {}
        }
    }
    false
}

fn binder_matches_target(binder: &Binder, target: VarId, target_name: &str) -> bool {
    binder.id == target || binder.name == target_name
}

fn pattern_binds_id(pattern: &WhenPattern, target: VarId, target_name: &str) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } => fields
            .iter()
            .any(|f| binder_matches_target(f, target, target_name)),
        WhenPattern::List { elements, tail } => {
            elements
                .iter()
                .any(|e| binder_matches_target(e, target, target_name))
                || tail
                    .as_ref()
                    .is_some_and(|t| binder_matches_target(t, target, target_name))
        }
        WhenPattern::Tuple(items) => items
            .iter()
            .any(|i| binder_matches_target(i, target, target_name)),
        WhenPattern::Pair(a, b) => {
            binder_matches_target(a, target, target_name)
                || binder_matches_target(b, target, target_name)
        }
        WhenPattern::Var(name) => binder_matches_target(name, target, target_name),
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}

pub(crate) fn uses_var_as_control_subject(
    expr: &PseudoExpr,
    target: VarId,
    target_name: &str,
) -> bool {
    let mut stack: Vec<(&PseudoExpr, bool)> = vec![(expr, false)];

    while let Some((current, shadowed)) = stack.pop() {
        match current {
            PseudoExpr::Lambda { params, body } => {
                let next_shadowed = shadowed
                    || params
                        .iter()
                        .any(|p| binder_matches_target(p, target, target_name));
                stack.push((body.as_ref(), next_shadowed));
            }
            PseudoExpr::RecFn { name, params, body } => {
                let next_shadowed = shadowed
                    || binder_matches_target(name, target, target_name)
                    || params
                        .iter()
                        .any(|p| binder_matches_target(p, target, target_name));
                stack.push((body.as_ref(), next_shadowed));
            }
            PseudoExpr::Let {
                id,
                name,
                value,
                body,
                ..
            } => {
                stack.push((value.as_ref(), shadowed));
                let body_shadowed = shadowed || *id == Some(target) || name == target_name;
                stack.push((body.as_ref(), body_shadowed));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                if !shadowed && matches_var_or_forced_var(condition.as_ref(), target, target_name) {
                    return true;
                }
                stack.push((condition.as_ref(), shadowed));
                stack.push((then_branch.as_ref(), shadowed));
                stack.push((else_branch.as_ref(), shadowed));
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                if !shadowed && matches_var_or_forced_var(subject.as_ref(), target, target_name) {
                    return true;
                }
                stack.push((subject.as_ref(), shadowed));
                for clause in clauses {
                    let clause_shadowed = shadowed
                        || subject_name
                            .as_ref()
                            .is_some_and(|n| binder_matches_target(n, target, target_name))
                        || pattern_binds_id(&clause.pattern, target, target_name);
                    if let Some(guard) = &clause.guard {
                        stack.push((guard, clause_shadowed));
                    }
                    stack.push((&clause.body, clause_shadowed));
                    if let WhenPattern::Literal(lit) = &clause.pattern {
                        stack.push((lit, shadowed));
                    }
                }
            }
            PseudoExpr::Apply { function, args } => {
                stack.push((function.as_ref(), shadowed));
                for arg in args {
                    stack.push((arg, shadowed));
                }
            }
            PseudoExpr::List { elements, tail } => {
                for element in elements {
                    stack.push((element, shadowed));
                }
                if let Some(tail_expr) = tail {
                    stack.push((tail_expr.as_ref(), shadowed));
                }
            }
            PseudoExpr::Tuple(items) => {
                for item in items {
                    stack.push((item, shadowed));
                }
            }
            PseudoExpr::Pair(left, right) | PseudoExpr::BinOp { left, right, .. } => {
                stack.push((left.as_ref(), shadowed));
                stack.push((right.as_ref(), shadowed));
            }
            PseudoExpr::Constr { fields, .. } => {
                for field in fields {
                    stack.push((field, shadowed));
                }
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    stack.push((arg, shadowed));
                }
            }
            PseudoExpr::FieldAccess { record, .. } => {
                stack.push((record.as_ref(), shadowed));
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                stack.push((collection.as_ref(), shadowed));
            }
            PseudoExpr::UnOp { operand, .. }
            | PseudoExpr::Delay(operand)
            | PseudoExpr::Force(operand) => {
                stack.push((operand.as_ref(), shadowed));
            }
            PseudoExpr::Trace { message, value } => {
                stack.push((message.as_ref(), shadowed));
                stack.push((value.as_ref(), shadowed));
            }
            PseudoExpr::Var { .. }
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(..)
            | PseudoExpr::HelperSymbol(_)
            | PseudoExpr::Int(..)
            | PseudoExpr::ByteArray(..)
            | PseudoExpr::String(..)
            | PseudoExpr::Bool(..)
            | PseudoExpr::Unit => {}
        }
    }

    false
}

#[cfg(test)]
mod tests;
