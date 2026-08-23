use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::decompile::constructor_data::{
    is_standard_option_none_candidate, is_standard_option_some_candidate,
};
use crate::decompile::mid::type_env::TypeEnvironment;
use crate::pseudo::ast::{PseudoExpr, PseudoType, WhenClause, WhenPattern};
use crate::pseudo::constructor::KnownConstructor;
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

pub(crate) fn rewrite_option_cps_calls(
    expr: PseudoExpr,
    _env: Option<&TypeEnvironment>,
) -> PseudoExpr {
    OptionCpsLateRewriter::rewrite(expr)
}

pub(crate) fn try_rewrite_option_cps_apply(
    function: PseudoExpr,
    args: Vec<PseudoExpr>,
    option_like_callee: bool,
) -> Option<PseudoExpr> {
    try_rewrite_option_cps_apply_with_reserved(function, args, option_like_callee, None)
}

fn try_rewrite_option_cps_apply_with_reserved(
    function: PseudoExpr,
    args: Vec<PseudoExpr>,
    option_like_callee: bool,
    reserved_let_names: Option<&mut HashSet<String>>,
) -> Option<PseudoExpr> {
    if args.len() < 3 || !(function_returns_option(&function) || option_like_callee) {
        return None;
    }

    let fail_branch = args.last()?.clone();
    if !is_fail_body(&fail_branch) {
        return None;
    }

    let PseudoExpr::Lambda {
        params: success_params,
        body: success_body,
    } = args[args.len() - 2].clone()
    else {
        return None;
    };

    if success_params.len() != 1 {
        return None;
    }

    let mut core_args = args[..args.len() - 2].to_vec();
    if core_args.len() >= 2 && should_strip_recursive_self_arg(&function, &core_args[0]) {
        core_args.remove(0);
    }

    let clauses = vec![
        WhenClause::new(
            WhenPattern::constructor_known(KnownConstructor::Some, vec![success_params[0].clone()]),
            success_body.into_inner(),
        ),
        WhenClause::new(
            WhenPattern::constructor_known(KnownConstructor::None, vec![]),
            fail_branch,
        ),
    ];

    Some(match function {
        PseudoExpr::RecFn { name, params, body } => {
            let let_name = reserved_let_names.map_or_else(
                || name.to_string(),
                |reserved| fresh_let_name(name.as_str(), reserved),
            );
            let subject = PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::var_with_id(let_name.clone(), name.id)),
                args: core_args.into(),
            };
            PseudoExpr::Let {
                name: let_name,
                id: Some(name.id),
                value: PBox::new(PseudoExpr::RecFn { name, params, body }),
                body: PBox::new(PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name: None,
                    clauses,
                }),
            }
        }
        other => PseudoExpr::When {
            subject: PBox::new(PseudoExpr::Apply {
                function: PBox::new(other),
                args: core_args.into(),
            }),
            subject_name: None,
            clauses,
        },
    })
}

struct OptionCpsLateRewriter {
    option_like_bindings: Vec<HashSet<VarId>>,
    used_let_names: HashSet<String>,
}

impl OptionCpsLateRewriter {
    fn rewrite(expr: PseudoExpr) -> PseudoExpr {
        let used_let_names = collect_let_names(&expr);
        Self {
            option_like_bindings: vec![HashSet::new()],
            used_let_names,
        }
        .rewrite_expr(expr)
    }

    fn rewrite_expr(&mut self, expr: PseudoExpr) -> PseudoExpr {
        ExprFolder::fold(self, expr)
    }

    fn is_option_like_binding(&self, id: VarId) -> bool {
        self.option_like_bindings
            .iter()
            .rev()
            .any(|scope| scope.contains(&id))
    }

    fn is_option_like_fn_value(&self, expr: &PseudoExpr) -> bool {
        let mut current = expr;
        loop {
            match current {
                PseudoExpr::RecFn { name, params, body } => {
                    let mut recursive_ids = HashSet::new();
                    let mut recursive_names = HashSet::new();
                    recursive_ids.insert(name.id);
                    recursive_names.insert(name.name.clone());
                    if let Some(first_param) = params.first() {
                        recursive_ids.insert(first_param.id);
                        recursive_names.insert(first_param.name.clone());
                    }
                    return self.body_returns_option_like(body, &recursive_ids, &recursive_names);
                }
                PseudoExpr::Lambda { params, body } => {
                    let mut recursive_ids = HashSet::new();
                    let mut recursive_names = HashSet::new();
                    if let Some(first_param) = params.first() {
                        recursive_ids.insert(first_param.id);
                        recursive_names.insert(first_param.name.clone());
                    }
                    return self.body_returns_option_like(body, &recursive_ids, &recursive_names);
                }
                PseudoExpr::Let { body, .. } => current = body,
                _ => return false,
            }
        }
    }

    fn body_returns_option_like(
        &self,
        expr: &PseudoExpr,
        recursive_ids: &HashSet<VarId>,
        recursive_names: &HashSet<String>,
    ) -> bool {
        // Unlike the usual existential (`||`) search, this predicate is a
        // universal (`&&`/`.all()`) one: `If` requires BOTH branches to
        // qualify, `When` requires ALL clause bodies to. So the worklist is
        // inverted from the usual template — default to "all satisfied" and
        // bail out `false` the moment any queued node fails, instead of
        // defaulting to `false` and returning `true` on a hit. Order doesn't
        // matter: this is a pure boolean predicate with no side effects, so
        // AND is associative/commutative regardless of visit order.
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                expr if is_standard_option_some_candidate(expr)
                    || is_standard_option_none_candidate(expr) => {}
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                PseudoExpr::When { clauses, .. } if !clauses.is_empty() => {
                    pending.extend(clauses.iter().map(|clause| &clause.body));
                }
                PseudoExpr::Let { body, .. } => pending.push(body),
                PseudoExpr::Trace { value, .. } => pending.push(value),
                PseudoExpr::Apply { function, .. } => {
                    let ok = matches!(
                        function.as_ref(),
                        PseudoExpr::Var { name, id, .. }
                            if id.is_some_and(|v| recursive_ids.contains(&v))
                                || recursive_names.contains(name)
                                || id.is_some_and(|v| self.is_option_like_binding(v))
                    );
                    if !ok {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

impl ExprFolder for OptionCpsLateRewriter {
    // Runs before the value is folded: insert the binder name into
    // `used_let_names` before walking `value`.
    fn pre_let(
        &mut self,
        name: &str,
        _id: &Option<VarId>,
        _value: &PseudoExpr,
        _body: &PseudoExpr,
    ) -> FoldAction {
        self.used_let_names.insert(name.to_string());
        FoldAction::Walk
    }

    fn enter_let(&mut self, name: &str, id: &Option<VarId>, value: &PseudoExpr) -> String {
        let option_like_value = self.is_option_like_fn_value(value);
        self.option_like_bindings.push(HashSet::new());
        if option_like_value && let Some(id_val) = id {
            self.option_like_bindings
                .last_mut()
                .expect("pushed scope")
                .insert(*id_val);
        }
        name.to_string()
    }

    fn exit_let(&mut self, _name: &str) {
        self.option_like_bindings.pop();
    }

    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        let option_like_callee = self.is_option_like_fn_value(&function)
            || matches!(
                &function,
                PseudoExpr::Var { id: Some(var_id), .. } if self.is_option_like_binding(*var_id)
            );
        try_rewrite_option_cps_apply_with_reserved(
            function.clone(),
            args.clone(),
            option_like_callee,
            Some(&mut self.used_let_names),
        )
        .unwrap_or(PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        })
    }

    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }
}

fn collect_let_names(expr: &PseudoExpr) -> HashSet<String> {
    fn go(expr: &PseudoExpr, out: &mut HashSet<String>) {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(cur) = pending.pop() {
            match cur {
                PseudoExpr::Let {
                    name, value, body, ..
                } => {
                    out.insert(name.clone());
                    pending.push(body);
                    pending.push(value);
                }
                PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                    pending.push(body);
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
                    }
                    pending.push(function);
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(else_branch);
                    pending.push(then_branch);
                    pending.push(condition);
                }
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    for clause in clauses.iter().rev() {
                        pending.push(&clause.body);
                        if let Some(guard) = &clause.guard {
                            pending.push(guard);
                        }
                        if let WhenPattern::Literal(lit) = &clause.pattern {
                            pending.push(lit);
                        }
                    }
                    pending.push(subject);
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        pending.push(tail);
                    }
                    for element in elements.iter().rev() {
                        pending.push(element);
                    }
                }
                PseudoExpr::Tuple(elements) => {
                    for element in elements.iter().rev() {
                        pending.push(element);
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    pending.push(b);
                    pending.push(a);
                }
                PseudoExpr::Constr { fields, .. } => {
                    for field in fields.iter().rev() {
                        pending.push(field);
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => pending.push(record),
                PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                PseudoExpr::UnOp { operand, .. }
                | PseudoExpr::Delay(operand)
                | PseudoExpr::Force(operand) => pending.push(operand),
                PseudoExpr::Trace { message, value } => {
                    pending.push(value);
                    pending.push(message);
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    for arg in args.iter().rev() {
                        pending.push(arg);
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
    }

    let mut names = HashSet::new();
    go(expr, &mut names);
    names
}

fn fresh_let_name(base: &str, used: &mut HashSet<String>) -> String {
    if used.insert(base.to_string()) {
        return base.to_string();
    }

    let mut suffix = 2usize;
    loop {
        let candidate = format!("{base}_{suffix}");
        if used.insert(candidate.clone()) {
            return candidate;
        }
        suffix += 1;
    }
}

fn is_fail_body(expr: &PseudoExpr) -> bool {
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Error { .. } => return true,
            PseudoExpr::Trace { value, .. } => current = value,
            _ => return false,
        }
    }
}

fn function_returns_option(expr: &PseudoExpr) -> bool {
    matches!(
        expr.type_resolution().as_known().map(|tipo| tipo.as_ref()),
        Some(PseudoType::Function { ret, .. }) if matches!(ret.as_ref(), PseudoType::Option(_))
    )
}

fn should_strip_recursive_self_arg(function: &PseudoExpr, first_arg: &PseudoExpr) -> bool {
    let function_identity: Option<(&str, Option<VarId>)> = match function {
        PseudoExpr::Var { name, id, .. } => Some((name.as_str(), *id)),
        PseudoExpr::RecFn { name, .. } => Some((name.as_str(), Some(name.id))),
        _ => None,
    };

    let Some((function_name, function_id)) = function_identity else {
        return false;
    };

    // compat refs carry `id: None`, so the y-comb helper is matched by name
    // and self-recursion falls back to `refs_match`'s name comparison.
    let PseudoExpr::Var {
        name: arg_name,
        id: arg_id,
        ..
    } = first_arg
    else {
        return false;
    };

    if arg_name.starts_with("__y_comb_") {
        return true;
    }

    crate::decompile::var_match::refs_match(
        function_name,
        function_id.and_then(|v| v.get()),
        arg_name,
        arg_id.get(),
    )
}

#[cfg(test)]
mod tests;
