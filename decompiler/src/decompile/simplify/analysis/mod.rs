//! AST analysis and usage-count helpers for simplification.

mod capture;
mod use_counts;
mod value_form;

use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr};

use super::Simplifier;

impl Simplifier {
    /// Count the number of AST nodes in an expression (for inlining decisions).
    pub(crate) fn expr_size(expr: &PseudoExpr) -> usize {
        let mut size = 0usize;
        let mut stack = vec![expr];

        while let Some(current) = stack.pop() {
            size += 1;

            match current {
                PseudoExpr::Var { .. }
                | PseudoExpr::Int(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::String(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::HelperSymbol(_) => {}
                PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                    stack.push(body);
                }
                PseudoExpr::Apply { function, args } => {
                    stack.push(function);
                    stack.extend(args.iter().rev());
                }
                PseudoExpr::Let { value, body, .. } => {
                    stack.push(body);
                    stack.push(value);
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
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    for clause in clauses.iter().rev() {
                        stack.push(&clause.body);
                    }
                    stack.push(subject);
                }
                PseudoExpr::BinOp { left, right, .. } | PseudoExpr::Pair(left, right) => {
                    stack.push(right);
                    stack.push(left);
                }
                PseudoExpr::UnOp { operand, .. }
                | PseudoExpr::Force(operand)
                | PseudoExpr::Delay(operand)
                | PseudoExpr::FieldAccess {
                    record: operand, ..
                }
                | PseudoExpr::IndexAccess {
                    collection: operand,
                    ..
                } => {
                    stack.push(operand);
                }
                PseudoExpr::BuiltinCall { args, .. } | PseudoExpr::Constr { fields: args, .. } => {
                    stack.extend(args.iter().rev());
                }
                PseudoExpr::Trace { message, value } => {
                    stack.push(value);
                    stack.push(message);
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        stack.push(tail);
                    }
                    stack.extend(elements.iter().rev());
                }
                PseudoExpr::Tuple(elements) => {
                    stack.extend(elements.iter().rev());
                }
            }
        }

        size
    }

    fn is_projection_accessor_expr(expr: &PseudoExpr, param: &str, saw_projection: bool) -> bool {
        let mut current = expr;
        let mut saw_projection = saw_projection;
        loop {
            match current {
                PseudoExpr::Var { name, .. } => return saw_projection && name == param,
                PseudoExpr::FieldAccess { record, .. } => {
                    saw_projection = true;
                    current = record;
                }
                PseudoExpr::IndexAccess { collection, .. } => {
                    saw_projection = true;
                    current = collection;
                }
                PseudoExpr::BuiltinCall { name, args } if args.len() == 1 => {
                    if !name.is_projection_wrapper() {
                        return false;
                    }
                    saw_projection = saw_projection || name.starts_projection_chain();
                    current = &args[0];
                }
                PseudoExpr::Apply { function, args } if args.len() == 1 => {
                    match function.as_ref() {
                        PseudoExpr::BuiltinCall {
                            name,
                            args: builtin_args,
                        } if builtin_args.is_empty() => {
                            if !name.is_projection_wrapper() {
                                return false;
                            }
                            saw_projection = saw_projection || name.starts_projection_chain();
                            current = &args[0];
                        }
                        _ => return false,
                    }
                }
                _ => return false,
            }
        }
    }

    pub(crate) fn is_single_param_projection_accessor(
        params: &[Binder],
        body: &PseudoExpr,
    ) -> bool {
        if params.len() != 1 || params[0] == "_" {
            return false;
        }

        let param = params[0].as_str();
        Self::count_var_uses(body, param) == 1
            && !Self::contains_control_flow_expr(body)
            && Self::is_projection_accessor_expr(body, param, false)
    }

    pub(crate) fn is_small_delayed_call_wrapper(params: &[Binder], body: &PseudoExpr) -> bool {
        if params.is_empty() || params.iter().any(|param| param == "_") {
            return false;
        }

        let PseudoExpr::Delay(inner) = body else {
            return false;
        };

        if Self::contains_control_flow_expr(inner) || Self::expr_size(inner) > 7 {
            return false;
        }

        match inner.as_ref() {
            PseudoExpr::Apply { function, .. } => {
                let use_counts = Self::count_binding_uses(inner, params);
                (matches!(function.as_ref(), PseudoExpr::Var { .. })
                    || matches!(
                        function.as_ref(),
                        PseudoExpr::BuiltinCall { args, .. } if args.is_empty()
                    ))
                    && use_counts.iter().all(|count| *count <= 1)
                    && use_counts.iter().any(|count| *count > 0)
            }
            _ => false,
        }
    }

    pub(crate) fn is_small_boolean_helper(params: &[Binder], body: &PseudoExpr) -> bool {
        if params.is_empty() || Self::contains_control_flow_expr(body) || Self::expr_size(body) > 12
        {
            return false;
        }

        fn is_param_derived(expr: &PseudoExpr, params: &[Binder]) -> bool {
            let mut current = expr;
            loop {
                match current {
                    PseudoExpr::Var { name, .. } => {
                        return params.iter().any(|param| param == name.as_str());
                    }
                    PseudoExpr::Int(_)
                    | PseudoExpr::Bool(_)
                    | PseudoExpr::ByteArray(_)
                    | PseudoExpr::String(_)
                    | PseudoExpr::Unit => return true,
                    PseudoExpr::FieldAccess { record, .. } => current = record,
                    PseudoExpr::IndexAccess { collection, .. } => current = collection,
                    PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => current = inner,
                    PseudoExpr::Apply { function, args } => {
                        if !args.is_empty() {
                            return false;
                        }
                        current = function;
                    }
                    _ => return false,
                }
            }
        }

        fn is_boolean_expr(expr: &PseudoExpr, params: &[Binder]) -> bool {
            let mut pending: Vec<&PseudoExpr> = vec![expr];
            while let Some(current) = pending.pop() {
                match current {
                    PseudoExpr::Bool(_) => {}
                    PseudoExpr::UnOp {
                        op: crate::pseudo::ast::UnaryOp::Not,
                        operand,
                    } => pending.push(operand),
                    PseudoExpr::BinOp { op, left, right } => match op {
                        BinaryOp::And | BinaryOp::Or => {
                            pending.push(left);
                            pending.push(right);
                        }
                        BinaryOp::Eq
                        | BinaryOp::Neq
                        | BinaryOp::Lt
                        | BinaryOp::Lte
                        | BinaryOp::Gt
                        | BinaryOp::Gte => {
                            if !(is_param_derived(left, params) && is_param_derived(right, params))
                            {
                                return false;
                            }
                        }
                        _ => return false,
                    },
                    _ => return false,
                }
            }
            true
        }

        let use_counts = Self::count_binding_uses(body, params);
        is_boolean_expr(body, params)
            && params
                .iter()
                .zip(use_counts.iter())
                .filter(|(param, _)| param.as_str() != "_")
                .all(|(_, count)| *count <= 4)
    }
}

#[cfg(test)]
mod tests;
