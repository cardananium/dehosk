use crate::decompile::simplify::Simplifier;
use crate::pseudo::ast::PseudoExpr;

impl Simplifier {
    pub(crate) fn collect_referenced_vars(expr: &PseudoExpr, vars: &mut Vec<String>) {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Var { name, .. } => {
                    if !vars.contains(name) {
                        vars.push(name.clone());
                    }
                }
                PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                    pending.push(body);
                }
                PseudoExpr::Apply { function, args } => {
                    for a in args.iter().rev() {
                        pending.push(a);
                    }
                    pending.push(function);
                }
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(body);
                    pending.push(value);
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
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                PseudoExpr::UnOp { operand, .. } => {
                    pending.push(operand);
                }
                PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => {
                    pending.push(inner);
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    for a in args.iter().rev() {
                        pending.push(a);
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => {
                    pending.push(record);
                }
                PseudoExpr::IndexAccess { collection, .. } => {
                    pending.push(collection);
                }
                PseudoExpr::Constr { fields, .. } => {
                    for f in fields.iter().rev() {
                        pending.push(f);
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    pending.push(value);
                    pending.push(message);
                }
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    for c in clauses.iter().rev() {
                        pending.push(&c.body);
                    }
                    pending.push(subject);
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        pending.push(t);
                    }
                    for e in elements.iter().rev() {
                        pending.push(e);
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    pending.push(b);
                    pending.push(a);
                }
                _ => {}
            }
        }
    }

    pub(crate) fn has_binding_for_any(body: &PseudoExpr, var_names: &[String]) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![body];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Lambda { params, body: b } => {
                    if params
                        .iter()
                        .any(|p| var_names.iter().any(|name| name == p.as_str()))
                    {
                        return true;
                    }
                    pending.push(b);
                }
                PseudoExpr::RecFn {
                    name, params, body, ..
                } => {
                    if var_names.contains(&name.to_string())
                        || params.iter().any(|p| var_names.contains(&p.to_string()))
                    {
                        return true;
                    }
                    pending.push(body);
                }
                PseudoExpr::Let {
                    name, value, body, ..
                } => {
                    if var_names.contains(name) {
                        return true;
                    }
                    pending.push(value);
                    pending.push(body);
                }
                PseudoExpr::Apply { function, args } => {
                    pending.push(function);
                    pending.extend(args.iter());
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(condition);
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(left);
                    pending.push(right);
                }
                PseudoExpr::UnOp { operand, .. } => pending.push(operand),
                PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => pending.push(inner),
                PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
                PseudoExpr::FieldAccess { record, .. } => pending.push(record),
                PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
                PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
                PseudoExpr::Trace { message, value } => {
                    pending.push(message);
                    pending.push(value);
                }
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    pending.push(subject);
                    for c in clauses {
                        if var_names
                            .iter()
                            .any(|v| Self::pattern_binds_var(&c.pattern, v))
                        {
                            return true;
                        }
                        pending.push(&c.body);
                    }
                }
                PseudoExpr::List { elements, tail } => {
                    pending.extend(elements.iter());
                    if let Some(t) = tail.as_ref() {
                        pending.push(t);
                    }
                }
                PseudoExpr::Tuple(items) => pending.extend(items.iter()),
                PseudoExpr::Pair(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                _ => {}
            }
        }
        false
    }
}
