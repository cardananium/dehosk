use std::collections::HashSet;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};

use super::Simplifier;

impl Simplifier {
    pub(crate) fn is_generated_temp_name(name: &str) -> bool {
        if name == "_" {
            return true;
        }
        // `helper_*` and `fn_*` are both multi-param Lambda
        // generated names; the rename pass hints `helper`, not
        // the keyword `fn`, to avoid the `fn fn_` artifact.
        if name.starts_with("fn_")
            || name.starts_with("helper_")
            || name.starts_with("x_")
            || name.starts_with("y_")
            || name.starts_with("to_")
        {
            return true;
        }
        name.chars()
            .last()
            .map(|c| c.is_ascii_digit())
            .unwrap_or(false)
    }

    pub(crate) fn sanitize_name_stem(name: &str) -> String {
        let mut out = String::new();
        for ch in name.chars() {
            if ch.is_ascii_alphanumeric() {
                out.push(ch.to_ascii_lowercase());
            } else if ch == '_' && !out.ends_with('_') {
                out.push('_');
            }
        }
        out = out.trim_matches('_').to_string();
        if out.is_empty() {
            return out;
        }
        if out
            .chars()
            .next()
            .map(|c| c.is_ascii_digit())
            .unwrap_or(false)
        {
            out.insert(0, 'c');
        }
        out
    }

    pub(crate) fn fresh_readability_name(used: &mut HashSet<String>, base: String) -> String {
        let mut stem = Self::sanitize_name_stem(&base);
        if stem.is_empty() {
            stem = "value".to_string();
        }
        if !used.contains(&stem) {
            used.insert(stem.clone());
            return stem;
        }

        let mut idx = 2usize;
        loop {
            let candidate = format!("{}_{}", stem, idx);
            if !used.contains(&candidate) {
                used.insert(candidate.clone());
                return candidate;
            }
            idx += 1;
        }
    }

    pub(crate) fn collect_var_names(expr: &PseudoExpr, vars: &mut HashSet<String>) {
        enum Pending<'a> {
            Expr(&'a PseudoExpr),
            Pattern(&'a WhenPattern),
        }
        let mut pending = vec![Pending::Expr(expr)];
        while let Some(item) = pending.pop() {
            let expr = match item {
                Pending::Pattern(pattern) => {
                    match pattern {
                        WhenPattern::Wildcard => {}
                        WhenPattern::Literal(expr) => pending.push(Pending::Expr(expr)),
                        WhenPattern::Var(binder) => {
                            vars.insert(binder.to_string());
                        }
                        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                            Self::collect_binder_names(fields, vars);
                        }
                        WhenPattern::List { elements, tail } => {
                            Self::collect_binder_names(elements, vars);
                            if let Some(tail) = tail {
                                vars.insert(tail.to_string());
                            }
                        }
                        WhenPattern::Pair(a, b) => {
                            vars.insert(a.to_string());
                            vars.insert(b.to_string());
                        }
                    }
                    continue;
                }
                Pending::Expr(expr) => expr,
            };
            match expr {
                PseudoExpr::Var { name, .. } => {
                    vars.insert(name.clone());
                }
                PseudoExpr::Lambda { params, body } => {
                    Self::collect_binder_names(params, vars);
                    pending.push(Pending::Expr(body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    vars.insert(name.to_string());
                    Self::collect_binder_names(params, vars);
                    pending.push(Pending::Expr(body));
                }
                PseudoExpr::Delay(body) | PseudoExpr::Force(body) => {
                    pending.push(Pending::Expr(body));
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        pending.push(Pending::Expr(arg));
                    }
                    pending.push(Pending::Expr(function));
                }
                PseudoExpr::Let {
                    name, value, body, ..
                } => {
                    vars.insert(name.clone());
                    pending.push(Pending::Expr(body));
                    pending.push(Pending::Expr(value));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(Pending::Expr(else_branch));
                    pending.push(Pending::Expr(then_branch));
                    pending.push(Pending::Expr(condition));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    if let Some(subject_name) = subject_name {
                        vars.insert(subject_name.to_string());
                    }
                    for clause in clauses.iter().rev() {
                        pending.push(Pending::Expr(&clause.body));
                        if let Some(guard) = &clause.guard {
                            pending.push(Pending::Expr(guard));
                        }
                        pending.push(Pending::Pattern(&clause.pattern));
                    }
                    pending.push(Pending::Expr(subject));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        pending.push(Pending::Expr(t));
                    }
                    for el in elements.iter().rev() {
                        pending.push(Pending::Expr(el));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for item in items.iter().rev() {
                        pending.push(Pending::Expr(item));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    pending.push(Pending::Expr(b));
                    pending.push(Pending::Expr(a));
                }
                PseudoExpr::Constr { fields, .. } => {
                    for field in fields.iter().rev() {
                        pending.push(Pending::Expr(field));
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => pending.push(Pending::Expr(record)),
                PseudoExpr::IndexAccess { collection, .. } => {
                    pending.push(Pending::Expr(collection))
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(Pending::Expr(right));
                    pending.push(Pending::Expr(left));
                }
                PseudoExpr::UnOp { operand, .. } => pending.push(Pending::Expr(operand)),
                PseudoExpr::BuiltinCall { args, .. } => {
                    for arg in args.iter().rev() {
                        pending.push(Pending::Expr(arg));
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    pending.push(Pending::Expr(value));
                    pending.push(Pending::Expr(message));
                }
                PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::HelperSymbol(_) => {}
            }
        }
    }

    fn collect_binder_names(binders: &[Binder], vars: &mut HashSet<String>) {
        for binder in binders {
            vars.insert(binder.to_string());
        }
    }
}
