use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

use super::Simplifier;

impl Simplifier {
    pub(crate) fn ref_matches_var_id(
        name: &str,
        id: Option<VarId>,
        var_name: &str,
        var_id: Option<VarId>,
    ) -> bool {
        // `.get()` strips compat-placeholder ids on the ref side so a
        // compat-id ref falls back to name comparison against an auth-id
        // target. Without the strip `(Some(compat), Some(auth))` compares
        // as unequal ids and the match misses compat refs.
        crate::decompile::var_match::refs_match(name, id.get(), var_name, var_id)
    }

    pub(crate) fn binder_matches_var_id(
        binder: &Binder,
        var_name: &str,
        var_id: Option<VarId>,
    ) -> bool {
        crate::decompile::var_match::refs_match(binder.as_str(), binder.id.get(), var_name, var_id)
    }

    pub(crate) fn is_closed_expr(expr: &PseudoExpr) -> bool {
        enum Step<'e> {
            Visit(&'e PseudoExpr),
            /// Restore `bound` to a length a now-finished scope grew from.
            PopTo(usize),
            EnterLetBody {
                name: &'e str,
                body: &'e PseudoExpr,
            },
            /// Subject confirmed closed: bind its name (if any) for every
            /// clause, then walk the clauses, then drop that binding.
            EnterWhenClauses {
                subject_name: &'e Option<Binder>,
                clauses: &'e [WhenClause],
            },
            Clause(&'e WhenClause),
        }

        let mut bound: Vec<String> = Vec::new();
        let mut steps: Vec<Step> = vec![Step::Visit(expr)];

        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(e) => match e {
                    PseudoExpr::Var { name, .. } => {
                        if !bound.iter().any(|n| n == name) {
                            return false;
                        }
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let old_len = bound.len();
                        bound.extend(params.iter().map(ToString::to_string));
                        steps.push(Step::PopTo(old_len));
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let old_len = bound.len();
                        bound.push(name.to_string());
                        bound.extend(params.iter().map(ToString::to_string));
                        steps.push(Step::PopTo(old_len));
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for a in args.iter().rev() {
                            steps.push(Step::Visit(a));
                        }
                        steps.push(Step::Visit(function));
                    }
                    PseudoExpr::Let {
                        name, value, body, ..
                    } => {
                        steps.push(Step::EnterLetBody { name, body });
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
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        steps.push(Step::EnterWhenClauses {
                            subject_name,
                            clauses,
                        });
                        steps.push(Step::Visit(subject));
                    }
                    PseudoExpr::BinOp { left, right, .. } => {
                        steps.push(Step::Visit(right));
                        steps.push(Step::Visit(left));
                    }
                    PseudoExpr::UnOp { operand, .. } => steps.push(Step::Visit(operand)),
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for a in args.iter().rev() {
                            steps.push(Step::Visit(a));
                        }
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(t) = tail.as_ref() {
                            steps.push(Step::Visit(t));
                        }
                        for e in elements.iter().rev() {
                            steps.push(Step::Visit(e));
                        }
                    }
                    PseudoExpr::Tuple(elements) => {
                        for e in elements.iter().rev() {
                            steps.push(Step::Visit(e));
                        }
                    }
                    PseudoExpr::Pair(first, second) => {
                        steps.push(Step::Visit(second));
                        steps.push(Step::Visit(first));
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for f in fields.iter().rev() {
                            steps.push(Step::Visit(f));
                        }
                    }
                    PseudoExpr::FieldAccess { record, .. } => steps.push(Step::Visit(record)),
                    PseudoExpr::IndexAccess { collection, .. } => {
                        steps.push(Step::Visit(collection))
                    }
                    PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => {
                        steps.push(Step::Visit(inner))
                    }
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
                Step::PopTo(len) => bound.truncate(len),
                Step::EnterLetBody { name, body } => {
                    let old_len = bound.len();
                    bound.push(name.to_string());
                    steps.push(Step::PopTo(old_len));
                    steps.push(Step::Visit(body));
                }
                Step::EnterWhenClauses {
                    subject_name,
                    clauses,
                } => {
                    let old_len = bound.len();
                    if let Some(name) = subject_name {
                        bound.push(name.to_string());
                    }
                    steps.push(Step::PopTo(old_len));
                    for c in clauses.iter().rev() {
                        steps.push(Step::Clause(c));
                    }
                }
                Step::Clause(c) => {
                    let clause_old_len = bound.len();
                    steps.push(Step::PopTo(clause_old_len));
                    match &c.pattern {
                        WhenPattern::Constructor { fields, .. } => {
                            bound.extend(fields.iter().map(ToString::to_string));
                        }
                        WhenPattern::List { elements, tail } => {
                            bound.extend(elements.iter().map(ToString::to_string));
                            if let Some(t) = tail {
                                bound.push(t.to_string());
                            }
                        }
                        WhenPattern::Tuple(fields) => {
                            bound.extend(fields.iter().map(ToString::to_string))
                        }
                        WhenPattern::Pair(a, b) => {
                            bound.push(a.to_string());
                            bound.push(b.to_string());
                        }
                        WhenPattern::Var(name) => bound.push(name.to_string()),
                        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
                    }
                    steps.push(Step::Visit(&c.body));
                    if let Some(guard) = &c.guard {
                        steps.push(Step::Visit(guard));
                    }
                    if let WhenPattern::Literal(lit) = &c.pattern {
                        steps.push(Step::Visit(lit));
                    }
                }
            }
        }

        true
    }

    pub(crate) fn pattern_binds_var(pattern: &WhenPattern, var_name: &str) -> bool {
        match pattern {
            WhenPattern::Constructor { fields, .. } => fields.iter().any(|f| f == var_name),
            WhenPattern::List { elements, tail } => {
                elements.iter().any(|e| e == var_name)
                    || tail.as_ref().is_some_and(|t| t == var_name)
            }
            WhenPattern::Tuple(fields) => fields.iter().any(|f| f == var_name),
            WhenPattern::Pair(a, b) => a == var_name || b == var_name,
            WhenPattern::Var(name) => name == var_name,
            WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
        }
    }

    pub(crate) fn pattern_binds_var_id(
        pattern: &WhenPattern,
        var_name: &str,
        var_id: Option<VarId>,
    ) -> bool {
        match pattern {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => fields
                .iter()
                .any(|field| Self::binder_matches_var_id(field, var_name, var_id)),
            WhenPattern::List { elements, tail } => {
                elements
                    .iter()
                    .any(|element| Self::binder_matches_var_id(element, var_name, var_id))
                    || tail
                        .as_ref()
                        .is_some_and(|tail| Self::binder_matches_var_id(tail, var_name, var_id))
            }
            WhenPattern::Pair(left, right) => {
                Self::binder_matches_var_id(left, var_name, var_id)
                    || Self::binder_matches_var_id(right, var_name, var_id)
            }
            WhenPattern::Var(name) => Self::binder_matches_var_id(name, var_name, var_id),
            WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
        }
    }
}
