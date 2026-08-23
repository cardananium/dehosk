use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

#[cfg(test)]
pub(crate) fn debug_repair_underscore_lambda_params_with_dangling_uses(
    expr: PseudoExpr,
) -> PseudoExpr {
    repair_underscore_lambda_params_with_dangling_uses(expr)
}

// Repair `fn(_, …)` whose body uses free `v_NNN` simplifier temps.
//
// The simplifier renames a lambda parameter to `_` as unused but leaves
// the body referencing the original `v_NNN` name. When the lambda's
// underscore slots are at least as many as the distinct free `v_NNN`
// names in the body, each temp takes one `_` slot — temps ascending by
// number, slots left to right. A name whose free uses carry conflicting
// VarIds is ambiguous and is dropped, so no slot is bound on a guess.

pub(super) fn repair_underscore_lambda_params_with_dangling_uses(expr: PseudoExpr) -> PseudoExpr {
    fn is_simplifier_temp(name: &str) -> bool {
        if let Some(rest) = name.strip_prefix("v_") {
            return !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit());
        }
        false
    }

    fn record_free_temp(
        name: &str,
        id: Option<VarId>,
        out: &mut HashMap<String, Option<VarId>>,
        ambiguous: &mut HashSet<String>,
    ) {
        if ambiguous.contains(name) {
            return;
        }
        let candidate = id.get();
        let mut remove_existing = false;
        match out.get_mut(name) {
            Some(existing) => match (*existing, candidate) {
                (Some(current), Some(next)) if current != next => remove_existing = true,
                (None, Some(next)) => *existing = Some(next),
                _ => {}
            },
            None => {
                out.insert(name.to_string(), candidate);
            }
        }
        if remove_existing {
            ambiguous.insert(name.to_string());
            out.remove(name);
        }
    }

    /// One pending step of [`collect_free_temps`]'s worklist.
    enum Step<'a> {
        Visit(&'a PseudoExpr),
        /// A `let`: its VALUE is walked outside the binding, its body
        /// inside — opening the binding is a step of its own so the value
        /// keeps seeing exactly the scope that enclosed the `let`.
        EnterLetBody {
            name: &'a str,
            body: &'a PseudoExpr,
        },
        /// A `when` clause: the subject name and pattern binders are in
        /// scope for its guard and body only.
        EnterClause {
            subject_name: Option<&'a Binder>,
            clause: &'a WhenClause,
        },
        /// Drop whatever a scope pushed, back to the length it saved.
        TruncateTo(usize),
    }

    fn collect_free_temps(
        expr: &PseudoExpr,
        bound: &mut Vec<String>,
        out: &mut HashMap<String, Option<VarId>>,
        ambiguous: &mut HashSet<String>,
    ) {
        let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];
        while let Some(step) = steps.pop() {
            match step {
                Step::Visit(expr) => match expr {
                    PseudoExpr::Var { name, id } => {
                        if is_simplifier_temp(name) && !bound.iter().any(|b| b == name) {
                            record_free_temp(name, *id, out, ambiguous);
                        }
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let base = bound.len();
                        bound.extend(params.iter().map(|p| p.to_string()));
                        steps.push(Step::TruncateTo(base));
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let base = bound.len();
                        bound.push(name.to_string());
                        bound.extend(params.iter().map(|p| p.to_string()));
                        steps.push(Step::TruncateTo(base));
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::Let {
                        name, value, body, ..
                    } => {
                        steps.push(Step::EnterLetBody { name, body });
                        steps.push(Step::Visit(value));
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
                        for a in args.iter().rev() {
                            steps.push(Step::Visit(a));
                        }
                        steps.push(Step::Visit(function));
                    }
                    PseudoExpr::FieldAccess { record, .. } => steps.push(Step::Visit(record)),
                    PseudoExpr::IndexAccess { collection, .. } => {
                        steps.push(Step::Visit(collection))
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
                        if let Some(t) = tail {
                            steps.push(Step::Visit(t));
                        }
                        for e in elements.iter().rev() {
                            steps.push(Step::Visit(e));
                        }
                    }
                    PseudoExpr::Tuple(items) => {
                        for i in items.iter().rev() {
                            steps.push(Step::Visit(i));
                        }
                    }
                    PseudoExpr::Pair(a, b) => {
                        steps.push(Step::Visit(b));
                        steps.push(Step::Visit(a));
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for f in fields.iter().rev() {
                            steps.push(Step::Visit(f));
                        }
                    }
                    PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                        steps.push(Step::Visit(inner));
                    }
                    PseudoExpr::Trace { message, value } => {
                        steps.push(Step::Visit(value));
                        steps.push(Step::Visit(message));
                    }
                    _ => {}
                },
                Step::EnterLetBody { name, body } => {
                    let base = bound.len();
                    bound.push(name.to_string());
                    steps.push(Step::TruncateTo(base));
                    steps.push(Step::Visit(body));
                }
                Step::EnterClause {
                    subject_name,
                    clause,
                } => {
                    let base = bound.len();
                    if let Some(s) = subject_name {
                        bound.push(s.to_string());
                    }
                    match &clause.pattern {
                        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                            bound.extend(fields.iter().map(|b| b.to_string()));
                        }
                        WhenPattern::List { elements, tail } => {
                            bound.extend(elements.iter().map(|b| b.to_string()));
                            if let Some(t) = tail {
                                bound.push(t.to_string());
                            }
                        }
                        WhenPattern::Pair(a, b) => {
                            bound.push(a.to_string());
                            bound.push(b.to_string());
                        }
                        WhenPattern::Var(b) => bound.push(b.to_string()),
                        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
                    }
                    steps.push(Step::TruncateTo(base));
                    steps.push(Step::Visit(&clause.body));
                    if let Some(g) = &clause.guard {
                        steps.push(Step::Visit(g));
                    }
                }
                Step::TruncateTo(base) => bound.truncate(base),
            }
        }
    }

    struct RewriteFreeTempRefs {
        target: String,
        new_id: VarId,
        bound: Vec<String>,
    }

    impl RewriteFreeTempRefs {
        fn is_shadowed(&self) -> bool {
            self.bound.iter().rev().any(|b| b == &self.target)
        }
    }

    impl ExprFolder for RewriteFreeTempRefs {
        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            if name == self.target && !self.is_shadowed() {
                PseudoExpr::Var {
                    name,
                    id: Some(self.new_id),
                }
            } else {
                PseudoExpr::Var { name, id }
            }
        }

        fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
            self.bound.extend(params.iter().map(|p| p.to_string()));
            params.to_vec()
        }

        fn exit_lambda(&mut self, params: &[Binder]) {
            let new_len = self.bound.len() - params.len();
            self.bound.truncate(new_len);
        }

        fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
            self.bound.push(name.to_string());
            self.bound.extend(params.iter().map(|p| p.to_string()));
            (name.clone(), params.to_vec())
        }

        fn exit_recfn(&mut self, _name: &Binder, params: &[Binder]) {
            let new_len = self.bound.len() - params.len() - 1;
            self.bound.truncate(new_len);
        }

        fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
            self.bound.push(name.to_string());
            name.to_string()
        }

        fn exit_let(&mut self, _name: &str) {
            self.bound.pop();
        }

        fn fold_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            let subject = self.fold(subject);
            let clauses = clauses
                .into_iter()
                .map(|clause| {
                    let base = self.bound.len();
                    if let Some(ref s) = subject_name {
                        self.bound.push(s.to_string());
                    }
                    match &clause.pattern {
                        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                            self.bound.extend(fields.iter().map(|b| b.to_string()));
                        }
                        WhenPattern::List { elements, tail } => {
                            self.bound.extend(elements.iter().map(|b| b.to_string()));
                            if let Some(tail) = tail {
                                self.bound.push(tail.to_string());
                            }
                        }
                        WhenPattern::Pair(a, b) => {
                            self.bound.push(a.to_string());
                            self.bound.push(b.to_string());
                        }
                        WhenPattern::Var(binder) => self.bound.push(binder.to_string()),
                        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
                    }
                    let guard = clause.guard.map(|guard| self.fold(guard));
                    let body = self.fold(clause.body);
                    self.bound.truncate(base);
                    WhenClause {
                        pattern: clause.pattern,
                        guard,
                        body,
                    }
                })
                .collect();
            self.post_when(subject, subject_name, clauses)
        }
    }

    fn rewrite_free_temp_refs(expr: PseudoExpr, name: &str, new_id: VarId) -> PseudoExpr {
        RewriteFreeTempRefs {
            target: name.to_string(),
            new_id,
            bound: Vec::new(),
        }
        .fold(expr)
    }

    struct RepairFold;

    impl ExprFolder for RepairFold {
        fn fold_clause(&mut self, clause: WhenClause) -> WhenClause {
            let mut clause = clause;
            clause.body = self.fold(clause.body);
            clause.guard = clause.guard.map(|g| self.fold(g));
            clause
        }

        fn post_lambda(&mut self, params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
            let mut body = body;
            let underscore_slots: Vec<usize> = params
                .iter()
                .enumerate()
                .filter(|(_, p)| p.as_str() == "_")
                .map(|(i, _)| i)
                .collect();
            if !underscore_slots.is_empty() {
                let mut free_temps = HashMap::new();
                let mut ambiguous = HashSet::new();
                let mut bound: Vec<String> = params
                    .iter()
                    .filter(|p| p.as_str() != "_")
                    .map(|p| p.to_string())
                    .collect();
                collect_free_temps(&body, &mut bound, &mut free_temps, &mut ambiguous);
                if !free_temps.is_empty() && free_temps.len() <= underscore_slots.len() {
                    let mut sorted_temps: Vec<(String, Option<VarId>)> =
                        free_temps.into_iter().collect();
                    sorted_temps.sort_by_key(|(temp, _)| {
                        temp.strip_prefix("v_")
                            .and_then(|n| n.parse::<usize>().ok())
                            .unwrap_or(usize::MAX)
                    });
                    let mut new_params = params;
                    for (slot, (temp, maybe_id)) in underscore_slots.iter().zip(sorted_temps.iter())
                    {
                        let new_id = maybe_id.unwrap_or(new_params[*slot].id);
                        new_params[*slot] = Binder::new(temp.clone(), new_id);
                        body = rewrite_free_temp_refs(body, temp, new_id);
                    }
                    return PseudoExpr::Lambda {
                        params: new_params,
                        body: PBox::new(body),
                    };
                }
            }
            PseudoExpr::Lambda {
                params,
                body: PBox::new(body),
            }
        }
    }

    RepairFold.fold(expr)
}
