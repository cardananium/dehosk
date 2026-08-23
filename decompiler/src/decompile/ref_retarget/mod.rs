//! Upstream ref retargeting.
//!
//! Walks a `PseudoExpr` tracking the nearest in-scope binder by
//! name. For every `Var { name, id }` reference, if a same-name
//! binder is in scope and its id differs from the ref's id, the
//! ref's id is rewritten to the binder's id. Shadowing-aware
//! (nearest binder wins). A ref with no same-name binder in
//! scope is left alone.
//!
//! `display_rewrite` and the naming transforms are correct only
//! where a ref's id matches its lexical binder's id. A stale ref
//! — one whose MIR binder was inlined away, leaving an obsolete
//! id while a same-name pattern binder lives nearby — makes the
//! audit report `name_orphan` and id-only renames miss their
//! targets.

use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

pub(crate) fn refs_need_retarget_by_scope(expr: &PseudoExpr) -> bool {
    let mut stack: Vec<HashMap<String, VarId>> = vec![HashMap::new()];
    needs_retarget(expr, &mut stack)
}

pub(crate) fn retarget_refs_by_scope(expr: PseudoExpr) -> PseudoExpr {
    // Precondition: no two binders in scope share a name. Retargeting
    // rewrites a `Var { name }` ref to the NEAREST same-name binder, so
    // a nested clause shadowing an outer binder by name — two cons
    // clauses both binding `tail` in a parallel two-list recursion —
    // would capture a ref meant for the OUTER binder, collapsing
    // `rec(tail, tail_inner)` into `rec(tail_inner, tail_inner)`.
    // Disambiguating when-pattern binder NAMES first (suffix `_N`, uses
    // rewired by VarId) makes each in-scope binder uniquely named.
    // (Idempotent: no shadow → no-op.)
    let expr = crate::decompile::render_prep::disambiguate_shadowed_pattern_binders(expr);
    let mut folder = RetargetFolder {
        stack: vec![HashMap::new()],
    };
    folder.fold(expr)
}

/// [`ExprFolder`] impl for `retarget_refs_by_scope`.
struct RetargetFolder {
    stack: Vec<HashMap<String, VarId>>,
}

impl ExprFolder for RetargetFolder {
    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        let retargeted_id = match lookup(&self.stack, &name) {
            Some(bid) if Some(bid) != id => Some(bid),
            _ => id,
        };
        PseudoExpr::Var {
            name,
            id: retargeted_id,
        }
    }

    fn enter_let(&mut self, name: &str, id: &Option<VarId>, _value: &PseudoExpr) -> String {
        self.stack.push(HashMap::new());
        // Keep the binder's own id, compat-placeholders included — see
        // same rationale in `needs_retarget`.
        bind(
            &mut self.stack,
            name,
            id.unwrap_or_else(VarId::fresh_compat_placeholder),
        );
        name.to_string()
    }

    fn exit_let(&mut self, _name: &str) {
        self.stack.pop();
    }

    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        self.stack.push(HashMap::new());
        for p in params {
            bind(&mut self.stack, p.as_str(), p.var_id());
        }
        params.to_vec()
    }

    fn exit_lambda(&mut self, _params: &[Binder]) {
        self.stack.pop();
    }

    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        self.stack.push(HashMap::new());
        bind(&mut self.stack, name.as_str(), name.var_id());
        for p in params {
            bind(&mut self.stack, p.as_str(), p.var_id());
        }
        (name.clone(), params.to_vec())
    }

    fn exit_recfn(&mut self, _name: &Binder, _params: &[Binder]) {
        self.stack.pop();
    }

    fn fold_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let subject = self.fold(subject);
        let pushed_subject = subject_name.is_some();
        if let Some(sn) = &subject_name {
            self.stack.push(HashMap::new());
            bind(&mut self.stack, sn.as_str(), sn.var_id());
        }
        let clauses = clauses.into_iter().map(|c| self.fold_clause(c)).collect();
        if pushed_subject {
            self.stack.pop();
        }
        self.post_when(subject, subject_name, clauses)
    }

    fn fold_clause(&mut self, clause: WhenClause) -> WhenClause {
        self.stack.push(HashMap::new());
        bind_pattern(&clause.pattern, &mut self.stack);
        let guard = clause.guard.map(|g| self.fold(g));
        let body = self.fold(clause.body);
        self.stack.pop();
        WhenClause {
            pattern: clause.pattern,
            guard,
            body,
        }
    }
}

fn lookup(stack: &[HashMap<String, VarId>], name: &str) -> Option<VarId> {
    for frame in stack.iter().rev() {
        if let Some(&id) = frame.get(name) {
            return Some(id);
        }
    }
    None
}

fn bind(stack: &mut [HashMap<String, VarId>], name: &str, id: VarId) {
    if let Some(top) = stack.last_mut() {
        top.insert(name.to_string(), id);
    }
}

/// One pending step of [`needs_retarget`]'s explicit stack.
enum NeedsRetargetStep<'a> {
    Visit(&'a PseudoExpr),
    EnterLetBody {
        name: &'a str,
        id: Option<VarId>,
        body: &'a PseudoExpr,
    },
    EnterLambdaBody {
        params: &'a [Binder],
        body: &'a PseudoExpr,
    },
    EnterRecFnBody {
        name: &'a Binder,
        params: &'a [Binder],
        body: &'a PseudoExpr,
    },
    EnterWhenScope {
        subject_name: Option<&'a Binder>,
        clauses: &'a [WhenClause],
    },
    VisitClause(&'a WhenClause),
    PopScope,
}

fn needs_retarget(expr: &PseudoExpr, stack: &mut Vec<HashMap<String, VarId>>) -> bool {
    let mut steps: Vec<NeedsRetargetStep<'_>> = vec![NeedsRetargetStep::Visit(expr)];
    while let Some(step) = steps.pop() {
        match step {
            NeedsRetargetStep::Visit(expr) => match expr {
                PseudoExpr::Var { name, id } => {
                    if matches!(lookup(stack, name), Some(bound_id) if Some(bound_id) != *id) {
                        return true;
                    }
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(NeedsRetargetStep::EnterLetBody {
                        name,
                        id: *id,
                        body,
                    });
                    steps.push(NeedsRetargetStep::Visit(value));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(NeedsRetargetStep::EnterLambdaBody { params, body });
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(NeedsRetargetStep::EnterRecFnBody { name, params, body });
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    steps.push(NeedsRetargetStep::EnterWhenScope {
                        subject_name: subject_name.as_ref(),
                        clauses,
                    });
                    steps.push(NeedsRetargetStep::Visit(subject));
                }
                PseudoExpr::Apply { function, args } => {
                    for arg in args.iter().rev() {
                        steps.push(NeedsRetargetStep::Visit(arg));
                    }
                    steps.push(NeedsRetargetStep::Visit(function));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(NeedsRetargetStep::Visit(else_branch));
                    steps.push(NeedsRetargetStep::Visit(then_branch));
                    steps.push(NeedsRetargetStep::Visit(condition));
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    steps.push(NeedsRetargetStep::Visit(right));
                    steps.push(NeedsRetargetStep::Visit(left));
                }
                PseudoExpr::UnOp { operand, .. } => {
                    steps.push(NeedsRetargetStep::Visit(operand));
                }
                PseudoExpr::BuiltinCall { args, .. } => {
                    for arg in args.iter().rev() {
                        steps.push(NeedsRetargetStep::Visit(arg));
                    }
                }
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                    steps.push(NeedsRetargetStep::Visit(inner));
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(NeedsRetargetStep::Visit(value));
                    steps.push(NeedsRetargetStep::Visit(message));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(tail) = tail {
                        steps.push(NeedsRetargetStep::Visit(tail));
                    }
                    for element in elements.iter().rev() {
                        steps.push(NeedsRetargetStep::Visit(element));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for item in items.iter().rev() {
                        steps.push(NeedsRetargetStep::Visit(item));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    steps.push(NeedsRetargetStep::Visit(b));
                    steps.push(NeedsRetargetStep::Visit(a));
                }
                PseudoExpr::Constr { fields, .. } => {
                    for field in fields.iter().rev() {
                        steps.push(NeedsRetargetStep::Visit(field));
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => {
                    steps.push(NeedsRetargetStep::Visit(record));
                }
                PseudoExpr::IndexAccess { collection, .. } => {
                    steps.push(NeedsRetargetStep::Visit(collection));
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
            NeedsRetargetStep::EnterLetBody { name, id, body } => {
                stack.push(HashMap::new());
                // Keep the binder's own id, compat-placeholders included.
                // Re-keying a compat binder would perturb identity
                // comparisons against same-name refs that carry the
                // original compat id.
                bind(
                    stack,
                    name,
                    id.unwrap_or_else(VarId::fresh_compat_placeholder),
                );
                steps.push(NeedsRetargetStep::PopScope);
                steps.push(NeedsRetargetStep::Visit(body));
            }
            NeedsRetargetStep::EnterLambdaBody { params, body } => {
                stack.push(HashMap::new());
                for p in params {
                    bind(stack, p.as_str(), p.var_id());
                }
                steps.push(NeedsRetargetStep::PopScope);
                steps.push(NeedsRetargetStep::Visit(body));
            }
            NeedsRetargetStep::EnterRecFnBody { name, params, body } => {
                stack.push(HashMap::new());
                bind(stack, name.as_str(), name.var_id());
                for p in params {
                    bind(stack, p.as_str(), p.var_id());
                }
                steps.push(NeedsRetargetStep::PopScope);
                steps.push(NeedsRetargetStep::Visit(body));
            }
            NeedsRetargetStep::EnterWhenScope {
                subject_name,
                clauses,
            } => {
                let pushed_subject = subject_name.is_some();
                if let Some(sn) = subject_name {
                    stack.push(HashMap::new());
                    bind(stack, sn.as_str(), sn.var_id());
                }
                if pushed_subject {
                    steps.push(NeedsRetargetStep::PopScope);
                }
                for clause in clauses.iter().rev() {
                    steps.push(NeedsRetargetStep::VisitClause(clause));
                }
            }
            NeedsRetargetStep::VisitClause(clause) => {
                stack.push(HashMap::new());
                bind_pattern(&clause.pattern, stack);
                steps.push(NeedsRetargetStep::PopScope);
                steps.push(NeedsRetargetStep::Visit(&clause.body));
                if let Some(guard) = &clause.guard {
                    steps.push(NeedsRetargetStep::Visit(guard));
                }
            }
            NeedsRetargetStep::PopScope => {
                stack.pop();
            }
        }
    }
    false
}

fn bind_pattern(pattern: &WhenPattern, stack: &mut [HashMap<String, VarId>]) {
    match pattern {
        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        WhenPattern::Var(b) => bind(stack, b.as_str(), b.var_id()),
        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
            for b in fields {
                bind(stack, b.as_str(), b.var_id());
            }
        }
        WhenPattern::List { elements, tail } => {
            for b in elements {
                bind(stack, b.as_str(), b.var_id());
            }
            if let Some(t) = tail {
                bind(stack, t.as_str(), t.var_id());
            }
        }
        WhenPattern::Pair(a, b) => {
            bind(stack, a.as_str(), a.var_id());
            bind(stack, b.as_str(), b.var_id());
        }
    }
}

#[cfg(test)]
mod tests;
