//! Invariant validators for [`NamelessExpr`].
//!
//! The nameless IR carries variable identity only as `VarId`,
//! so name desync cannot occur; only scope stays checkable.
//!
//! [`validate_nameless_invariants`] walks the AST tracking the
//! lexical-binder set and reports every `Var(id)` that neither
//! references an in-scope binder nor sits in the entry-lambda
//! parameter set (the only legitimate "free" vars).

use std::collections::HashSet;

use super::super::var_id::VarId;
#[cfg(test)]
use super::NamelessClause;
use super::{NamelessExpr, NamelessPattern, VarTable};

/// Result of [`validate_nameless_invariants`]. Carries the list
/// of free-var violations found, if any.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct NamelessValidation {
    /// Var IDs referenced but never bound in their lexical scope.
    pub free_vars: Vec<VarId>,
}

impl NamelessValidation {
    pub(crate) fn is_ok(&self) -> bool {
        self.free_vars.is_empty()
    }
}

/// Walk the [`NamelessExpr`] and collect every `Var(id)` whose
/// `id` is not bound by an enclosing Lambda / RecFn / Let / When
/// / pattern in the lexical scope.
///
/// `entry_params` gives the set of VarIds that are legitimately
/// free at the root (e.g. the script's lambda parameters bound
/// by the outermost `fn(script_context)`). Pass an empty set to
/// require a fully-closed expression.
pub(crate) fn validate_nameless_invariants(
    expr: &NamelessExpr,
    entry_params: &HashSet<VarId>,
) -> NamelessValidation {
    use crate::pseudo::nameless::fold::NamelessVisitor;

    let mut state = ValidationState {
        free: Vec::new(),
        scope_chain: vec![entry_params.clone()],
    };
    state.walk(expr);
    NamelessValidation {
        free_vars: state.free,
    }
}

impl crate::pseudo::nameless::fold::NamelessVisitor for ValidationState {
    fn visit_var(&mut self, id: VarId) {
        if !self.is_bound(id) {
            self.free.push(id);
        }
    }
    fn enter_lambda(&mut self, params: &[VarId]) {
        self.push_scope(params.iter().copied());
    }
    fn exit_lambda(&mut self, _: &[VarId]) {
        self.pop_scope();
    }
    fn enter_recfn(&mut self, name: VarId, params: &[VarId]) {
        self.push_scope(std::iter::once(name).chain(params.iter().copied()));
    }
    fn exit_recfn(&mut self, _: VarId, _: &[VarId]) {
        self.pop_scope();
    }
    fn enter_let(&mut self, binder: VarId, _: &NamelessExpr) {
        self.push_scope(std::iter::once(binder));
    }
    fn exit_let(&mut self, _: VarId) {
        self.pop_scope();
    }
    fn enter_when(&mut self, _: &NamelessExpr, subject_name: Option<VarId>) {
        // Push subject_name as its own scope frame so each clause
        // sees it; stacking it apart from the pattern binders is
        // equivalent for "is this id bound" lookups.
        self.push_scope(subject_name);
    }
    fn exit_when(&mut self, _: Option<VarId>) {
        self.pop_scope();
    }
    fn enter_clause(&mut self, pattern: &NamelessPattern) {
        self.push_scope(pattern_binders(pattern));
    }
    fn exit_clause(&mut self, _: &NamelessPattern) {
        self.pop_scope();
    }
}

pub(crate) fn nameless_free_var_id_set(expr: &NamelessExpr) -> HashSet<VarId> {
    validate_nameless_invariants(expr, &HashSet::new())
        .free_vars
        .into_iter()
        .collect()
}

pub(crate) fn nameless_introduces_new_free_var_ids(
    expr: &NamelessExpr,
    baseline_free_vars: &HashSet<VarId>,
) -> bool {
    let after_free_vars = nameless_free_var_id_set(expr);
    !after_free_vars.is_subset(baseline_free_vars)
}

pub(crate) fn nameless_render_orphan_name_set(
    expr: &NamelessExpr,
    table: &VarTable,
) -> HashSet<String> {
    validate_nameless_invariants(expr, &HashSet::new())
        .free_vars
        .iter()
        .filter_map(|id| render_name(*id, table))
        .collect()
}

pub(crate) fn nameless_render_binder_name_set(
    expr: &NamelessExpr,
    table: &VarTable,
) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_binder_names(expr, table, &mut names);
    names
}

pub(crate) fn nameless_render_var_name_set(
    expr: &NamelessExpr,
    table: &VarTable,
) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_var_names(expr, table, &mut names);
    names
}

/// Every `VarId` OCCURRING in the expression — binders (let/lambda/recfn
/// name+params/when subject_name/pattern binders) AND `Var` references
/// (including refs inside `NamelessPattern::Literal` payload expressions).
/// This is the LIVE set for `assign_names`: a table entry whose id never
/// occurs here can't render, so it must not consume a display name.
pub(crate) fn nameless_live_var_id_set(expr: &NamelessExpr) -> HashSet<VarId> {
    let mut ids = HashSet::new();
    collect_all_var_ids(expr, &mut ids);
    ids
}

fn collect_all_var_ids(expr: &NamelessExpr, out: &mut HashSet<VarId>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        let mut kids: Vec<&NamelessExpr> = Vec::new();
        match cur {
            NamelessExpr::Var(id) => {
                out.insert(*id);
            }
            NamelessExpr::Let {
                binder,
                value,
                body,
            } => {
                out.insert(*binder);
                kids.push(value);
                kids.push(body);
            }
            NamelessExpr::Lambda { params, body } => {
                out.extend(params.iter().copied());
                kids.push(body);
            }
            NamelessExpr::RecFn { name, params, body } => {
                out.insert(*name);
                out.extend(params.iter().copied());
                kids.push(body);
            }
            NamelessExpr::Apply { function, args } => {
                kids.push(function);
                for arg in args {
                    kids.push(arg);
                }
            }
            NamelessExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                kids.push(condition);
                kids.push(then_branch);
                kids.push(else_branch);
            }
            NamelessExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                kids.push(subject);
                if let Some(subject_name) = subject_name {
                    out.insert(*subject_name);
                }
                for clause in clauses {
                    out.extend(pattern_binders(&clause.pattern));
                    if let NamelessPattern::Literal(payload) = &clause.pattern {
                        kids.push(payload);
                    }
                    if let Some(guard) = &clause.guard {
                        kids.push(guard);
                    }
                    kids.push(&clause.body);
                }
            }
            NamelessExpr::List { elements, tail } => {
                for element in elements {
                    kids.push(element);
                }
                if let Some(tail) = tail {
                    kids.push(tail);
                }
            }
            NamelessExpr::Tuple(items) => {
                for item in items {
                    kids.push(item);
                }
            }
            NamelessExpr::Pair(left, right) => {
                kids.push(left);
                kids.push(right);
            }
            NamelessExpr::Constr { fields, .. } => {
                for field in fields {
                    kids.push(field);
                }
            }
            NamelessExpr::FieldAccess { record, .. } => kids.push(record),
            NamelessExpr::IndexAccess { collection, .. } => kids.push(collection),
            NamelessExpr::BinOp { left, right, .. } => {
                kids.push(left);
                kids.push(right);
            }
            NamelessExpr::UnOp { operand, .. } => kids.push(operand),
            NamelessExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    kids.push(arg);
                }
            }
            NamelessExpr::Delay(inner) | NamelessExpr::Force(inner) => {
                kids.push(inner);
            }
            NamelessExpr::Trace { message, value } => {
                kids.push(message);
                kids.push(value);
            }
            NamelessExpr::Int(_)
            | NamelessExpr::ByteArray(_)
            | NamelessExpr::String(_)
            | NamelessExpr::Bool(_)
            | NamelessExpr::Unit
            | NamelessExpr::Error { .. }
            | NamelessExpr::Raw { .. }
            | NamelessExpr::Data(_)
            | NamelessExpr::HelperSymbol(_) => {}
        }
        pending.extend(kids.into_iter().rev());
    }
}

fn render_name(id: VarId, table: &VarTable) -> Option<String> {
    table
        .get(id)
        .and_then(|metadata| metadata.render_name_hint().map(str::to_string))
}

fn record_render_name(id: VarId, table: &VarTable, out: &mut HashSet<String>) {
    if let Some(name) = render_name(id, table) {
        out.insert(name);
    }
}

struct ValidationState {
    free: Vec<VarId>,
    scope_chain: Vec<HashSet<VarId>>,
}

impl ValidationState {
    fn is_bound(&self, id: VarId) -> bool {
        self.scope_chain.iter().any(|s| s.contains(&id))
    }

    fn push_scope(&mut self, ids: impl IntoIterator<Item = VarId>) {
        self.scope_chain.push(ids.into_iter().collect());
    }

    fn pop_scope(&mut self) {
        self.scope_chain.pop();
    }
}

fn pattern_binders(pattern: &NamelessPattern) -> Vec<VarId> {
    match pattern {
        NamelessPattern::Wildcard | NamelessPattern::Literal(_) => Vec::new(),
        NamelessPattern::Var(id) => vec![*id],
        NamelessPattern::Constructor { fields, .. } | NamelessPattern::Tuple(fields) => {
            fields.clone()
        }
        NamelessPattern::List { elements, tail } => {
            let mut out = elements.clone();
            if let Some(t) = tail {
                out.push(*t);
            }
            out
        }
        NamelessPattern::Pair(a, b) => vec![*a, *b],
    }
}

fn collect_pattern_binder_names(
    pattern: &NamelessPattern,
    table: &VarTable,
    out: &mut HashSet<String>,
) {
    for id in pattern_binders(pattern) {
        record_render_name(id, table, out);
    }
}

fn collect_binder_names(expr: &NamelessExpr, table: &VarTable, out: &mut HashSet<String>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        let mut kids: Vec<&NamelessExpr> = Vec::new();
        match cur {
            NamelessExpr::Let {
                binder,
                value,
                body,
            } => {
                record_render_name(*binder, table, out);
                kids.push(value);
                kids.push(body);
            }
            NamelessExpr::Lambda { params, body } => {
                for param in params {
                    record_render_name(*param, table, out);
                }
                kids.push(body);
            }
            NamelessExpr::RecFn { name, params, body } => {
                record_render_name(*name, table, out);
                for param in params {
                    record_render_name(*param, table, out);
                }
                kids.push(body);
            }
            NamelessExpr::Apply { function, args } => {
                kids.push(function);
                for arg in args {
                    kids.push(arg);
                }
            }
            NamelessExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                kids.push(condition);
                kids.push(then_branch);
                kids.push(else_branch);
            }
            NamelessExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                kids.push(subject);
                if let Some(subject_name) = subject_name {
                    record_render_name(*subject_name, table, out);
                }
                for clause in clauses {
                    collect_pattern_binder_names(&clause.pattern, table, out);
                    if let Some(guard) = &clause.guard {
                        kids.push(guard);
                    }
                    kids.push(&clause.body);
                }
            }
            NamelessExpr::List { elements, tail } => {
                for element in elements {
                    kids.push(element);
                }
                if let Some(tail) = tail {
                    kids.push(tail);
                }
            }
            NamelessExpr::Tuple(items) => {
                for item in items {
                    kids.push(item);
                }
            }
            NamelessExpr::Pair(left, right) => {
                kids.push(left);
                kids.push(right);
            }
            NamelessExpr::Constr { fields, .. } => {
                for field in fields {
                    kids.push(field);
                }
            }
            NamelessExpr::FieldAccess { record, .. } => kids.push(record),
            NamelessExpr::IndexAccess { collection, .. } => {
                kids.push(collection);
            }
            NamelessExpr::BinOp { left, right, .. } => {
                kids.push(left);
                kids.push(right);
            }
            NamelessExpr::UnOp { operand, .. } => kids.push(operand),
            NamelessExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    kids.push(arg);
                }
            }
            NamelessExpr::Delay(inner) | NamelessExpr::Force(inner) => {
                kids.push(inner);
            }
            NamelessExpr::Trace { message, value } => {
                kids.push(message);
                kids.push(value);
            }
            NamelessExpr::Var(_)
            | NamelessExpr::Int(_)
            | NamelessExpr::ByteArray(_)
            | NamelessExpr::String(_)
            | NamelessExpr::Bool(_)
            | NamelessExpr::Unit
            | NamelessExpr::Error { .. }
            | NamelessExpr::Raw { .. }
            | NamelessExpr::Data(_)
            | NamelessExpr::HelperSymbol(_) => {}
        }
        pending.extend(kids.into_iter().rev());
    }
}

fn collect_var_names(expr: &NamelessExpr, table: &VarTable, out: &mut HashSet<String>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        let mut kids: Vec<&NamelessExpr> = Vec::new();
        match cur {
            NamelessExpr::Var(id) => {
                record_render_name(*id, table, out);
            }
            NamelessExpr::Let { value, body, .. } => {
                kids.push(value);
                kids.push(body);
            }
            NamelessExpr::Lambda { body, .. } | NamelessExpr::RecFn { body, .. } => {
                kids.push(body);
            }
            NamelessExpr::Apply { function, args } => {
                kids.push(function);
                for arg in args {
                    kids.push(arg);
                }
            }
            NamelessExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                kids.push(condition);
                kids.push(then_branch);
                kids.push(else_branch);
            }
            NamelessExpr::When {
                subject, clauses, ..
            } => {
                kids.push(subject);
                for clause in clauses {
                    if let Some(guard) = &clause.guard {
                        kids.push(guard);
                    }
                    kids.push(&clause.body);
                }
            }
            NamelessExpr::List { elements, tail } => {
                for element in elements {
                    kids.push(element);
                }
                if let Some(tail) = tail {
                    kids.push(tail);
                }
            }
            NamelessExpr::Tuple(items) => {
                for item in items {
                    kids.push(item);
                }
            }
            NamelessExpr::Pair(left, right) => {
                kids.push(left);
                kids.push(right);
            }
            NamelessExpr::Constr { fields, .. } => {
                for field in fields {
                    kids.push(field);
                }
            }
            NamelessExpr::FieldAccess { record, .. } => kids.push(record),
            NamelessExpr::IndexAccess { collection, .. } => kids.push(collection),
            NamelessExpr::BinOp { left, right, .. } => {
                kids.push(left);
                kids.push(right);
            }
            NamelessExpr::UnOp { operand, .. } => kids.push(operand),
            NamelessExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    kids.push(arg);
                }
            }
            NamelessExpr::Delay(inner) | NamelessExpr::Force(inner) => {
                kids.push(inner);
            }
            NamelessExpr::Trace { message, value } => {
                kids.push(message);
                kids.push(value);
            }
            NamelessExpr::Int(_)
            | NamelessExpr::ByteArray(_)
            | NamelessExpr::String(_)
            | NamelessExpr::Bool(_)
            | NamelessExpr::Unit
            | NamelessExpr::Error { .. }
            | NamelessExpr::Raw { .. }
            | NamelessExpr::Data(_)
            | NamelessExpr::HelperSymbol(_) => {}
        }
        pending.extend(kids.into_iter().rev());
    }
}

// =============================================================
// Tests
// =============================================================

#[cfg(test)]
mod tests;
