//! Uniquify pass for let-binding names.
//!
//! The simplifier's semantic naming produces duplicate names in different scopes
//! (several `List.tail` chains each named "tail"); the inliner's use-count is
//! name-based, so duplicates inflate the count and prevent correct inlining.
//! This pass renames shadowed let bindings with numeric suffixes so every
//! binding name is unique across the whole expression.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use super::list_traversal::is_list_tail_call;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::{ExprFolder, ExprVisitor, FoldAction};
use crate::pseudo::var_id::VarId;

// ============================================================
// Shared helpers
// ============================================================

fn make_unique(name: &str, global_names: &mut HashSet<String>) -> String {
    if !global_names.contains(name) {
        global_names.insert(name.to_string());
        return name.to_string();
    }
    let mut idx = 2usize;
    loop {
        let candidate = format!("{}_{}", name, idx);
        if !global_names.contains(&candidate) {
            global_names.insert(candidate.clone());
            return candidate;
        }
        idx += 1;
    }
}

/// True when `target` occurs as a free Var reference; occurrences
/// under a same-named Let/Lambda/RecFn binder do not count.
#[cfg(test)]
fn expr_contains_var(expr: &PseudoExpr, target: &str) -> bool {
    struct ExprContainsVar<'a> {
        target: &'a str,
        blocked_depth: usize,
        found: bool,
    }

    impl ExprVisitor for ExprContainsVar<'_> {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            if self.blocked_depth == 0 && name == self.target {
                self.found = true;
            }
        }

        fn visit_let_value_post(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) {
            if name == self.target {
                self.blocked_depth += 1;
            }
        }

        fn visit_let_post(&mut self, name: &str) {
            if name == self.target {
                self.blocked_depth -= 1;
            }
        }

        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            if params.iter().any(|param| param == self.target) {
                self.blocked_depth += 1;
            }
        }

        fn visit_lambda_post(&mut self, params: &[Binder]) {
            if params.iter().any(|param| param == self.target) {
                self.blocked_depth -= 1;
            }
        }

        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            if name == self.target || params.iter().any(|param| param == self.target) {
                self.blocked_depth += 1;
            }
        }

        fn visit_recfn_post(&mut self, name: &Binder, params: &[Binder]) {
            if name == self.target || params.iter().any(|param| param == self.target) {
                self.blocked_depth -= 1;
            }
        }
    }

    let mut visitor = ExprContainsVar {
        target,
        blocked_depth: 0,
        found: false,
    };
    visitor.walk(expr);
    visitor.found
}

/// Insert into `global_names` every Var reference in `expr` not bound by an
/// enclosing Let/Lambda/RecFn (or listed in `bound`), so later Let-bindings
/// uniquify away from closure-captured names.
#[cfg(test)]
fn register_free_vars(
    expr: &PseudoExpr,
    bound: &HashSet<String>,
    global_names: &mut HashSet<String>,
) {
    struct RegisterFreeVars<'a> {
        local_bound: HashSet<String>,
        global_names: &'a mut HashSet<String>,
    }

    impl ExprVisitor for RegisterFreeVars<'_> {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            if !self.local_bound.contains(name) {
                self.global_names.insert(name.to_string());
            }
        }

        fn visit_let_value_post(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) {
            self.local_bound.insert(name.to_string());
        }

        fn visit_let_post(&mut self, name: &str) {
            self.local_bound.remove(name);
        }

        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for param in params {
                self.local_bound.insert(param.to_string());
            }
        }

        fn visit_lambda_post(&mut self, params: &[Binder]) {
            for param in params {
                self.local_bound.remove(param.as_str());
            }
        }

        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            self.local_bound.insert(name.to_string());
            for param in params {
                self.local_bound.insert(param.to_string());
            }
        }

        fn visit_recfn_post(&mut self, name: &Binder, params: &[Binder]) {
            self.local_bound.remove(name.as_str());
            for param in params {
                self.local_bound.remove(param.as_str());
            }
        }
    }

    RegisterFreeVars {
        local_bound: bound.clone(),
        global_names,
    }
    .walk(expr);
}

// ============================================================
// 1. Uniquify pass — ExprFolder
// ============================================================

pub(crate) fn uniquify_let_names(expr: PseudoExpr) -> PseudoExpr {
    let mut folder = UniquifyFolder {
        global_names: HashSet::new(),
        renames: HashMap::new(),
        renames_by_id: HashMap::new(),
        scope_stack: Vec::new(),
        id_scope_stack: Vec::new(),
    };
    folder.fold(expr)
}

#[cfg(test)]
fn collect_all_var_names(expr: &PseudoExpr, names: &mut HashSet<String>) {
    struct CollectAllVarNames<'a> {
        names: &'a mut HashSet<String>,
    }

    impl ExprVisitor for CollectAllVarNames<'_> {
        fn visit_var(&mut self, name: &str, _id: &Option<VarId>) {
            self.names.insert(name.to_string());
        }
    }

    CollectAllVarNames { names }.walk(expr);
}

/// A saved rename entry: (original_name, previous_mapping_if_any).
type SavedRename = (String, Option<String>);

struct UniquifyFolder {
    global_names: HashSet<String>,
    /// Maps original name -> current unique name.
    renames: HashMap<String, String>,
    /// Maps binding VarId -> current unique name.
    renames_by_id: HashMap<VarId, String>,
    /// Stack of saved renames per scope, so exit_* can restore them.
    scope_stack: Vec<Vec<SavedRename>>,
    /// Snapshots of id-based renames per scope.
    id_scope_stack: Vec<HashMap<VarId, String>>,
}

impl UniquifyFolder {
    fn push_rename(&mut self, old: String, new: String) -> SavedRename {
        let prev = self.renames.insert(old.clone(), new);
        (old, prev)
    }

    fn restore_rename(&mut self, saved: SavedRename) {
        match saved.1 {
            Some(prev) => {
                self.renames.insert(saved.0, prev);
            }
            None => {
                self.renames.remove(&saved.0);
            }
        }
    }

    fn push_scope_frame(&mut self, saved: Vec<SavedRename>, saved_ids: HashMap<VarId, String>) {
        self.scope_stack.push(saved);
        self.id_scope_stack.push(saved_ids);
    }

    fn lookup_with_id(&self, name: &str, var_id: Option<VarId>) -> String {
        if let Some(var_id) = var_id
            && let Some(renamed) = self.renames_by_id.get(&var_id)
        {
            return renamed.clone();
        }
        self.renames
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string())
    }

    fn uniquify_binder(&mut self, binder: &Binder) -> (Binder, Option<SavedRename>) {
        let new_name = make_unique(binder.as_str(), &mut self.global_names);
        self.renames_by_id.insert(binder.id, new_name.clone());
        let saved = if new_name != binder.as_str() {
            Some(self.push_rename(binder.to_string(), new_name.clone()))
        } else {
            None
        };
        (binder.renamed(new_name), saved)
    }

    fn uniquify_param_binders(
        &mut self,
        params: &[crate::pseudo::ast::Binder],
    ) -> Vec<crate::pseudo::ast::Binder> {
        let saved_ids = self.renames_by_id.clone();
        let mut saved = Vec::new();
        let new_params: Vec<_> = params
            .iter()
            .map(|p| {
                let (new_param, maybe_saved) = self.uniquify_binder(p);
                if let Some(saved_rename) = maybe_saved {
                    saved.push(saved_rename);
                }
                new_param
            })
            .collect();
        self.push_scope_frame(saved, saved_ids);
        new_params
    }

    fn uniquify_pattern_binders(&mut self, pattern: WhenPattern) -> WhenPattern {
        match pattern {
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            } => WhenPattern::Constructor {
                type_hint,
                tag,
                fields: fields
                    .into_iter()
                    .map(|field| self.uniquify_binder(&field).0)
                    .collect(),
                shape,
            },
            WhenPattern::List { elements, tail } => WhenPattern::List {
                elements: elements
                    .into_iter()
                    .map(|element| self.uniquify_binder(&element).0)
                    .collect(),
                tail: tail.map(|tail| self.uniquify_binder(&tail).0),
            },
            WhenPattern::Tuple(fields) => WhenPattern::Tuple(
                fields
                    .into_iter()
                    .map(|field| self.uniquify_binder(&field).0)
                    .collect(),
            ),
            WhenPattern::Pair(a, b) => {
                let (a, _) = self.uniquify_binder(&a);
                let (b, _) = self.uniquify_binder(&b);
                WhenPattern::Pair(a, b)
            }
            WhenPattern::Wildcard => WhenPattern::Wildcard,
            WhenPattern::Var(name) => {
                let (name, _) = self.uniquify_binder(&name);
                WhenPattern::Var(name)
            }
            WhenPattern::Literal(expr) => WhenPattern::Literal(self.fold(expr)),
        }
    }

    fn fold_when_scoped(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        let subject = self.fold(subject);
        self.push_scope_frame(Vec::new(), self.renames_by_id.clone());
        let subject_name = subject_name.map(|binder| self.uniquify_binder(&binder).0);
        let clauses = clauses
            .into_iter()
            .map(|clause| {
                self.push_scope_frame(Vec::new(), self.renames_by_id.clone());
                let pattern = self.uniquify_pattern_binders(clause.pattern);
                let guard = clause.guard.map(|guard| self.fold(guard));
                let body = self.fold(clause.body);
                self.pop_scope();
                WhenClause {
                    pattern,
                    guard,
                    body,
                }
            })
            .collect();
        self.pop_scope();
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name,
            clauses,
        }
    }

    fn pop_scope(&mut self) {
        if let Some(saved) = self.scope_stack.pop() {
            for s in saved.into_iter().rev() {
                self.restore_rename(s);
            }
        }
        if let Some(prev) = self.id_scope_stack.pop() {
            self.renames_by_id = prev;
        }
    }

    /// Handle `let name = rec fn name(params) { fn_body } in body` as a unit.
    /// The Let name and RecFn name are the same binding — they must be renamed together.
    fn fold_let_recfn(
        &mut self,
        let_name: String,
        let_id: Option<VarId>,
        fn_name: crate::pseudo::ast::Binder,
        fn_params: Vec<crate::pseudo::ast::Binder>,
        fn_body: PseudoExpr,
        let_body: PseudoExpr,
    ) -> PseudoExpr {
        // One unique name, shared by the Let binder and the RecFn name.
        let new_name = make_unique(&let_name, &mut self.global_names);
        let saved_ids = self.renames_by_id.clone();

        // The rename covers both RecFn body self-refs and Let body refs.
        let mut name_saved = Vec::new();
        if new_name != let_name {
            name_saved.push(self.push_rename(let_name, new_name.clone()));
        }
        if let Some(let_id) = let_id.get() {
            self.renames_by_id.insert(let_id, new_name.clone());
        }
        self.renames_by_id.insert(fn_name.id, new_name.clone());
        self.push_scope_frame(name_saved, saved_ids);

        let new_params = self.uniquify_param_binders(&fn_params);

        // The name rename is active, so self-references are renamed too.
        let new_fn_body = self.fold(fn_body);

        // Params are not in scope for the Let body.
        self.pop_scope();

        // The name rename is still active for references from the Let body.
        let new_let_body = self.fold(let_body);

        // Restore name/id rename scope for the let/recfn binder
        self.pop_scope();

        PseudoExpr::Let {
            name: new_name.clone(),
            id: let_id,
            value: PBox::new(PseudoExpr::RecFn {
                name: fn_name.renamed(new_name),
                params: new_params,
                body: PBox::new(new_fn_body),
            }),
            body: PBox::new(new_let_body),
        }
    }
}

impl ExprFolder for UniquifyFolder {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        // Intercept Let-wrapping-RecFn with the same name to handle as a unit.
        if let PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } = expr
            && let PseudoExpr::RecFn {
                name: fn_name,
                params,
                body: fn_body,
            } = value.as_ref()
            && fn_name == name
        {
            let result = self.fold_let_recfn(
                name.clone(),
                *id,
                fn_name.clone(),
                params.clone(),
                fn_body.as_ref().clone(),
                body.as_ref().clone(),
            );
            return FoldAction::Replace(result);
        }
        if let PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } = expr
        {
            return FoldAction::Replace(self.fold_when_scoped(
                subject.as_ref().clone(),
                subject_name.clone(),
                clauses.clone(),
            ));
        }
        FoldAction::Walk
    }

    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        let resolved = self.lookup_with_id(&name, id.get());
        PseudoExpr::Var { name: resolved, id }
    }

    fn enter_let(&mut self, name: &str, id: &Option<VarId>, _value: &PseudoExpr) -> String {
        let saved_ids = self.renames_by_id.clone();
        let new_name = make_unique(name, &mut self.global_names);
        let mut saved = Vec::new();
        if new_name != name {
            saved.push(self.push_rename(name.to_string(), new_name.clone()));
        }
        if let Some(var_id) = id.get() {
            self.renames_by_id.insert(var_id, new_name.clone());
        }
        self.push_scope_frame(saved, saved_ids);
        new_name
    }

    fn exit_let(&mut self, _name: &str) {
        self.pop_scope();
    }

    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        self.uniquify_param_binders(params)
    }

    fn exit_lambda(&mut self, _params: &[Binder]) {
        self.pop_scope();
    }

    fn enter_recfn(
        &mut self,
        name: &crate::pseudo::ast::Binder,
        params: &[crate::pseudo::ast::Binder],
    ) -> (crate::pseudo::ast::Binder, Vec<crate::pseudo::ast::Binder>) {
        // Uniquify the recfn name
        let saved_ids = self.renames_by_id.clone();
        let mut name_saved = Vec::new();
        let new_name = make_unique(name.as_str(), &mut self.global_names);
        self.renames_by_id.insert(name.id, new_name.clone());
        if new_name != name.as_str() {
            name_saved.push(self.push_rename(name.to_string(), new_name.clone()));
        }
        self.push_scope_frame(name_saved, saved_ids);
        // Uniquify params (this pushes its own scope)
        let new_params = self.uniquify_param_binders(params);
        (name.renamed(new_name), new_params)
    }

    fn exit_recfn(
        &mut self,
        _name: &crate::pseudo::ast::Binder,
        _params: &[crate::pseudo::ast::Binder],
    ) {
        // Pop param scope (pushed by uniquify_params)
        self.pop_scope();
        // Pop name scope (pushed before the params)
        self.pop_scope();
    }

    fn post_when(
        &mut self,
        subject: PseudoExpr,
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    ) -> PseudoExpr {
        // Rename subject_name if it's in the renames map
        let new_subject_name =
            subject_name.map(|n| n.renamed(self.lookup_with_id(n.as_ref(), Some(n.id))));
        PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name: new_subject_name,
            clauses,
        }
    }
}

// ============================================================
// 2. Variable use counter — ExprVisitor
// ============================================================

fn var_ref_matches_target_id(id: &Option<VarId>, target_id: VarId) -> bool {
    id.get() == Some(target_id)
}

fn binder_shadows_target_id(binder: &Binder, target_id: VarId) -> bool {
    binder.id.get() == Some(target_id)
}

fn pattern_shadows_target_id(pattern: &WhenPattern, target_id: VarId) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => fields
            .iter()
            .any(|field| binder_shadows_target_id(field, target_id)),
        WhenPattern::List { elements, tail } => {
            elements
                .iter()
                .any(|element| binder_shadows_target_id(element, target_id))
                || tail
                    .as_ref()
                    .is_some_and(|tail| binder_shadows_target_id(tail, target_id))
        }
        WhenPattern::Pair(first, second) => {
            binder_shadows_target_id(first, target_id)
                || binder_shadows_target_id(second, target_id)
        }
        WhenPattern::Var(name) => binder_shadows_target_id(name, target_id),
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}

/// Count references to `target_id`, matched by `VarId`: names are
/// unique after uniquify, but a non-let binder can shadow.
fn count_var_uses_by_id(expr: &PseudoExpr, target_id: VarId) -> usize {
    let mut counter = VarUseCounter {
        target_id,
        blocked_depth: 0,
        let_block_stack: Vec::new(),
        when_block_stack: Vec::new(),
        count: 0,
    };
    counter.walk(expr);
    counter.count
}

struct VarUseCounter {
    target_id: VarId,
    blocked_depth: usize,
    let_block_stack: Vec<bool>,
    when_block_stack: Vec<bool>,
    count: usize,
}

impl ExprVisitor for VarUseCounter {
    fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
        if self.blocked_depth == 0 && var_ref_matches_target_id(id, self.target_id) {
            self.count += 1;
        }
    }

    fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, _value: &PseudoExpr) {
        let blocks = id.get() == Some(self.target_id);
        self.let_block_stack.push(blocks);
        if blocks {
            self.blocked_depth += 1;
        }
    }

    fn visit_let_post(&mut self, _name: &str) {
        if self.let_block_stack.pop().unwrap_or(false) {
            self.blocked_depth -= 1;
        }
    }

    fn visit_lambda_pre(&mut self, params: &[Binder]) {
        if params
            .iter()
            .any(|param| binder_shadows_target_id(param, self.target_id))
        {
            self.blocked_depth += 1;
        }
    }

    fn visit_lambda_post(&mut self, params: &[Binder]) {
        if params
            .iter()
            .any(|param| binder_shadows_target_id(param, self.target_id))
        {
            self.blocked_depth -= 1;
        }
    }

    fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
        if binder_shadows_target_id(name, self.target_id)
            || params
                .iter()
                .any(|param| binder_shadows_target_id(param, self.target_id))
        {
            self.blocked_depth += 1;
        }
    }

    fn visit_recfn_post(&mut self, name: &Binder, params: &[Binder]) {
        if binder_shadows_target_id(name, self.target_id)
            || params
                .iter()
                .any(|param| binder_shadows_target_id(param, self.target_id))
        {
            self.blocked_depth -= 1;
        }
    }

    fn visit_when_clause_pre(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
        let blocks = subject_name
            .is_some_and(|subject_name| binder_shadows_target_id(subject_name, self.target_id))
            || pattern_shadows_target_id(&clause.pattern, self.target_id);
        self.when_block_stack.push(blocks);
        if blocks {
            self.blocked_depth += 1;
        }
    }

    fn visit_when_clause_post(&mut self, _subject_name: Option<&Binder>, _clause: &WhenClause) {
        if self.when_block_stack.pop().unwrap_or(false) {
            self.blocked_depth -= 1;
        }
    }
}

// ============================================================
// 3. Variable substitution — ExprFolder
// ============================================================

/// Replace references to `target_id` with `replacement`, by `VarId`:
/// names are unique after uniquify, but a non-let binder can shadow.
fn subst_var_by_id(expr: PseudoExpr, target_id: VarId, replacement: &PseudoExpr) -> PseudoExpr {
    let mut folder = SubstVarFolder {
        target_id,
        replacement: replacement.clone(),
        blocked_depth: 0,
        let_block_stack: Vec::new(),
    };
    folder.fold(expr)
}

struct SubstVarFolder {
    target_id: VarId,
    replacement: PseudoExpr,
    blocked_depth: usize,
    let_block_stack: Vec<bool>,
}

impl SubstVarFolder {
    fn binder_shadows(&self, binder: &Binder) -> bool {
        binder_shadows_target_id(binder, self.target_id)
    }

    fn pattern_shadows(&self, pattern: &WhenPattern) -> bool {
        pattern_shadows_target_id(pattern, self.target_id)
    }

    fn fold_clause_with_subject(
        &mut self,
        subject_name: Option<&Binder>,
        clause: WhenClause,
    ) -> WhenClause {
        let pattern = self.fold_pattern(clause.pattern);
        let blocks = subject_name.is_some_and(|subject_name| self.binder_shadows(subject_name))
            || self.pattern_shadows(&pattern);
        if blocks {
            self.blocked_depth += 1;
        }
        let guard = clause.guard.map(|guard| self.fold(guard));
        let body = self.fold(clause.body);
        if blocks {
            self.blocked_depth -= 1;
        }
        WhenClause {
            pattern,
            guard,
            body,
        }
    }
}

impl ExprFolder for SubstVarFolder {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        if self.blocked_depth > 0 {
            return FoldAction::Replace(expr.clone());
        }

        match expr {
            PseudoExpr::Var { id, .. } if var_ref_matches_target_id(id, self.target_id) => {
                FoldAction::Replace(self.replacement.clone())
            }
            // Stop recursing if a lambda shadows the target
            PseudoExpr::Lambda { params, .. } if params.iter().any(|p| self.binder_shadows(p)) => {
                FoldAction::Replace(expr.clone())
            }
            // Stop recursing if a recfn shadows the target
            PseudoExpr::RecFn { name, params, .. }
                if self.binder_shadows(name) || params.iter().any(|p| self.binder_shadows(p)) =>
            {
                FoldAction::Replace(expr.clone())
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                let subject = self.fold((**subject).clone());
                let subject_name = subject_name.clone();
                let clauses = clauses
                    .clone()
                    .into_iter()
                    .map(|clause| self.fold_clause_with_subject(subject_name.as_ref(), clause))
                    .collect();
                FoldAction::Replace(PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                })
            }
            _ => FoldAction::Walk,
        }
    }

    fn enter_let(&mut self, name: &str, id: &Option<VarId>, _value: &PseudoExpr) -> String {
        let blocks = id.get() == Some(self.target_id);
        self.let_block_stack.push(blocks);
        if blocks {
            self.blocked_depth += 1;
        }
        name.to_string()
    }

    fn exit_let(&mut self, _name: &str) {
        if self.let_block_stack.pop().unwrap_or(false) {
            self.blocked_depth -= 1;
        }
    }
}

// ============================================================
// 4. Tail chain collapsing
// ============================================================

/// Collapse single-use `List.tail` let chains into nested calls.
///
/// Transforms:
///   let a = List.tail(x)
///   let b = List.tail(a)
///   List.tail(b)
/// Into:
///   List.tail(List.tail(List.tail(x)))
///
/// The pretty printer then renders the nested calls as `x[3..]`.
/// Must run after `uniquify_let_names` so variable names are globally unique.
pub(crate) fn collapse_tail_chains(expr: PseudoExpr) -> PseudoExpr {
    collapse_tails_rec(expr)
}

/// Bottom-up: recurse into children, then try to collapse the current Let.
struct TailCollapseFolder;

impl ExprFolder for TailCollapseFolder {
    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        if let Some(target_id) = id.get()
            && is_list_tail_call(&value)
            && count_var_uses_by_id(&body, target_id) == 1
        {
            // Inline: replace refs to this exact binder with the List.tail call.
            return subst_var_by_id(body, target_id, &value);
        }
        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }

    // The original hand-rolled recursion left `when` clause patterns
    // untouched (only `subject`, `guard`, and `body` were walked) — match
    // that exactly rather than picking up the default's recursion into
    // `WhenPattern::Literal`'s inner expression.
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }
}

fn collapse_tails_rec(expr: PseudoExpr) -> PseudoExpr {
    TailCollapseFolder.fold(expr)
}

#[cfg(test)]
mod tests;
