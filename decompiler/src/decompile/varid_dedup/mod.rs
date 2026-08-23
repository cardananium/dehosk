//! VarId deduplication — make every binding-site VarId unique.
//!
//! Upstream stages can emit a `PseudoExpr` where two distinct binding
//! sites share one `VarId` (aggressive cloning, or a MIR lowering that
//! re-emits a binder under a different lexical scope). Naming, the type
//! solver, the simplifier and pretty-printing all identify a binder by
//! its `VarId`, so a duplicate becomes silent cross-scope aliasing.
//!
//! The pass walks top-down, renames every repeat binding-site `VarId`
//! to a freshly-allocated id, and rewrites references inside the
//! renamed scope via the lexical rewrite stack.
//!
//! Runs as a standalone pre-pass before type constraint solving.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

/// Test-only: the pipeline dedups through the pass registry.
/// Rename every duplicate binding-site `VarId` so that all binders in the
/// returned expression carry a unique id. Var references are rewritten
/// to follow their nearest in-scope binder.
#[cfg(test)]
pub(crate) fn deduplicate_var_ids(expr: PseudoExpr) -> PseudoExpr {
    let mut empty: std::collections::HashMap<VarId, crate::pseudo::nameless::VarKind> =
        std::collections::HashMap::new();
    deduplicate_var_ids_with_annotations(expr, &mut empty)
}

/// Variant of [`deduplicate_var_ids`] that also propagates
/// `kind_annotations`: a renamed binder's VarKind migrates to the
/// new id, and the old id stays in the map because stale refs the
/// recovery passes chase still carry it. Without this migration
/// every rename drops the entry, leaving the recovery passes'
/// typed predicate with no annotation to find.
pub(crate) fn deduplicate_var_ids_with_annotations(
    expr: PseudoExpr,
    kind_annotations: &mut std::collections::HashMap<VarId, crate::pseudo::nameless::VarKind>,
) -> PseudoExpr {
    let mut deduper = VarIdDeduplicator::new(&expr);
    let rewritten = deduper.dedup(expr);
    deduper.propagate_kind_annotations(kind_annotations);
    rewritten
}

pub(crate) fn has_duplicate_binding_ids(expr: &PseudoExpr) -> bool {
    struct DuplicateBindingIdVisitor {
        seen: HashSet<VarId>,
        has_duplicate: bool,
    }

    impl DuplicateBindingIdVisitor {
        fn record_let_id(&mut self, id: &Option<VarId>) {
            if let Some(id) = id.get() {
                self.record_binding_id(id);
            }
        }

        fn record_binder(&mut self, binder: &Binder) {
            self.record_binding_id(binder.id);
        }

        fn record_binding_id(&mut self, id: VarId) {
            if !self.seen.insert(id) {
                self.has_duplicate = true;
            }
        }

        fn record_pattern(&mut self, pattern: &WhenPattern) {
            match pattern {
                WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                    for field in fields {
                        self.record_binder(field);
                    }
                }
                WhenPattern::List { elements, tail } => {
                    for element in elements {
                        self.record_binder(element);
                    }
                    if let Some(tail) = tail {
                        self.record_binder(tail);
                    }
                }
                WhenPattern::Pair(left, right) => {
                    self.record_binder(left);
                    self.record_binder(right);
                }
                WhenPattern::Var(binder) => self.record_binder(binder),
                WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
            }
        }
    }

    impl ExprVisitor for DuplicateBindingIdVisitor {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, _value: &PseudoExpr) {
            self.record_let_id(id);
        }

        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for param in params {
                self.record_binder(param);
            }
        }

        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            self.record_binder(name);
            for param in params {
                self.record_binder(param);
            }
        }

        fn visit_when(
            &mut self,
            _subject: &PseudoExpr,
            subject_name: Option<&Binder>,
            clauses: &[WhenClause],
        ) {
            if let Some(subject_name) = subject_name {
                self.record_binder(subject_name);
            }
            for clause in clauses {
                self.record_pattern(&clause.pattern);
            }
        }
    }

    let mut visitor = DuplicateBindingIdVisitor {
        seen: HashSet::new(),
        has_duplicate: false,
    };
    visitor.walk(expr);
    visitor.has_duplicate
}

/// A job on [`VarIdDeduplicator::dedup`]'s stack. Scope changes between two
/// child descents — a `let` binding coming into scope after its value, a
/// clause frame opened after the subject — stay their own steps.
enum DedupStep {
    Visit(PseudoExpr),
    /// One `when` clause: opens its scope, rewrites its pattern binders, and
    /// queues its guard and body under that scope.
    Clause {
        original_subject_name: Option<Binder>,
        rewritten_subject_name: Option<Binder>,
        clause: WhenClause,
    },
    Post(DedupPost),
}

enum DedupPost {
    /// The value is rewritten; open the binding and walk the body under it.
    LetBody {
        name: String,
        id: Option<VarId>,
        body: PBox,
    },
    LetPost {
        name: String,
        /// Already rewritten by [`DedupPost::LetBody`].
        id: Option<VarId>,
    },
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    /// The subject is rewritten: mint the subject-name binder, then queue the clauses.
    /// Minting sits here, not before the subject, because reserved that id after
    /// folding the subject.
    WhenAfterSubject {
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    },
    /// One clause's guard/body are on `done`: close its scope and reassemble.
    ClauseClose {
        pattern: WhenPattern,
        has_guard: bool,
    },
    When {
        subject_name: Option<Binder>,
        clause_count: usize,
    },
    /// Any other node: its rewritten children sit on `done`; put them back
    /// into the shell they were taken out of.
    Plain {
        shell: PseudoExpr,
        count: usize,
    },
}

/// Split a node into a SHELL — every immediate child replaced by a `Unit`
/// placeholder — plus those children in `map_children` order.
fn split_children(expr: PseudoExpr) -> (PseudoExpr, Vec<PseudoExpr>) {
    let mut kids: Vec<PseudoExpr> = Vec::new();
    let shell = crate::decompile::render_prep::scope_recurse::map_children(expr, |c| {
        kids.push(c);
        PseudoExpr::Unit
    });
    (shell, kids)
}

/// Put rewritten children back into a shell from [`split_children`].
fn join_children(shell: PseudoExpr, kids: Vec<PseudoExpr>) -> PseudoExpr {
    let mut kids = kids.into_iter();
    crate::decompile::render_prep::scope_recurse::map_children(shell, |_| {
        kids.next().expect("split_children left one child per slot")
    })
}

struct VarIdDeduplicator {
    seen_binding_ids: HashSet<VarId>,
    id_rewrites: Vec<HashMap<VarId, VarId>>,
    next_fresh_var_id: u32,
    /// Every binder rename `(original, rewritten)`, so
    /// [`deduplicate_var_ids_with_annotations`] can migrate
    /// `kind_annotations` from the old id to the new one.
    rename_history: Vec<(VarId, VarId)>,
}

impl VarIdDeduplicator {
    fn new(expr: &PseudoExpr) -> Self {
        Self {
            seen_binding_ids: HashSet::new(),
            id_rewrites: vec![HashMap::new()],
            next_fresh_var_id: max_explicit_var_id(expr).saturating_add(1),
            rename_history: Vec::new(),
        }
    }

    fn propagate_kind_annotations(
        &self,
        annotations: &mut std::collections::HashMap<VarId, crate::pseudo::nameless::VarKind>,
    ) {
        for (original, rewritten) in &self.rename_history {
            if let Some(kind) = annotations.get(original).cloned() {
                annotations.entry(*rewritten).or_insert(kind);
            }
        }
    }

    fn push_scope(&mut self) {
        self.id_rewrites.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.id_rewrites
            .pop()
            .expect("varid dedup id rewrite stack should not underflow");
    }

    fn fresh_var_id(&mut self) -> VarId {
        let id = VarId::from_raw(self.next_fresh_var_id);
        self.next_fresh_var_id = self.next_fresh_var_id.saturating_add(1);
        id
    }

    fn reserve_binding_id(&mut self, original: VarId) -> VarId {
        if self.seen_binding_ids.insert(original) {
            original
        } else {
            let fresh = self.fresh_var_id();
            self.seen_binding_ids.insert(fresh);
            self.rename_history.push((original, fresh));
            fresh
        }
    }

    fn record_id_rewrite(&mut self, original: VarId, rewritten: VarId) {
        self.id_rewrites
            .last_mut()
            .expect("varid dedup id rewrite scope should always exist")
            .insert(original, rewritten);
    }

    fn rewrite_reference_id(&self, original: VarId) -> VarId {
        self.id_rewrites
            .iter()
            .rev()
            .find_map(|scope| scope.get(&original).copied())
            .unwrap_or(original)
    }

    fn rewrite_binder_for_scope(&mut self, binder: &Binder) -> Binder {
        let rewritten = Binder::new(binder.name.clone(), self.reserve_binding_id(binder.id));
        self.record_id_rewrite(binder.id, rewritten.id);
        rewritten
    }

    fn rewrite_binder_for_output(&mut self, binder: Binder) -> Binder {
        Binder::new(binder.name, self.reserve_binding_id(binder.id))
    }

    fn rewrite_pattern_bindings_for_scope(&mut self, pattern: WhenPattern) -> WhenPattern {
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
                    .map(|binder| self.rewrite_binder_for_scope(&binder))
                    .collect(),
                shape,
            },
            WhenPattern::List { elements, tail } => WhenPattern::List {
                elements: elements
                    .into_iter()
                    .map(|binder| self.rewrite_binder_for_scope(&binder))
                    .collect(),
                tail: tail.map(|binder| self.rewrite_binder_for_scope(&binder)),
            },
            WhenPattern::Tuple(items) => WhenPattern::Tuple(
                items
                    .into_iter()
                    .map(|binder| self.rewrite_binder_for_scope(&binder))
                    .collect(),
            ),
            WhenPattern::Pair(left, right) => WhenPattern::Pair(
                self.rewrite_binder_for_scope(&left),
                self.rewrite_binder_for_scope(&right),
            ),
            WhenPattern::Var(binder) => WhenPattern::Var(self.rewrite_binder_for_scope(&binder)),
            other => other,
        }
    }

    /// The top-down rewrite.
    ///
    /// The scope is the deduper's own `id_rewrites` stack; `push_scope` /
    /// `pop_scope` are steps that open and close a binder, and every
    /// `reserve_binding_id` keeps its position in the walk — it mints ids in
    /// call order, so a reordered traversal would renumber the whole program.
    fn dedup(&mut self, expr: PseudoExpr) -> PseudoExpr {
        let mut steps: Vec<DedupStep> = vec![DedupStep::Visit(expr)];
        let mut done: Vec<PseudoExpr> = Vec::new();
        // Rewritten clauses, pushed by `ClauseClose` and drained by the
        // matching `When`. LIFO like `done`: a clause's own subtree (and any
        // nested `when` in it) completes before the next clause's step runs.
        let mut clauses_done: Vec<WhenClause> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                DedupStep::Visit(expr) => match expr {
                    PseudoExpr::Var { name, id } => {
                        // Keep the original id when the ref is a compat
                        // placeholder (`id.get() == None`). Returning `None`
                        // here would let the optional-id bridge allocate a
                        // fresh id via `VarId::fresh_compat_placeholder()`,
                        // re-minting every such ref on every run and leaving
                        // same-name/different-id orphans in the final AST.
                        let new_id = match id.get() {
                            Some(concrete) => Some(self.rewrite_reference_id(concrete)),
                            None => id,
                        };
                        done.push(PseudoExpr::Var { name, id: new_id });
                    }
                    PseudoExpr::Lambda { params, body } => {
                        self.push_scope();
                        let params: Vec<Binder> = params
                            .iter()
                            .map(|param| self.rewrite_binder_for_scope(param))
                            .collect();
                        steps.push(DedupStep::Post(DedupPost::Lambda { params }));
                        steps.push(DedupStep::Visit(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        self.push_scope();
                        let name = self.rewrite_binder_for_scope(&name);
                        let params: Vec<Binder> = params
                            .iter()
                            .map(|param| self.rewrite_binder_for_scope(param))
                            .collect();
                        steps.push(DedupStep::Post(DedupPost::RecFn { name, params }));
                        steps.push(DedupStep::Visit(body.into_inner()));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        // The binding comes into scope BETWEEN the value and
                        // the body, so opening it is a step of its own.
                        steps.push(DedupStep::Post(DedupPost::LetBody { name, id, body }));
                        steps.push(DedupStep::Visit(value.into_inner()));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        steps.push(DedupStep::Post(DedupPost::WhenAfterSubject {
                            subject_name,
                            clauses,
                        }));
                        steps.push(DedupStep::Visit(subject.into_inner()));
                    }
                    // The non-binding variants, in `map_children`'s order;
                    // leaves split into zero children and rejoin unchanged.
                    other => {
                        let (shell, kids) = split_children(other);
                        steps.push(DedupStep::Post(DedupPost::Plain {
                            shell,
                            count: kids.len(),
                        }));
                        for kid in kids.into_iter().rev() {
                            steps.push(DedupStep::Visit(kid));
                        }
                    }
                },
                DedupStep::Clause {
                    original_subject_name,
                    rewritten_subject_name,
                    clause,
                } => {
                    let pattern = clause.pattern;

                    self.push_scope();
                    if let (Some(original_subject_binder), Some(subject_binder)) = (
                        original_subject_name.as_ref(),
                        rewritten_subject_name.as_ref(),
                    ) {
                        self.record_id_rewrite(original_subject_binder.id, subject_binder.id);
                    }
                    let pattern = self.rewrite_pattern_bindings_for_scope(pattern);

                    let has_guard = clause.guard.is_some();
                    steps.push(DedupStep::Post(DedupPost::ClauseClose {
                        pattern,
                        has_guard,
                    }));
                    steps.push(DedupStep::Visit(clause.body));
                    if let Some(guard) = clause.guard {
                        steps.push(DedupStep::Visit(guard));
                    }
                }
                DedupStep::Post(post) => match post {
                    DedupPost::Lambda { params } => {
                        let body = done.pop().expect("lambda body");
                        self.pop_scope();
                        done.push(PseudoExpr::Lambda {
                            params,
                            body: PBox::new(body),
                        });
                    }
                    DedupPost::RecFn { name, params } => {
                        let body = done.pop().expect("recfn body");
                        self.pop_scope();
                        done.push(PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(body),
                        });
                    }
                    DedupPost::LetBody { name, id, body } => {
                        self.push_scope();
                        let rewritten_id: Option<VarId> = match id.get() {
                            Some(original) => {
                                let rewritten = self.reserve_binding_id(original);
                                self.record_id_rewrite(original, rewritten);
                                Some(rewritten)
                            }
                            None => id,
                        };
                        steps.push(DedupStep::Post(DedupPost::LetPost {
                            name,
                            id: rewritten_id,
                        }));
                        steps.push(DedupStep::Visit(body.into_inner()));
                    }
                    DedupPost::LetPost { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        self.pop_scope();
                        done.push(PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        });
                    }
                    DedupPost::WhenAfterSubject {
                        subject_name,
                        clauses,
                    } => {
                        let rewritten_subject_name = subject_name
                            .clone()
                            .map(|binder| self.rewrite_binder_for_output(binder));
                        steps.push(DedupStep::Post(DedupPost::When {
                            subject_name: rewritten_subject_name.clone(),
                            clause_count: clauses.len(),
                        }));
                        // Reversed so the clauses pop in source order.
                        for clause in clauses.into_iter().rev() {
                            steps.push(DedupStep::Clause {
                                original_subject_name: subject_name.clone(),
                                rewritten_subject_name: rewritten_subject_name.clone(),
                                clause,
                            });
                        }
                    }
                    DedupPost::ClauseClose { pattern, has_guard } => {
                        let body = done.pop().expect("clause body");
                        let guard = if has_guard {
                            Some(done.pop().expect("clause guard"))
                        } else {
                            None
                        };
                        self.pop_scope();
                        clauses_done.push(WhenClause {
                            pattern,
                            guard,
                            body,
                        });
                    }
                    DedupPost::When {
                        subject_name,
                        clause_count,
                    } => {
                        let at = clauses_done.len() - clause_count;
                        let clauses = clauses_done.split_off(at);
                        let subject = done.pop().expect("when subject");
                        done.push(PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        });
                    }
                    DedupPost::Plain { shell, count } => {
                        let at = done.len() - count;
                        let kids = done.split_off(at);
                        done.push(join_children(shell, kids));
                    }
                },
            }
        }

        done.pop().expect("dedup leaves exactly one result")
    }
}

fn max_explicit_var_id(expr: &PseudoExpr) -> u32 {
    struct MaxExplicitVarIdVisitor {
        max_id: u32,
    }

    impl ExprVisitor for MaxExplicitVarIdVisitor {
        fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
            if let Some(id) = id.get() {
                self.max_id = self.max_id.max(id.as_u32());
            }
        }

        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, _value: &PseudoExpr) {
            if let Some(id) = id.get() {
                self.max_id = self.max_id.max(id.as_u32());
            }
        }

        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for param in params {
                bump_max_authoritative(&mut self.max_id, param.id);
            }
        }

        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            bump_max_authoritative(&mut self.max_id, name.id);
            for param in params {
                bump_max_authoritative(&mut self.max_id, param.id);
            }
        }

        fn visit_when(
            &mut self,
            _subject: &PseudoExpr,
            subject_name: Option<&Binder>,
            clauses: &[WhenClause],
        ) {
            if let Some(subject_name) = subject_name {
                bump_max_authoritative(&mut self.max_id, subject_name.id);
            }
            for clause in clauses {
                self.max_id = max_pattern_var_id(self.max_id, &clause.pattern);
            }
        }
    }

    let mut visitor = MaxExplicitVarIdVisitor { max_id: 0 };
    visitor.walk(expr);
    visitor.max_id
}

fn max_pattern_var_id(mut max_id: u32, pattern: &WhenPattern) -> u32 {
    match pattern {
        WhenPattern::Constructor { fields, .. } => {
            for field in fields {
                bump_max_authoritative(&mut max_id, field.id);
            }
        }
        WhenPattern::List { elements, tail } => {
            for element in elements {
                bump_max_authoritative(&mut max_id, element.id);
            }
            if let Some(tail) = tail {
                bump_max_authoritative(&mut max_id, tail.id);
            }
        }
        WhenPattern::Tuple(items) => {
            for item in items {
                bump_max_authoritative(&mut max_id, item.id);
            }
        }
        WhenPattern::Pair(left, right) => {
            bump_max_authoritative(&mut max_id, left.id);
            bump_max_authoritative(&mut max_id, right.id);
        }
        WhenPattern::Var(binder) => {
            bump_max_authoritative(&mut max_id, binder.id);
        }
        WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
    }
    max_id
}

/// Update `max_id` only for ids in the authoritative range: a
/// compat-placeholder sentinel means "no real id" and would inflate
/// the next `fresh_binding` allocation if it seeded the allocator.
/// Mirrors the `.get().is_some()` gate in `visit_var` /
/// `visit_let_value_post`; no production path mints binders with
/// compat ids, but the filter keeps the invariant explicit at every
/// collection site.
fn bump_max_authoritative(max_id: &mut u32, id: VarId) {
    if let Some(real) = id.get() {
        *max_id = (*max_id).max(real.as_u32());
    }
}

#[cfg(test)]
mod tests;
