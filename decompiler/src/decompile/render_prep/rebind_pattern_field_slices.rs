//! Rebind positional field re-derivations to the pattern binder that
//! already names them, and drop the now-dead slice aliases.
//!
//! A constructor pattern on `subj` already binds `f_k = subj.fields[k]`,
//! but the body often re-derives those fields as `subj.fields[k..].head`
//! and leaves the binders dead. Binder and slice are the same raw
//! undecoded `Data` field, so the substitution is alias-collapse.
//! `expect Ctor(fields) = subj` and `when subj is { Ctor(fields) -> … }`
//! are the same `When` node.
//!
//! Tail `subj.fields[j..]`: bare `.fields` → 0; `List.tail` depth `d`
//! over a tail-from-`j` → `j+d`; an alias of that tail → `j`.
//! Single field `subj.fields[k]`: `<tail-from-j>.head` → `k=j`;
//! `<tail-from-j>[i]` → `k=j+i`. Bare `subj.fields` is not a field.
//!
//! Fail-closed:
//! 1. Slice base and pattern subject share a `VarId`.
//! 2. Substitution only inside the dominating clause body.
//! 3. `k < arity` and position `k` is a live non-`_` binder.
//! 4. Binder is a bare constructor field (same representation).
//! 5. Collided subject/binder ids are skipped.
//!    Unresolved index arithmetic leaves the slice untouched.
//!
//! Dead `let w = subj.fields[j..]` aliases are dropped; a still-used
//! single-field alias keeps its `let` with the value rewritten to `f_j`.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;
use std::rc::Rc;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

/// A subject `subj` whose fields are bound by a Constructor pattern in scope.
#[derive(Clone)]
struct SubjectBinding {
    /// `field_index → (binder name, binder VarId)`. Only non-`_` positions.
    binders: HashMap<usize, (String, VarId)>,
}

/// What a let-alias `Var` denotes, relative to a subject.
#[derive(Clone, Copy)]
enum AliasDenotation {
    /// `let a = subj.fields[j..]` — a tail list starting at index `j`.
    Tail { subject: VarId, start: usize },
    /// `let w = subj.fields[j..].head` — the single raw field at index `j`.
    Field { subject: VarId, index: usize },
}

/// Immutable per-scope environment. Cloned + extended on descent.
#[derive(Clone, Default)]
struct Scope {
    /// subject VarId → its pattern binders.
    subjects: HashMap<VarId, SubjectBinding>,
    /// alias binder VarId → what it denotes.
    aliases: HashMap<VarId, AliasDenotation>,
}

impl Scope {
    /// Invalidate any subject/alias whose VarId is re-bound in a child scope
    /// (collision discipline — should not happen post-uniquify, but fail-safe).
    fn shadow_id(&mut self, id: VarId) {
        self.subjects.remove(&id);
        self.aliases.remove(&id);
    }

    fn shadow_binder(&mut self, b: &Binder) {
        self.shadow_id(b.var_id());
    }

    fn shadow_pattern(&mut self, pattern: &WhenPattern) {
        match pattern {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                for b in fields {
                    self.shadow_binder(b);
                }
            }
            WhenPattern::List { elements, tail } => {
                for b in elements {
                    self.shadow_binder(b);
                }
                if let Some(t) = tail {
                    self.shadow_binder(t);
                }
            }
            WhenPattern::Pair(l, r) => {
                self.shadow_binder(l);
                self.shadow_binder(r);
            }
            WhenPattern::Var(b) => self.shadow_binder(b),
            WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        }
    }
}

pub(super) fn rebind_pattern_field_slices(expr: PseudoExpr) -> PseudoExpr {
    rewrite(expr)
}

/// One pending step of [`rewrite`]'s explicit job stack. Every step carries
/// the `Rc<Scope>` its subtree runs under: a scope is immutable once built,
/// so a whole subtree shares one allocation and there is nothing to
/// save/restore on the way back up.
enum Step {
    Enter(PseudoExpr, Rc<Scope>),
    /// The `let` VALUE has been rewritten; derive the body's scope from it.
    /// A step of its own because `child` is built between the
    /// value and the body descents, reading the REWRITTEN value.
    LetBody {
        name: String,
        id: Option<VarId>,
        body: PseudoExpr,
        outer: Rc<Scope>,
    },
    /// The `when` SUBJECT has been rewritten; derive each clause's scope
    /// from it — again work between two descents.
    WhenClauses {
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
        outer: Rc<Scope>,
    },
    Post(PostKind),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum PostKind {
    /// A `let`'s post-processing needs the OUTER scope (for its `subjects`)
    /// and the alias the body scope recorded for this binder.
    Let {
        name: String,
        id: Option<VarId>,
        outer: Rc<Scope>,
        alias: Option<AliasDenotation>,
    },
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    When {
        subject_name: Option<Binder>,
        /// Per clause: its pattern (never descended into) and whether it
        /// had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Children are pushed in REVERSE so they pop in source order, and are popped off
/// `done` in that same order when the node is rebuilt. Building a `let` body's scope
/// from the rewritten value, and registering a clause's pattern binders against the
/// rewritten subject, are distinct step variants between those descents.
fn rewrite(expr: PseudoExpr) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Enter(expr, Rc::new(Scope::default()))];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr, scope) => {
                // Rebind a matching slice/access node to its pattern binder first.
                if let Some(binder_var) = try_rebind(&expr, &scope) {
                    done.push(binder_var);
                    continue;
                }

                match expr {
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        steps.push(Step::WhenClauses {
                            subject_name,
                            clauses,
                            outer: Rc::clone(&scope),
                        });
                        steps.push(Step::Enter(subject.into_inner(), scope));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        steps.push(Step::LetBody {
                            name,
                            id,
                            body: body.into_inner(),
                            outer: Rc::clone(&scope),
                        });
                        steps.push(Step::Enter(value.into_inner(), scope));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let mut child = (*scope).clone();
                        for p in &params {
                            child.shadow_binder(p);
                        }
                        steps.push(Step::Post(PostKind::Lambda { params }));
                        steps.push(Step::Enter(body.into_inner(), Rc::new(child)));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let mut child = (*scope).clone();
                        child.shadow_binder(&name);
                        for p in &params {
                            child.shadow_binder(p);
                        }
                        steps.push(Step::Post(PostKind::RecFn { name, params }));
                        steps.push(Step::Enter(body.into_inner(), Rc::new(child)));
                    }
                    other => match plain_children(other) {
                        Ok((kind, children)) => {
                            steps.push(Step::Post(PostKind::Plain(kind)));
                            for c in children.into_iter().rev() {
                                steps.push(Step::Enter(c, Rc::clone(&scope)));
                            }
                        }
                        Err(leaf) => done.push(leaf),
                    },
                }
            }
            Step::LetBody {
                name,
                id,
                body,
                outer,
            } => {
                let new_value = done.last().expect("let value");
                let mut child = (*outer).clone();
                let mut alias = None;
                if let Some(let_id) = id {
                    // A new binding of `let_id` shadows any prior meaning.
                    child.shadow_id(let_id);
                    // Record a slice/single-field alias for the body if the VALUE
                    // denotes a subject field-tail or single field.
                    if let Some(denot) = classify_alias_value(new_value, &outer) {
                        child.aliases.insert(let_id, denot);
                        alias = Some(denot);
                    }
                }
                steps.push(Step::Post(PostKind::Let {
                    name,
                    id,
                    outer,
                    alias,
                }));
                steps.push(Step::Enter(body, Rc::new(child)));
            }
            Step::WhenClauses {
                subject_name,
                clauses,
                outer,
            } => {
                // Gate 1: the subject must be a bare `Var { id: Some(_) }` so a
                // Constructor pattern's binders provably alias `subj.fields[k]`.
                let subject_id = match done.last().expect("when subject") {
                    PseudoExpr::Var { id: Some(id), .. } => Some(*id),
                    _ => None,
                };
                let mut clause_meta = Vec::with_capacity(clauses.len());
                let mut clause_children: Vec<(PseudoExpr, Rc<Scope>)> = Vec::new();
                for c in clauses {
                    let mut clause_scope = (*outer).clone();
                    // The subject_name binder (`when X as name is …`) shadows
                    // its own id in the clause; be collision-safe.
                    if let Some(sn) = &subject_name {
                        clause_scope.shadow_binder(sn);
                    }
                    // Register the Constructor pattern's field binders against
                    // the subject id so the clause body can rebind.
                    if let (Some(sid), WhenPattern::Constructor { fields, .. }) =
                        (subject_id, &c.pattern)
                    {
                        register_constructor(&mut clause_scope, sid, fields);
                    }
                    // Pattern binders shadow any homonymous subject/alias ids.
                    clause_scope.shadow_pattern(&c.pattern);
                    let clause_scope = Rc::new(clause_scope);
                    clause_meta.push((c.pattern, c.guard.is_some()));
                    if let Some(g) = c.guard {
                        clause_children.push((g, Rc::clone(&clause_scope)));
                    }
                    clause_children.push((c.body, clause_scope));
                }
                steps.push(Step::Post(PostKind::When {
                    subject_name,
                    clause_meta,
                }));
                for (c, sc) in clause_children.into_iter().rev() {
                    steps.push(Step::Enter(c, sc));
                }
            }
            Step::Post(post) => {
                let rebuilt = match post {
                    PostKind::Let {
                        name,
                        id,
                        outer,
                        alias,
                    } => {
                        let new_body = done.pop().expect("let body");
                        let new_value = done.pop().expect("let value");
                        finish_let(name, id, &outer, alias, new_value, new_body)
                    }
                    PostKind::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    PostKind::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    PostKind::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = take(&mut done, total).into_iter();
                        let subject = parts.next().expect("when subject");
                        let clauses = clause_meta
                            .into_iter()
                            .map(|(pattern, has_guard)| WhenClause {
                                pattern,
                                guard: has_guard.then(|| parts.next().expect("when guard")),
                                body: parts.next().expect("when clause body"),
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    PostKind::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    done.pop().expect("rewrite leaves exactly one result")
}

/// A `let`'s own logic, run once its value and body are rewritten.
///
/// Single-field alias (`let w = subj.fields[j..].head`): rewrite the VALUE
/// to the binder `f_j`, keeping the let — `w` may still be used. Tail alias
/// (`let w = subj.fields[j..]`): DROP the let if its binder is now dead.
fn finish_let(
    name: String,
    id: Option<VarId>,
    outer: &Scope,
    alias: Option<AliasDenotation>,
    new_value: PseudoExpr,
    new_body: PseudoExpr,
) -> PseudoExpr {
    if let Some(let_id) = id {
        match alias {
            Some(AliasDenotation::Field { subject, index }) => {
                if let Some(binder_var) = outer
                    .subjects
                    .get(&subject)
                    .and_then(|s| binder_ref(s, index))
                {
                    return PseudoExpr::Let {
                        name,
                        id,
                        value: PBox::new(binder_var),
                        body: PBox::new(new_body),
                    };
                }
            }
            Some(AliasDenotation::Tail { .. }) => {
                if !body_uses_id(&new_body, let_id) {
                    // Dead slice alias — drop the let entirely.
                    return new_body;
                }
            }
            None => {}
        }
    }
    PseudoExpr::Let {
        name,
        id,
        value: PBox::new(new_value),
        body: PBox::new(new_body),
    }
}

/// Register a Constructor pattern's field binders (non-`_`) against `subject`.
fn register_constructor(scope: &mut Scope, subject: VarId, fields: &[Binder]) {
    let mut binders: HashMap<usize, (String, VarId)> = HashMap::new();
    for (i, b) in fields.iter().enumerate() {
        // Gate 3: `_` positions bind no name — skip.
        if b.as_str() == "_" {
            continue;
        }
        binders.insert(i, (b.as_str().to_string(), b.var_id()));
    }
    scope.subjects.insert(subject, SubjectBinding { binders });
}

/// Build a `Var` reference to the pattern binder at `index` of `subject`,
/// if that position is a live (non-`_`) binder.
fn binder_ref(binding: &SubjectBinding, index: usize) -> Option<PseudoExpr> {
    binding
        .binders
        .get(&index)
        .map(|(name, id)| PseudoExpr::Var {
            name: name.clone(),
            id: Some(*id),
        })
}

/// If `expr` is a single-field re-derivation of `subj.fields[k]` (for a subject
/// in scope, with a live binder at `k < arity`), return the binder `Var`.
fn try_rebind(expr: &PseudoExpr, scope: &Scope) -> Option<PseudoExpr> {
    let (subject, index) = resolve_single_field(expr, scope)?;
    let binding = scope.subjects.get(&subject)?;
    binder_ref(binding, index)
}

/// Resolve `expr` to the `(subject, field_index)` it denotes as a SINGLE raw
/// field, or `None` if it is not a provable single-field re-derivation.
fn resolve_single_field(expr: &PseudoExpr, scope: &Scope) -> Option<(VarId, usize)> {
    match expr {
        // `<tail>.head` → the field at the tail's start index.
        PseudoExpr::FieldAccess { record, selector }
            if matches!(selector, FieldSelector::ListHead) =>
        {
            let (subject, start) = resolve_tail(record, scope)?;
            Some((subject, start))
        }
        // `<tail>[i]` → the field at start + i. `IndexAccess` over a single
        // field (not a tail) yields `None` from `resolve_tail`, so this is safe.
        PseudoExpr::IndexAccess { collection, index } => {
            let (subject, start) = resolve_tail(collection, scope)?;
            Some((subject, start + index))
        }
        // A bare `Var(w)` aliasing a single field (`let w = subj.fields[j..].head`)
        // is intentionally NOT rebound: `w` is a named local the reader can use
        // directly, and its `let`'s value is rewritten to `f_j` separately.
        _ => None,
    }
}

/// Resolve `expr` to the `(subject, start_index)` it denotes as a TAIL LIST
/// (`subj.fields[start..]`), or `None`.
fn resolve_tail(expr: &PseudoExpr, scope: &Scope) -> Option<(VarId, usize)> {
    // `subj.fields` bare — a `FieldAccess NamedField("fields")` over `Var(subj)`.
    if let PseudoExpr::FieldAccess { record, selector } = expr
        && matches!(selector, FieldSelector::NamedField(n) if n == "fields")
        && let PseudoExpr::Var { id: Some(sid), .. } = record.as_ref()
    {
        return Some((*sid, 0));
    }
    // A `List.tail` chain of depth `d` over an inner tail.
    let (inner, depth) = count_tail_chain(expr);
    if depth > 0 {
        let (subject, start) = resolve_tail(inner, scope)?;
        return Some((subject, start + depth));
    }
    // `Var(a)` aliasing a tail `subj.fields[j..]`.
    if let PseudoExpr::Var { id: Some(id), .. } = expr
        && let Some(AliasDenotation::Tail { subject, start }) = scope.aliases.get(id)
    {
        return Some((*subject, *start));
    }
    None
}

/// Classify a `let` VALUE as a subject tail / single-field alias relative to a
/// subject in `scope`; `None` when it is not a provable subject-field slice.
fn classify_alias_value(value: &PseudoExpr, scope: &Scope) -> Option<AliasDenotation> {
    // Single field first: `<tail>.head` / `<tail>[i]` / a field-alias `Var`.
    if let Some((subject, index)) = resolve_single_field(value, scope) {
        return Some(AliasDenotation::Field { subject, index });
    }
    // Tail list: `subj.fields[j..]` (bare `.fields`, a tail chain, or a tail-alias
    // `Var`). A bare whole `.fields` is a legitimate tail alias here, even though
    // it is never substituted as a single field.
    if let Some((subject, start)) = resolve_tail(value, scope) {
        return Some(AliasDenotation::Tail { subject, start });
    }
    None
}

/// Peel `List.tail` wrappers (both the curried `Apply(BuiltinCall(ListTail,[]),[x])`
/// and direct `BuiltinCall(ListTail,[x])` encodings). Returns `(inner, depth)`.
fn count_tail_chain(expr: &PseudoExpr) -> (&PseudoExpr, usize) {
    let mut current = expr;
    let mut depth = 0usize;
    loop {
        match current {
            PseudoExpr::BuiltinCall { name, args }
                if *name == crate::BuiltinId::ListTail && args.len() == 1 =>
            {
                depth += 1;
                current = &args[0];
            }
            PseudoExpr::Apply { function, args }
                if args.len() == 1
                    && matches!(
                        function.as_ref(),
                        PseudoExpr::BuiltinCall { name, args: ba }
                            if *name == crate::BuiltinId::ListTail && ba.is_empty()
                    ) =>
            {
                depth += 1;
                current = &args[0];
            }
            _ => return (current, depth),
        }
    }
}

/// `true` if `id` is referenced anywhere in `expr` (occurs-scan via
/// `ExprVisitor`, which visits when-clause bodies + guards).
fn body_uses_id(expr: &PseudoExpr, id: VarId) -> bool {
    struct Occurs {
        target: VarId,
        found: bool,
    }
    impl ExprVisitor for Occurs {
        fn visit_var(&mut self, _name: &str, vid: &Option<VarId>) {
            if *vid == Some(self.target) {
                self.found = true;
            }
        }
    }
    let mut v = Occurs {
        target: id,
        found: false,
    };
    v.walk(expr);
    v.found
}

#[cfg(test)]
mod tests;
