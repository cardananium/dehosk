//! Inline `subject.fields.head` (or `subject.fields[N]`) to the
//! matching When-clause pattern binder.
//!
//! The constructor pattern already binds field 0 / N, so the
//! access is the same value spelled twice. When the access is the
//! whole value of a `let`, the let is dropped and references are
//! rewritten to that binder.
//!
//! Missing names are manufactured rather than skipped: a `_` binder
//! whose field the body accesses becomes `field_{i}`, and a pattern
//! shorter than the highest accessed index grows fresh `field_N`
//! binders, bumping the `Unknown` shape's arity with them.
//!
//! The When subject must be a `Var { id: Some(_), .. }`. `f(x).fields.head`
//! is not safe: `f(x)` may have side effects, while the binder
//! captured the value at pattern-bind time. `Known(_)` shapes name a
//! closed-set ADT constructor and keep their arity; only `Unknown`
//! patterns grow. Field selectors must match `NamedField("fields")`
//! then `ListHead`/`Index(N)` exactly — `subject.tag` and custom
//! record fields are left alone.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;
use std::rc::Rc;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

pub(super) fn inline_pattern_field_access(expr: PseudoExpr) -> PseudoExpr {
    // Pre-pass: inline `let X = subject.fields` aliases so indirect
    // accesses (`X[N]`) reach the main pass in the direct form
    // (`subject.fields[N]`) it recognizes.
    let normalized = inline_subject_fields_aliases(expr);
    let scope: PatternScope = PatternScope::default();
    rewrite(normalized, &scope)
}

/// Inline lets whose value is `subject.fields` (a FieldAccess with
/// `NamedField("fields")` selector over a Var record): every
/// reference to the binder becomes a clone of that FieldAccess and
/// the let is dropped.
///
/// Targets the synthetic `let fields: List<Data> = t2.fields` alias
/// in front of a chain of `let f_N = fields[N]` projections, common
/// for 0-arity Constr patterns. After inlining each `fields[N]` is
/// `t2.fields[N]`, the canonical form
/// `inline_pattern_field_access` recognizes.
///
/// Guards: the let-value must be exactly that FieldAccess shape
/// (other selectors and non-Var records are left alone), and the
/// let-binder must have an id.
fn inline_subject_fields_aliases(expr: PseudoExpr) -> PseudoExpr {
    map_tree(expr, |e| {
        NodeAction::Descend(settle_subject_fields_alias(e))
    })
}

/// Whether `expr` is exactly the `let X = <Var>.fields` alias shape (an
/// id-carrying `let` whose value is a `NamedField("fields")` access over a
/// `Var` record).
fn is_subject_fields_alias(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Let {
        id: Some(_), value, ..
    } = expr
    else {
        return false;
    };
    matches!(
        value.as_ref(),
        PseudoExpr::FieldAccess {
            record,
            selector: FieldSelector::NamedField(sel_name),
        } if sel_name == "fields"
            && matches!(record.as_ref(), PseudoExpr::Var { id: Some(_), .. })
    )
}

/// Drop every `let X = subject.fields` alias rooted AT `expr`, substituting each one
/// into its own body. This is the loop ran by re-entering itself on `body_substituted`:
/// a chain of stacked aliases settles here before the walk descends into what is left.
fn settle_subject_fields_alias(mut expr: PseudoExpr) -> PseudoExpr {
    while is_subject_fields_alias(&expr) {
        let PseudoExpr::Let {
            id: Some(let_id),
            value,
            body,
            ..
        } = expr
        else {
            unreachable!("shape checked by is_subject_fields_alias");
        };
        let replacement = value.into_inner();
        expr = substitute_var_with_expr(body.into_inner(), let_id, &replacement);
    }
    expr
}

/// Substitute every `Var { id: Some(id) }` matching `let_id` with a
/// clone of `replacement` throughout `expr`.
fn substitute_var_with_expr(
    expr: PseudoExpr,
    let_id: VarId,
    replacement: &PseudoExpr,
) -> PseudoExpr {
    map_tree(expr, |e| match &e {
        PseudoExpr::Var { id: Some(id), .. } if *id == let_id => {
            NodeAction::Done(replacement.clone())
        }
        _ => NodeAction::Descend(e),
    })
}

/// Maps `(subject_var_id, field_index)` → the pattern binder that
/// already names that field. Holds every currently-active
/// When-pattern binding: each clause extends a clone of the outer
/// scope, so inner When clauses still see the outer bindings.
#[derive(Default, Clone)]
struct PatternScope {
    bindings: HashMap<(VarId, usize), (String, VarId)>,
}

impl PatternScope {
    fn lookup(&self, subject_id: VarId, index: usize) -> Option<(&String, VarId)> {
        self.bindings
            .get(&(subject_id, index))
            .map(|(n, id)| (n, *id))
    }

    /// Extend the scope with the bindings a When-clause Constructor
    /// pattern makes over `subject_id`. Skips binders named `_` —
    /// there's no name to substitute to.
    fn extend(&self, subject_id: VarId, fields: &[Binder]) -> Self {
        let mut out = self.clone();
        for (i, b) in fields.iter().enumerate() {
            let name = b.to_string();
            if name == "_" {
                continue;
            }
            out.bindings.insert((subject_id, i), (name, b.var_id()));
        }
        out
    }
}

/// Rewrite `expr` under `scope`, inlining every pattern-field access.
///
/// The [`PatternScope`] travels WITH the node (`Rc`, so a clause's extended scope is
/// shared by its whole subtree) rather than as a call argument. Work between two
/// child descents is its own step variant:
///
/// * [`RwStep::WhenClauses`] — reading the REWRITTEN subject's `VarId`, which
///   every clause's pattern promotion keys on.
/// * [`RwStep::Clause`] — promoting/expanding one clause's binders. This
///   MINTS ids via `VarId::fresh_binding()`, so it must run after the previous
///   clause's whole subtree and before this clause's guard and body, or the
///   whole program renumbers.
/// * [`RwPost::LetDrop`] — rewiring the dropped alias let's references after
///   its body is rewritten.
fn rewrite(expr: PseudoExpr, scope: &PatternScope) -> PseudoExpr {
    let mut steps: Vec<RwStep> = vec![RwStep::Visit(expr, Rc::new(scope.clone()))];
    let mut done: Vec<PseudoExpr> = Vec::new();
    // `When` clause reassembly data, pushed by `Clause` and drained by the
    // matching `Post::When`. LIFO like `done`: a clause's own subtree (and any
    // nested `When` in it) completes before the next clause's step runs.
    let mut clauses_done: Vec<(WhenPattern, bool)> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RwStep::Visit(expr, scope) => {
                // Try to match the pattern-field-access shape at THIS node first.
                if let Some(substituted) = try_substitute(&expr, &scope) {
                    done.push(substituted);
                    continue;
                }
                // Otherwise recurse, extending scope at When-clause boundaries.
                match expr {
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        steps.push(RwStep::Post(RwPost::When {
                            subject_name,
                            count: clauses.len(),
                        }));
                        steps.push(RwStep::WhenClauses {
                            clauses,
                            scope: Rc::clone(&scope),
                        });
                        steps.push(RwStep::Visit(subject.into_inner(), scope));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        // A let whose value is itself such a field access, and
                        // that has an id, is a redundant alias to a pattern
                        // binder: substitute body[Var(let_id) → Var(binder)] and
                        // DROP the let. A self-referential `let x = x` is left
                        // alone.
                        let dropped = id.and_then(|let_id| match try_substitute(&value, &scope) {
                            Some(PseudoExpr::Var {
                                name: target_name,
                                id: Some(target_id),
                            }) if target_id != let_id => Some((let_id, target_name, target_id)),
                            _ => None,
                        });
                        if let Some((let_id, target_name, target_id)) = dropped {
                            steps.push(RwStep::Post(RwPost::LetDrop {
                                let_id,
                                target_name,
                                target_id,
                            }));
                            steps.push(RwStep::Visit(body.into_inner(), scope));
                            continue;
                        }
                        steps.push(RwStep::Post(RwPost::Let { name, id }));
                        steps.push(RwStep::Visit(body.into_inner(), Rc::clone(&scope)));
                        steps.push(RwStep::Visit(value.into_inner(), scope));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        steps.push(RwStep::Post(RwPost::Lambda { params }));
                        steps.push(RwStep::Visit(body.into_inner(), scope));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        steps.push(RwStep::Post(RwPost::RecFn { name, params }));
                        steps.push(RwStep::Visit(body.into_inner(), scope));
                    }
                    // No binder of its own: every child stays in this scope.
                    other => match super::scope_recurse::plain_children(other) {
                        Ok((kind, children)) => {
                            steps.push(RwStep::Post(RwPost::Plain(kind)));
                            // Reversed so they pop in source order.
                            for c in children.into_iter().rev() {
                                steps.push(RwStep::Visit(c, Rc::clone(&scope)));
                            }
                        }
                        Err(leaf) => done.push(leaf),
                    },
                }
            }
            // Ran after the `when` subject, before the first clause.
            RwStep::WhenClauses { clauses, scope } => {
                let subject_var_id = extract_var_id(done.last().expect("when subject"));
                // Reversed so clause 0 is processed first: a later clause's
                // binder synthesis must see everything the earlier clauses
                // minted, since `fresh_binding` hands out ids in call order.
                for clause in clauses.into_iter().rev() {
                    steps.push(RwStep::Clause {
                        clause,
                        scope: Rc::clone(&scope),
                        subject_var_id,
                    });
                }
            }
            // One clause: yields the (possibly rewritten) pattern plus the
            // scope its body and guard are traversed under.
            RwStep::Clause {
                clause: c,
                scope,
                subject_var_id,
            } => {
                let (pattern, clause_scope) = match (c.pattern, subject_var_id) {
                    (
                        WhenPattern::Constructor {
                            type_hint,
                            tag,
                            fields,
                            shape,
                        },
                        Some(sid),
                    ) => {
                        // (a) Promote `_` binders for accessed fields
                        //     within the declared arity.
                        // (b) Expand the pattern with synthesized
                        //     `field_N` binders for accesses past it.
                        let promoted_fields =
                            promote_used_underscore_binders(&fields, sid, &c.body);
                        let expanded_fields =
                            expand_pattern_for_overflow_accesses(&promoted_fields, sid, &c.body);
                        let new_shape =
                            update_shape_for_expanded_fields(shape, expanded_fields.len());
                        let new_scope = scope.extend(sid, &expanded_fields);
                        (
                            WhenPattern::Constructor {
                                type_hint,
                                tag,
                                fields: expanded_fields,
                                shape: new_shape,
                            },
                            new_scope,
                        )
                    }
                    (pat, _) => (pat, (*scope).clone()),
                };
                let clause_scope = Rc::new(clause_scope);
                clauses_done.push((pattern, c.guard.is_some()));
                // Reversed: the guard is rewritten before the body.
                steps.push(RwStep::Visit(c.body, Rc::clone(&clause_scope)));
                if let Some(g) = c.guard {
                    steps.push(RwStep::Visit(g, clause_scope));
                }
            }
            RwStep::Post(post) => {
                let rebuilt = match post {
                    RwPost::When {
                        subject_name,
                        count,
                    } => {
                        let layout = clauses_done.split_off(clauses_done.len() - count);
                        let total = 1 + layout
                            .iter()
                            .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = super::scope_recurse::take(&mut done, total).into_iter();
                        let new_subject = parts.next().expect("when subject");
                        let new_clauses = layout
                            .into_iter()
                            .map(|(pattern, has_guard)| WhenClause {
                                pattern,
                                guard: has_guard.then(|| parts.next().expect("when guard")),
                                body: parts.next().expect("when clause body"),
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(new_subject),
                            subject_name,
                            clauses: new_clauses,
                        }
                    }
                    RwPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    RwPost::LetDrop {
                        let_id,
                        target_name,
                        target_id,
                    } => substitute_var(
                        done.pop().expect("let body"),
                        let_id,
                        target_name.as_str(),
                        target_id,
                    ),
                    RwPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    RwPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    RwPost::Plain(kind) => super::scope_recurse::rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

/// A job on [`rewrite`]'s stack. `WhenClauses` and `Clause` are the points run between
/// two child walks.
enum RwStep {
    Visit(PseudoExpr, Rc<PatternScope>),
    WhenClauses {
        clauses: Vec<WhenClause>,
        scope: Rc<PatternScope>,
    },
    Clause {
        clause: WhenClause,
        scope: Rc<PatternScope>,
        subject_var_id: Option<VarId>,
    },
    Post(RwPost),
}

enum RwPost {
    When {
        subject_name: Option<Binder>,
        count: usize,
    },
    Let {
        name: String,
        id: Option<VarId>,
    },
    /// The dropped alias `let`: after its body is rewritten, references to the
    /// dead binder are rewired onto the pattern binder.
    LetDrop {
        let_id: VarId,
        target_name: String,
        target_id: VarId,
    },
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    Plain(super::scope_recurse::PlainPost),
}

/// Match the field-access shape and return the pattern binder
/// Var the scope names for it, or `None` if there is no match.
fn try_substitute(expr: &PseudoExpr, scope: &PatternScope) -> Option<PseudoExpr> {
    // (A) `FieldAccess { record: FieldAccess { record: Var(s),
    //      selector: NamedField("fields") }, selector: ListHead }`
    //     → field 0
    // (B) `IndexAccess { collection: <same>, index: N }` → field N
    match expr {
        PseudoExpr::FieldAccess { record, selector }
            if matches!(selector, FieldSelector::ListHead) =>
        {
            let inner = match record.as_ref() {
                PseudoExpr::FieldAccess {
                    record: inner_record,
                    selector: inner_selector,
                } if matches!(inner_selector, FieldSelector::NamedField(n) if n == "fields") => {
                    inner_record.as_ref()
                }
                _ => return None,
            };
            let s_id = extract_var_id(inner)?;
            let (name, binder_id) = scope.lookup(s_id, 0)?;
            Some(PseudoExpr::Var {
                name: name.clone(),
                id: Some(binder_id),
            })
        }
        PseudoExpr::IndexAccess { collection, index } => {
            let inner = match collection.as_ref() {
                PseudoExpr::FieldAccess {
                    record: inner_record,
                    selector: inner_selector,
                } if matches!(inner_selector, FieldSelector::NamedField(n) if n == "fields") => {
                    inner_record.as_ref()
                }
                _ => return None,
            };
            let s_id = extract_var_id(inner)?;
            let (name, binder_id) = scope.lookup(s_id, *index)?;
            Some(PseudoExpr::Var {
                name: name.clone(),
                id: Some(binder_id),
            })
        }
        _ => None,
    }
}

fn extract_var_id(expr: &PseudoExpr) -> Option<VarId> {
    if let PseudoExpr::Var { id: Some(id), .. } = expr {
        Some(*id)
    } else {
        None
    }
}

/// Rename each `_`-named binder whose field the body actually reads
/// via `subject.fields.head` / `subject.fields[i]` to `field_{i}`,
/// so the substitution has a name to point to. Other binders are
/// left unchanged.
fn promote_used_underscore_binders(
    fields: &[Binder],
    subject_id: VarId,
    body: &PseudoExpr,
) -> Vec<Binder> {
    fields
        .iter()
        .enumerate()
        .map(|(i, b)| {
            if b == "_" && body_accesses_field(body, subject_id, i) {
                Binder::new(format!("field_{}", i), b.var_id())
            } else {
                b.clone()
            }
        })
        .collect()
}

/// Append `field_N` binders for any field index N the body reads
/// via `subject.fields.head` / `subject.fields[N]` beyond the
/// pattern's declared arity — a 0-arity `expect` whose body then
/// projects a dozen fields is the common case. Each synthesized
/// binder gets a fresh VarId.
///
/// `fields` is the already-promoted binder vector; returns it
/// unchanged when there is nothing to append.
fn expand_pattern_for_overflow_accesses(
    fields: &[Binder],
    subject_id: VarId,
    body: &PseudoExpr,
) -> Vec<Binder> {
    let max_accessed = collect_max_field_index(body, subject_id);
    let Some(max_index) = max_accessed else {
        return fields.to_vec();
    };
    if max_index < fields.len() {
        return fields.to_vec();
    }
    let mut out: Vec<Binder> = fields.to_vec();
    for i in fields.len()..=max_index {
        out.push(Binder::new(format!("field_{}", i), VarId::fresh_binding()));
    }
    out
}

/// Grow the pattern's ConstructorShape arity to the (possibly
/// expanded) field-binder count. Only `Unknown { tag, arity }`
/// shapes grow — `Known(_)` names a closed-set ADT constructor
/// whose arity is fixed.
fn update_shape_for_expanded_fields(shape: ConstructorShape, new_arity: usize) -> ConstructorShape {
    match shape {
        ConstructorShape::Unknown { arity, .. } if new_arity > arity => shape.with_arity(new_arity),
        other => other,
    }
}

/// Walk `body` collecting the maximum field index accessed via
/// `subject.fields.head` (index 0) or `subject.fields[N]` (index N).
/// Returns `None` if no accesses found.
fn collect_max_field_index(body: &PseudoExpr, subject_id: VarId) -> Option<usize> {
    let mut max: Option<usize> = None;
    walk_max_index(body, subject_id, &mut max);
    max
}

/// The structural descent was `map_children`'s child set exactly, so it is
/// now `scope_recurse::children`; children are pushed in REVERSE so they pop
/// in source order (`max` itself is order-independent).
fn walk_max_index(expr: &PseudoExpr, subject_id: VarId, max: &mut Option<usize>) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        let observed: Option<usize> = match expr {
            PseudoExpr::FieldAccess { record, selector }
                if matches!(selector, FieldSelector::ListHead) =>
            {
                if let PseudoExpr::FieldAccess {
                    record: inner_record,
                    selector: inner_selector,
                } = record.as_ref()
                    && matches!(inner_selector, FieldSelector::NamedField(n) if n == "fields")
                    && matches!(inner_record.as_ref(), PseudoExpr::Var { id: Some(sid), .. } if *sid == subject_id)
                {
                    Some(0)
                } else {
                    None
                }
            }
            PseudoExpr::IndexAccess { collection, index } => {
                if let PseudoExpr::FieldAccess {
                    record: inner_record,
                    selector: inner_selector,
                } = collection.as_ref()
                    && matches!(inner_selector, FieldSelector::NamedField(n) if n == "fields")
                    && matches!(inner_record.as_ref(), PseudoExpr::Var { id: Some(sid), .. } if *sid == subject_id)
                {
                    Some(*index)
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(i) = observed {
            *max = Some(max.map(|m| m.max(i)).unwrap_or(i));
        }
        // Descend structurally.
        for child in super::scope_recurse::children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// True when `expr` contains the shape this pass substitutes for
/// `index`: `subject.fields.head` (index 0) or
/// `subject.fields[index]`, over `Var(subject_id)`.
fn body_accesses_field(expr: &PseudoExpr, subject_id: VarId, index: usize) -> bool {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if accesses_field_here(expr, subject_id, index) {
            return true;
        }
        for child in super::scope_recurse::children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
    false
}

/// The access shape, tested at THIS node only: `subject.fields.head`
/// (index 0) or `subject.fields[index]`, over `Var(subject_id)`.
fn accesses_field_here(expr: &PseudoExpr, subject_id: VarId, index: usize) -> bool {
    let inner = match expr {
        PseudoExpr::FieldAccess { record, selector }
            if matches!(selector, FieldSelector::ListHead) && index == 0 =>
        {
            record.as_ref()
        }
        PseudoExpr::IndexAccess {
            collection,
            index: i,
        } if *i == index => collection.as_ref(),
        _ => return false,
    };
    matches!(
        inner,
        PseudoExpr::FieldAccess {
            record: inner_record,
            selector: inner_selector,
        } if matches!(inner_selector, FieldSelector::NamedField(n) if n == "fields")
            && matches!(inner_record.as_ref(), PseudoExpr::Var { id: Some(sid), .. } if *sid == subject_id)
    )
}

/// Substitute every `Var { id: Some(let_id), .. }` in `expr` with
/// `Var { name: target_name, id: Some(target_id) }`.
fn substitute_var(
    expr: PseudoExpr,
    let_id: VarId,
    target_name: &str,
    target_id: VarId,
) -> PseudoExpr {
    map_tree(expr, |e| match &e {
        PseudoExpr::Var { id: Some(id), .. } if *id == let_id => {
            NodeAction::Done(PseudoExpr::Var {
                name: target_name.to_string(),
                id: Some(target_id),
            })
        }
        _ => NodeAction::Descend(e),
    })
}

/// What [`map_tree`]'s per-node hook decided for one node.
enum NodeAction {
    /// Use this expression verbatim; do not descend into it.
    Done(PseudoExpr),
    /// Rebuild this expression from its mapped children.
    Descend(PseudoExpr),
}

/// A job on [`map_tree`]'s stack. This pass carries no scope of its own — the
/// same rule applies to every child — so a step needs no environment.
enum MapStep {
    Visit(PseudoExpr),
    Post(MapPost),
}

enum MapPost {
    Let {
        name: String,
        id: Option<VarId>,
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
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(super::scope_recurse::PlainPost),
}

/// Rebuild `expr` bottom-up, consulting `at_node` on the way down: a
/// [`NodeAction::Done`] replaces the node without descending into it, a
/// [`NodeAction::Descend`] is rebuilt from its mapped children exactly as
/// `scope_recurse::map_children` would.
///
/// Shared by this file's three whole-tree maps — the alias inliner and the
/// two `Var` substitutions — which differ only in that hook.
///
/// Children are pushed in REVERSE so they pop in source order, and a node's
/// children come off `done` in that same order when it is rebuilt.
fn map_tree(expr: PseudoExpr, mut at_node: impl FnMut(PseudoExpr) -> NodeAction) -> PseudoExpr {
    let mut steps: Vec<MapStep> = vec![MapStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            MapStep::Visit(expr) => {
                let expr = match at_node(expr) {
                    NodeAction::Done(e) => {
                        done.push(e);
                        continue;
                    }
                    NodeAction::Descend(e) => e,
                };
                match expr {
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        steps.push(MapStep::Post(MapPost::Let { name, id }));
                        steps.push(MapStep::Visit(body.into_inner()));
                        steps.push(MapStep::Visit(value.into_inner()));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        steps.push(MapStep::Post(MapPost::Lambda { params }));
                        steps.push(MapStep::Visit(body.into_inner()));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        steps.push(MapStep::Post(MapPost::RecFn { name, params }));
                        steps.push(MapStep::Visit(body.into_inner()));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let mut clause_meta = Vec::with_capacity(clauses.len());
                        let mut clause_children = Vec::new();
                        for c in clauses {
                            clause_meta.push((c.pattern, c.guard.is_some()));
                            if let Some(g) = c.guard {
                                clause_children.push(g);
                            }
                            clause_children.push(c.body);
                        }
                        steps.push(MapStep::Post(MapPost::When {
                            subject_name,
                            clause_meta,
                        }));
                        for c in clause_children.into_iter().rev() {
                            steps.push(MapStep::Visit(c));
                        }
                        steps.push(MapStep::Visit(subject.into_inner()));
                    }
                    other => match super::scope_recurse::plain_children(other) {
                        Ok((kind, children)) => {
                            steps.push(MapStep::Post(MapPost::Plain(kind)));
                            for c in children.into_iter().rev() {
                                steps.push(MapStep::Visit(c));
                            }
                        }
                        Err(leaf) => done.push(leaf),
                    },
                }
            }
            MapStep::Post(post) => {
                let rebuilt = match post {
                    MapPost::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    MapPost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    MapPost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    MapPost::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total = 1 + clause_meta
                            .iter()
                            .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = super::scope_recurse::take(&mut done, total).into_iter();
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
                    MapPost::Plain(kind) => super::scope_recurse::rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "map_tree must leave one result");
    done.pop().expect("map_tree result")
}

#[cfg(test)]
mod tests;
