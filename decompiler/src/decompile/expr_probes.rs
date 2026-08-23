//! Structural probes and small rewrites over `PseudoExpr`.
//!
//! Two kinds of thing, both shared by the orchestration in
//! `decompile/mod.rs` and by the purpose splitter: predicates that ask
//! whether a tree CONTAINS some shape, and the name/id-keyed rewrites
//! (alias elimination, dead-let removal, scoped rename) those predicates
//! guard.
//!
//! Everything here is scope-aware: a probe that walks past a binder of
//! the same name would answer about the wrong binding, so the shadowing
//! checks (`binder_shadows_binding`, `when_pattern_shadows_binding`) are
//! part of the walk rather than a caller's responsibility.

use super::*;
use crate::pseudo::ast::PBox;

/// Walk a PseudoExpr tree and check if any node matches the predicate.
pub(super) fn contains_predicate(expr: &PseudoExpr, pred: &dyn Fn(&PseudoExpr) -> bool) -> bool {
    contains_predicate_with_options(expr, pred, true)
}

pub(super) fn contains_predicate_with_options(
    expr: &PseudoExpr,
    pred: &dyn Fn(&PseudoExpr) -> bool,
    include_literal_patterns: bool,
) -> bool {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(e) = stack.pop() {
        if pred(e) {
            return true;
        }
        match e {
            PseudoExpr::Let { value, body, .. } => {
                stack.push(body);
                stack.push(value);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                stack.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    stack.push(a);
                }
                stack.push(function);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.push(else_branch);
                stack.push(then_branch);
                stack.push(condition);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    stack.push(&c.body);
                    if let Some(g) = &c.guard {
                        stack.push(g);
                    }
                    if include_literal_patterns
                        && let crate::pseudo::ast::WhenPattern::Literal(lit) = &c.pattern
                    {
                        stack.push(lit);
                    }
                }
                stack.push(subject);
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    stack.push(t);
                }
                for e in elements.iter().rev() {
                    stack.push(e);
                }
            }
            PseudoExpr::Tuple(elements) => {
                for e in elements.iter().rev() {
                    stack.push(e);
                }
            }
            PseudoExpr::Pair(a, b) => {
                stack.push(b);
                stack.push(a);
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    stack.push(f);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => stack.push(record),
            PseudoExpr::IndexAccess { collection, .. } => stack.push(collection),
            PseudoExpr::BinOp { left, right, .. } => {
                stack.push(right);
                stack.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => stack.push(operand),
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    stack.push(a);
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => stack.push(inner),
            PseudoExpr::Trace { message, value } => {
                stack.push(value);
                stack.push(message);
            }
            // `Data`'s inner value is deliberately not explored.
            PseudoExpr::Data(_)
            | PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
    false
}

pub(super) fn contains_builtin_call_named(expr: &PseudoExpr, builtin_name: &str) -> bool {
    contains_predicate(
        expr,
        &|e| matches!(e, PseudoExpr::BuiltinCall { name, .. } if name == builtin_name),
    )
}

pub(super) fn contains_expect_unpack_tag_check(expr: &PseudoExpr) -> bool {
    fn extract_unpack_subject(expr: &PseudoExpr) -> Option<&str> {
        if let PseudoExpr::BuiltinCall { name, args } = expr
            && (*name == crate::BuiltinId::ConstrUnpack || *name == crate::BuiltinId::DataUnConstr)
            && args.len() == 1
            && let PseudoExpr::Var { name, .. } = &args[0]
        {
            return Some(name.as_str());
        }
        None
    }

    fn extract_unpack_fst_subject(expr: &PseudoExpr) -> Option<&str> {
        match expr {
            PseudoExpr::FieldAccess {
                record, selector, ..
            } if selector.is_pair_fst() => extract_unpack_subject(record),
            PseudoExpr::IndexAccess {
                collection,
                index: 0,
            } => extract_unpack_subject(collection),
            _ => None,
        }
    }

    fn is_expect_unpack_tag_check(expr: &PseudoExpr) -> bool {
        if let PseudoExpr::BinOp {
            op: crate::pseudo::ast::BinaryOp::Eq,
            left,
            right,
        } = expr
        {
            return (extract_unpack_fst_subject(left).is_some()
                && matches!(right.as_ref(), PseudoExpr::Int(_)))
                || (extract_unpack_fst_subject(right).is_some()
                    && matches!(left.as_ref(), PseudoExpr::Int(_)));
        }
        false
    }

    contains_predicate(expr, &|e| {
        matches!(
            e,
            PseudoExpr::Apply { function, args }
                if matches!(
                    function.as_ref(),
                    PseudoExpr::Var { name, .. } if name == "expect!"
                ) && args.len() == 2
                    && is_expect_unpack_tag_check(&args[0])
        )
    })
}

pub(super) fn contains_nested_recfn_body(expr: &PseudoExpr) -> bool {
    contains_predicate(
        expr,
        &|e| matches!(e, PseudoExpr::RecFn { body, .. } if matches!(body.as_ref(), PseudoExpr::RecFn { .. })),
    )
}

pub(super) fn contains_immediate_lambda_application(expr: &PseudoExpr) -> bool {
    contains_predicate(expr, &|e| {
        matches!(
            e,
            PseudoExpr::Apply { function, args }
                if matches!(
                    function.as_ref(),
                    PseudoExpr::Lambda { params, .. } if !params.is_empty() && params.len() == args.len()
                )
        )
    })
}

/// Remove Let bindings whose bound variable is unused in the body —
/// those that survive the simplifier's depth-guard bail-out.
pub(super) fn eliminate_dead_lets_pseudo(expr: PseudoExpr) -> PseudoExpr {
    let (nameless, table) = crate::pseudo::nameless::convert::pseudo_to_nameless(&expr);
    let cleaned = crate::decompile::dead_let_nameless::eliminate_dead_lets_nameless(nameless);
    crate::pseudo::nameless::convert::nameless_to_pseudo(&cleaned, &table)
}

/// Check if a name is rebound (shadowed) anywhere inside an expression.
pub(super) fn name_is_rebound_in(expr: &PseudoExpr, target: &str) -> bool {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Let {
                name, value, body, ..
            } => {
                if name == target {
                    return true;
                }
                pending.push(value.as_ref());
                pending.push(body.as_ref());
            }
            PseudoExpr::Lambda { params, body } => {
                if params.iter().any(|p| p == target) {
                    return true;
                }
                pending.push(body.as_ref());
            }
            PseudoExpr::RecFn { name, params, body } => {
                if name == target || params.iter().any(|p| p == target) {
                    return true;
                }
                pending.push(body.as_ref());
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition.as_ref());
                pending.push(then_branch.as_ref());
                pending.push(else_branch.as_ref());
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                if subject_name_matches_target(subject_name.as_ref(), target) {
                    return true;
                }
                pending.push(subject.as_ref());
                for c in clauses {
                    if when_pattern_binds_name(&c.pattern, target) {
                        return true;
                    }
                    if let WhenPattern::Literal(lit) = &c.pattern {
                        pending.push(lit);
                    }
                    if let Some(guard) = &c.guard {
                        pending.push(guard);
                    }
                    pending.push(&c.body);
                }
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function.as_ref());
                pending.extend(args.iter());
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left.as_ref());
                pending.push(right.as_ref());
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand.as_ref()),
            PseudoExpr::Trace { message, value } => {
                pending.push(message.as_ref());
                pending.push(value.as_ref());
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner.as_ref()),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record.as_ref()),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection.as_ref()),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(t) = tail.as_deref() {
                    pending.push(t);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items.iter()),
            PseudoExpr::Pair(a, b) => {
                pending.push(a.as_ref());
                pending.push(b.as_ref());
            }
            _ => {}
        }
    }
    false
}

pub(super) fn subject_name_matches_target(subject_name: Option<&Binder>, target: &str) -> bool {
    subject_name.is_some_and(|subject_name| subject_name == target)
}

pub(super) fn when_pattern_binds_name(pattern: &WhenPattern, target: &str) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
            fields.iter().any(|field| field == target)
        }
        WhenPattern::List { elements, tail } => {
            elements.iter().any(|element| element == target)
                || tail.as_ref().is_some_and(|tail| tail == target)
        }
        WhenPattern::Pair(first, second) => first == target || second == target,
        WhenPattern::Var(name) => name == target,
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}

pub(super) fn var_ref_matches_binding(
    ref_name: &str,
    ref_id: &Option<crate::pseudo::var_id::VarId>,
    binding_name: &str,
    binding_id: Option<crate::pseudo::var_id::VarId>,
) -> bool {
    crate::decompile::var_match::refs_match(ref_name, ref_id.get(), binding_name, binding_id)
}

pub(super) fn binder_shadows_binding(
    binder: &Binder,
    binding_name: &str,
    binding_id: Option<crate::pseudo::var_id::VarId>,
) -> bool {
    binder == binding_name
        || crate::decompile::var_match::ids_match_strict(binding_id, binder.id.get())
}

pub(super) fn when_pattern_shadows_binding(
    pattern: &WhenPattern,
    binding_name: &str,
    binding_id: Option<crate::pseudo::var_id::VarId>,
) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => fields
            .iter()
            .any(|field| binder_shadows_binding(field, binding_name, binding_id)),
        WhenPattern::List { elements, tail } => {
            elements
                .iter()
                .any(|element| binder_shadows_binding(element, binding_name, binding_id))
                || tail
                    .as_ref()
                    .is_some_and(|tail| binder_shadows_binding(tail, binding_name, binding_id))
        }
        WhenPattern::Pair(first, second) => {
            binder_shadows_binding(first, binding_name, binding_id)
                || binder_shadows_binding(second, binding_name, binding_id)
        }
        WhenPattern::Var(name) => binder_shadows_binding(name, binding_name, binding_id),
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}

/// Split a node into a SHELL — every immediate child replaced by a `Unit`
/// placeholder — plus those children in `map_children` order. The shell is
/// refilled by [`join_children`], which re-walks the same slots in the same
/// order, so the placeholders are never observed.
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

/// Takes the last `n` items off `done` — the children of the node being
/// reassembled, left there in source order by the walk.
fn take_done(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
    let at = done.len() - n;
    done.split_off(at)
}

enum RenameStep {
    Visit(PseudoExpr),
    Post(RenamePost),
}

enum RenamePost {
    /// `body` is `Some` when the `let` shadows `from`, so its body was kept
    /// verbatim and no `Visit` step was queued for it.
    Let {
        name: String,
        id: Option<crate::pseudo::var_id::VarId>,
        body: Option<PBox>,
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
        layout: Vec<RenameClause>,
    },
    /// Any other node: its rewritten children sit on `done`; put them back
    /// into the shell they were taken out of.
    Plain {
        shell: PseudoExpr,
        count: usize,
    },
}

/// One `when` clause awaiting reassembly: everything that is NOT a queued
/// child, plus how many children it left on `done`.
struct RenameClause {
    /// `None` for a `Literal` pattern, whose payload went through the walk
    /// and is rebuilt from `done`.
    pattern: Option<WhenPattern>,
    guard: Option<RenameSlot>,
    body: RenameSlot,
}

/// A clause's guard/body position.
enum RenameSlot {
    /// A `Visit` step was queued; the renamed result is on `done`.
    Queued,
    /// The clause shadows `from` — left untouched.
    Kept(PseudoExpr),
}

impl RenameSlot {
    fn take(self, parts: &mut impl Iterator<Item = PseudoExpr>) -> PseudoExpr {
        match self {
            Self::Queued => parts.next().expect("queued clause child"),
            Self::Kept(expr) => expr,
        }
    }
}

impl RenameClause {
    fn child_count(&self) -> usize {
        usize::from(self.pattern.is_none())
            + usize::from(matches!(self.guard, Some(RenameSlot::Queued)))
            + usize::from(matches!(self.body, RenameSlot::Queued))
    }

    fn rebuild(
        self,
        parts: &mut impl Iterator<Item = PseudoExpr>,
    ) -> crate::pseudo::ast::WhenClause {
        let pattern = match self.pattern {
            Some(p) => p,
            None => WhenPattern::Literal(parts.next().expect("literal payload")),
        };
        let guard = self.guard.map(|g| g.take(parts));
        let body = self.body.take(parts);
        crate::pseudo::ast::WhenClause {
            pattern,
            guard,
            body,
        }
    }
}

/// Rename all free occurrences of `from` to `to` in a body expression.
/// Stops at binders that shadow `from`.
///
/// When `to_id` is `Some`, Var refs get the substituted id too (proper
/// alias-substitution; matches `Simplifier::substitute_var_for_var`).
/// When `None`, the ref keeps its original VarId; minting a fresh
/// synthetic id per rename instead orphans the reference from its
/// binder.
pub(super) fn rename_in_body_with_id(
    expr: PseudoExpr,
    from: &str,
    from_id: Option<crate::pseudo::var_id::VarId>,
    to: &str,
    to_id: Option<crate::pseudo::var_id::VarId>,
) -> PseudoExpr {
    let mut steps: Vec<RenameStep> = vec![RenameStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RenameStep::Visit(expr) => match expr {
                PseudoExpr::Var { ref name, id }
                    if var_ref_matches_binding(name, &id, from, from_id) =>
                {
                    done.push(PseudoExpr::Var {
                        name: to.to_string(),
                        id: to_id.or(id),
                    });
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    // If this let shadows `from`, stop renaming in body
                    let body_shadowed = name == from
                        || crate::decompile::var_match::ids_match_strict(from_id, id.get());
                    if body_shadowed {
                        steps.push(RenameStep::Post(RenamePost::Let {
                            name,
                            id,
                            body: Some(body),
                        }));
                    } else {
                        steps.push(RenameStep::Post(RenamePost::Let {
                            name,
                            id,
                            body: None,
                        }));
                        steps.push(RenameStep::Visit(body.into_inner()));
                    }
                    steps.push(RenameStep::Visit(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    if params
                        .iter()
                        .any(|p| binder_shadows_binding(p, from, from_id))
                    {
                        done.push(PseudoExpr::Lambda { params, body });
                    } else {
                        steps.push(RenameStep::Post(RenamePost::Lambda { params }));
                        steps.push(RenameStep::Visit(body.into_inner()));
                    }
                }
                PseudoExpr::RecFn { name, params, body } => {
                    if binder_shadows_binding(&name, from, from_id)
                        || params
                            .iter()
                            .any(|p| binder_shadows_binding(p, from, from_id))
                    {
                        done.push(PseudoExpr::RecFn { name, params, body });
                    } else {
                        steps.push(RenameStep::Post(RenamePost::RecFn { name, params }));
                        steps.push(RenameStep::Visit(body.into_inner()));
                    }
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let subject_shadows = subject_name.as_ref().is_some_and(|subject_name| {
                        binder_shadows_binding(subject_name, from, from_id)
                    });
                    let mut layout: Vec<RenameClause> = Vec::with_capacity(clauses.len());
                    // Built in source order, then drained onto `steps` in
                    // reverse so the jobs pop in source order.
                    let mut jobs: Vec<RenameStep> = Vec::new();
                    for c in clauses {
                        // A literal pattern's payload is renamed
                        // unconditionally, before the clause's own shadowing
                        // is even known.
                        let pattern = match c.pattern {
                            WhenPattern::Literal(payload) => {
                                jobs.push(RenameStep::Visit(payload));
                                None
                            }
                            other => Some(other),
                        };
                        let clause_shadows = subject_shadows
                            || pattern.as_ref().is_some_and(|pattern| {
                                when_pattern_shadows_binding(pattern, from, from_id)
                            });
                        let guard = c.guard.map(|guard| {
                            if clause_shadows {
                                RenameSlot::Kept(guard)
                            } else {
                                jobs.push(RenameStep::Visit(guard));
                                RenameSlot::Queued
                            }
                        });
                        let body = if clause_shadows {
                            RenameSlot::Kept(c.body)
                        } else {
                            jobs.push(RenameStep::Visit(c.body));
                            RenameSlot::Queued
                        };
                        layout.push(RenameClause {
                            pattern,
                            guard,
                            body,
                        });
                    }
                    steps.push(RenameStep::Post(RenamePost::When {
                        subject_name,
                        layout,
                    }));
                    while let Some(job) = jobs.pop() {
                        steps.push(job);
                    }
                    steps.push(RenameStep::Visit(subject.into_inner()));
                }
                // The non-binding variants, in `map_children`'s order.
                // Leaves (Int, ByteArray, String, Bool, Unit, Error, Raw,
                // Data, non-matching Var) split into zero children and are
                // rejoined unchanged.
                other => {
                    let (shell, kids) = split_children(other);
                    steps.push(RenameStep::Post(RenamePost::Plain {
                        shell,
                        count: kids.len(),
                    }));
                    for k in kids.into_iter().rev() {
                        steps.push(RenameStep::Visit(k));
                    }
                }
            },
            RenameStep::Post(post) => {
                let rebuilt = match post {
                    RenamePost::Let { name, id, body } => {
                        let new_body = match body {
                            Some(kept) => kept,
                            None => PBox::new(done.pop().expect("let body")),
                        };
                        let new_value = PBox::new(done.pop().expect("let value"));
                        PseudoExpr::Let {
                            name,
                            id,
                            value: new_value,
                            body: new_body,
                        }
                    }
                    RenamePost::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    RenamePost::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    RenamePost::When {
                        subject_name,
                        layout,
                    } => {
                        let children: usize =
                            layout.iter().map(RenameClause::child_count).sum::<usize>() + 1;
                        let mut parts = take_done(&mut done, children).into_iter();
                        let subject = PBox::new(parts.next().expect("when subject"));
                        let clauses = layout.into_iter().map(|c| c.rebuild(&mut parts)).collect();
                        PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses,
                        }
                    }
                    RenamePost::Plain { shell, count } => {
                        let kids = take_done(&mut done, count);
                        join_children(shell, kids)
                    }
                };
                done.push(rebuilt);
            }
        }
    }

    done.pop()
        .expect("rename_in_body_with_id leaves exactly one result")
}

/// Eliminate trivial variable aliases: `let x = y in body` → `body[x/y]`.
/// Runs late in the pipeline after flatten_let_chains may expose new aliases.
pub(super) fn eliminate_var_aliases(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;
    use crate::pseudo::var_id::{OptionVarIdGet, VarId};

    struct AliasElim;
    impl ExprFolder for AliasElim {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_let(
            &mut self,
            name: String,
            id: Option<crate::pseudo::var_id::VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            let id_concrete = id.unwrap_or_else(VarId::fresh_compat_placeholder);
            // Drop `let x = fix` / `let x = delay(fix)` / `let x = force(fix)` bindings —
            // Y-combinator residues the rec fn conversion pass did not resolve. Only drop
            // when the binding is unreferenced in the body. The residue appears either as
            // `HelperSymbol(Fix)` (what `fix_helper()` emits) or as `Var("fix")`, so match
            // both shapes.
            {
                let inner = match &value {
                    PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => inner.as_ref(),
                    other => other,
                };
                let is_fix_residue = matches!(inner, PseudoExpr::Var { name: n, .. } if n == "fix")
                    || matches!(
                        inner,
                        PseudoExpr::HelperSymbol(crate::pseudo::ast::HelperIntrinsic::Fix)
                    );
                if is_fix_residue
                    && !crate::decompile::helper::hoist::var_is_referenced_id_aware(
                        &body,
                        id_concrete,
                        &name,
                    )
                {
                    return body;
                }
            }

            if let PseudoExpr::Var {
                name: ref aliased,
                id: Some(alias_id),
            } = value
            {
                // Safety: only inline if the alias target is not shadowed in the body.
                // If `aliased` is rebound anywhere in `body` (let name, lambda param,
                // or recfn param), the substitution could capture.
                if name_is_rebound_in(&body, aliased) {
                    return PseudoExpr::Let {
                        name,
                        id,
                        value: PBox::new(value),
                        body: PBox::new(body),
                    };
                }
                let aliased = aliased.clone();
                // Pass the alias target's VarId so renamed refs resolve
                // against the aliased binder's id. Without it,
                // `rename_in_body` mints an orphan
                // `VarId::fresh_compat_placeholder()` per ref.
                rename_in_body_with_id(body, &name, id.get(), &aliased, Some(alias_id))
            } else {
                PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(body),
                }
            }
        }
    }
    AliasElim.fold(expr)
}

/// Recover a Scott-encoded constructor from a lambda over its case
/// continuations: with N >= 2 params of which exactly one, at index `i`,
/// is used, `fn(x0, ..., xN) { xi(args) }` becomes `Constr<i>(args)`, and
/// a bare `fn(x0, ..., xN) { xi }` becomes the nullary `Constr<i>`.
///
/// Returns `None` if any other param is live, or if the used param also
/// occurs inside `args` — that is not a plain injection.
pub(super) fn try_scott_constructor_lambda(
    params: &[Binder],
    body: &PseudoExpr,
) -> Option<PseudoExpr> {
    if params.len() < 2 {
        return None;
    }

    let mut used_idx: Option<usize> = None;
    for (i, p) in params.iter().enumerate() {
        if crate::decompile::simplify::Simplifier::is_var_used_by_id(
            body,
            p.as_str(),
            Some(p.var_id()),
        ) {
            if used_idx.is_some() {
                return None;
            }
            used_idx = Some(i);
        }
    }
    let used_idx = used_idx?;
    let used_name = &params[used_idx];

    match body {
        PseudoExpr::Var { id, .. } if *id == Some(used_name.var_id()) => Some(PseudoExpr::constr(
            ConstructorShape::unknown_data(used_idx, 0),
            vec![],
        )),
        PseudoExpr::Apply { function, args } => {
            if let PseudoExpr::Var { id, .. } = function.as_ref()
                && *id == Some(used_name.var_id())
            {
                if args.iter().any(|arg| {
                    crate::decompile::simplify::Simplifier::is_var_used_by_id(
                        arg,
                        used_name.as_str(),
                        Some(used_name.var_id()),
                    )
                }) {
                    return None;
                }
                return Some(PseudoExpr::constr(
                    ConstructorShape::unknown_data(used_idx, args.len()),
                    (args.clone()).into_vec(),
                ));
            }
            None
        }
        _ => None,
    }
}

pub(super) fn resolve_scott_constructor_lambdas(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    struct ScottConstructorLambdaResolver;

    impl ExprFolder for ScottConstructorLambdaResolver {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_lambda(&mut self, params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
            if let Some(constr) = try_scott_constructor_lambda(&params, &body) {
                return constr;
            }
            PseudoExpr::Lambda {
                params,
                body: PBox::new(body),
            }
        }
    }

    ScottConstructorLambdaResolver.fold(expr)
}

/// Recover `let bound_tag = subject.tag in if bound_tag == ...` dispatch
/// shapes.
///
/// A **no-op compatibility seam**: the dispatch normalization happens in
/// earlier MIR-level structural-recovery passes (Z-combinator collapse,
/// when-subject extraction, etc.). The hook stays so that the pipeline
/// pass ID (`RecoverLetBoundTagIfDispatch`) and its property contract
/// stay reachable for testing, and so that callers can opt out through
/// `StructuralRecoveryPasses::recover_let_bound_tag_dispatch` without
/// disabling the whole structural-recovery group.
///
/// Output is bitwise-identical to input, so that leaf toggle has no
/// observable effect — recorded in
/// `tests/basic.rs::LEAVES_WITHOUT_OBSERVED_EFFECT`.
pub(super) fn recover_let_bound_tag_if_dispatch(expr: PseudoExpr) -> PseudoExpr {
    expr
}

/// Convert `Apply { function: Lambda { params, body }, args }` where
/// `args.len() == params.len()` into a chain of Let bindings.
pub(super) fn resolve_immediate_applications(expr: PseudoExpr) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    struct ImmediateAppResolver;

    impl ExprFolder for ImmediateAppResolver {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
            if let PseudoExpr::Lambda { ref params, .. } = function
                && params.len() == args.len()
                && !params.is_empty()
            {
                // Destructure — the pattern is checked above.
                let (params, body) = match function {
                    PseudoExpr::Lambda { params, body } => (params, body.into_inner()),
                    _ => unreachable!(),
                };
                // Build let chain: let p0 = a0 in let p1 = a1 in ... body
                let mut result = body;
                for (param, value) in params.into_iter().zip(args).rev() {
                    result = PseudoExpr::Let {
                        name: param.to_string(),
                        id: Some(param.id),
                        value: PBox::new(value),
                        body: PBox::new(result),
                    };
                }
                return result;
            }
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
    }

    ImmediateAppResolver.fold(expr)
}

// Boolean / identity / thunk simplification passes live in `boolean_cleanup.rs`.

// Cardano context type propagation + named field resolution passes
// (`propagate_types_and_name_constructors`, `resolve_cardano_field_names`)
// live in `cardano_context_naming.rs`.
