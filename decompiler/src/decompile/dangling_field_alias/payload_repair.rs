use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::builtins::BuiltinId;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::type_hint::TypeHintId;
use crate::pseudo::var_id::VarId;

// Dangling Constr payload binders left over from earlier renames
//
// Cardano-context naming may rename a Constructor pattern's payload binder
// to its schema-defined name (e.g. `Constr<2>(item_0)` →
// `Constr<2>(credential)`) without propagating the rename into the clause
// body, leaving `item_0` as a free reference. Symmetrically, a clause whose
// pattern has no binder may end up with body references to a synthetic
// `item_*` / `t_*` / `t1_*` name that was elided from the pattern.
//
// For every `When` clause with a Constructor or List pattern, free
// synthetic payload refs (see `SYNTHETIC_ROOTS`) are substituted with the
// pattern binder at the matching position, or introduced as the binder
// when the pattern has only `_` or no binders at all.

pub(super) fn repair_dangling_constr_payload_binders(
    expr: PseudoExpr,
    kind_annotations: &HashMap<VarId, VarKind>,
    use_varkind_recovery: bool,
) -> PseudoExpr {
    // Lets the typed predicate resolve refs whose VarId diverged
    // from the binder's via post-mint rename/clone, falling back
    // to a name-resolved kind lookup.
    let name_to_binder_id = crate::decompile::varkind_recovery::build_name_to_binder_id_map(&expr);
    let mut walker = PayloadRepair {
        scope: vec![std::collections::HashSet::new()],
        kind_annotations,
        use_varkind_recovery,
        name_to_binder_id: &name_to_binder_id,
    };
    walker.go(expr)
}

fn looks_like_synthetic_payload(name: &str) -> bool {
    if name == "_" {
        return false;
    }
    // Common simplifier/naming-pass placeholder roots, suffixed with `_N`
    // (or `_N_M` for shadow-disambiguated variants) — the names that leak
    // as orphans across pattern-vs-body rename mismatches.
    const SYNTHETIC_ROOTS: &[&str] = &[
        "item",
        "items",
        "field",
        "fields",
        "int_value",
        "variant",
        "payload",
        "t",
        "t1",
        "t2",
        "i",
    ];
    for root in SYNTHETIC_ROOTS {
        if let Some(rest) = name.strip_prefix(*root)
            && let Some(rest) = rest.strip_prefix('_')
            && !rest.is_empty()
            && rest.chars().all(|c| c == '_' || c.is_ascii_digit())
        {
            return true;
        }
    }
    false
}

/// Selects dangling Constr-payload synthetic refs: typed-affirmative,
/// or legacy name shape. Name resolution lets a ref whose VarId has
/// diverged from its binder still find the binder's kind.
fn is_dangling_synthetic_payload_ref(
    name: &str,
    id: VarId,
    kind_annotations: &HashMap<VarId, VarKind>,
    name_to_binder_id: &HashMap<String, VarId>,
    use_varkind_recovery: bool,
) -> bool {
    crate::decompile::varkind_recovery::is_orphan_payload_ref_typed_or_legacy_with_name_resolution(
        name,
        id,
        kind_annotations,
        name_to_binder_id,
        use_varkind_recovery,
        looks_like_synthetic_payload,
        "dangling",
    )
}

/// A job on [`PayloadRepair::go`]'s stack. `Push`/`Pop` are the scope changes
/// between two child descents; `Post::Clause` is the per-clause repair after
/// them. Each stays its own step.
enum RepairStep {
    Visit(PseudoExpr),
    Push(Vec<VarId>),
    Pop,
    Post(RepairPost),
}

enum RepairPost {
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    Let {
        name: String,
        id: Option<VarId>,
    },
    /// One clause: its repaired guard/body sit on `done`.
    Clause {
        pattern: WhenPattern,
        has_guard: bool,
        subject_name: Option<Binder>,
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

/// Takes the last `n` items off `done`, in source order.
fn take_done(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
    let at = done.len() - n;
    done.split_off(at)
}

struct PayloadRepair<'a> {
    scope: Vec<std::collections::HashSet<VarId>>,
    kind_annotations: &'a HashMap<VarId, VarKind>,
    use_varkind_recovery: bool,
    /// Name → first-binder-id map over the entry expression,
    /// recovering a binder's `kind_annotations` entry when a Var
    /// ref's id has diverged via post-mint rename/clone. Borrowed
    /// because the struct is cloned at every scope push.
    name_to_binder_id: &'a HashMap<String, VarId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SyntheticPayloadRef {
    name: String,
    id: VarId,
}

impl<'a> PayloadRepair<'a> {
    fn push<I: IntoIterator<Item = VarId>>(&mut self, ids: I) {
        self.scope.push(ids.into_iter().collect());
    }

    fn pop(&mut self) {
        self.scope.pop();
    }

    /// One scope stack for the whole walk. `Push`/`Pop` open and close a
    /// binder's frame around its subtree.
    fn collect_free_synthetic(
        &self,
        expr: &PseudoExpr,
        out: &mut std::collections::HashSet<SyntheticPayloadRef>,
    ) {
        enum Step<'e> {
            Visit(&'e PseudoExpr),
            /// Open a binder's scope frame — the matching `Pop` was queued
            /// under it, so it closes when that subtree is done.
            Push(std::collections::HashSet<VarId>),
            Pop,
        }

        let mut scope: Vec<std::collections::HashSet<VarId>> = self.scope.clone();
        let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];

        while let Some(step) = steps.pop() {
            let expr = match step {
                Step::Visit(expr) => expr,
                Step::Push(frame) => {
                    scope.push(frame);
                    continue;
                }
                Step::Pop => {
                    scope.pop();
                    continue;
                }
            };
            match expr {
                PseudoExpr::Var { name, id } => {
                    // A ref with no resolved id gets a fresh compat
                    // placeholder rather than being skipped: it is never in
                    // scope, so unresolved synthetic payload refs still
                    // surface as orphans.
                    let vid = id.unwrap_or_else(VarId::fresh_compat_placeholder);
                    if !scope.iter().any(|s| s.contains(&vid))
                        && is_dangling_synthetic_payload_ref(
                            name,
                            vid,
                            self.kind_annotations,
                            self.name_to_binder_id,
                            self.use_varkind_recovery,
                        )
                    {
                        out.insert(SyntheticPayloadRef {
                            name: name.clone(),
                            id: vid,
                        });
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    let frame: std::collections::HashSet<_> =
                        params.iter().map(|binder| binder.id).collect();
                    steps.push(Step::Pop);
                    steps.push(Step::Visit(body));
                    steps.push(Step::Push(frame));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let mut frame = std::collections::HashSet::new();
                    frame.insert(name.id);
                    for p in params {
                        frame.insert(p.id);
                    }
                    steps.push(Step::Pop);
                    steps.push(Step::Visit(body));
                    steps.push(Step::Push(frame));
                }
                PseudoExpr::Let {
                    id, value, body, ..
                } => {
                    let mut frame = std::collections::HashSet::new();
                    if let Some(vid) = *id {
                        frame.insert(vid);
                    }
                    // Reversed: the value is walked OUTSIDE the binding, the
                    // body inside it.
                    steps.push(Step::Pop);
                    steps.push(Step::Visit(body));
                    steps.push(Step::Push(frame));
                    steps.push(Step::Visit(value));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    // Built in source order, then drained onto `steps` in
                    // reverse so the jobs run in source order.
                    let mut jobs: Vec<Step<'_>> = Vec::new();
                    for clause in clauses {
                        let mut frame: std::collections::HashSet<VarId> =
                            clause.pattern.bound_ids().into_iter().collect();
                        if let Some(s) = subject_name {
                            frame.insert(s.id);
                        }
                        jobs.push(Step::Push(frame));
                        jobs.push(Step::Visit(&clause.body));
                        if let Some(g) = &clause.guard {
                            jobs.push(Step::Visit(g));
                        }
                        jobs.push(Step::Pop);
                    }
                    while let Some(job) = jobs.pop() {
                        steps.push(job);
                    }
                    steps.push(Step::Visit(subject));
                }
                _ => {
                    for child in expr.provenance_children().into_iter().rev() {
                        steps.push(Step::Visit(child));
                    }
                }
            }
        }
    }

    /// The scope stack is the walker's own `self.scope`. `Push`/`Pop` open
    /// and close a binder; a clause's repair (which mints binder ids, so
    /// order matters) runs after that clause's subtree and after its `Pop`.
    fn go(&mut self, expr: PseudoExpr) -> PseudoExpr {
        let mut steps: Vec<RepairStep> = vec![RepairStep::Visit(expr)];
        let mut done: Vec<PseudoExpr> = Vec::new();
        // Repaired clauses, pushed by `Clause` and drained by the matching
        // `When`. LIFO like `done`: a clause's own subtree (and any nested
        // `When` in it) completes before the next clause's step runs.
        let mut clauses_done: Vec<WhenClause> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                RepairStep::Push(ids) => self.push(ids),
                RepairStep::Pop => self.pop(),
                RepairStep::Visit(expr) => match expr {
                    PseudoExpr::Lambda { params, body } => {
                        let ids: Vec<VarId> = params.iter().map(|binder| binder.id).collect();
                        steps.push(RepairStep::Post(RepairPost::Lambda { params }));
                        steps.push(RepairStep::Pop);
                        steps.push(RepairStep::Visit(body.into_inner()));
                        steps.push(RepairStep::Push(ids));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let mut bound_ids: Vec<VarId> = vec![name.id];
                        bound_ids.extend(params.iter().map(|binder| binder.id));
                        steps.push(RepairStep::Post(RepairPost::RecFn { name, params }));
                        steps.push(RepairStep::Pop);
                        steps.push(RepairStep::Visit(body.into_inner()));
                        steps.push(RepairStep::Push(bound_ids));
                    }
                    PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body,
                    } => {
                        // Reversed: the value is walked OUTSIDE the binding,
                        // the body inside it.
                        steps.push(RepairStep::Post(RepairPost::Let { name, id }));
                        steps.push(RepairStep::Pop);
                        steps.push(RepairStep::Visit(body.into_inner()));
                        steps.push(RepairStep::Push(id.into_iter().collect()));
                        steps.push(RepairStep::Visit(value.into_inner()));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        // Built in source order, then drained onto `steps` in
                        // reverse so the jobs run in source order.
                        let mut jobs: Vec<RepairStep> = Vec::new();
                        let clause_count = clauses.len();
                        for clause in clauses {
                            let mut bound = clause.pattern.bound_ids();
                            if let Some(s) = &subject_name {
                                bound.push(s.id);
                            }
                            let has_guard = clause.guard.is_some();
                            jobs.push(RepairStep::Push(bound));
                            jobs.push(RepairStep::Visit(clause.body));
                            if let Some(guard) = clause.guard {
                                jobs.push(RepairStep::Visit(guard));
                            }
                            jobs.push(RepairStep::Pop);
                            jobs.push(RepairStep::Post(RepairPost::Clause {
                                pattern: clause.pattern,
                                has_guard,
                                subject_name: subject_name.clone(),
                            }));
                        }
                        steps.push(RepairStep::Post(RepairPost::When {
                            subject_name,
                            clause_count,
                        }));
                        while let Some(job) = jobs.pop() {
                            steps.push(job);
                        }
                        steps.push(RepairStep::Visit(subject.into_inner()));
                    }
                    // The non-binding variants, in `map_children`'s order;
                    // leaves split into zero children and rejoin unchanged.
                    other => {
                        let (shell, kids) = split_children(other);
                        steps.push(RepairStep::Post(RepairPost::Plain {
                            shell,
                            count: kids.len(),
                        }));
                        for kid in kids.into_iter().rev() {
                            steps.push(RepairStep::Visit(kid));
                        }
                    }
                },
                RepairStep::Post(post) => match post {
                    RepairPost::Lambda { params } => {
                        let body = PBox::new(done.pop().expect("lambda body"));
                        done.push(PseudoExpr::Lambda { params, body });
                    }
                    RepairPost::RecFn { name, params } => {
                        let body = PBox::new(done.pop().expect("recfn body"));
                        done.push(PseudoExpr::RecFn { name, params, body });
                    }
                    RepairPost::Let { name, id } => {
                        let body = PBox::new(done.pop().expect("let body"));
                        let value = PBox::new(done.pop().expect("let value"));
                        done.push(PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body,
                        });
                    }
                    RepairPost::Clause {
                        pattern,
                        has_guard,
                        subject_name,
                    } => {
                        let guard = if has_guard {
                            Some(done.pop().expect("clause guard"))
                        } else {
                            None
                        };
                        let body = done.pop().expect("clause body");
                        clauses_done.push(self.repair_clause(
                            pattern,
                            guard,
                            body,
                            subject_name.as_ref(),
                        ));
                    }
                    RepairPost::When {
                        subject_name,
                        clause_count,
                    } => {
                        let at = clauses_done.len() - clause_count;
                        let clauses = clauses_done.split_off(at);
                        let subject = PBox::new(done.pop().expect("when subject"));
                        done.push(PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses,
                        });
                    }
                    RepairPost::Plain { shell, count } => {
                        let kids = take_done(&mut done, count);
                        done.push(join_children(shell, kids));
                    }
                },
            }
        }

        done.pop().expect("go leaves exactly one result")
    }

    /// The repair half of a `when` clause: its guard and body have already
    /// been walked (under the clause's scope frame, which is closed again by
    /// the time this runs).
    fn repair_clause(
        &mut self,
        pattern: WhenPattern,
        guard: Option<PseudoExpr>,
        body: PseudoExpr,
        subject_name: Option<&crate::pseudo::ast::Binder>,
    ) -> WhenClause {
        // Attempt repair.
        match pattern {
            WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            } => {
                let mut free = std::collections::HashSet::new();
                let mut frame: std::collections::HashSet<VarId> =
                    fields.iter().map(|binder| binder.id).collect();
                if let Some(s) = subject_name {
                    frame.insert(s.id);
                }
                let mut child = PayloadRepair {
                    scope: self.scope.clone(),
                    kind_annotations: self.kind_annotations,
                    use_varkind_recovery: self.use_varkind_recovery,
                    name_to_binder_id: self.name_to_binder_id,
                };
                child.scope.push(frame);
                child.collect_free_synthetic(&body, &mut free);
                if let Some(g) = &guard {
                    child.collect_free_synthetic(g, &mut free);
                }

                let synth: Vec<SyntheticPayloadRef> = free.into_iter().collect();
                if synth.len() == 1 {
                    let orphan = &synth[0];
                    let non_underscore: Vec<usize> = fields
                        .iter()
                        .enumerate()
                        .filter(|(_, b)| b.as_str() != "_")
                        .map(|(i, _)| i)
                        .collect();

                    if fields.is_empty() {
                        // Bare `Constr<N>` pattern, but the body still
                        // references the orphan. Re-introduce binders at
                        // the shape's declared arity so pretty-printing
                        // renders them: orphan in slot 0, `_` elsewhere.
                        let arity = shape.arity().max(1);
                        let mut new_fields = Vec::with_capacity(arity);
                        // Body refs get retargeted onto this id.
                        let new_binder_id = crate::pseudo::var_id::VarId::fresh_binding();
                        new_fields
                            .push(crate::pseudo::ast::Binder::new(&orphan.name, new_binder_id));
                        for _ in 1..arity {
                            new_fields.push(crate::pseudo::ast::Binder::new(
                                "_",
                                crate::pseudo::var_id::VarId::fresh_binding(),
                            ));
                        }
                        let body = rewrite_var_ref_id(body, orphan.id, &orphan.name, new_binder_id);
                        let guard = guard
                            .map(|g| rewrite_var_ref_id(g, orphan.id, &orphan.name, new_binder_id));
                        return WhenClause {
                            pattern: WhenPattern::Constructor {
                                type_hint,
                                tag,
                                fields: new_fields,
                                shape,
                            },
                            guard,
                            body,
                        };
                    }
                    if fields.len() == 1 {
                        let pattern_binder_name = fields[0].to_string();
                        if pattern_binder_name == "_" {
                            // Pattern dropped its binder — re-introduce
                            // the orphan name as the binder.
                            let new_binder_id = crate::pseudo::var_id::VarId::fresh_binding();
                            let new_binder =
                                crate::pseudo::ast::Binder::new(&orphan.name, new_binder_id);
                            let body =
                                rewrite_var_ref_id(body, orphan.id, &orphan.name, new_binder_id);
                            let guard = guard.map(|g| {
                                rewrite_var_ref_id(g, orphan.id, &orphan.name, new_binder_id)
                            });
                            return WhenClause {
                                pattern: WhenPattern::Constructor {
                                    type_hint,
                                    tag,
                                    fields: vec![new_binder],
                                    shape,
                                },
                                guard,
                                body,
                            };
                        }
                        if pattern_binder_name != orphan.name {
                            // Renamed by Cardano-naming but the body
                            // uses the old name — rewrite the orphan
                            // refs by id onto the pattern binder,
                            // leaving unrelated same-name refs alone.
                            let body = rewrite_var_ref_to_binder(body, orphan.id, &fields[0]);
                            let guard =
                                guard.map(|g| rewrite_var_ref_to_binder(g, orphan.id, &fields[0]));
                            return WhenClause {
                                pattern: WhenPattern::Constructor {
                                    type_hint,
                                    tag,
                                    fields,
                                    shape,
                                },
                                guard,
                                body,
                            };
                        }
                    } else if non_underscore.len() == 1 && fields.len() > 1 {
                        // Multi-field pattern, exactly one named binder —
                        // substitute orphan → that binder if names differ.
                        let binder_idx = non_underscore[0];
                        let pattern_binder_name = fields[binder_idx].to_string();
                        if pattern_binder_name != orphan.name {
                            let body =
                                rewrite_var_ref_to_binder(body, orphan.id, &fields[binder_idx]);
                            let guard = guard.map(|g| {
                                rewrite_var_ref_to_binder(g, orphan.id, &fields[binder_idx])
                            });
                            return WhenClause {
                                pattern: WhenPattern::Constructor {
                                    type_hint,
                                    tag,
                                    fields,
                                    shape,
                                },
                                guard,
                                body,
                            };
                        }
                    }
                }

                // Multi-orphan: each orphan `item_K` / `field_K` /
                // `fields_K` may name the K-th field of a
                // multi-binder Constr pattern. Substitute only if
                // every orphan maps to a distinct such position.
                if synth.len() > 1 {
                    let mut substitutions: Vec<(SyntheticPayloadRef, usize)> = Vec::new();
                    let mut seen_indices = HashSet::new();
                    let mut all_resolved = true;
                    for orphan in &synth {
                        if let Some(idx) = orphan
                            .name
                            .strip_prefix("item_")
                            .or_else(|| orphan.name.strip_prefix("field_"))
                            .or_else(|| orphan.name.strip_prefix("fields_"))
                            .and_then(|rest| rest.parse::<usize>().ok())
                        {
                            if !seen_indices.insert(idx) {
                                all_resolved = false;
                                break;
                            }
                            if let Some(binder) = fields.get(idx)
                                && binder.as_str() != "_"
                                && binder.as_str() != orphan.name
                            {
                                substitutions.push((orphan.clone(), idx));
                                continue;
                            }
                        }
                        all_resolved = false;
                        break;
                    }
                    if all_resolved && !substitutions.is_empty() {
                        let mut new_body = body;
                        let mut new_guard = guard;
                        for (orphan, binder_idx) in &substitutions {
                            new_body = rewrite_var_ref_to_binder(
                                new_body,
                                orphan.id,
                                &fields[*binder_idx],
                            );
                            new_guard = new_guard.map(|g| {
                                rewrite_var_ref_to_binder(g, orphan.id, &fields[*binder_idx])
                            });
                        }
                        return WhenClause {
                            pattern: WhenPattern::Constructor {
                                type_hint,
                                tag,
                                fields,
                                shape,
                            },
                            guard: new_guard,
                            body: new_body,
                        };
                    }
                }

                WhenClause {
                    pattern: WhenPattern::Constructor {
                        type_hint,
                        tag,
                        fields,
                        shape,
                    },
                    guard,
                    body,
                }
            }
            WhenPattern::List { elements, tail } => {
                // List pattern `[head, ..tail]`: a single free
                // synthetic ref in the body is substituted with the
                // first non-`_` element binder, falling back to the
                // tail binder.
                let mut frame: std::collections::HashSet<VarId> =
                    elements.iter().map(|binder| binder.id).collect();
                if let Some(t) = &tail {
                    frame.insert(t.id);
                }
                if let Some(s) = subject_name {
                    frame.insert(s.id);
                }
                let mut child = PayloadRepair {
                    scope: self.scope.clone(),
                    kind_annotations: self.kind_annotations,
                    use_varkind_recovery: self.use_varkind_recovery,
                    name_to_binder_id: self.name_to_binder_id,
                };
                child.scope.push(frame);
                let mut free = std::collections::HashSet::new();
                child.collect_free_synthetic(&body, &mut free);
                if let Some(g) = &guard {
                    child.collect_free_synthetic(g, &mut free);
                }
                if free.len() == 1 {
                    let orphan = free.into_iter().next().unwrap();
                    let target_binder = elements
                        .iter()
                        .find(|b| b.as_str() != "_")
                        .or_else(|| tail.as_ref().filter(|t| t.as_str() != "_"));
                    if let Some(target_binder) = target_binder
                        && target_binder.as_str() != orphan.name
                    {
                        let body = rewrite_var_ref_to_binder(body, orphan.id, target_binder);
                        let guard =
                            guard.map(|g| rewrite_var_ref_to_binder(g, orphan.id, target_binder));
                        return WhenClause {
                            pattern: WhenPattern::List { elements, tail },
                            guard,
                            body,
                        };
                    }
                }
                WhenClause {
                    pattern: WhenPattern::List { elements, tail },
                    guard,
                    body,
                }
            }
            other => WhenClause {
                pattern: other,
                guard,
                body,
            },
        }
    }
}

/// One pending step of [`rewrite_var_ref`].
enum RewriteStep {
    /// Rewrite this subtree.
    Enter(PseudoExpr),
    /// Its children are on `done`: rebuild the node around them.
    Post(RewritePost),
}

enum RewritePost {
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    /// `body` is `Some` when the `let` shadows `capture_name`, so its body was
    /// kept verbatim and no `Enter` step was queued for it.
    Let {
        name: String,
        id: Option<VarId>,
        body: Option<PBox>,
    },
    If,
    Apply {
        argc: usize,
    },
    BuiltinCall {
        name: BuiltinId,
        argc: usize,
    },
    BinOp {
        op: BinaryOp,
    },
    UnOp {
        op: UnaryOp,
    },
    FieldAccess {
        selector: FieldSelector,
    },
    IndexAccess {
        index: usize,
    },
    Constr {
        type_hint: Option<TypeHintId>,
        tag: usize,
        count: usize,
        shape: ConstructorShape,
    },
    List {
        count: usize,
        has_tail: bool,
    },
    Tuple {
        count: usize,
    },
    Pair,
    Delay,
    Force,
    Trace,
    When {
        subject_name: Option<Binder>,
        clauses: Vec<ClauseFrame>,
    },
}

/// A `when` clause mid-rewrite: the pattern, plus each of guard/body either
/// queued for rewriting or kept verbatim because the clause shadowed
/// `capture_name`.
struct ClauseFrame {
    pattern: WhenPattern,
    /// `None` = the clause has no guard.
    guard: Option<Slot>,
    body: Slot,
}

/// A clause's guard/body position.
enum Slot {
    /// An `Enter` step was queued; the rewritten result is on `done`.
    Queued,
    /// The clause shadowed `capture_name` — left untouched.
    Kept(PseudoExpr),
}

/// Retarget every `Var` whose id is `target_id` onto `replacement_id` (and
/// `replacement_name`, when given), stopping at any binder that re-binds
/// `capture_name`.
fn rewrite_var_ref(
    expr: PseudoExpr,
    target_id: VarId,
    replacement_name: Option<&str>,
    capture_name: Option<&str>,
    replacement_id: VarId,
) -> PseudoExpr {
    /// Take the last `n` rewritten children off `done`, in source order.
    fn take(done: &mut Vec<PseudoExpr>, n: usize) -> Vec<PseudoExpr> {
        let at = done.len() - n;
        done.split_off(at)
    }

    let mut steps: Vec<RewriteStep> = vec![RewriteStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RewriteStep::Enter(expr) => match expr {
                PseudoExpr::Var { name, id } if id == Some(target_id) => {
                    done.push(PseudoExpr::Var {
                        name: replacement_name
                            .map(std::string::ToString::to_string)
                            .unwrap_or(name),
                        id: Some(replacement_id),
                    });
                }
                PseudoExpr::Lambda { params, body } => {
                    if capture_name
                        .is_some_and(|target| params.iter().any(|param| param.as_str() == target))
                    {
                        done.push(PseudoExpr::Lambda { params, body });
                    } else {
                        steps.push(RewriteStep::Post(RewritePost::Lambda { params }));
                        steps.push(RewriteStep::Enter(body.into_inner()));
                    }
                }
                PseudoExpr::RecFn { name, params, body } => {
                    if capture_name.is_some_and(|target| {
                        name.as_str() == target
                            || params.iter().any(|param| param.as_str() == target)
                    }) {
                        done.push(PseudoExpr::RecFn { name, params, body });
                    } else {
                        steps.push(RewriteStep::Post(RewritePost::RecFn { name, params }));
                        steps.push(RewriteStep::Enter(body.into_inner()));
                    }
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    if capture_name.is_some_and(|target| name == target) {
                        steps.push(RewriteStep::Post(RewritePost::Let {
                            name,
                            id,
                            body: Some(body),
                        }));
                        steps.push(RewriteStep::Enter(value.into_inner()));
                    } else {
                        steps.push(RewriteStep::Post(RewritePost::Let {
                            name,
                            id,
                            body: None,
                        }));
                        steps.push(RewriteStep::Enter(value.into_inner()));
                        steps.push(RewriteStep::Enter(body.into_inner()));
                    }
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(RewriteStep::Post(RewritePost::If));
                    steps.push(RewriteStep::Enter(else_branch.into_inner()));
                    steps.push(RewriteStep::Enter(then_branch.into_inner()));
                    steps.push(RewriteStep::Enter(condition.into_inner()));
                }
                PseudoExpr::Apply { function, args } => {
                    steps.push(RewriteStep::Post(RewritePost::Apply { argc: args.len() }));
                    for arg in args.into_iter().rev() {
                        steps.push(RewriteStep::Enter(arg));
                    }
                    steps.push(RewriteStep::Enter(function.into_inner()));
                }
                PseudoExpr::BuiltinCall { name, args } => {
                    steps.push(RewriteStep::Post(RewritePost::BuiltinCall {
                        name,
                        argc: args.len(),
                    }));
                    for arg in args.into_iter().rev() {
                        steps.push(RewriteStep::Enter(arg));
                    }
                }
                PseudoExpr::BinOp { op, left, right } => {
                    steps.push(RewriteStep::Post(RewritePost::BinOp { op }));
                    steps.push(RewriteStep::Enter(right.into_inner()));
                    steps.push(RewriteStep::Enter(left.into_inner()));
                }
                PseudoExpr::UnOp { op, operand } => {
                    steps.push(RewriteStep::Post(RewritePost::UnOp { op }));
                    steps.push(RewriteStep::Enter(operand.into_inner()));
                }
                PseudoExpr::FieldAccess { record, selector } => {
                    steps.push(RewriteStep::Post(RewritePost::FieldAccess { selector }));
                    steps.push(RewriteStep::Enter(record.into_inner()));
                }
                PseudoExpr::IndexAccess { collection, index } => {
                    steps.push(RewriteStep::Post(RewritePost::IndexAccess { index }));
                    steps.push(RewriteStep::Enter(collection.into_inner()));
                }
                PseudoExpr::Constr {
                    type_hint,
                    tag,
                    fields,
                    shape,
                } => {
                    steps.push(RewriteStep::Post(RewritePost::Constr {
                        type_hint,
                        tag,
                        count: fields.len(),
                        shape,
                    }));
                    for field in fields.into_iter().rev() {
                        steps.push(RewriteStep::Enter(field));
                    }
                }
                PseudoExpr::List { elements, tail } => {
                    steps.push(RewriteStep::Post(RewritePost::List {
                        count: elements.len(),
                        has_tail: tail.is_some(),
                    }));
                    if let Some(tail) = tail {
                        steps.push(RewriteStep::Enter(tail.into_inner()));
                    }
                    for element in elements.into_iter().rev() {
                        steps.push(RewriteStep::Enter(element));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    steps.push(RewriteStep::Post(RewritePost::Tuple { count: items.len() }));
                    for item in items.into_iter().rev() {
                        steps.push(RewriteStep::Enter(item));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    steps.push(RewriteStep::Post(RewritePost::Pair));
                    steps.push(RewriteStep::Enter(b.into_inner()));
                    steps.push(RewriteStep::Enter(a.into_inner()));
                }
                PseudoExpr::Delay(inner) => {
                    steps.push(RewriteStep::Post(RewritePost::Delay));
                    steps.push(RewriteStep::Enter(inner.into_inner()));
                }
                PseudoExpr::Force(inner) => {
                    steps.push(RewriteStep::Post(RewritePost::Force));
                    steps.push(RewriteStep::Enter(inner.into_inner()));
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(RewriteStep::Post(RewritePost::Trace));
                    steps.push(RewriteStep::Enter(value.into_inner()));
                    steps.push(RewriteStep::Enter(message.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let subject_name_blocks = capture_name.is_some_and(|target| {
                        subject_name
                            .as_ref()
                            .is_some_and(|name| name.as_str() == target)
                    });
                    let mut frames: Vec<ClauseFrame> = Vec::with_capacity(clauses.len());
                    let mut queued: Vec<PseudoExpr> = Vec::new();
                    for clause in clauses {
                        let clause_blocks = subject_name_blocks
                            || capture_name
                                .is_some_and(|target| pattern_binds_name(&clause.pattern, target));
                        let guard = match clause.guard {
                            None => None,
                            Some(guard) if clause_blocks => Some(Slot::Kept(guard)),
                            Some(guard) => {
                                queued.push(guard);
                                Some(Slot::Queued)
                            }
                        };
                        let body = if clause_blocks {
                            Slot::Kept(clause.body)
                        } else {
                            queued.push(clause.body);
                            Slot::Queued
                        };
                        frames.push(ClauseFrame {
                            pattern: clause.pattern,
                            guard,
                            body,
                        });
                    }
                    steps.push(RewriteStep::Post(RewritePost::When {
                        subject_name,
                        clauses: frames,
                    }));
                    for child in queued.into_iter().rev() {
                        steps.push(RewriteStep::Enter(child));
                    }
                    steps.push(RewriteStep::Enter(subject.into_inner()));
                }
                other => done.push(other),
            },
            RewriteStep::Post(post) => match post {
                RewritePost::Lambda { params } => {
                    let body = done.pop().expect("lambda body");
                    done.push(PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    });
                }
                RewritePost::RecFn { name, params } => {
                    let body = done.pop().expect("recfn body");
                    done.push(PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(body),
                    });
                }
                RewritePost::Let { name, id, body } => {
                    let value = done.pop().expect("let value");
                    let body = match body {
                        Some(kept) => kept,
                        None => PBox::new(done.pop().expect("let body")),
                    };
                    done.push(PseudoExpr::Let {
                        name,
                        id,
                        value: PBox::new(value),
                        body,
                    });
                }
                RewritePost::If => {
                    let else_branch = done.pop().expect("if else");
                    let then_branch = done.pop().expect("if then");
                    let condition = done.pop().expect("if condition");
                    done.push(PseudoExpr::If {
                        condition: PBox::new(condition),
                        then_branch: PBox::new(then_branch),
                        else_branch: PBox::new(else_branch),
                    });
                }
                RewritePost::Apply { argc } => {
                    let args = take(&mut done, argc);
                    let function = done.pop().expect("apply function");
                    done.push(PseudoExpr::Apply {
                        function: PBox::new(function),
                        args: args.into(),
                    });
                }
                RewritePost::BuiltinCall { name, argc } => {
                    let args = take(&mut done, argc);
                    done.push(PseudoExpr::BuiltinCall {
                        name,
                        args: args.into(),
                    });
                }
                RewritePost::BinOp { op } => {
                    let right = done.pop().expect("binop right");
                    let left = done.pop().expect("binop left");
                    done.push(PseudoExpr::BinOp {
                        op,
                        left: PBox::new(left),
                        right: PBox::new(right),
                    });
                }
                RewritePost::UnOp { op } => {
                    let operand = done.pop().expect("unop operand");
                    done.push(PseudoExpr::UnOp {
                        op,
                        operand: PBox::new(operand),
                    });
                }
                RewritePost::FieldAccess { selector } => {
                    let record = done.pop().expect("field access record");
                    done.push(PseudoExpr::FieldAccess {
                        record: PBox::new(record),
                        selector,
                    });
                }
                RewritePost::IndexAccess { index } => {
                    let collection = done.pop().expect("index access collection");
                    done.push(PseudoExpr::IndexAccess {
                        collection: PBox::new(collection),
                        index,
                    });
                }
                RewritePost::Constr {
                    type_hint,
                    tag,
                    count,
                    shape,
                } => {
                    let fields = take(&mut done, count);
                    done.push(PseudoExpr::Constr {
                        type_hint,
                        tag,
                        fields: fields.into(),
                        shape,
                    });
                }
                RewritePost::List { count, has_tail } => {
                    let tail = if has_tail {
                        Some(PBox::new(done.pop().expect("list tail")))
                    } else {
                        None
                    };
                    let elements = take(&mut done, count);
                    done.push(PseudoExpr::List {
                        elements: elements.into(),
                        tail,
                    });
                }
                RewritePost::Tuple { count } => {
                    let items = take(&mut done, count);
                    done.push(PseudoExpr::Tuple(items.into()));
                }
                RewritePost::Pair => {
                    let b = done.pop().expect("pair second");
                    let a = done.pop().expect("pair first");
                    done.push(PseudoExpr::Pair(PBox::new(a), PBox::new(b)));
                }
                RewritePost::Delay => {
                    let inner = done.pop().expect("delay inner");
                    done.push(PseudoExpr::Delay(PBox::new(inner)));
                }
                RewritePost::Force => {
                    let inner = done.pop().expect("force inner");
                    done.push(PseudoExpr::Force(PBox::new(inner)));
                }
                RewritePost::Trace => {
                    let value = done.pop().expect("trace value");
                    let message = done.pop().expect("trace message");
                    done.push(PseudoExpr::Trace {
                        message: PBox::new(message),
                        value: PBox::new(value),
                    });
                }
                RewritePost::When {
                    subject_name,
                    clauses,
                } => {
                    // `done` holds the subject, then each queued guard/body in
                    // clause order — so unwind clauses back to front, body
                    // before guard.
                    let mut rebuilt: Vec<WhenClause> = Vec::with_capacity(clauses.len());
                    for frame in clauses.into_iter().rev() {
                        let body = match frame.body {
                            Slot::Kept(body) => body,
                            Slot::Queued => done.pop().expect("when clause body"),
                        };
                        let guard = match frame.guard {
                            None => None,
                            Some(Slot::Kept(guard)) => Some(guard),
                            Some(Slot::Queued) => Some(done.pop().expect("when clause guard")),
                        };
                        rebuilt.push(WhenClause {
                            pattern: frame.pattern,
                            guard,
                            body,
                        });
                    }
                    rebuilt.reverse();
                    let subject = done.pop().expect("when subject");
                    done.push(PseudoExpr::When {
                        subject: PBox::new(subject),
                        subject_name,
                        clauses: rebuilt,
                    });
                }
            },
        }
    }

    debug_assert_eq!(done.len(), 1, "the rewrite machine must leave one result");
    done.pop().expect("rewrite result")
}

fn rewrite_var_ref_id(
    expr: PseudoExpr,
    target_id: VarId,
    capture_name: &str,
    new_id: VarId,
) -> PseudoExpr {
    rewrite_var_ref(expr, target_id, None, Some(capture_name), new_id)
}

fn rewrite_var_ref_to_binder(
    expr: PseudoExpr,
    target_id: VarId,
    binder: &crate::pseudo::ast::Binder,
) -> PseudoExpr {
    rewrite_var_ref(
        expr,
        target_id,
        Some(binder.as_str()),
        Some(binder.as_str()),
        binder.var_id(),
    )
}

fn pattern_binds_name(pattern: &WhenPattern, target: &str) -> bool {
    match pattern {
        WhenPattern::Constructor { fields, .. } => {
            fields.iter().any(|binder| binder.as_str() == target)
        }
        WhenPattern::Pair(left, right) => left.as_str() == target || right.as_str() == target,
        WhenPattern::Tuple(fields) => fields.iter().any(|binder| binder.as_str() == target),
        WhenPattern::List { elements, tail } => {
            elements.iter().any(|binder| binder.as_str() == target)
                || tail
                    .as_ref()
                    .is_some_and(|binder| binder.as_str() == target)
        }
        WhenPattern::Var(binder) => binder.as_str() == target,
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}
