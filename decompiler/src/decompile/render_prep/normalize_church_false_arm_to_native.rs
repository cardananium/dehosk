//! Rewrite a hoisted `church_false` Var used as a `when`-arm result to
//! native `False`, only when a sibling arm of that `when` is already
//! native-Bool (fail-closed).
//!
//! Inverse-CIP Bool-collapse commits `church_false = Constr<1> = False`
//! for inline sites, but the same term also survives as a hoisted Scott
//! FALSE selector `fn(_, f) { f }`. Next to a sibling `False`/`&&` that
//! is a render inconsistency, not a polarity choice — the sibling already
//! fixed polarity, so the rewrite cannot invert it.
//!
//! 1. Selector: `Lambda { params: [a, b], body: Var(b) }`. Church-TRUE
//!    (`fn(t, _) { t }`) is not a match. Collided VarIds are dropped.
//! 2. The `when` has no concrete non-Bool leaf and at least one definite
//!    Bool leaf (`Bool`, comparison/logical `BinOp`, `!`). `fail` and the
//!    candidate itself are neutral. An opaque arm vetoes unless it also
//!    has a definite Bool leaf. A mixed `when` with `Some(x)` / a list
//!    cell is rejected. The candidate never grounds the witness.
//! 3. Only arm-result tails are rewritten (`let`/`if`/`when`/`trace`
//!    tails). `church_false(x, y)` is an `Apply` and is never touched.
//!
//! After the last ref is gone this pass drops the selector def itself.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn normalize_church_false_arm_to_native(expr: PseudoExpr) -> PseudoExpr {
    let selector_ids = collect_church_false_selector_ids(&expr);
    if selector_ids.is_empty() {
        return expr;
    }
    let rewritten = rewrite(expr, &selector_ids);
    // A selector def whose references were all normalized away is provably
    // dead. Remove it here rather than leaning on the marker-gated
    // `drop_dead_pure_lets`, which does NOT run on non-wrapped v1/v2 plain-fn
    // modules and would leave them an orphan `fn church_false(_, f) { f }`. A
    // selector still used as a genuine `church_false(x, y)` CALL keeps a live
    // ref and is retained.
    let referenced = collect_referenced_var_ids(&rewritten);
    let dead: HashSet<VarId> = selector_ids
        .iter()
        .copied()
        .filter(|id| !referenced.contains(id))
        .collect();
    if dead.is_empty() {
        return rewritten;
    }
    remove_dead_selector_lets(rewritten, &dead)
}

/// Every `VarId` in a `Var` REFERENCE position anywhere in `expr`. Uses the
/// `ExprVisitor::visit_var` hook rather than `scope_recurse::children`,
/// which omits some positions. A `Let`/`Lambda` BINDING site is not a `Var`
/// reference, so an unused def scans as 0 refs.
fn collect_referenced_var_ids(expr: &PseudoExpr) -> HashSet<VarId> {
    use crate::pseudo::fold::ExprVisitor;
    struct Refs {
        ids: HashSet<VarId>,
    }
    impl ExprVisitor for Refs {
        fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
            if let Some(vid) = id {
                self.ids.insert(*vid);
            }
        }
    }
    let mut refs = Refs {
        ids: HashSet::new(),
    };
    refs.walk(expr);
    refs.ids
}

/// One pending job of this module's two whole-tree owned walks
/// (`remove_dead_selector_lets`, `rewrite`). Neither carries a scope — both
/// were `map_children` recursions applying the same rule to every child — so
/// a job is just the node, or the reassembly tag for a node whose children
/// are already folded onto `done`.
enum Step {
    Visit(PseudoExpr),
    Post(Post),
}

enum Post {
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
    Plain(PlainPost),
}

/// Push `expr`'s children in REVERSE (so they pop, and so land on `done`, in
/// source order) plus the step that reassembles it — reproducing
/// `map_children`'s child order and reconstruction exactly. A leaf has no
/// children and goes straight onto `done`, matching `map_children`'s
/// `other => other`.
fn push_children(expr: PseudoExpr, steps: &mut Vec<Step>, done: &mut Vec<PseudoExpr>) {
    match expr {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            steps.push(Step::Post(Post::Let { name, id }));
            steps.push(Step::Visit(body.into_inner()));
            steps.push(Step::Visit(value.into_inner()));
        }
        PseudoExpr::Lambda { params, body } => {
            steps.push(Step::Post(Post::Lambda { params }));
            steps.push(Step::Visit(body.into_inner()));
        }
        PseudoExpr::RecFn { name, params, body } => {
            steps.push(Step::Post(Post::RecFn { name, params }));
            steps.push(Step::Visit(body.into_inner()));
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
            steps.push(Step::Post(Post::When {
                subject_name,
                clause_meta,
            }));
            for c in clause_children.into_iter().rev() {
                steps.push(Step::Visit(c));
            }
            steps.push(Step::Visit(subject.into_inner()));
        }
        other => match plain_children(other) {
            Ok((kind, children)) => {
                steps.push(Step::Post(Post::Plain(kind)));
                for c in children.into_iter().rev() {
                    steps.push(Step::Visit(c));
                }
            }
            Err(leaf) => done.push(leaf),
        },
    }
}

/// Rebuild one node from its already-folded children on `done`.
fn rebuild(post: Post, done: &mut Vec<PseudoExpr>) -> PseudoExpr {
    match post {
        Post::Let { name, id } => {
            let body = done.pop().expect("let body");
            let value = done.pop().expect("let value");
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
        Post::Lambda { params } => PseudoExpr::Lambda {
            params,
            body: PBox::new(done.pop().expect("lambda body")),
        },
        Post::RecFn { name, params } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(done.pop().expect("recfn body")),
        },
        Post::When {
            subject_name,
            clause_meta,
        } => {
            let total = 1 + clause_meta
                .iter()
                .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                .sum::<usize>();
            let mut parts = take(done, total).into_iter();
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
        Post::Plain(kind) => rebuild_plain(kind, done),
    }
}

/// Splice out `Let` bindings whose bound id is in `dead`. Removing an
/// unreferenced binding is sound, and the selector value `fn(_, f) { f }`
/// references nothing, so no cascade is possible.
fn remove_dead_selector_lets(expr: PseudoExpr, dead: &HashSet<VarId>) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(mut expr) => {
                // A dead `let` is spliced out and its BODY takes its place — and that
                // body may itself be a dead `let`, so peel the whole chain right here,
                // where tail-called.
                while matches!(&expr, PseudoExpr::Let { id: Some(vid), .. } if dead.contains(vid)) {
                    let PseudoExpr::Let { body, .. } = expr else {
                        unreachable!("guarded by the `matches!` above")
                    };
                    expr = body.into_inner();
                }
                push_children(expr, &mut steps, &mut done);
            }
            Step::Post(post) => {
                let rebuilt = rebuild(post, &mut done);
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(
        done.len(),
        1,
        "remove_dead_selector_lets must leave one result"
    );
    done.pop().expect("remove_dead_selector_lets result")
}

/// Is `expr` the Scott/church FALSE selector `Lambda { [a, b], Var(b) }`?
/// Rejects the church-TRUE selector `fn(t, _) { t }` (body = FIRST param).
fn is_church_false_selector(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    if params.len() != 2 {
        return false;
    }
    let PseudoExpr::Var {
        id: Some(body_id), ..
    } = body.as_ref()
    else {
        return false;
    };
    // Body must be the SECOND param and NOT the first — a degenerate
    // `fn(x, x) { x }` is genuinely ambiguous.
    *body_id == params[1].var_id() && *body_id != params[0].var_id()
}

/// Collect the `VarId` of every `let`-bound def whose value is a
/// church-FALSE selector.  A `VarId` bound at more than one site is
/// dropped: a rewrite keyed on it could otherwise hit the wrong binding.
fn collect_church_false_selector_ids(expr: &PseudoExpr) -> HashSet<VarId> {
    let mut hits: HashMap<VarId, usize> = HashMap::new();
    walk(expr, &mut hits);
    hits.into_iter()
        .filter(|&(_, count)| count == 1)
        .map(|(id, _)| id)
        .collect()
}

/// A pure pre-order visitor with nothing to do after a child, so it needs no
/// `Post` step: children go on in REVERSE, popping in source order.
fn walk(expr: &PseudoExpr, hits: &mut HashMap<VarId, usize>) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            ..
        } = expr
            && is_church_false_selector(value)
        {
            *hits.entry(*vid).or_insert(0) += 1;
        }
        for child in super::scope_recurse::children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// A per-tail-leaf classification for the Bool-typing witness.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Leaf {
    /// A definite native-Bool leaf (comparison / logical `BinOp`, `!`, or a
    /// `Bool` literal). GROUNDS the witness.
    DefBool,
    /// Non-committal AND non-value: a divergent `fail`/`Error`, the
    /// `church_false` selector candidate itself, or an opaque marker
    /// (`Raw`/`HelperSymbol`). Yields no surface value to type, so it
    /// neither grounds nor vetoes.
    Neutral,
    /// A value whose Bool-ness is not readable off the surface: a bare `Var`,
    /// a call `Apply`/`BuiltinCall`, a projection `FieldAccess`/`IndexAccess`,
    /// a `Force`/`Delay`, a `Lambda`/`RecFn`. UNLIKE `Neutral` this IS a value
    /// and could be non-Bool, so it never grounds; and (per `classify_arm`) an
    /// arm whose only value leaves are `Opaque` VETOES the `when`, nothing
    /// having proved that arm — hence the `when` — Bool-typed.
    Opaque,
    /// A definite NON-Bool VALUE leaf — a `Constr` (`Some`/`None`/list-nil/any
    /// tagged data), a `List`/`Pair`/`Tuple` cell, or an `Int`/`ByteArray`/
    /// `String`/`Unit` literal. VETOES the whole `when` (it cannot be Bool).
    NonBool,
}

/// Classify one arm's tail/result leaves and fold the verdict for the arm:
/// `None` = veto the `when` (the arm carries a definite NON-Bool leaf, OR
/// its only value leaves are OPAQUE with no definite-Bool leaf — either way
/// it is not provably Bool); `Some(grounded)` = provably Bool-or-empty,
/// `grounded` iff ≥ 1 definite Bool leaf.
///
/// Recurses only TAIL positions (`if` branches, `when` clause bodies, `let`
/// bodies, `trace` values) — the same surface the normalizer rewrites. A
/// tail that is the `church_false` candidate (or a `fail`) is `Neutral`: it
/// yields no value to type, so it must neither veto nor self-ground. An
/// OPAQUE value tail DOES veto UNLESS the arm also carries a definite Bool
/// leaf, as in `if … { call } else { … && call }`.
///
/// The inner `leaf` short-circuits through `&&` / `.all()`; `break`ing out
/// of the worklist on the first `NonBool` stops at that same leaf, having
/// mutated `grounded`/`saw_opaque` from the same prefix of leaves.
fn classify_arm(expr: &PseudoExpr, selector_ids: &HashSet<VarId>) -> Option<bool> {
    let mut grounded = false;
    let mut saw_opaque = false;
    let mut vetoed = false;
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr {
            // Tail-structural forms: push in REVERSE so they pop in source order.
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                stack.push(else_branch);
                stack.push(then_branch);
            }
            PseudoExpr::When { clauses, .. } => {
                for c in clauses.iter().rev() {
                    stack.push(&c.body);
                }
            }
            PseudoExpr::Let { body, .. } => stack.push(body),
            PseudoExpr::Trace { value, .. } => stack.push(value),
            other => match classify_leaf(other, selector_ids) {
                Leaf::DefBool => grounded = true,
                Leaf::Neutral => {}
                Leaf::Opaque => saw_opaque = true,
                // A concrete non-Bool VALUE leaf — immediate veto.
                Leaf::NonBool => {
                    vetoed = true;
                    break;
                }
            },
        }
    }
    if vetoed {
        return None; // a concrete non-Bool value leaf.
    }
    // Opaque value leaves with no native-Bool leaf anywhere in the arm do not
    // prove the arm Bool — veto rather than assume a sibling `church_false` is
    // `False`. Opaque tails alongside a `&&`/`==`/`False` leaf still qualify.
    if saw_opaque && !grounded {
        return None;
    }
    Some(grounded)
}

/// Classify a NON-tail-structural leaf expression.
fn classify_leaf(expr: &PseudoExpr, selector_ids: &HashSet<VarId>) -> Leaf {
    match expr {
        PseudoExpr::Bool(_) => Leaf::DefBool,
        PseudoExpr::BinOp { op, .. } if is_bool_binop(op) => Leaf::DefBool,
        PseudoExpr::UnOp {
            op: UnaryOp::Not, ..
        } => Leaf::DefBool,
        // Divergent tail — neutral (bottom, yields no non-Bool value).
        PseudoExpr::Error { .. } => Leaf::Neutral,
        PseudoExpr::BuiltinCall {
            name: crate::BuiltinId::Error,
            ..
        } => Leaf::Neutral,
        // The church_false selector candidate itself — neutral, so
        // it never self-grounds the witness that proves it False.
        PseudoExpr::Var { id: Some(vid), .. } if selector_ids.contains(vid) => Leaf::Neutral,
        // Opaque VALUES whose Bool-ness is not readable off the surface but
        // which are NOT concrete non-Bool literals: a bare Var, a call, a
        // data projection, a function abstraction. Unlike a `Neutral` these
        // veto an arm with no definite Bool leaf (see `Leaf::Opaque`).
        PseudoExpr::Var { .. }
        | PseudoExpr::Apply { .. }
        | PseudoExpr::BuiltinCall { .. }
        | PseudoExpr::FieldAccess { .. }
        | PseudoExpr::IndexAccess { .. }
        | PseudoExpr::Force(_)
        | PseudoExpr::Delay(_)
        | PseudoExpr::Lambda { .. }
        | PseudoExpr::RecFn { .. } => Leaf::Opaque,
        // A non-Bool arithmetic/other BinOp (e.g. `+`, `%`) is a concrete
        // non-Bool value.
        PseudoExpr::BinOp { .. } | PseudoExpr::UnOp { .. } => Leaf::NonBool,
        // Concrete NON-Bool VALUES: a tagged constructor, a list/pair/tuple
        // cell, or a non-Bool literal. These VETO the `when`.
        PseudoExpr::Constr { .. }
        | PseudoExpr::List { .. }
        | PseudoExpr::Pair(_, _)
        | PseudoExpr::Tuple(_)
        | PseudoExpr::Int(_)
        | PseudoExpr::ByteArray(_)
        | PseudoExpr::String(_)
        | PseudoExpr::Data(_)
        | PseudoExpr::Unit => Leaf::NonBool,
        // Opaque markers whose type the surface does not show — neutral.
        PseudoExpr::Raw { .. } | PseudoExpr::HelperSymbol(_) => Leaf::Neutral,
        // Tail-structural forms are consumed by `classify_arm`'s recursion and
        // never reach here; treat defensively as Neutral (never veto on a
        // control-flow node — only on a concrete non-Bool VALUE).
        PseudoExpr::Let { .. }
        | PseudoExpr::If { .. }
        | PseudoExpr::When { .. }
        | PseudoExpr::Trace { .. } => Leaf::Neutral,
    }
}

fn is_bool_binop(op: &BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::Eq
            | BinaryOp::Neq
            | BinaryOp::Lt
            | BinaryOp::Lte
            | BinaryOp::Gt
            | BinaryOp::Gte
            | BinaryOp::And
            | BinaryOp::Or
    )
}

/// A `when` is provably Bool-typed (so its `church_false` arm is a native
/// `False`) iff EVERY arm is Bool-or-neutral (no arm carries a concrete
/// NON-Bool value leaf) AND at least one arm carries a definite Bool leaf.
///
/// A UNIVERSAL witness with a NON-Bool VETO, strictly stronger than a bare
/// existence check: `{ A -> a == b; B -> Some(x); C -> church_false }` is
/// REJECTED because arm B is a concrete `Some`, so its `church_false` is
/// never wrongly rewritten. An opaque helper CALL returning Bool is
/// neutral and does not veto, which is why a genuinely Bool-typed `when`
/// whose cons arms end in `if … { call } else { … && call }` still
/// qualifies via its definite `False` / `&&` sibling leaf.
fn when_is_bool_typed(
    clauses: &[crate::pseudo::ast::WhenClause],
    selector_ids: &HashSet<VarId>,
) -> bool {
    let mut grounded = false;
    for c in clauses {
        match classify_arm(&c.body, selector_ids) {
            Some(g) => grounded |= g,
            None => return false, // a concrete non-Bool arm vetoes.
        }
    }
    grounded
}

/// The `When` arm's work sits AFTER its children, so it lives in the
/// `Post` step — the only place a `When` is ever reassembled here — leaving
/// the bottom-up order (nested whens first) untouched.
fn rewrite(expr: PseudoExpr, selector_ids: &HashSet<VarId>) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(expr) => push_children(expr, &mut steps, &mut done),
            Step::Post(post) => {
                let rebuilt = match rebuild(post, &mut done) {
                    // The subject and all clause bodies have been rewritten by
                    // now (nested whens are handled bottom-up); apply the
                    // arm-result normalization if THIS when carries the
                    // sibling witness.
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let witnessed = when_is_bool_typed(&clauses, selector_ids);
                        let clauses = if witnessed {
                            clauses
                                .into_iter()
                                .map(|mut c| {
                                    c.body = normalize_tail_church_false(c.body, selector_ids);
                                    c
                                })
                                .collect()
                        } else {
                            clauses
                        };
                        PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses,
                        }
                    }
                    other => other,
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

/// Replace a bare `Var(church_false_selector)` in TAIL/result positions of
/// an arm body with `Bool(false)`, following the tail chain
/// (`let … ; result`, `if`/`when`/`trace` tails) but never descending into
/// arguments, subjects, operands, conditions, or call heads — a genuine
/// `church_false(x, y)` is an `Apply`, not a bare `Var`, and is untouched.
fn normalize_tail_church_false(expr: PseudoExpr, selector_ids: &HashSet<VarId>) -> PseudoExpr {
    let mut steps: Vec<TailStep> = vec![TailStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            TailStep::Visit(expr) => match expr {
                PseudoExpr::Var { id: Some(vid), .. } if selector_ids.contains(&vid) => {
                    done.push(PseudoExpr::Bool(false));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(TailStep::Post(TailPost::Let { name, id, value }));
                    steps.push(TailStep::Visit(body.into_inner()));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(TailStep::Post(TailPost::If { condition }));
                    // Reversed so they pop — and so land on `done` — in order.
                    steps.push(TailStep::Visit(else_branch.into_inner()));
                    steps.push(TailStep::Visit(then_branch.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_meta = Vec::with_capacity(clauses.len());
                    let mut bodies = Vec::with_capacity(clauses.len());
                    for c in clauses {
                        clause_meta.push((c.pattern, c.guard));
                        bodies.push(c.body);
                    }
                    steps.push(TailStep::Post(TailPost::When {
                        subject,
                        subject_name,
                        clause_meta,
                    }));
                    for b in bodies.into_iter().rev() {
                        steps.push(TailStep::Visit(b));
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(TailStep::Post(TailPost::Trace { message }));
                    steps.push(TailStep::Visit(value.into_inner()));
                }
                other => done.push(other),
            },
            TailStep::Post(post) => {
                let rebuilt = match post {
                    TailPost::Let { name, id, value } => PseudoExpr::Let {
                        name,
                        id,
                        value,
                        body: PBox::new(done.pop().expect("let body")),
                    },
                    TailPost::If { condition } => {
                        let mut parts = take(&mut done, 2).into_iter();
                        let then_branch = parts.next().expect("if then");
                        let else_branch = parts.next().expect("if else");
                        PseudoExpr::If {
                            condition,
                            then_branch: PBox::new(then_branch),
                            else_branch: PBox::new(else_branch),
                        }
                    }
                    TailPost::When {
                        subject,
                        subject_name,
                        clause_meta,
                    } => {
                        let bodies = take(&mut done, clause_meta.len());
                        PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses: clause_meta
                                .into_iter()
                                .zip(bodies)
                                .map(|((pattern, guard), body)| WhenClause {
                                    pattern,
                                    guard,
                                    body,
                                })
                                .collect(),
                        }
                    }
                    TailPost::Trace { message } => PseudoExpr::Trace {
                        message,
                        value: PBox::new(done.pop().expect("trace value")),
                    },
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(
        done.len(),
        1,
        "normalize_tail_church_false must leave one result"
    );
    done.pop().expect("normalize_tail_church_false result")
}

/// A job on [`normalize_tail_church_false`]'s stack. Each `Post` carries the
/// node's NON-tail children verbatim — left untouched.
enum TailStep {
    Visit(PseudoExpr),
    Post(TailPost),
}

enum TailPost {
    Let {
        name: String,
        id: Option<VarId>,
        value: PBox,
    },
    If {
        condition: PBox,
    },
    When {
        subject: PBox,
        subject_name: Option<Binder>,
        clause_meta: Vec<(WhenPattern, Option<PseudoExpr>)>,
    },
    Trace {
        message: PBox,
    },
}

#[cfg(test)]
mod tests;
