//! Inverse-CIP church_true that list/type recovery mislabelled `Nil` → `True`.
//!
//! In an inverse-CIP program `church_true` and the Scott list-`nil`
//! are the same term — a nullary `Constr<0>` (the K combinator
//! `λt._. t` ≡ `λn._. n`). List-recovery / type-inference therefore
//! shapes a church_true return as `KnownConstructor::Nil`, so a
//! Bool-predicate fold renders its base case as `[] -> Nil` instead
//! of `[] -> True`. The control flow is already correct; only the
//! label is wrong.
//!
//! Gated on [`ChurchPolarity::InverseCip`]. A nullary `Known(Nil)`
//! value leaf is relabelled to `Known(True)` only inside a function
//! that provably returns `Bool` — there a `Known(Nil)` leaf must be
//! church_true, never a genuine list `nil`. Only tail/return
//! positions are relabelled; arguments and non-tail sub-terms are
//! left alone.
//!
//! [`proves_bool`] vetoes (`None`) on any non-Bool value leaf — a
//! `List`/`Tuple`/`Pair` cell, a list builtin, an unknown call — so
//! a genuine list-returning fold is never classified Bool. A
//! function qualifies only when at least one leaf is a concrete
//! Bool (a `Bool` literal, `Known(True/False)`, a comparison,
//! `&&`/`||`, or `!`) — a `Known(Nil)` leaf alone does not ground
//! it, so a vacuous `{ [] -> Nil; [_, ..t] -> self(t) }` is
//! rejected. Local recursive/mutually-recursive calls are followed
//! through the in-scope fn definitions with an `in_progress` set
//! breaking the cycle (an in-progress callee is assumed Bool but
//! does not ground).

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::decompile::church_polarity::ChurchPolarity;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

use super::ctx::RenderCtx;
use super::scope_recurse::{rewrite_bottom_up, take};

pub(super) fn recover_inverse_cip_nil_as_true(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    if ctx.church_polarity() != ChurchPolarity::InverseCip {
        return expr;
    }
    let mut defs: HashMap<VarId, FnDef> = HashMap::new();
    collect_fn_defs(&expr, &mut defs);
    if defs.is_empty() {
        return expr;
    }
    // Resolve the bool-returning set once (read-only), then rewrite.
    let bool_fns: HashSet<VarId> = defs
        .keys()
        .copied()
        .filter(|id| {
            let mut in_progress = HashSet::new();
            in_progress.insert(*id);
            proves_bool(defs[id].body, &defs, &mut in_progress) == Some(true)
        })
        .collect();
    if bool_fns.is_empty() {
        return expr;
    }
    rewrite(expr, &bool_fns)
}

/// A local function definition reachable by `VarId`.
struct FnDef<'a> {
    arity: usize,
    body: &'a PseudoExpr,
}

/// Collect every `rec fn` (by its self-name id) and `let`-bound `Lambda`
/// (by its binder id) in scope.
fn collect_fn_defs<'a>(expr: &'a PseudoExpr, out: &mut HashMap<VarId, FnDef<'a>>) {
    let mut stack = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr {
            PseudoExpr::RecFn { name, params, body } => {
                out.insert(
                    name.id,
                    FnDef {
                        arity: params.len(),
                        body,
                    },
                );
            }
            PseudoExpr::Let {
                id: Some(vid),
                value,
                ..
            } => {
                // Register the let binder id against the fn body so a call by
                // the let name resolves; the RecFn arm registers the
                // self-name id separately when `children` reaches the value.
                let fn_body = match value.as_ref() {
                    PseudoExpr::Lambda { params, body } => Some((params.len(), body.as_ref())),
                    PseudoExpr::RecFn { params, body, .. } => Some((params.len(), body.as_ref())),
                    _ => None,
                };
                if let Some((arity, body)) = fn_body {
                    out.insert(*vid, FnDef { arity, body });
                }
            }
            _ => {}
        }
        for child in super::scope_recurse::children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// One pending step of [`proves_bool`]'s explicit stack.
enum BoolStep<'a> {
    /// Prove this sub-term.
    Visit(&'a PseudoExpr),
    /// Leave a callee's cycle-break set — the `in_progress.remove(&f)` that
    /// sat right after the recursive call. Pushed BELOW the callee body, so
    /// it still fires exactly when that body is finished and before any
    /// sibling tail is proved.
    Unmark(VarId),
}

/// Does `expr` provably evaluate to `Bool`? `Some(true)` = yes AND grounded
/// (≥1 concrete-Bool leaf); `Some(false)` = Bool but ungrounded (only
/// church_true `Nil` / in-progress self-calls); `None` = NOT provably Bool
/// (veto).
fn proves_bool<'a>(
    expr: &'a PseudoExpr,
    defs: &HashMap<VarId, FnDef<'a>>,
    in_progress: &mut HashSet<VarId>,
) -> Option<bool> {
    let mut grounded = false;
    let mut steps: Vec<BoolStep<'a>> = vec![BoolStep::Visit(expr)];

    while let Some(step) = steps.pop() {
        let expr = match step {
            BoolStep::Visit(expr) => expr,
            BoolStep::Unmark(f) => {
                in_progress.remove(&f);
                continue;
            }
        };
        match expr {
            PseudoExpr::Bool(_) => grounded = true,
            PseudoExpr::Constr { shape, fields, .. } if fields.is_empty() => match shape {
                ConstructorShape::Known(KnownConstructor::True | KnownConstructor::False) => {
                    grounded = true;
                }
                // church_true mislabelled Nil: Bool, but not a grounding witness.
                ConstructorShape::Known(KnownConstructor::Nil) => {}
                _ => return None,
            },
            PseudoExpr::BinOp { op, .. } => match op {
                BinaryOp::Eq
                | BinaryOp::Neq
                | BinaryOp::Lt
                | BinaryOp::Lte
                | BinaryOp::Gt
                | BinaryOp::Gte
                | BinaryOp::And
                | BinaryOp::Or => grounded = true,
                _ => return None,
            },
            PseudoExpr::UnOp {
                op: UnaryOp::Not, ..
            } => grounded = true,
            PseudoExpr::Let { body, .. } => steps.push(BoolStep::Visit(body.as_ref())),
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                let tails = join_tails(vec![then_branch.as_ref(), else_branch.as_ref()])?;
                for tail in tails.into_iter().rev() {
                    steps.push(BoolStep::Visit(tail));
                }
            }
            PseudoExpr::When { clauses, .. } => {
                let bodies: Vec<&PseudoExpr> = clauses.iter().map(|c| &c.body).collect();
                for tail in join_tails(bodies)?.into_iter().rev() {
                    steps.push(BoolStep::Visit(tail));
                }
            }
            PseudoExpr::Trace { value, .. } => steps.push(BoolStep::Visit(value.as_ref())),
            PseudoExpr::Apply { function, args } => {
                // `expect P = X` desugars to a `When` (handled above), not an
                // `Apply`, so no `expect!` special-case is needed here.
                let mut head = function.as_ref();
                while let PseudoExpr::Force(inner) = head {
                    head = inner.as_ref();
                }
                let head_id = match head {
                    PseudoExpr::Var { id: Some(f), .. } => Some(*f),
                    PseudoExpr::RecFn { name, .. } => Some(name.id),
                    _ => None,
                };
                match head_id {
                    // An in-progress callee is assumed Bool (cycle break); does
                    // not ground.
                    Some(f) if in_progress.contains(&f) => {}
                    Some(f) => match defs.get(&f) {
                        Some(def) if args.len() == def.arity => {
                            let body = def.body;
                            in_progress.insert(f);
                            steps.push(BoolStep::Unmark(f));
                            steps.push(BoolStep::Visit(body));
                        }
                        // unknown callee or arity mismatch → cannot prove Bool.
                        _ => return None,
                    },
                    None => return None,
                }
            }
            // `join_tails` skips diverging tails, so an `Error` only reaches
            // here outside a join, where it is not Bool evidence.
            PseudoExpr::Error { .. } => return None,
            _ => return None,
        }
    }

    Some(grounded)
}

/// Join over branch tails: every NON-diverging tail must prove Bool, ≥1
/// non-diverging tail must exist, and grounding is the OR over tails.
///
/// The "must prove Bool" and the OR now happen in [`proves_bool`]'s loop —
/// the surviving tails become ordinary jobs on its stack — so all that is
/// left here is the diverging filter and the ≥1 requirement.
fn join_tails<'a>(tails: Vec<&'a PseudoExpr>) -> Option<Vec<&'a PseudoExpr>> {
    let kept: Vec<&'a PseudoExpr> = tails.into_iter().filter(|t| !is_diverging(t)).collect();
    if kept.is_empty() { None } else { Some(kept) }
}

fn is_diverging(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Error { .. })
        || matches!(
            expr,
            PseudoExpr::BuiltinCall {
                name: crate::BuiltinId::Error,
                ..
            }
        )
}

/// Rewrite: inside a bool-returning fn body, relabel TAIL `Known(Nil)` value
/// leaves → `Known(True)`.
///
/// Each arm's own logic runs AFTER its children are rewritten
/// (`relabel_tail_nil(rewrite(body))`), which is the node
/// `rewrite_bottom_up` hands to `f`. The `Let`-bound-`Lambda` arm never
/// walks the `Lambda` node itself, only its body — and `f` leaves a plain
/// `Lambda` alone.
fn rewrite(expr: PseudoExpr, bool_fns: &HashSet<VarId>) -> PseudoExpr {
    rewrite_bottom_up(expr, |expr| match expr {
        PseudoExpr::RecFn { name, params, body } if bool_fns.contains(&name.id) => {
            PseudoExpr::RecFn {
                name,
                params,
                body: PBox::new(relabel_tail_nil(body.into_inner())),
            }
        }
        PseudoExpr::Let {
            name,
            id: Some(vid),
            value,
            body,
        } if bool_fns.contains(&vid) && matches!(value.as_ref(), PseudoExpr::Lambda { .. }) => {
            let PseudoExpr::Lambda {
                params,
                body: lbody,
            } = value.into_inner()
            else {
                unreachable!()
            };
            PseudoExpr::Let {
                name,
                id: Some(vid),
                value: PBox::new(PseudoExpr::Lambda {
                    params,
                    body: PBox::new(relabel_tail_nil(lbody.into_inner())),
                }),
                body,
            }
        }
        other => other,
    })
}

/// One pending step of [`relabel_tail_nil`]'s explicit stack. Only TAIL
/// positions are descended into, so a step carries the node's non-tail parts
/// (let value, if condition, when subject/patterns/guards, trace message)
/// verbatim.
enum TailStep {
    Enter(PseudoExpr),
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
        clause_rest: Vec<(WhenPattern, Option<PseudoExpr>)>,
    },
    Trace {
        message: PBox,
    },
}

/// Relabel `Known(Nil)` nullary VALUE leaves → `Known(True)` in tail
/// positions only (when-clause bodies, if branches, let bodies, trace
/// value). Does NOT descend into arguments / subjects / operator operands.
fn relabel_tail_nil(expr: PseudoExpr) -> PseudoExpr {
    let mut steps: Vec<TailStep> = vec![TailStep::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            TailStep::Enter(expr) => match expr {
                PseudoExpr::Constr {
                    shape: ConstructorShape::Known(KnownConstructor::Nil),
                    fields,
                    ..
                } if fields.is_empty() => done.push(PseudoExpr::constr(
                    ConstructorShape::Known(KnownConstructor::True),
                    vec![],
                )),
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(TailStep::Post(TailPost::Let { name, id, value }));
                    steps.push(TailStep::Enter(body.into_inner()));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    steps.push(TailStep::Post(TailPost::If { condition }));
                    steps.push(TailStep::Enter(else_branch.into_inner()));
                    steps.push(TailStep::Enter(then_branch.into_inner()));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let mut clause_rest = Vec::with_capacity(clauses.len());
                    let mut bodies = Vec::with_capacity(clauses.len());
                    for c in clauses {
                        clause_rest.push((c.pattern, c.guard));
                        bodies.push(c.body);
                    }
                    steps.push(TailStep::Post(TailPost::When {
                        subject,
                        subject_name,
                        clause_rest,
                    }));
                    for b in bodies.into_iter().rev() {
                        steps.push(TailStep::Enter(b));
                    }
                }
                PseudoExpr::Trace { message, value } => {
                    steps.push(TailStep::Post(TailPost::Trace { message }));
                    steps.push(TailStep::Enter(value.into_inner()));
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
                        let else_branch = done.pop().expect("if else");
                        let then_branch = done.pop().expect("if then");
                        PseudoExpr::If {
                            condition,
                            then_branch: PBox::new(then_branch),
                            else_branch: PBox::new(else_branch),
                        }
                    }
                    TailPost::When {
                        subject,
                        subject_name,
                        clause_rest,
                    } => {
                        let mut parts = take(&mut done, clause_rest.len()).into_iter();
                        let clauses = clause_rest
                            .into_iter()
                            .map(|(pattern, guard)| WhenClause {
                                pattern,
                                guard,
                                body: parts.next().expect("when clause body"),
                            })
                            .collect();
                        PseudoExpr::When {
                            subject,
                            subject_name,
                            clauses,
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

    debug_assert_eq!(done.len(), 1, "relabel_tail_nil must leave one result");
    done.pop().expect("relabel_tail_nil result")
}

#[cfg(test)]
mod tests;
