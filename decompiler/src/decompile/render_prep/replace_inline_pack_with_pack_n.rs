//! Replace inline `fn(x) { x(args...) }` church-pack literals with
//! calls to the `pack_N` / `pair_pack` helper of matching arity.
//!
//! `rename_church_n_pack_helpers` hoists `helper_X` → `pack_N` for
//! N ≥ 3 (`pair_pack` for N = 2), but inline sites producing the same
//! church-pack survive when `hoist_church_pair_pack` refuses them on
//! purity grounds (args with impure components like
//! `builtin.un_b_data(field_0)`).
//!
//! If the top-level chain already binds a `pack_N` (any N ≥ 2), every
//! inline `Lambda { [x], Apply { Var(x), args } }` becomes
//! `Apply { Var(pack_N), args }`. No new helper is introduced — inline
//! sites are routed through the existing one.
//!
//! The inline pack delays its args, the helper call does not. For pure
//! args the two are observationally identical; for impure args (a
//! `builtin.un_b_data` that fails on a wrong tag) the order of failure
//! could shift when several args fail. The Plutus simplifier already
//! evaluates args eagerly before invoking lambdas at this surface-AST
//! level, so the rewrite preserves observable behaviour.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn replace_inline_pack_with_pack_n(expr: PseudoExpr) -> PseudoExpr {
    let mut packs: HashMap<usize, (VarId, String)> = HashMap::new();
    collect_pack_helpers(&expr, &mut packs);
    if packs.is_empty() {
        return expr;
    }
    // Helper-binder VarIds. Rewriting inside a helper's own value
    // would turn its body into an unbounded self-call
    // (`fn pack_3(a,b,c) { pack_3(a,b,c) }`).
    let helper_ids: std::collections::HashSet<VarId> =
        packs.values().map(|(vid, _)| *vid).collect();
    rewrite(expr, &packs, &helper_ids)
}

fn collect_pack_helpers(expr: &PseudoExpr, out: &mut HashMap<usize, (VarId, String)>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Let {
                name,
                id: Some(vid),
                value,
                body,
                ..
            } => {
                if let Some(arity) = match_pack_helper(value) {
                    // Only store the FIRST helper found per arity — there
                    // shouldn't be two pack_N with the same N in practice.
                    out.entry(arity).or_insert_with(|| (*vid, name.clone()));
                }
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            _ => {}
        }
    }
}

fn match_pack_helper(expr: &PseudoExpr) -> Option<usize> {
    let PseudoExpr::Lambda { params, body } = expr else {
        return None;
    };
    let n = params.len();
    if n < 2 {
        return None;
    }
    let outer_ids: Vec<VarId> = params.iter().map(|b| b.id).collect();
    let PseudoExpr::Lambda {
        params: inner_params,
        body: inner_body,
    } = body.as_ref()
    else {
        return None;
    };
    if inner_params.len() != 1 {
        return None;
    }
    let x_id = inner_params[0].id;
    let PseudoExpr::Apply { function, args } = inner_body.as_ref() else {
        return None;
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        return None;
    };
    if *fn_id != x_id || args.len() != n {
        return None;
    }
    for (i, a) in args.iter().enumerate() {
        let PseudoExpr::Var {
            id: Some(arg_id), ..
        } = a
        else {
            return None;
        };
        if *arg_id != outer_ids[i] {
            return None;
        }
    }
    Some(n)
}

/// Checks whether `Lambda { [x], body }` is an inline church-N-pack
/// (`fn(x) { x(a0..a_{n-1}) }`) that a stored `pack_N` helper can stand in
/// for, returning the helper's id/name and the (unrewritten) args to
/// splice into the replacement `Apply`.
fn match_inline_pack(
    params: &[Binder],
    body: &PseudoExpr,
    packs: &HashMap<usize, (VarId, String)>,
) -> Option<(VarId, String, Vec<PseudoExpr>)> {
    if params.len() != 1 {
        return None;
    }
    let p_id = params[0].id;
    let PseudoExpr::Apply { function, args } = body else {
        return None;
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        return None;
    };
    if *fn_id != p_id {
        return None;
    }
    let n = args.len();
    if n < 2 {
        return None;
    }
    let (pack_id, pack_name) = packs.get(&n)?;
    Some((*pack_id, pack_name.clone(), (args.clone()).into_vec()))
}

/// One pending step of [`rewrite`]'s explicit stack.
enum Step {
    Enter(PseudoExpr),
    /// Move the subtree onto `done` untouched — used to skip rewriting
    /// inside a pack helper's own value (see [`Post::LetBody`]).
    Passthrough(PseudoExpr),
    Post(Post),
}

enum Post {
    Lambda {
        params: Vec<Binder>,
    },
    LetBody {
        name: String,
        id: Option<VarId>,
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

/// `Lambda`, `Let`, `RecFn`, and `When` get their own arms (an inline pack
/// is substituted before its children are queued, a helper `Let`'s value is
/// skipped rather than descended into, and `When`'s clauses carry their
/// pattern through unchanged); every other kind shares the `PlainPost`
/// reassembly this module's sibling passes already use for "wrap every
/// child, no extra logic" nodes.
fn rewrite(
    expr: PseudoExpr,
    packs: &HashMap<usize, (VarId, String)>,
    helper_ids: &std::collections::HashSet<VarId>,
) -> PseudoExpr {
    let mut steps = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match expr {
                PseudoExpr::Lambda { params, body } => {
                    if let Some((pack_id, pack_name, args)) =
                        match_inline_pack(&params, &body, packs)
                    {
                        // Recurse into the args first so nested packs
                        // collapse too; the synthesized `Var` needs no
                        // rewriting itself.
                        steps.push(Step::Post(Post::Plain(PlainPost::Apply {
                            argc: args.len(),
                        })));
                        for a in args.into_iter().rev() {
                            steps.push(Step::Enter(a));
                        }
                        steps.push(Step::Enter(PseudoExpr::Var {
                            name: pack_name,
                            id: Some(pack_id),
                        }));
                    } else {
                        steps.push(Step::Post(Post::Lambda { params }));
                        steps.push(Step::Enter(body.into_inner()));
                    }
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(Step::Post(Post::LetBody { name, id }));
                    steps.push(Step::Enter(body.into_inner()));
                    // Skip rewriting INSIDE the pack helper's own value;
                    // otherwise the helper body becomes a recursive call.
                    if id.is_some_and(|v| helper_ids.contains(&v)) {
                        steps.push(Step::Passthrough(value.into_inner()));
                    } else {
                        steps.push(Step::Enter(value.into_inner()));
                    }
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(Step::Post(Post::RecFn { name, params }));
                    steps.push(Step::Enter(body.into_inner()));
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
                        steps.push(Step::Enter(c));
                    }
                    steps.push(Step::Enter(subject.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(Step::Post(Post::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(Step::Enter(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            Step::Passthrough(expr) => done.push(expr),
            Step::Post(post) => {
                let rebuilt = match post {
                    Post::Lambda { params } => {
                        let body = done.pop().expect("lambda body");
                        PseudoExpr::Lambda {
                            params,
                            body: PBox::new(body),
                        }
                    }
                    Post::LetBody { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    Post::RecFn { name, params } => {
                        let body = done.pop().expect("recfn body");
                        PseudoExpr::RecFn {
                            name,
                            params,
                            body: PBox::new(body),
                        }
                    }
                    Post::When {
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
                    Post::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}
