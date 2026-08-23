//! Decode church-list fold-partial application to a Lambda-of-applies.
//!
//! After `decode_church_to_native` + `inline_pack_call_use_sites`, V1
//! scripts leave church-list fold-partial applications: a list
//! literal applied to one arg. That is invalid surface syntax.
//! Semantically the church list is applied to just the cons-step `k`,
//! leaving a fold still awaiting its nil case:
//! `[H1, …, HN, ..nil](k) = fn(n) -> k(H1, k(H2, …, k(HN, n)))`.
//!
//! The rewrite binds `k` once via `let k_alias = k` (UPLC is
//! call-by-value, so `k` evaluates once; cloning the AST N times
//! would duplicate that work for a non-trivial `k`). If `k` is
//! already a `Var`, the alias let is skipped.
//!
//! Fires only when `function` (or its peeled Let-chain final body) is
//! `PseudoExpr::List { elements, tail: Some(Var(s_id)) }` and `s_id`
//! is a known zero-arity `Constr` — the church-nil sentinel.
//! `args.len()` must be exactly 1 (strict partial; 2-arg complete
//! folds are a different shape handled elsewhere).
//! `elements.is_empty()` is a no-op: an empty list would produce
//! `fn(n) -> n`. Any tail other than the nil sentinel skips —
//! multi-list concat semantics aren't expressible here. The `n`
//! binder gets a freshly allocated `VarId`, so it cannot capture
//! anything in scope, including free vars of `k`. `Force` wrappers
//! around the inner List are peeled, as in `inline_pack_call_use_sites`.
//! Idempotent — after the rewrite the outermost node is `Lambda` (or
//! `Let { …, body: Lambda }` when the function position was a Let-chain),
//! which no longer matches the `Apply { fn: List, [k] }` detector.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children as scope_children;

pub(super) fn decode_church_list_fold_partial(expr: PseudoExpr) -> PseudoExpr {
    let mut nil_vids: HashMap<VarId, ()> = HashMap::new();
    collect_nil_sentinels(&expr, &mut nil_vids);
    if nil_vids.is_empty() {
        return expr;
    }
    rewrite(expr, &nil_vids)
}

fn rewrite(expr: PseudoExpr, nil_vids: &HashMap<VarId, ()>) -> PseudoExpr {
    RewriteFoldPartial { nil_vids }.fold(expr)
}

struct RewriteFoldPartial<'a> {
    nil_vids: &'a HashMap<VarId, ()>,
}

impl ExprFolder for RewriteFoldPartial<'_> {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    // Runs after `function`/`args` are already folded (bottom-up), same as
    // the old post-order `map_children` call.
    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        try_rewrite_apply(
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            },
            self.nil_vids,
        )
    }
}

/// Zero-arity tag-0 `Constr` lets, anywhere in the tree — the
/// church-nil convention. The same value form also serves as a
/// church bool; only the elimination context tells them apart.
fn collect_nil_sentinels(expr: &PseudoExpr, out: &mut HashMap<VarId, ()>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            body,
            ..
        } = cur
        {
            if let PseudoExpr::Constr { tag, fields, .. } = value.as_ref() {
                if *tag == 0 && fields.is_empty() {
                    out.insert(*vid, ());
                }
            }
            pending.push(body.as_ref());
            pending.push(value.as_ref());
            continue;
        }
        pending.extend(scope_children(cur).into_iter().rev());
    }
}

/// `push_rewrite_inward`'s `Let` arm uses this to detect that
/// pushing the rewrite inside a let-binding would change `k`'s
/// binding scope.
fn k_contains_var_id(k: &PseudoExpr, target_id: VarId) -> bool {
    let mut pending = vec![k];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Var { id: Some(v), .. } => {
                if *v == target_id {
                    return true;
                }
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args.iter());
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for c in clauses {
                    if let Some(g) = &c.guard {
                        pending.push(g);
                    }
                    pending.push(&c.body);
                }
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(t) = tail.as_deref() {
                    pending.push(t);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items.iter()),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
            _ => {}
        }
    }
    false
}

fn try_rewrite_apply(expr: PseudoExpr, nil_vids: &HashMap<VarId, ()>) -> PseudoExpr {
    let PseudoExpr::Apply { function, args } = expr else {
        return expr;
    };
    // Strict partial: exactly 1 arg.
    if args.len() != 1 {
        return PseudoExpr::Apply { function, args };
    }
    let mut args_vec = args;
    let k = args_vec.pop().expect("args.len() == 1");
    match push_rewrite_inward(function.into_inner(), &k, nil_vids) {
        PushResult::Rewritten(new_expr) => new_expr,
        PushResult::NoMatch(function_back) => PseudoExpr::Apply {
            function: PBox::new(function_back),
            args: vec![k].into(),
        },
    }
}

enum PushResult {
    Rewritten(PseudoExpr),
    NoMatch(PseudoExpr),
}

/// Walk `expr` (the function side of an `Apply { fn: expr, args: [k] }`)
/// looking for a `List { tail: Some(Var(nil_sentinel)) }` leaf wrapped
/// in any combination of `Let` and `When`, and replace that leaf with
/// the church-list-fold Lambda form, keeping the outer structure
/// intact.
///
/// `When` peeling: the church-list literal often sits inside an
/// `expect Pattern = subject` desugaring — a `When` whose single
/// non-fail clause carries the continuation body while the rest lead
/// to `Error` / `Trace { value: Error }`. The rewrite goes into that
/// clause. A `When` with more than one non-fail clause is a real
/// match and is not pushed through: `k` would then be applied to a
/// different list per branch.
/// One un-rewound layer of the descent: the parts of a `Let` / `When` /
/// `Force` wrapper that are NOT on the path being followed, kept aside so
/// the unwind can rebuild the original wrapper around whatever the descent
/// found (rewritten or not).
enum Frame {
    Let {
        name: String,
        id: Option<VarId>,
        value: PBox,
    },
    When {
        subject: PBox,
        subject_name: Option<Binder>,
        clauses_vec: Vec<crate::pseudo::ast::WhenClause>,
        success_idx: usize,
        pattern: crate::pseudo::ast::WhenPattern,
        guard: Option<PseudoExpr>,
    },
    Force,
}

fn push_rewrite_inward(
    expr: PseudoExpr,
    k: &PseudoExpr,
    nil_vids: &HashMap<VarId, ()>,
) -> PushResult {
    let mut frames: Vec<Frame> = Vec::new();
    let mut cur = expr;
    let mut result = loop {
        match cur {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                // Capture safety: if `k` references the let-bound `id`,
                // pushing the rewrite INSIDE the let rebinds `k`'s Var
                // to this binding, not the outer one it named. Abort
                // the push here. Defensive — VarIds are hygienic
                // elsewhere in the pipeline.
                if let Some(let_id) = id {
                    if k_contains_var_id(k, let_id) {
                        break PushResult::NoMatch(PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body,
                        });
                    }
                }
                frames.push(Frame::Let { name, id, value });
                cur = body.into_inner();
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                // Identify single non-Error clause as the push target.
                let (success_idx, _fail_count) = classify_when_for_push(&clauses);
                let Some(success_idx) = success_idx else {
                    break PushResult::NoMatch(PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    });
                };
                // Push the rewrite into the success clause's body.
                let mut clauses_vec = clauses;
                let success_clause = std::mem::replace(
                    &mut clauses_vec[success_idx],
                    crate::pseudo::ast::WhenClause {
                        pattern: crate::pseudo::ast::WhenPattern::Wildcard,
                        guard: None,
                        body: PseudoExpr::Unit,
                    },
                );
                let crate::pseudo::ast::WhenClause {
                    pattern,
                    guard,
                    body,
                } = success_clause;
                frames.push(Frame::When {
                    subject,
                    subject_name,
                    clauses_vec,
                    success_idx,
                    pattern,
                    guard,
                });
                cur = body;
            }
            PseudoExpr::Force(inner) => {
                // Treat Force as transparent — peel and try again, but
                // preserve the Force wrapper if no match.
                frames.push(Frame::Force);
                cur = inner.into_inner();
            }
            PseudoExpr::List {
                elements,
                tail: Some(tail_box),
            } => {
                if elements.is_empty() {
                    break PushResult::NoMatch(PseudoExpr::List {
                        elements,
                        tail: Some(tail_box),
                    });
                }
                // Verify tail is a known nil sentinel.
                let nil_ok = matches!(
                    tail_box.as_ref(),
                    PseudoExpr::Var { id: Some(v), .. } if nil_vids.contains_key(v)
                );
                if !nil_ok {
                    break PushResult::NoMatch(PseudoExpr::List {
                        elements,
                        tail: Some(tail_box),
                    });
                }
                break PushResult::Rewritten(build_fold_lambda(elements.into_vec(), k.clone()));
            }
            other => break PushResult::NoMatch(other),
        }
    };
    while let Some(frame) = frames.pop() {
        result = match frame {
            Frame::Let { name, id, value } => match result {
                PushResult::Rewritten(new_body) => PushResult::Rewritten(PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body: PBox::new(new_body),
                }),
                PushResult::NoMatch(body_back) => PushResult::NoMatch(PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body: PBox::new(body_back),
                }),
            },
            Frame::When {
                subject,
                subject_name,
                mut clauses_vec,
                success_idx,
                pattern,
                guard,
            } => match result {
                PushResult::Rewritten(new_body) => {
                    clauses_vec[success_idx] = crate::pseudo::ast::WhenClause {
                        pattern,
                        guard,
                        body: new_body,
                    };
                    PushResult::Rewritten(PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses: clauses_vec,
                    })
                }
                PushResult::NoMatch(body_back) => {
                    clauses_vec[success_idx] = crate::pseudo::ast::WhenClause {
                        pattern,
                        guard,
                        body: body_back,
                    };
                    PushResult::NoMatch(PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses: clauses_vec,
                    })
                }
            },
            Frame::Force => match result {
                PushResult::Rewritten(new) => PushResult::Rewritten(new),
                PushResult::NoMatch(inner_back) => {
                    PushResult::NoMatch(PseudoExpr::Force(PBox::new(inner_back)))
                }
            },
        };
    }
    result
}

/// Index of the one clause whose body is not an `Error` (or a Trace
/// leading to one). `Some` only when EXACTLY one such clause
/// exists; a multi-success When binds a different list per branch
/// and is not pushed through.
fn classify_when_for_push(clauses: &[crate::pseudo::ast::WhenClause]) -> (Option<usize>, usize) {
    let mut success_idx: Option<usize> = None;
    let mut fail_count = 0;
    let mut success_count = 0;
    for (i, clause) in clauses.iter().enumerate() {
        if clause.guard.is_some() {
            // Guarded clauses are conservatively treated as "complex"
            // — skip the push.
            return (None, 0);
        }
        if is_fail_body(&clause.body) {
            fail_count += 1;
        } else {
            success_count += 1;
            success_idx = Some(i);
        }
    }
    if success_count == 1 {
        (success_idx, fail_count)
    } else {
        (None, 0)
    }
}

fn is_fail_body(expr: &PseudoExpr) -> bool {
    let mut cur = expr;
    // Peel Trace wrappers — `trace @"msg": fail @"x"` is still a fail.
    loop {
        match cur {
            PseudoExpr::Error { .. } => return true,
            PseudoExpr::Trace { value, .. } => cur = value.as_ref(),
            _ => return false,
        }
    }
}

fn build_fold_lambda(elements: Vec<PseudoExpr>, k: PseudoExpr) -> PseudoExpr {
    let n_id = VarId::fresh_binding();
    let n_var = PseudoExpr::Var {
        name: "n".to_string(),
        id: Some(n_id),
    };
    let (alias_var, alias_let_wrapper): (PseudoExpr, Option<(String, VarId)>) =
        if matches!(&k, PseudoExpr::Var { .. }) {
            (k.clone(), None)
        } else {
            let alias_id = VarId::fresh_binding();
            (
                PseudoExpr::Var {
                    name: "k_alias".to_string(),
                    id: Some(alias_id),
                },
                Some(("k_alias".to_string(), alias_id)),
            )
        };
    let mut chain = n_var;
    for h in elements.into_iter().rev() {
        chain = PseudoExpr::Apply {
            function: PBox::new(alias_var.clone()),
            args: vec![h, chain].into(),
        };
    }
    let lambda_body = if let Some((alias_name, alias_id)) = alias_let_wrapper {
        PseudoExpr::Let {
            name: alias_name,
            id: Some(alias_id),
            value: PBox::new(k),
            body: PBox::new(chain),
        }
    } else {
        chain
    };
    PseudoExpr::Lambda {
        params: vec![Binder::new("n".to_string(), n_id)],
        body: PBox::new(lambda_body),
    }
}

#[cfg(test)]
mod tests;
