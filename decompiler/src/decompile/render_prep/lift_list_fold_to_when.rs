//! Rewrite the 4-arg `List.fold(xs, nil, fn(_) { cons_body }, k)` residue to
//! an idiomatic `when xs is { [] -> nil; [_, ..] -> cons_body }` match.
//!
//! UPLC's `chooseList` is logically 3-arg. Plutus's church-list builders
//! emit a CPS-style 4-arg variant applied to an identity continuation.
//! The MID `try_recognize_choose_list` recognizer requires exactly 3
//! args, so this form survives as a raw `List.fold` BuiltinCall that
//! reads as a fold rather than the structural list match it is.
//!
//! The identity continuation is often not an inline `fn(x) { x }` but a
//! reference to a CSE-hoisted identity helper `fn d(x) { x }` shared
//! across call sites. Both are accepted; a `Var` is matched by `VarId`,
//! so it is provably the identity and never a same-named imposter.
//!
//! The cons body's references to the outer `xs` (`xs.head`, `xs[1..]`)
//! stay valid: the enclosing rec-fn param is still in scope inside the
//! `when`.
//!
//! - Fires only on `BuiltinCall::ListFold` (alias `choose_list`) with
//!   exactly 4 args whose 4th is the identity (CPS form) or `Unit`
//!   (forced-thunk form).
//! - The 3rd arg must be a 1-arg ignore-param Lambda; any other shape
//!   leaves the BuiltinCall alone.
//! - The 2nd arg (nil case) is taken as-is in the CPS form. In the
//!   forced-thunk form a Lambda nil must be a 1-arg ignore-param thunk,
//!   which is unwrapped; any other Lambda bails.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::BuiltinId;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn lift_list_fold_to_when(expr: PseudoExpr) -> PseudoExpr {
    // Collected once over the whole tree so the walk can match a 4th
    // arg that references a hoisted identity helper.
    let identity_ids = collect_identity_helper_ids(&expr);
    rewrite(expr, &identity_ids)
}

/// `VarId`s of every let-binding whose value is an identity lambda
/// `fn(p) { p }` — the CSE-hoisted continuations a `List.fold` 4th arg
/// may reference by name.
fn collect_identity_helper_ids(expr: &PseudoExpr) -> HashSet<VarId> {
    struct Collector {
        ids: HashSet<VarId>,
    }
    impl ExprVisitor for Collector {
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, value: &PseudoExpr) {
            if let Some(vid) = id
                && is_identity_lambda(value)
            {
                self.ids.insert(*vid);
            }
        }
    }
    let mut c = Collector {
        ids: HashSet::new(),
    };
    c.walk(expr);
    c.ids
}

/// One pending step of [`rewrite`]'s explicit job stack.
enum Step {
    Enter(PseudoExpr),
    Post(PostKind),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being rewritten.
enum PostKind {
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
        /// Per clause: its pattern (never descended into, exactly as
        /// `recurse_children` left it) and whether it had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    Plain(PlainPost),
}

/// Rebuild each node from its already-rewritten children, then try to fire
/// at it.
///
/// Children are pushed in REVERSE so they pop in source order, and are
/// popped off `done` in that same order when the node is rebuilt.
fn rewrite(expr: PseudoExpr, identity_ids: &HashSet<VarId>) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match expr {
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
                    steps.push(Step::Post(PostKind::When {
                        subject_name,
                        clause_meta,
                    }));
                    for c in clause_children.into_iter().rev() {
                        steps.push(Step::Enter(c));
                    }
                    steps.push(Step::Enter(subject.into_inner()));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(Step::Post(PostKind::Let { name, id }));
                    steps.push(Step::Enter(body.into_inner()));
                    steps.push(Step::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(Step::Post(PostKind::Lambda { params }));
                    steps.push(Step::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(Step::Post(PostKind::RecFn { name, params }));
                    steps.push(Step::Enter(body.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(Step::Post(PostKind::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(Step::Enter(c));
                        }
                    }
                    // `recurse_children` returned a leaf unchanged, and the
                    // node's own attempt still ran on it.
                    Err(leaf) => done.push(try_rewrite_list_fold(leaf, identity_ids)),
                },
            },
            Step::Post(post) => {
                let rebuilt = match post {
                    PostKind::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
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
                // Children rebuilt, now try to fire at this node.
                done.push(try_rewrite_list_fold(rebuilt, identity_ids));
            }
        }
    }

    done.pop().expect("rewrite leaves exactly one result")
}

fn try_rewrite_list_fold(expr: PseudoExpr, identity_ids: &HashSet<VarId>) -> PseudoExpr {
    let PseudoExpr::BuiltinCall { name, args } = expr else {
        return expr;
    };
    if name != BuiltinId::ListFold || args.len() != 4 {
        return PseudoExpr::BuiltinCall { name, args };
    }
    // Two 4th-arg conventions for the church `chooseList` residue:
    //   - CPS: an identity continuation `fn(x){x}` (or a hoisted identity
    //     helper) — `(chooseList xs nil consThunk) (fn(x){x})`.
    //   - Forced-thunk: an applied `unit`/`Void` forcing the SELECTED (thunk)
    //     branch — `chooseList xs (lam _ nil) (lam _ cons) (con unit ())`.
    // Both denote the same `when xs is { [] -> nil; [_, ..] -> cons }`.
    let is_void_form = matches!(&args[3], PseudoExpr::Unit);
    if !is_void_form && !is_identity_continuation(&args[3], identity_ids) {
        return PseudoExpr::BuiltinCall { name, args };
    }
    let [list, nil_case, cons_thunk, fourth] =
        <[PseudoExpr; 4]>::try_from(args.into_vec()).unwrap();

    // Validate the branch shapes BEFORE consuming, so a bail can reconstruct
    // the original call losslessly. The cons branch is a 1-arg ignore-param
    // thunk in both forms.
    let cons_ok = is_ignored_unit_thunk(&cons_thunk);
    // In the forced-thunk (Void) form the applied `unit` forces the SELECTED
    // branch, so a lambda nil branch must be a clean ignore-param thunk; any
    // other lambda does not reduce to itself and the rewrite must bail:
    //   - `fn(u){ u }` (used param)    -> `()`, not the lambda
    //   - `fn(a, b){ .. }` (multi-arg) -> a partial application, not the lambda
    // A non-lambda nil (Simplify often pre-reduces a constant nil thunk to a
    // bare value) is used as-is, as is nil in the CPS form.
    let nil_strip = is_void_form && is_ignored_unit_thunk(&nil_case);
    let nil_ok = !is_void_form
        || !matches!(&nil_case, PseudoExpr::Lambda { .. })
        || is_ignored_unit_thunk(&nil_case);
    if !cons_ok || !nil_ok {
        return PseudoExpr::BuiltinCall {
            name,
            args: vec![list, nil_case, cons_thunk, fourth].into(),
        };
    }

    let cons_body = strip_one_arg_lambda_body(cons_thunk);
    let nil_body = if nil_strip {
        strip_one_arg_lambda_body(nil_case)
    } else {
        nil_case
    };

    let nil_pattern = WhenPattern::List {
        elements: vec![],
        tail: None,
    };
    let cons_pattern = WhenPattern::List {
        elements: vec![Binder::synthetic("_")],
        tail: Some(Binder::synthetic("_")),
    };
    PseudoExpr::When {
        subject: PBox::new(list),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: nil_pattern,
                guard: None,
                body: nil_body,
            },
            WhenClause {
                pattern: cons_pattern,
                guard: None,
                body: cons_body,
            },
        ],
    }
}

/// Is `expr` a 1-arg thunk `fn(p) { body }` whose param `p` is NOT
/// referenced anywhere in `body`? Forced by an applied `unit` such a thunk
/// reduces to `body`: `(fn(_) { branch }) ()` ≡ `branch`. A thunk whose
/// param is used is not a unit-ignoring delay, so stripping it would leave a
/// dangling var.
fn is_ignored_unit_thunk(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Lambda { params, body }
            if params.len() == 1 && !var_referenced(body, params[0].id)
    )
}

/// Unwrap a 1-arg `Lambda` to its body. The caller must have established the
/// shape via [`is_ignored_unit_thunk`] first.
fn strip_one_arg_lambda_body(expr: PseudoExpr) -> PseudoExpr {
    match expr {
        PseudoExpr::Lambda { body, .. } => body.into_inner(),
        other => other,
    }
}

/// Does `expr` reference `target` as a `Var` anywhere? The
/// [`ExprVisitor`] walk is COMPLETE — it descends into `when`-clause
/// `WhenPattern::Literal` payloads, which `scope_recurse::children` omits.
fn var_referenced(expr: &PseudoExpr, target: VarId) -> bool {
    struct RefFinder {
        target: VarId,
        found: bool,
    }
    impl ExprVisitor for RefFinder {
        fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
            if *id == Some(self.target) {
                self.found = true;
            }
        }
    }
    let mut finder = RefFinder {
        target,
        found: false,
    };
    finder.walk(expr);
    finder.found
}

/// The 4th `List.fold` arg is an identity continuation: an inline
/// `fn(x) { x }`, or a `Var` whose `VarId` is a let-bound identity helper.
fn is_identity_continuation(expr: &PseudoExpr, identity_ids: &HashSet<VarId>) -> bool {
    if is_identity_lambda(expr) {
        return true;
    }
    matches!(expr, PseudoExpr::Var { id: Some(vid), .. } if identity_ids.contains(vid))
}

/// Is `expr` an identity Lambda `fn(x) { x }`? Exactly one param, body a
/// `Var` resolving to it.
fn is_identity_lambda(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let param = &params[0];
    let PseudoExpr::Var {
        name: body_name,
        id: body_id,
    } = body.as_ref()
    else {
        return false;
    };
    // Match either by id (preferred) or by name (fallback for nameless
    // shapes where ids were stripped upstream).
    match body_id {
        Some(body_var_id) => *body_var_id == param.id,
        None => body_name == &param.name,
    }
}

#[cfg(test)]
mod tests;
