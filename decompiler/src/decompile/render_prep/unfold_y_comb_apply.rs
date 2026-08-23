//! Unfold a Y-combinator instantiation into a bare `rec fn`.
//!
//! Plutus's lambda-only IR emits
//! `(fn(v) { rec fn self(x) { v(self, x) } })(driver)` for what is
//! `rec fn self(x) { driver(self, x) }`. The wrapper introduces
//! recursion and is applied at once to the driver. Unfolding
//! substitutes `v := driver` into the recfn body — operationally
//! equivalent when the gates hold.
//!
//! Fail-closed: outer Apply has exactly one arg; the function head is
//! `Lambda { params: [v], body: RecFn { … } }`; the RecFn is
//! `rec fn self(x) { v(self, x) }` (same shape
//! `is_y_comb_defining_lambda` recognizes in `cse_y_comb_consts.rs`),
//! so `v` occurs exactly once; the Apply's arg is a pure value per
//! `super::purity::is_pure_value`. The driver becomes a free variable
//! evaluated on every `self` call, which is sound only for pure values.
//!
//! A 2-param `Lambda` driver is then beta-reduced against
//! `(Var(self), Var(x))`; any other driver stays as the Apply head.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn unfold_y_comb_applications(expr: PseudoExpr) -> PseudoExpr {
    let mut folder = YCombUnfolder;
    folder.fold(expr)
}

struct YCombUnfolder;

impl ExprFolder for YCombUnfolder {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    /// Unfold THIS node first, then re-fold the result so nested Y-comb
    /// instantiations also unfold.
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        match try_unfold(expr) {
            Some(unfolded) => FoldAction::Replace(self.fold(unfolded)),
            None => FoldAction::Walk,
        }
    }
}

/// Attempt to recognize the Y-comb-application shape on `expr` and
/// emit the unfolded RecFn. Returns `None` if any guard fails.
fn try_unfold(expr: &PseudoExpr) -> Option<PseudoExpr> {
    let PseudoExpr::Apply { function, args } = expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let driver = &args[0];
    if !super::purity::is_pure_value(driver) {
        return None;
    }
    let PseudoExpr::Lambda {
        params: outer_params,
        body: outer_body,
    } = function.as_ref()
    else {
        return None;
    };
    if outer_params.len() != 1 {
        return None;
    }
    let v_binder = &outer_params[0];
    let v_id = v_binder.var_id();
    let PseudoExpr::RecFn {
        name: self_binder,
        params: inner_params,
        body: rec_body,
    } = outer_body.as_ref()
    else {
        return None;
    };
    let self_id = self_binder.var_id();
    if inner_params.len() != 1 {
        return None;
    }
    let x_binder = &inner_params[0];
    let x_id = x_binder.var_id();
    // rec_body must be exactly `Apply { function: Var(v_id), args:
    // [Var(self_id), Var(x_id)] }` — the canonical shape.
    let PseudoExpr::Apply {
        function: rec_fn,
        args: rec_args,
    } = rec_body.as_ref()
    else {
        return None;
    };
    if !matches!(
        rec_fn.as_ref(),
        PseudoExpr::Var { id: Some(vid), .. } if *vid == v_id
    ) {
        return None;
    }
    if rec_args.len() != 2 {
        return None;
    }
    let self_arg_ok = matches!(
        &rec_args[0],
        PseudoExpr::Var { id: Some(sid), .. } if *sid == self_id
    );
    let x_arg_ok = matches!(
        &rec_args[1],
        PseudoExpr::Var { id: Some(xid), .. } if *xid == x_id
    );
    if !self_arg_ok || !x_arg_ok {
        return None;
    }
    // Substitute `driver` for `Var(v_id)` — the rec body's function
    // head; the args (Var(self), Var(x)) are kept unchanged.
    let new_body =
        beta_reduce_driver_apply(driver, &rec_args[0], &rec_args[1]).unwrap_or_else(|| {
            PseudoExpr::Apply {
                function: PBox::new(driver.clone()),
                args: rec_args.clone(),
            }
        });
    Some(PseudoExpr::RecFn {
        name: self_binder.clone(),
        params: vec![x_binder.clone()],
        body: PBox::new(new_body),
    })
}

/// Beta-reduce `driver(self_arg, x_arg)` when `driver` is a 2-param
/// `Lambda { params: [p_self, p_x], body }` — substitute `Var(p_self.id)`
/// → `self_arg` and `Var(p_x.id)` → `x_arg` throughout `body`.
///
/// `None` when the driver isn't a 2-param Lambda. The substitution
/// assumes `self_arg`/`x_arg` are pure Var references, which they are by
/// construction in `try_unfold`.
///
/// Without it the unfolded recfn keeps a beta-redex the reader must
/// collapse: `rec fn self(v) { fn(p_self, p_x) { body }(self, v) }`.
fn beta_reduce_driver_apply(
    driver: &PseudoExpr,
    self_arg: &PseudoExpr,
    x_arg: &PseudoExpr,
) -> Option<PseudoExpr> {
    let PseudoExpr::Lambda {
        params: drv_params,
        body: drv_body,
    } = driver
    else {
        return None;
    };
    if drv_params.len() != 2 {
        return None;
    }
    let p_self_id = drv_params[0].var_id();
    let p_x_id = drv_params[1].var_id();
    let mut sub = HashMap::new();
    sub.insert(p_self_id, self_arg.clone());
    sub.insert(p_x_id, x_arg.clone());
    Some(substitute_vars((**drv_body).clone(), &sub))
}

/// Walk `expr` substituting every `Var { id: Some(id), .. }` whose
/// `id` is a key in `sub` with the corresponding replacement.
///
/// A substituted `Var` is pushed as-is — the replacement is NOT re-walked, 's terminal
/// arm.
fn substitute_vars(expr: PseudoExpr, sub: &HashMap<VarId, PseudoExpr>) -> PseudoExpr {
    let mut steps: Vec<SubStep> = vec![SubStep::Visit(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            SubStep::Visit(expr) => match expr {
                PseudoExpr::Var { id: Some(id), .. } if sub.contains_key(&id) => {
                    done.push(sub[&id].clone())
                }
                other => push_map_children(other, &mut steps, &mut done),
            },
            SubStep::Post(post) => {
                let rebuilt = rebuild_step(post, &mut done);
                done.push(rebuilt);
            }
        }
    }

    debug_assert_eq!(done.len(), 1, "substitute_vars must leave one result");
    done.pop().expect("substitute_vars result")
}

/// A job on [`substitute_vars`]'s stack: a node still to visit, or rebuild after
/// children.
enum SubStep {
    Visit(PseudoExpr),
    Post(SubPost),
}

enum SubPost {
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

/// Per-variant descent as jobs: push the node's
/// reconstruction, then its children in REVERSE so they pop — and so land on `done` —
/// in source order. Leaves are finished on the spot.
fn push_map_children(node: PseudoExpr, steps: &mut Vec<SubStep>, done: &mut Vec<PseudoExpr>) {
    match node {
        PseudoExpr::Let {
            name,
            id,
            value,
            body,
        } => {
            steps.push(SubStep::Post(SubPost::Let { name, id }));
            steps.push(SubStep::Visit(body.into_inner()));
            steps.push(SubStep::Visit(value.into_inner()));
        }
        PseudoExpr::Lambda { params, body } => {
            steps.push(SubStep::Post(SubPost::Lambda { params }));
            steps.push(SubStep::Visit(body.into_inner()));
        }
        PseudoExpr::RecFn { name, params, body } => {
            steps.push(SubStep::Post(SubPost::RecFn { name, params }));
            steps.push(SubStep::Visit(body.into_inner()));
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
            steps.push(SubStep::Post(SubPost::When {
                subject_name,
                clause_meta,
            }));
            for c in clause_children.into_iter().rev() {
                steps.push(SubStep::Visit(c));
            }
            steps.push(SubStep::Visit(subject.into_inner()));
        }
        other => match plain_children(other) {
            Ok((kind, children)) => {
                steps.push(SubStep::Post(SubPost::Plain(kind)));
                for c in children.into_iter().rev() {
                    steps.push(SubStep::Visit(c));
                }
            }
            Err(leaf) => done.push(leaf),
        },
    }
}

/// Reassemble one node from the already-substituted children on `done`.
fn rebuild_step(post: SubPost, done: &mut Vec<PseudoExpr>) -> PseudoExpr {
    match post {
        SubPost::Let { name, id } => {
            let body = done.pop().expect("let body");
            let value = done.pop().expect("let value");
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
        SubPost::Lambda { params } => PseudoExpr::Lambda {
            params,
            body: PBox::new(done.pop().expect("lambda body")),
        },
        SubPost::RecFn { name, params } => PseudoExpr::RecFn {
            name,
            params,
            body: PBox::new(done.pop().expect("recfn body")),
        },
        SubPost::When {
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
        SubPost::Plain(kind) => rebuild_plain(kind, done),
    }
}

// suppress unused-import warning — Binder/VarId are referenced indirectly
// via the AST destructuring patterns.
#[allow(dead_code)]
fn _unused_imports(_b: Binder, _v: VarId) {}

#[cfg(test)]
mod tests;
