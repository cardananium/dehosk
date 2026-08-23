//! Free variable analysis for MidExpr.
//!
//! `Closure` nodes carry no capture set, so callers compute free
//! variables on demand with `free_vars`.

use std::collections::HashSet;

use crate::pseudo::mid::expr::{MidBranch, MidExpr};
use crate::pseudo::var_id::VarId;

pub(crate) fn free_vars(expr: &MidExpr) -> HashSet<VarId> {
    let mut fv = HashSet::new();
    free_vars_rec(expr, &mut HashSet::new(), &mut fv);
    fv
}

/// One pending step of the scoped free-variable walk.
enum Step<'a> {
    Visit(&'a MidExpr),
    /// A `let`: its VALUE is walked outside the binding, its body inside.
    EnterLetBody {
        var: VarId,
        body: &'a MidExpr,
    },
    /// A `case` branch: its binders are in scope for its body only.
    EnterBranch(&'a MidBranch),
    /// Drop the binders a scope ADDED — never the ones it shadowed, which
    /// were already bound by an enclosing scope and must survive.
    Unbind(Vec<VarId>),
}

/// Collect the free variables of `expr`, iteratively.
fn free_vars_rec(expr: &MidExpr, bound: &mut HashSet<VarId>, free: &mut HashSet<VarId>) {
    /// Bind `vars`, reporting the ones that were NOT already bound.
    fn bind(vars: impl IntoIterator<Item = VarId>, bound: &mut HashSet<VarId>) -> Vec<VarId> {
        vars.into_iter().filter(|v| bound.insert(*v)).collect()
    }

    let mut steps: Vec<Step<'_>> = vec![Step::Visit(expr)];
    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(expr) => match expr {
                MidExpr::Var { var, .. } => {
                    if !bound.contains(var) {
                        free.insert(*var);
                    }
                }
                MidExpr::Closure { params, body, .. } => {
                    let added = bind(params.iter().copied(), bound);
                    steps.push(Step::Unbind(added));
                    steps.push(Step::Visit(body));
                }
                MidExpr::Let {
                    var, value, body, ..
                } => {
                    steps.push(Step::EnterLetBody { var: *var, body });
                    steps.push(Step::Visit(value));
                }
                MidExpr::Case {
                    scrutinee,
                    branches,
                    ..
                } => {
                    for b in branches.iter().rev() {
                        steps.push(Step::EnterBranch(b));
                    }
                    steps.push(Step::Visit(scrutinee));
                }
                other => {
                    for child in other.children().into_iter().rev() {
                        steps.push(Step::Visit(child));
                    }
                }
            },
            Step::EnterLetBody { var, body } => {
                let added = bind([var], bound);
                steps.push(Step::Unbind(added));
                steps.push(Step::Visit(body));
            }
            Step::EnterBranch(b) => {
                let added = bind(b.binders.iter().copied(), bound);
                steps.push(Step::Unbind(added));
                steps.push(Step::Visit(&b.body));
            }
            Step::Unbind(added) => {
                for v in added {
                    bound.remove(&v);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
