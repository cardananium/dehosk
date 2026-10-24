//! Fold `Apply { Var(c), [] }` → `Var(c)` when `c` is let-bound to a
//! `Lambda` or `RecFn` value (i.e. provably non-`Delay`).
//!
//! UPLC's `force` undoes a `delay`. At the pseudo-AST level a `force`
//! survives as `Apply { function: Var(c), args: [] }`, which the
//! renderer prints as `c()`. Some V1 scripts bind a frequently-used
//! helper (`const c = fn(x) { x }`) and then write `c()(arg)` at every
//! use site, forcing a value that is not a Delay anyway.
//!
//! `force(x)` is a no-op only when `x` is not a `Delay`, so the fold
//! fires only for bindings whose value is a `Lambda` or `RecFn` — both
//! syntactically guaranteed non-`Delay`. Other bound shapes (Apply,
//! Force, BuiltinCall — anything that might evaluate to a `Delay` at
//! runtime) are left alone.

use std::collections::HashMap;

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

pub(super) fn fold_force_on_lambda_var(expr: PseudoExpr) -> PseudoExpr {
    let mut lambda_bound: HashMap<VarId, ()> = HashMap::new();
    collect_lambda_bindings(&expr, &mut lambda_bound);
    if lambda_bound.is_empty() {
        return expr;
    }
    ForceOnLambdaVarFolder {
        env: &lambda_bound,
        unmatched_below: 0,
    }
    .fold(expr)
}

fn collect_lambda_bindings(expr: &PseudoExpr, env: &mut HashMap<VarId, ()>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        let mut kids: Vec<&PseudoExpr> = Vec::new();
        match cur {
            PseudoExpr::Let {
                id: Some(vid),
                value,
                body,
                ..
            } => {
                if matches!(
                    value.as_ref(),
                    PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. }
                ) {
                    env.insert(*vid, ());
                }
                kids.push(value);
                kids.push(body);
            }
            PseudoExpr::Let { value, body, .. } => {
                kids.push(value);
                kids.push(body);
            }
            PseudoExpr::Lambda { body, .. } => kids.push(body),
            PseudoExpr::RecFn { body, .. } => kids.push(body),
            PseudoExpr::Apply { function, args } => {
                kids.push(function);
                for a in args {
                    kids.push(a);
                }
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                kids.push(subject);
                for c in clauses {
                    if let Some(g) = &c.guard {
                        kids.push(g);
                    }
                    kids.push(&c.body);
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                kids.push(condition);
                kids.push(then_branch);
                kids.push(else_branch);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                kids.push(left);
                kids.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => kids.push(operand),
            PseudoExpr::Constr { fields, .. } => {
                for f in fields {
                    kids.push(f);
                }
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args {
                    kids.push(a);
                }
            }
            PseudoExpr::List { elements, tail } => {
                for e in elements {
                    kids.push(e);
                }
                if let Some(t) = tail {
                    kids.push(t);
                }
            }
            PseudoExpr::Tuple(elements) => {
                for e in elements {
                    kids.push(e);
                }
            }
            PseudoExpr::Pair(a, b) => {
                kids.push(a);
                kids.push(b);
            }
            PseudoExpr::FieldAccess { record, .. } => kids.push(record),
            PseudoExpr::IndexAccess { collection, .. } => kids.push(collection),
            PseudoExpr::Trace { message, value } => {
                kids.push(message);
                kids.push(value);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => kids.push(inner),
            _ => {}
        }
        pending.extend(kids.into_iter().rev());
    }
}

struct ForceOnLambdaVarFolder<'a> {
    env: &'a HashMap<VarId, ()>,
    /// The `Force`s straight below the last one peeled without a match. They
    /// end at the same node, so they cannot match either — and peeling each
    /// again would cost time quadratic in the chain, whose length is the
    /// script's to choose. The machine enters them next, one after another.
    unmatched_below: usize,
}

impl ExprFolder for ForceOnLambdaVarFolder<'_> {
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        match expr {
            // `Force(...Force(Var(c)))` with `c` Lambda/RecFn-bound →
            // `Var(c)`. The renderer prints `Force(x)` as `x()`, so
            // peeling every wrapper folds `c()`, `c()()` and deeper.
            PseudoExpr::Force(inner) => {
                if self.unmatched_below > 0 {
                    self.unmatched_below -= 1;
                    return FoldAction::Walk;
                }
                let mut cur: &PseudoExpr = inner.as_ref();
                let mut below = 0;
                while let PseudoExpr::Force(deeper) = cur {
                    cur = deeper.as_ref();
                    below += 1;
                }
                if let PseudoExpr::Var { id: Some(vid), .. } = cur {
                    if self.env.contains_key(vid) {
                        return FoldAction::Replace(cur.clone());
                    }
                }
                self.unmatched_below = below;
                FoldAction::Walk
            }
            // Also handle the rare direct `Apply { Var(c), [] }` shape
            // (some upstream paths emit this instead of Force).
            PseudoExpr::Apply { function, args } if args.is_empty() => {
                if let PseudoExpr::Var { id: Some(vid), .. } = function.as_ref() {
                    if self.env.contains_key(vid) {
                        return FoldAction::Replace(self.fold((**function).clone()));
                    }
                }
                FoldAction::Walk
            }
            _ => FoldAction::Walk,
        }
    }

    // Folded flat — each clause's guard, then its body, patterns left as
    // they are, as the old clause hook did — so a deep `when` costs no
    // stack.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn machine_keeps_pattern_literals(&self) -> bool {
        true
    }
}
