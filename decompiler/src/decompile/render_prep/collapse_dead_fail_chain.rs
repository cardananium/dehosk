//! Collapse `let X = fail; fail` chains into a single `fail`.
//!
//! PlutusTx emits each source-level `error "msg"` as a synthetic
//! `let _ = error in error`. Once the message is reduced or dropped
//! by later simplification, the Let's value is the live error — it
//! terminates execution; the Let's body is dead.
//!
//! Fires only when both value and body are `PseudoExpr::Error { .. }`
//! and the binder is unreferenced, and collapses to the *value*, so
//! the surviving `fail` keeps the live site's optional message.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::{ExprFolder, ExprVisitor};
use crate::pseudo::var_id::VarId;

pub(super) fn collapse_dead_fail_chain(expr: PseudoExpr) -> PseudoExpr {
    let counts = count_var_uses(&expr);
    let mut collapser = Collapser { counts };
    collapser.fold(expr)
}

fn count_var_uses(expr: &PseudoExpr) -> HashMap<VarId, usize> {
    struct UseCounter {
        counts: HashMap<VarId, usize>,
    }
    impl ExprVisitor for UseCounter {
        fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
            if let Some(id) = id {
                *self.counts.entry(*id).or_insert(0) += 1;
            }
        }
    }
    let mut c = UseCounter {
        counts: HashMap::new(),
    };
    c.walk(expr);
    c.counts
}

struct Collapser {
    counts: HashMap<VarId, usize>,
}

impl ExprFolder for Collapser {
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
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let value_is_error = matches!(value, PseudoExpr::Error { .. });
        let body_is_error = matches!(body, PseudoExpr::Error { .. });
        if value_is_error && body_is_error {
            let binder_unused = id
                .map(|id| self.counts.get(&id).copied().unwrap_or(0) == 0)
                .unwrap_or(true);
            if binder_unused {
                return value;
            }
        }
        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }
}

#[cfg(test)]
mod tests;
