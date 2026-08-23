//! Drop a `Let`-bound helper function that nothing in the program
//! references.
//!
//! [`super::drop_dead_pure_lets`] keeps a dead `fn` whose body carries a
//! `trace`/`fail`, so the reader does not lose the message. That holds
//! for a binding whose scope the reader can still reach; it does not
//! hold for a helper no call site mentions. Its `fail` is unreachable,
//! and it tells the reader nothing about what the script does.
//!
//! PlutusTx emits these in bulk: its `expect`-shaped type assertions
//! survive compilation as uncalled top-level functions, and one V2
//! script in the corpus carried five of them — a fifth of the rendered
//! output with no reachable statement in it.
//!
//! Two things make this sound where the pure-let sweep has to be
//! careful:
//!
//!   * The value is a `Lambda` or `RecFn`. Binding a closure has no
//!     effect; the body runs only on application, and a binder with no
//!     reference is never applied. Nothing else is dropped here — the
//!     purity question for other values stays with the pure-let sweep.
//!   * Reference counting is WHOLE-TREE. Hoisting and inlining move
//!     call sites across binding boundaries, which is exactly why the
//!     pure-let sweep refuses a bare `RecFn` on a body-scoped scan.
//!     Counting every `Var` in the tree removes that doubt: zero
//!     occurrences anywhere means there is no call site to lose. A
//!     recursive helper's own self-reference is discounted, since a
//!     function calling only itself is still unreachable.
//!
//! Both an id count and a NAME count have to come out empty. A
//! `PseudoExpr::Var` may carry `id: None` and be resolved by name — the
//! pure-let sweep guards the same way — so an id-only scan would call a
//! called helper dead and render a free call.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::{ExprFolder, ExprVisitor};
use crate::pseudo::var_id::VarId;

use super::drop_dead_pure_lets::contains_decompiled_marker;

/// Bound on the fixpoint: dropping one helper can strand the ones it
/// was the only caller of, so the sweep repeats. Each round removes at
/// least one binding, so the chain length bounds it; the cap is only a
/// guard against a pathological tree.
const MAX_ROUNDS: usize = 64;

pub(super) fn drop_unreferenced_helper_fns(expr: PseudoExpr) -> PseudoExpr {
    // Same gate as the pure-let sweep: without the validator marker the
    // tree may be a fragment whose call sites live outside it.
    if !contains_decompiled_marker(&expr) {
        return expr;
    }
    let mut expr = expr;
    for _ in 0..MAX_ROUNDS {
        let (counts, name_counts) = count_var_uses(&expr);
        let mut dropper = Dropper {
            counts,
            name_counts,
            dropped: false,
        };
        expr = dropper.fold(expr);
        if !dropper.dropped {
            break;
        }
    }
    expr
}

/// Every `Var` occurrence, counted by id AND by name. The name tally
/// covers the id-less references the AST allows.
fn count_var_uses(expr: &PseudoExpr) -> (HashMap<VarId, usize>, HashMap<String, usize>) {
    struct UseCounter {
        counts: HashMap<VarId, usize>,
        name_counts: HashMap<String, usize>,
    }
    impl ExprVisitor for UseCounter {
        fn visit_var(&mut self, name: &str, id: &Option<VarId>) {
            if let Some(id) = id {
                *self.counts.entry(*id).or_insert(0) += 1;
            }
            *self.name_counts.entry(name.to_string()).or_insert(0) += 1;
        }
    }
    let mut c = UseCounter {
        counts: HashMap::new(),
        name_counts: HashMap::new(),
    };
    c.walk(expr);
    (c.counts, c.name_counts)
}

struct Dropper {
    counts: HashMap<VarId, usize>,
    name_counts: HashMap<String, usize>,
    dropped: bool,
}

impl ExprFolder for Dropper {
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
        // The validator entry is the program; it has no caller by design.
        let droppable = name != "decompiled"
            && matches!(value, PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. });
        if droppable && let Some(vid) = id {
            // A recursive helper mentions itself; that is not a call
            // site the reader can reach from anywhere else, so the
            // binding's own occurrences come off both tallies.
            let (own_ids, own_names) = count_var_uses(&value);
            let by_id = self
                .counts
                .get(&vid)
                .copied()
                .unwrap_or(0)
                .saturating_sub(own_ids.get(&vid).copied().unwrap_or(0));
            let by_name = self
                .name_counts
                .get(&name)
                .copied()
                .unwrap_or(0)
                .saturating_sub(own_names.get(&name).copied().unwrap_or(0));
            if by_id == 0 && by_name == 0 {
                self.dropped = true;
                return body;
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
