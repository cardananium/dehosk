//! Print a `let` nothing reads as the statement it actually is.
//!
//! PlutusTx compiles a total-match assertion into a value:
//!
//! ```text
//! let check_variant: Void =
//!   when datum is { Unknown_S_1_0(..) -> Void; _ -> fail }
//! ```
//!
//! Nothing reads `check_variant`. [`super::drop_dead_pure_lets`] is right
//! to keep the node — the `when` FAILS when the tag matches no arm, so
//! removing it would drop a runtime check — and it refuses every `when`
//! value for the same reason. But the BINDING is fiction either way:
//! only the check happens, and the reader is left hunting a value
//! nothing uses. One V2 corpus script carried six of them.
//!
//! The `Seq` statement chain already exists for exactly this shape, so
//! the rewrite is `Let(name, value, rest)` → `value; rest`. The value
//! keeps its place and its effect; the invented name goes.
//!
//! The rule is the binding, not the assertion: an unread `when`/`if`
//! that computes a real value is unnamed too, and rightly — the program
//! discards it, and a name (with a guessed type annotation beside it)
//! only suggests otherwise.
//!
//! A discarded CALL is the same shape from the other direction. UPLC
//! binds strictly, so `let _ = f(a, b)` runs `f` — that is why the dead
//! let sweep has to keep it — but the result goes nowhere, and the name
//! it is kept under is invented. `let u_result = u(datum, redeemer,
//! script_context, s)` is one such: the entire body of an OpShin
//! validator, whose program is a single discarded call to a
//! looked-up function. `u(datum, redeemer, script_context, s)` on its
//! own line says exactly that, and says it in one line rather than two.
//!
//! Gated three ways. The binder must be unreferenced by BOTH id and
//! name — the AST allows an id-less `Var` resolved by name, so an
//! id-only scan would unname something still read. The value must be a
//! `when`/`if` or a call with a non-builtin head, all of which read as
//! statements; a scalar printed bare (`1 + 2`) reads like a mistake, a
//! pure scalar would already be gone, and a bare builtin call is a
//! decode whose result the reader would look for. And the validator
//! entry is never touched.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PVec;
use std::collections::HashMap;

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::{ExprFolder, ExprVisitor};
use crate::pseudo::var_id::VarId;

use super::drop_dead_pure_lets::contains_decompiled_marker;

pub(super) fn unname_discarded_check(expr: PseudoExpr) -> PseudoExpr {
    // Same gate as the dead-let sweeps: without the validator marker the
    // tree may be a fragment whose readers live outside it.
    if !contains_decompiled_marker(&expr) {
        return expr;
    }
    let (counts, name_counts) = count_var_uses(&expr);
    let mut folder = Unnamer {
        counts,
        name_counts,
    };
    folder.fold(expr)
}

/// Every `Var` occurrence, counted by id AND by name.
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

struct Unnamer {
    counts: HashMap<VarId, usize>,
    name_counts: HashMap<String, usize>,
}

impl ExprFolder for Unnamer {
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
        let unnameable = name != "decompiled"
            && (matches!(value, PseudoExpr::When { .. } | PseudoExpr::If { .. })
                || is_discarded_call(&value));
        if unnameable
            && let Some(vid) = id
            && self.counts.get(&vid).copied().unwrap_or(0) == 0
            && self.name_counts.get(&name).copied().unwrap_or(0) == 0
        {
            return PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::BuiltinCall {
                    name: crate::BuiltinId::Seq,
                    args: PVec::new(),
                }),
                args: vec![value, body].into(),
            };
        }
        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }
}

/// A call whose head is NOT a builtin: unknown code, run for whatever it
/// does rather than for the value it returns.
///
/// Builtin-headed calls are left named. `un_list_data(field_1)` is a
/// decode, and a reader who meets it bare on a line looks for where its
/// result went; the same reader meeting `check_signatures(tx)` reads a
/// statement and moves on. The dead-let sweep keeps both for the same
/// reason — either can fail — so this is a rendering choice, not a
/// second effect judgement.
fn is_discarded_call(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Apply { function, .. } = expr else {
        return false;
    };
    !head_is_builtin(function)
}

fn head_is_builtin(function: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![function];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::BuiltinCall { .. } => return true,
            PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Apply { function, .. } => pending.push(function),
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests;
