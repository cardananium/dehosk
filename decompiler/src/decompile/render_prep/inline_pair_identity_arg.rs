//! Inline `pair_val.<slot>(arg)` to `arg` when the pair's `<slot>`
//! component is an identity lambda.
//!
//! V1 output binds a pair-pack with identity at one component, so
//! `pair_val.snd(arg)` is `(fn(x){x})(arg) = arg`. The let stays —
//! the pair value may be consumed elsewhere via `.fst`.
//!
//! Recognised pair shapes: an inline church-pair-pack
//! `Lambda { [x], Apply { Var(x), [a, b] } }` (id-verified); a
//! hoisted helper call `Apply { Var("pair_pack"), [a, b] }`,
//! matched on the name `hoist_church_pair_pack` emits; and a native
//! `PseudoExpr::Pair(a, b)` after `--decode-church-to-native`. If
//! `a` is an identity-lambda the slot is `PairFst`; if `b` is, the
//! slot is `PairSnd`. Both can fire independently.
//!
//! Replace a 1-arg apply of `FieldAccess { record: Var(binder_id),
//! selector: <slot> }` with just `arg`. `pair_val.snd(a, b)` and a
//! bare `f(pair_val.snd)` are left alone.
//!
//! Strict id-equality on the identity-lambda body (`p.id == body.id`)
//! and on the use site (`record.id == binder_id`), so a coincidental
//! `Lambda { [x], Var(y) }` cannot misfire. The let-binding itself
//! is preserved — other readers (via the non-identity slot, or as a
//! bare reference) keep working.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

pub(super) fn inline_pair_identity_arg(expr: PseudoExpr) -> PseudoExpr {
    rewrite(expr)
}

// `rewrite`'s Let case has a between-children dependency: `classify_pair_let_value`
// must run on the ALREADY-rewritten value (so a nested let inside the value is
// resolved first), and its result must be visible while the body — including
// any lets nested inside it — is rewritten, since `rewrite_body`'s original
// recursion swept the pattern through that entire subtree regardless of
// further let nesting. `ExprFolder`'s `enter_let`/`exit_let` hooks fire at
// exactly that boundary (after the value is folded, before the body is), so
// pushing/popping the binder's slots there — and checking the active set from
// `post_apply`, itself called bottom-up after children are folded — matches
// the original order: a binder becomes visible only once its value is fully
// classified, stays visible through the rest of its lexical scope (nested
// lets included), and each `Apply` is checked only once its own children are
// already resolved (which cannot change whether a `FieldAccess { Var, _ }`
// callee matches, since this pass never rewrites that shape itself).
fn rewrite(expr: PseudoExpr) -> PseudoExpr {
    ScopedPairIdentityRewriter::default().fold(expr)
}

/// `ExprFolder` for `rewrite`: tracks, in `active`, every enclosing
/// let-bound pair whose identity slot(s) are known, pushing on `enter_let`
/// (once the bound value is classified) and popping on `exit_let`.
#[derive(Default)]
struct ScopedPairIdentityRewriter {
    active: HashMap<VarId, IdentitySlots>,
    pushed: Vec<Option<VarId>>,
}

impl ExprFolder for ScopedPairIdentityRewriter {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn enter_let(&mut self, name: &str, id: &Option<VarId>, value: &PseudoExpr) -> String {
        match (id, classify_pair_let_value(value)) {
            (Some(binder_id), Some(slots)) => {
                self.active.insert(*binder_id, slots);
                self.pushed.push(Some(*binder_id));
            }
            _ => self.pushed.push(None),
        }
        name.to_string()
    }

    fn exit_let(&mut self, _name: &str) {
        if let Some(Some(binder_id)) = self.pushed.pop() {
            self.active.remove(&binder_id);
        }
    }

    fn post_apply(&mut self, function: PseudoExpr, mut args: Vec<PseudoExpr>) -> PseudoExpr {
        if args.len() == 1 && matches_active_slot(&function, &self.active) {
            return args.remove(0);
        }
        PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        }
    }
}

/// Which pair slots are identity in this value. Either or both may be set.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct IdentitySlots {
    pub fst: bool,
    pub snd: bool,
}

impl IdentitySlots {
    pub(crate) fn any(&self) -> bool {
        self.fst || self.snd
    }
}

/// Stage A classifier: return identity slots of the pair-shape `value`.
pub(crate) fn classify_pair_let_value(value: &PseudoExpr) -> Option<IdentitySlots> {
    let (a, b) = peek_pair_components(value)?;
    let slots = IdentitySlots {
        fst: is_identity_lambda(a),
        snd: is_identity_lambda(b),
    };
    if slots.any() { Some(slots) } else { None }
}

/// Peek the two pair components for the three recognised shapes.
fn peek_pair_components(value: &PseudoExpr) -> Option<(&PseudoExpr, &PseudoExpr)> {
    // Shape 3: native `Pair(a, b)`.
    if let PseudoExpr::Pair(a, b) = value {
        return Some((a, b));
    }
    // Shape 1: inline church-pair-pack `Lambda { [x], Apply { Var(x), [a, b] } }`.
    if let PseudoExpr::Lambda { params, body } = value
        && params.len() == 1
        && let PseudoExpr::Apply { function, args } = body.as_ref()
        && let PseudoExpr::Var {
            id: Some(fn_id), ..
        } = function.as_ref()
        && *fn_id == params[0].id
        && args.len() == 2
    {
        return Some((&args[0], &args[1]));
    }
    // Shape 2: hoisted `pair_pack(a, b)` call, matched by name
    // — `hoist_church_pair_pack` emits that literal string.
    if let PseudoExpr::Apply { function, args } = value
        && let PseudoExpr::Var { name, .. } = function.as_ref()
        && name == "pair_pack"
        && args.len() == 2
    {
        return Some((&args[0], &args[1]));
    }
    None
}

/// Strict identity-lambda recognizer: `Lambda { [p], Var(p) }` with the
/// inner Var's id matching the param's id.
fn is_identity_lambda(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let PseudoExpr::Var { id: Some(vid), .. } = body.as_ref() else {
        return false;
    };
    *vid == params[0].id
}

/// Shared collapse check for both rewriters above: does `function` select an
/// identity slot off a binder that is currently active?
fn matches_active_slot(function: &PseudoExpr, active: &HashMap<VarId, IdentitySlots>) -> bool {
    let PseudoExpr::FieldAccess { record, selector } = function else {
        return false;
    };
    let PseudoExpr::Var { id: Some(vid), .. } = record.as_ref() else {
        return false;
    };
    active
        .get(vid)
        .is_some_and(|slots| slot_matches(selector, *slots))
}

fn slot_matches(selector: &FieldSelector, slots: IdentitySlots) -> bool {
    match selector {
        FieldSelector::PairFst => slots.fst,
        FieldSelector::PairSnd => slots.snd,
        _ => false,
    }
}

#[cfg(test)]
mod tests;
