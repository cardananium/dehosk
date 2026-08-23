//! Rename synthetic `field_N(_M)?` let binders to the actual
//! Cardano-context field name when the let value is a field access on
//! `script_context`.
//!
//! The `field_N(_M)?` shape is minted for synthetic field aliases at
//! MIR lowering time, so overwriting it loses nothing. Scope:
//! - Binder name must be `field_<digits>` or `field_<digits>_<digits>`.
//! - Let value must be `FieldAccess { record: Var(name="script_context"),
//!   selector: name }` with `name` one of `tx_info` / `redeemer` /
//!   `script_info`.
//! - If the target name is already bound in scope at the let site, skip
//!   rather than shadow it.
//! - Only the binder and the references to its VarId inside the let body
//!   are renamed; the binder is not in scope above the let.

use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

pub(super) fn rename_synthetic_field_let_binders(expr: PseudoExpr) -> PseudoExpr {
    RenameWalker {
        scope: Vec::new(),
        active_renames: HashMap::new(),
        pending: Vec::new(),
    }
    .fold(expr)
}

/// The between-children work — deciding, at a `Let`, whether to rename its
/// binder — reads the already-folded `value`, exactly `enter_let`'s
/// contract. The rename itself (retargeting every `Var` referencing the
/// binder inside the body) is applied lazily by `post_var`, consulting a
/// `VarId -> name` map pushed for the extent of the body's fold and popped
/// after, rather than the eager whole-subtree `rename_var_in` pass the
/// recursive original ran before descending into the body. Since that
/// substitution only ever rewrites `Var` nodes matched by (unique) id,
/// doing it during the fold instead of before it changes nothing it
/// produces — it only changes when a given `Var` node gets rewritten
/// relative to unrelated tree nodes, never what it's rewritten to.
struct RenameWalker {
    /// Names already bound at the current point in the walk — checked so a
    /// rename never shadows an outer binding.
    scope: Vec<String>,
    /// `VarId` of a binder renamed at an enclosing `Let`, mapped to its new
    /// display name; an entry is present for exactly the extent of that
    /// `Let`'s body fold.
    active_renames: HashMap<VarId, String>,
    /// Per-`Let` (LIFO, mirrors the fold's own nesting): `Some(id)` when
    /// that `Let` registered a rename, so `exit_let` knows what to remove
    /// from `active_renames`; `None` otherwise.
    pending: Vec<Option<VarId>>,
}

impl ExprFolder for RenameWalker {
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }

    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        for p in params {
            self.scope.push(p.as_str().to_string());
        }
        params.to_vec()
    }

    fn exit_lambda(&mut self, params: &[Binder]) {
        for _ in params {
            self.scope.pop();
        }
    }

    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        self.scope.push(name.as_str().to_string());
        for p in params {
            self.scope.push(p.as_str().to_string());
        }
        (name.clone(), params.to_vec())
    }

    fn exit_recfn(&mut self, _name: &Binder, params: &[Binder]) {
        for _ in params {
            self.scope.pop();
        }
        self.scope.pop();
    }

    fn enter_let(&mut self, name: &str, id: &Option<VarId>, value: &PseudoExpr) -> String {
        // Detect the rename opportunity at THIS let — `value` here is
        // already folded.
        let new_name = if let Some(binder_id) = *id
            && is_synthetic_field_name(name)
            && let Some(target_name) = detect_context_field_target(value)
            && !self.scope.iter().any(|n| n == target_name)
        {
            Some((binder_id, target_name.to_string()))
        } else {
            None
        };

        let pushed = match new_name {
            Some((binder_id, target)) => {
                self.active_renames.insert(binder_id, target.clone());
                self.pending.push(Some(binder_id));
                target
            }
            None => {
                self.pending.push(None);
                name.to_string()
            }
        };
        self.scope.push(pushed.clone());
        pushed
    }

    fn exit_let(&mut self, _name: &str) {
        self.scope.pop();
        if let Some(binder_id) = self.pending.pop().flatten() {
            self.active_renames.remove(&binder_id);
        }
    }

    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        if let Some(vid) = id
            && let Some(new_name) = self.active_renames.get(&vid)
        {
            return PseudoExpr::Var {
                name: new_name.clone(),
                id,
            };
        }
        PseudoExpr::Var { name, id }
    }
}

/// Match `field_<digits>` or `field_<digits>_<digits>`.
pub(super) fn is_synthetic_field_name(name: &str) -> bool {
    let Some(rest) = name.strip_prefix("field_") else {
        return false;
    };
    if rest.is_empty() {
        return false;
    }
    // Either all digits, or digits + `_` + digits.
    let mut parts = rest.split('_');
    let Some(first) = parts.next() else {
        return false;
    };
    if first.is_empty() || !first.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }
    if let Some(second) = parts.next() {
        if second.is_empty() || !second.chars().all(|c| c.is_ascii_digit()) {
            return false;
        }
    }
    parts.next().is_none()
}

/// If `value` is a `FieldAccess { record: Var(name="script_context"),
/// selector: NamedField/ContextField(target) }` and target is a known
/// V3 ScriptContext field, returns the field name.
fn detect_context_field_target(value: &PseudoExpr) -> Option<&'static str> {
    let PseudoExpr::FieldAccess { record, selector } = value else {
        return None;
    };
    let PseudoExpr::Var { name, .. } = record.as_ref() else {
        return None;
    };
    if name != "script_context" {
        return None;
    }
    match selector {
        FieldSelector::NamedField(field) | FieldSelector::ContextField(field) => {
            match field.as_str() {
                "tx_info" => Some("tx_info"),
                "redeemer" => Some("redeemer"),
                "script_info" => Some("script_info"),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Rewrite every `Var { id: Some(target_id),.. }` in `expr` to `new_name`. `pub(super)`
/// so sibling render-prep passes (e.g. `fold_const_recfn_alias`) can reuse the
/// VarId-keyed rewire.
pub(super) fn rename_var_in(expr: PseudoExpr, target_id: VarId, new_name: &str) -> PseudoExpr {
    struct VarRenamer<'a> {
        target_id: VarId,
        new_name: &'a str,
    }

    impl ExprFolder for VarRenamer<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            if id == Some(self.target_id) {
                PseudoExpr::Var {
                    name: self.new_name.to_string(),
                    id,
                }
            } else {
                PseudoExpr::Var { name, id }
            }
        }
    }

    VarRenamer {
        target_id,
        new_name,
    }
    .fold(expr)
}

#[cfg(test)]
mod tests;
