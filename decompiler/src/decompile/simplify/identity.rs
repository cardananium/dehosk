use std::collections::HashMap;

use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr};
use crate::pseudo::var_id::VarId;

use super::{
    BuiltinId, Simplifier,
    state::{BindingVarMap, BindingVarSet},
};

impl Simplifier {
    pub(crate) fn binding_id(&self, name: &str, id: Option<VarId>) -> Option<VarId> {
        id.or_else(|| self.naming.name_to_id.get(name).copied())
    }

    pub(crate) fn fresh_synthetic_binding_id(&mut self) -> VarId {
        let id = VarId::from_raw(self.identity.next_synthetic_var_id);
        self.identity.next_synthetic_var_id = self.identity.next_synthetic_var_id.saturating_add(1);
        id
    }

    pub(crate) fn fresh_synthetic_binder(&mut self, name: &str) -> Binder {
        Binder::new(name, self.fresh_synthetic_binding_id())
    }

    pub(crate) fn make_var_for_binder(&self, binder: &Binder) -> PseudoExpr {
        PseudoExpr::var_with_id(binder.name.clone(), binder.id)
    }

    pub(crate) fn make_let_for_binder(
        &self,
        binder: Binder,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        PseudoExpr::let_bind_with_id(binder.name, binder.id, value, body)
    }

    pub(crate) fn bind_name_in_body(
        &mut self,
        name: &str,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let binding_id = Self::existing_binding_ref_id(&body, name)
            .unwrap_or_else(|| self.fresh_synthetic_binding_id());
        let bindings = HashMap::from([(name, binding_id)]);
        let body = Self::annotate_binding_refs(body, &bindings, &mut Vec::new());
        PseudoExpr::let_bind_with_id(name.to_string(), binding_id, value, body)
    }

    pub(crate) fn is_binder_used(expr: &PseudoExpr, binder: &Binder) -> bool {
        binder != "_" && Self::is_var_used_by_id(expr, binder.as_str(), binder.id.get())
    }

    pub(crate) fn bind_binder_in_body(
        &mut self,
        binder: &Binder,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let body = Self::substitute_var_for_var(
            &body,
            binder.as_str(),
            binder.id.get(),
            binder.as_str(),
            binder.id,
        );
        PseudoExpr::let_bind_with_id(binder.name.clone(), binder.id, value, body)
    }

    /// Get renamed name using stable binding identity when available.
    pub(crate) fn get_renamed_with_id(&self, name: &str, id: Option<VarId>) -> String {
        if let Some(renamed) = self
            .binding_id(name, id)
            .and_then(|vid| self.naming.renames.get(vid))
        {
            return renamed.clone();
        }
        name.to_string()
    }

    pub(crate) fn tracked_var<T: Clone>(
        &self,
        map: &BindingVarMap<T>,
        name: &str,
        id: Option<VarId>,
    ) -> Option<T> {
        self.binding_id(name, id)
            .and_then(|vid| map.get(vid).cloned())
    }

    pub(crate) fn tracked_binding(
        &self,
        set: &BindingVarSet,
        name: &str,
        id: Option<VarId>,
    ) -> bool {
        self.binding_id(name, id)
            .is_some_and(|vid| set.contains(vid))
    }

    /// Check if a variable is an AND function.
    pub(crate) fn is_and_var(&self, name: &str, id: Option<VarId>) -> bool {
        self.binding_id(name, id)
            .is_some_and(|vid| self.booleans.and_vars.contains(vid))
    }

    /// Check if a variable is an OR function.
    pub(crate) fn is_or_var(&self, name: &str, id: Option<VarId>) -> bool {
        self.binding_id(name, id)
            .is_some_and(|vid| self.booleans.or_vars.contains(vid))
    }

    pub(crate) fn builtin_alias_for_var(&self, name: &str, id: Option<VarId>) -> Option<BuiltinId> {
        self.binding_id(name, id)
            .and_then(|vid| self.naming.builtin_aliases.get(vid).copied())
    }

    /// Create a Var with VarId looked up from name_to_id registry.
    /// This preserves variable identity and prevents naming collisions.
    pub(crate) fn make_var(&self, name: &str) -> PseudoExpr {
        let id = self.binding_id(name, None);
        let renamed = self.get_renamed_with_id(name, id);
        match id {
            Some(id) => PseudoExpr::var_with_id(renamed, id),
            None => PseudoExpr::compat_var(renamed),
        }
    }
    /// Check if value is a simple builtin (no args).
    pub(crate) fn get_simple_builtin(value: &PseudoExpr) -> Option<BuiltinId> {
        if let PseudoExpr::BuiltinCall { name, args } = value
            && args.is_empty()
        {
            return Some(*name);
        }
        None
    }

    /// Check if value is a partial application like Int.eq(1).
    pub(crate) fn get_partial_app(value: &PseudoExpr) -> Option<(BinaryOp, PseudoExpr, bool)> {
        if let PseudoExpr::Lambda { params, body } = value
            && params.len() == 1
            && params[0] == "x"
            && let PseudoExpr::BinOp { op, left, right } = body.as_ref()
            && let PseudoExpr::Var { name, .. } = left.as_ref()
            && name == "x"
        {
            return Some((*op, (**right).clone(), false));
        }
        None
    }
}
