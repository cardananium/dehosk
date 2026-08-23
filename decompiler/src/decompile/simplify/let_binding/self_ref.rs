use super::Simplifier;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};
use crate::pseudo::walker::{FoldAction, Walker};

impl Simplifier {
    /// `let` binders scope over the body, not over their value. The walker
    /// registers the current binding before folding the value so body
    /// simplification can share the same state; undo any accidental
    /// value-side capture of the current VarId before downstream naming or
    /// alias tracking sees it.
    pub(super) fn restore_let_value_self_refs(
        &self,
        value: PseudoExpr,
        name: &str,
        current_id: Option<VarId>,
        shadow: &super::super::state::LexicalNameShadow,
    ) -> PseudoExpr {
        let Some(current_id) = current_id else {
            return value;
        };

        let replacement_id = shadow
            .var_id
            .unwrap_or_else(VarId::fresh_compat_placeholder);
        let replacement_name = shadow
            .var_id
            .and_then(|outer_id| self.naming.renames.get(outer_id).cloned())
            .unwrap_or_else(|| name.to_string());

        LetValueSelfRefRestorer {
            current_id,
            replacement_name,
            replacement_id,
            blocked_depth: 0,
            let_block_stack: Vec::new(),
        }
        .fold(value)
    }
}

struct LetValueSelfRefRestorer {
    current_id: VarId,
    replacement_name: String,
    replacement_id: VarId,
    blocked_depth: usize,
    let_block_stack: Vec<bool>,
}

impl Walker for LetValueSelfRefRestorer {
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        if self.blocked_depth > 0 {
            return FoldAction::Replace(expr.clone());
        }

        FoldAction::Walk
    }

    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        if id.get() == Some(self.current_id) {
            return PseudoExpr::Var {
                name: self.replacement_name.clone(),
                id: Some(self.replacement_id),
            };
        }

        PseudoExpr::Var { name, id }
    }

    fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
        if params.iter().any(|param| param.var_id() == self.current_id) {
            self.blocked_depth += 1;
        }
        params.to_vec()
    }

    fn exit_lambda(&mut self, params: &[Binder]) {
        if params.iter().any(|param| param.var_id() == self.current_id) {
            self.blocked_depth -= 1;
        }
    }

    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        if name.var_id() == self.current_id
            || params.iter().any(|param| param.var_id() == self.current_id)
        {
            self.blocked_depth += 1;
        }
        (name.clone(), params.to_vec())
    }

    fn exit_recfn(&mut self, name: &Binder, params: &[Binder]) {
        if name.var_id() == self.current_id
            || params.iter().any(|param| param.var_id() == self.current_id)
        {
            self.blocked_depth -= 1;
        }
    }

    fn enter_let(&mut self, name: &str, id: &Option<VarId>, _value: &PseudoExpr) -> String {
        let blocks = id.get() == Some(self.current_id);
        if blocks {
            self.blocked_depth += 1;
        }
        self.let_block_stack.push(blocks);
        name.to_string()
    }

    fn exit_let(&mut self, _name: &str) {
        if self.let_block_stack.pop().unwrap_or(false) {
            self.blocked_depth -= 1;
        }
    }
}
