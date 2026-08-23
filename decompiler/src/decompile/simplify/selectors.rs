use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::var_id::OptionVarIdGet;

use super::{Simplifier, state::SelectorBinding};

impl Simplifier {
    /// Check if expression is a "fst" selector: fn(x, _) { x }
    pub(crate) fn is_fst_selector(expr: &PseudoExpr) -> bool {
        if let PseudoExpr::Lambda { params, body } = expr
            && params.len() == 2
            && Self::root_var_matches_binder(body, &params[0])
            && (params[1] == "_"
                || !Self::is_var_used_by_id(body, params[1].as_str(), params[1].id.get()))
        {
            return true;
        }
        false
    }

    /// Check if a lambda is a pure selector: fn(params) { param_i }.
    /// Returns (param_count, selected_index) if it is.
    pub(crate) fn selector_signature(
        params: &[Binder],
        body: &PseudoExpr,
    ) -> Option<(usize, usize)> {
        if let PseudoExpr::Var { name, id } = body {
            for (i, p) in params.iter().enumerate() {
                let matches_param =
                    crate::decompile::var_match::ref_matches_binder(name, id.get(), p);
                if matches_param && p != "_" {
                    return Some((params.len(), i));
                }
            }
        }
        None
    }

    pub(crate) fn selector_binding_var(&self, selector: &SelectorBinding) -> Option<PseudoExpr> {
        let id = selector.id?;
        let name = self.get_renamed_with_id(&selector.name, Some(id));
        Some(PseudoExpr::var_with_id(name, id))
    }

    pub(crate) fn selector_binding_matches_ref(
        &self,
        selector: &SelectorBinding,
        name: &str,
        id: Option<crate::pseudo::var_id::VarId>,
    ) -> bool {
        selector.matches_resolved_ref(name, self.binding_id(name, id))
    }

    fn root_var_matches_binder(expr: &PseudoExpr, binder: &Binder) -> bool {
        match expr {
            PseudoExpr::Var { name, id } => Self::binder_matches_var_id(binder, name, id.get()),
            _ => false,
        }
    }

    /// Check if expression is a "snd" selector: fn(_, x) { x }
    pub(crate) fn is_snd_selector(expr: &PseudoExpr) -> bool {
        if let PseudoExpr::Lambda { params, body } = expr
            && params.len() == 2
            && Self::root_var_matches_binder(body, &params[1])
            && (params[0] == "_"
                || !Self::is_var_used_by_id(body, params[0].as_str(), params[0].id.get()))
        {
            return true;
        }
        false
    }

    /// Fst selector under ≥2 `Delay`s; returns the count.
    pub(crate) fn is_delayed_fst_selector(expr: &PseudoExpr) -> Option<u8> {
        let mut count = 0u8;
        let mut current = expr;

        while let PseudoExpr::Delay(inner) = current {
            count += 1;
            current = inner;
        }

        if count >= 2 && Self::is_fst_selector(current) {
            Some(count)
        } else {
            None
        }
    }

    /// Snd selector under ≥2 `Delay`s; returns the count.
    pub(crate) fn is_delayed_snd_selector(expr: &PseudoExpr) -> Option<u8> {
        let mut count = 0u8;
        let mut current = expr;

        while let PseudoExpr::Delay(inner) = current {
            count += 1;
            current = inner;
        }

        if count >= 2 && Self::is_snd_selector(current) {
            Some(count)
        } else {
            None
        }
    }

    /// Check if expression is exactly single-delay fst selector.
    pub(crate) fn is_single_delayed_fst_selector(expr: &PseudoExpr) -> bool {
        if let PseudoExpr::Delay(inner) = expr {
            return Self::is_fst_selector(inner);
        }
        false
    }

    /// Check if expression is exactly single-delay snd selector.
    pub(crate) fn is_single_delayed_snd_selector(expr: &PseudoExpr) -> bool {
        if let PseudoExpr::Delay(inner) = expr {
            return Self::is_snd_selector(inner);
        }
        false
    }

    /// Check if expression is a known fst selector: either inline (delay-wrapped or bare)
    /// or a variable tracked as a fst selector.
    pub(crate) fn is_known_fst_selector(&self, expr: &PseudoExpr) -> bool {
        if Self::is_fst_selector(expr) {
            return true;
        }
        if Self::is_single_delayed_fst_selector(expr) {
            return true;
        }
        if Self::is_delayed_fst_selector(expr).is_some() {
            return true;
        }
        if let PseudoExpr::Var { name, id, .. } = expr
            && (self.tracked_binding(&self.selectors.single_delayed_fst_params, name, id.get())
                || self.tracked_binding(&self.selectors.delayed_fst_selectors, name, id.get()))
        {
            return true;
        }
        false
    }

    /// Check if expression is a known snd selector: either inline (delay-wrapped or bare)
    /// or a variable tracked as a snd selector.
    pub(crate) fn is_known_snd_selector(&self, expr: &PseudoExpr) -> bool {
        if Self::is_snd_selector(expr) {
            return true;
        }
        if Self::is_single_delayed_snd_selector(expr) {
            return true;
        }
        if Self::is_delayed_snd_selector(expr).is_some() {
            return true;
        }
        if let PseudoExpr::Var { name, id, .. } = expr
            && (self.tracked_binding(&self.selectors.single_delayed_snd_params, name, id.get())
                || self.tracked_binding(&self.selectors.delayed_snd_selectors, name, id.get()))
        {
            return true;
        }
        false
    }
}
