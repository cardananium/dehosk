use super::Simplifier;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

impl Simplifier {
    pub(crate) fn call_result_callee_for_binding_name(
        name: &str,
        value: &PseudoExpr,
    ) -> Option<VarId> {
        // Accept the disambiguated form `<callee>_result_<N>`: a bare
        // strip_suffix("_result") fails on `lookup_result_2`.
        let trimmed = Self::strip_disambiguation_suffix_str(name);
        let stem = trimmed.strip_suffix("_result")?;
        if stem.is_empty() {
            return None;
        }
        let PseudoExpr::Apply { function, args } = value else {
            return None;
        };
        if args.is_empty() {
            return None;
        }
        let PseudoExpr::Var {
            name: callee_name,
            id: Some(callee_id),
        } = function.as_ref()
        else {
            return None;
        };
        if callee_name.starts_with("expect!") || Self::is_bare_generic_fn_name(callee_name) {
            return None;
        }
        if Self::sanitize_name_stem(stem) != Self::sanitize_name_stem(callee_name) {
            return None;
        }
        Some(*callee_id)
    }

    /// Strip a trailing `_<digits>` suffix. Used to peel off the
    /// `assign_names::fresh_name` disambiguation when matching the
    /// `_result` pattern.
    fn strip_disambiguation_suffix_str(name: &str) -> &str {
        if let Some(idx) = name.rfind('_') {
            let suffix = &name[idx + 1..];
            if !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()) {
                return &name[..idx];
            }
        }
        name
    }

    pub(super) fn record_call_result_kind_annotation(
        &mut self,
        name: &str,
        var_id: Option<VarId>,
        value: &PseudoExpr,
    ) {
        let Some(vid) = var_id else {
            return;
        };
        if let Some(callee) =
            Self::call_result_callee_for_binding_name(name, value).and_then(|id| id.get())
        {
            self.var_kinds
                .kind_annotations
                .insert(vid, VarKind::CallResult { callee });
        }
    }
}
