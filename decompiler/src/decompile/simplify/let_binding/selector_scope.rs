use super::Simplifier;
use crate::decompile::simplify::state::SelectorBinding;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;

/// `(selector_lambda_entry, tracked_non_thunk, already_tracked_non_thunk)`.
/// `selector_lambda_entry` is `Some((signature, prior_binding))` when the
/// bound value is a selector lambda; the signature is `(param_count,
/// selected_index)` and `prior_binding` is the `selector_vars` entry it
/// displaced, restored on scope exit.
pub(crate) type SelectorScopeTrackResult = (
    Option<((usize, usize), Option<SelectorBinding>)>,
    bool,
    bool,
);

impl Simplifier {
    pub(super) fn track_selector_scope_binding(
        &mut self,
        name: &str,
        var_id: Option<VarId>,
        simplified_value: &PseudoExpr,
    ) -> SelectorScopeTrackResult {
        let selector_entry = self.track_selector_lambda_binding(name, var_id, simplified_value);

        // Track locally-scoped non-thunk bindings so force(var) can be removed safely.
        let track_non_thunk = !self.safe_mode && Self::is_non_thunk_value(simplified_value);
        let already_tracked_non_thunk = if track_non_thunk {
            self.selectors
                .non_thunk_vars
                .insert_binding(name.to_string(), var_id)
        } else {
            false
        };

        (selector_entry, track_non_thunk, already_tracked_non_thunk)
    }

    pub(super) fn restore_selector_scope_binding(
        &mut self,
        var_id: Option<VarId>,
        selector_entry: Option<((usize, usize), Option<SelectorBinding>)>,
        track_non_thunk: bool,
        already_tracked_non_thunk: bool,
    ) {
        if track_non_thunk
            && !already_tracked_non_thunk
            && let Some(vid) = var_id
        {
            self.selectors.non_thunk_vars.remove(vid);
        }

        if let Some((sig, prev)) = selector_entry {
            match prev {
                Some(old_binding) => {
                    self.selectors.selector_vars.insert(sig, old_binding);
                }
                None => {
                    self.selectors.selector_vars.remove(&sig);
                }
            }
        }
    }

    fn track_selector_lambda_binding(
        &mut self,
        name: &str,
        var_id: Option<VarId>,
        simplified_value: &PseudoExpr,
    ) -> Option<((usize, usize), Option<SelectorBinding>)> {
        // Track selector lambdas for CSE: fn(params) { param_i } -> record (len, i) -> name.
        // Look through Delay wrappers since UPLC often wraps lambdas in delay().
        let mut inner = simplified_value;
        while let PseudoExpr::Delay(d) = inner {
            inner = d;
        }

        let PseudoExpr::Lambda { params, body } = inner else {
            return None;
        };

        let sig = Self::selector_signature(params, body)?;
        var_id.map(|id| {
            let prev = self
                .selectors
                .selector_vars
                .insert(sig, SelectorBinding::new(name.to_string(), Some(id)));
            (sig, prev)
        })
    }
}
