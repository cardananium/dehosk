use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::helper::hoist::var_is_referenced_id_aware;

/// Flatten nested let chains for readability.
///
/// Transforms:
/// ```text
/// let x = (let y = use_z in use_y) in
/// use_x
/// ```
/// Into (when safe):
/// ```text
/// let z = very_deep
/// let y = use_z
/// let x = use_y
/// use_x
/// ```
///
/// Safe only when the inner binder is not referenced in the outer
/// body, the outer binder appears in neither the inner value nor the
/// inner body, and the inner value is not a `Lambda`/`RecFn`.
pub(crate) fn flatten_let_chains(expr: PseudoExpr) -> PseudoExpr {
    let mut folder = LetFlattener;
    folder.fold(expr)
}

struct LetFlattener;

impl ExprFolder for LetFlattener {
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
        let outer_id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
        let should_hoist = if let PseudoExpr::Let {
            name: ref inner_name,
            id: Some(inner_id),
            value: ref inner_value,
            body: ref inner_body,
            ..
        } = value
        {
            // Hoisting only preserves scope ownership if the moved inner binder is
            // not referenced outside its current body and the outer binder does
            // not leak into the inner subtree being lifted above it.
            let inner_id_concrete = inner_id;
            let inner_not_in_outer =
                !var_is_referenced_id_aware(&body, inner_id_concrete, inner_name);
            let no_circular = !var_is_referenced_id_aware(inner_value, outer_id, &name);
            let inner_body_not_outer_self_ref =
                !var_is_referenced_id_aware(inner_body, outer_id, &name);
            let inner_is_func = matches!(
                inner_value.as_ref(),
                PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. }
            );
            inner_not_in_outer && no_circular && inner_body_not_outer_self_ref && !inner_is_func
        } else {
            false
        };

        if should_hoist
            && let PseudoExpr::Let {
                name: inner_name,
                id: Some(inner_id),
                value: inner_value,
                body: inner_body,
            } = value
        {
            return PseudoExpr::Let {
                name: inner_name,
                id: Some(inner_id),
                value: inner_value,
                body: PBox::new(PseudoExpr::Let {
                    name,
                    id,
                    value: inner_body,
                    body: PBox::new(body),
                }),
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

#[cfg(test)]
mod tests;
