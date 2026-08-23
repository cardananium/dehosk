//! Inline pass for single-use let bindings.
//!
//! Round-trips through the nameless inliner.

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;
use std::collections::HashSet;

/// Test-only: production inlines through `inline_single_use_preserving`,
/// which additionally honours the preserved-helper set.
/// Inline single-use let bindings.
#[cfg(test)]
pub(crate) fn inline_single_use(expr: PseudoExpr) -> PseudoExpr {
    inline_single_use_preserving(expr, &HashSet::new())
}

/// Variant of [`inline_single_use`] that refuses to inline let bindings
/// whose `VarId` is listed in `preserved`.
///
/// From [`super::preserved_helper_ids`]: user-declared helpers
/// identified via their MIR-recorded [`FnSignature`].
///
/// [`FnSignature`]: crate::decompile::mid::type_env::FnSignature
pub(crate) fn inline_single_use_preserving(
    expr: PseudoExpr,
    preserved: &HashSet<VarId>,
) -> PseudoExpr {
    let (nameless, table) = crate::pseudo::nameless::convert::pseudo_to_nameless(&expr);
    // The table-aware entry point is the one that can refuse alias
    // capture — rendering hygiene under name shadows.
    let inlined =
        crate::decompile::inline::nameless::inline_single_use_nameless_preserving_with_table(
            nameless, preserved, &table,
        );
    crate::pseudo::nameless::convert::nameless_to_pseudo(&inlined, &table)
}

#[cfg(test)]
mod tests;

pub mod nameless;
