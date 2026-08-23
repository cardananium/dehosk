use crate::pseudo::ast::PseudoExpr;
#[cfg(test)]
use crate::pseudo::var_id::VarId;
use crate::pseudo::walker::Walker;

mod capture;
mod force_var;
mod projections;
mod root;

use capture::expr_binds_name;
use root::normalize_cancel_root;

#[cfg(not(test))]
use force_var::{count_var_usages, strip_force_on_var};

#[cfg(test)]
pub(super) fn count_var_usages(
    expr: &PseudoExpr,
    name: &str,
    target_id: Option<VarId>,
) -> (usize, usize) {
    force_var::count_var_usages(expr, name, target_id)
}

#[cfg(test)]
pub(super) fn strip_force_on_var(
    expr: PseudoExpr,
    name: &str,
    target_id: Option<VarId>,
) -> PseudoExpr {
    force_var::strip_force_on_var(expr, name, target_id)
}

/// Cancel force/delay through let bindings: when `let x = delay(body)`
/// and every use of `x` is `force(x)`, rewrite to `let x = body` with
/// `force(x)` -> `x`. Avoids duplicating `body` at each force site.
pub(crate) fn cancel_force_delay_vars(expr: PseudoExpr) -> PseudoExpr {
    struct CancelForceDelayFolder;

    impl Walker for CancelForceDelayFolder {
        fn post_expr(&mut self, expr: PseudoExpr) -> PseudoExpr {
            normalize_cancel_root(expr)
        }
    }

    CancelForceDelayFolder.fold(expr)
}
