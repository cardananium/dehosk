use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;

mod count;
mod shadowing;
mod strip;

pub(super) fn count_var_usages(
    expr: &PseudoExpr,
    name: &str,
    target_id: Option<VarId>,
) -> (usize, usize) {
    count::count_var_usages(expr, name, target_id)
}

pub(super) fn strip_force_on_var(
    expr: PseudoExpr,
    name: &str,
    target_id: Option<VarId>,
) -> PseudoExpr {
    strip::strip_force_on_var(expr, name, target_id)
}
