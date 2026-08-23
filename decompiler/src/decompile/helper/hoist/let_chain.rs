use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::var_id::VarId;

use super::BindingTarget;

pub(crate) struct LiftedLet {
    pub(crate) name: String,
    pub(crate) id: Option<VarId>,
    pub(crate) value: PseudoExpr,
}

pub(crate) fn wrap_lifted_lets(lifted: Vec<LiftedLet>, body: PseudoExpr) -> PseudoExpr {
    lifted
        .into_iter()
        .rev()
        .fold(body, |body, binding| PseudoExpr::Let {
            name: binding.name,
            id: binding.id,
            value: PBox::new(binding.value),
            body: PBox::new(body),
        })
}

pub(crate) fn peel_leading_lets<F>(
    mut expr: PseudoExpr,
    mut should_lift: F,
) -> (Vec<LiftedLet>, PseudoExpr)
where
    F: FnMut(&LiftedLet, &[BindingTarget]) -> bool,
{
    let mut lifted = Vec::new();
    let mut kept = Vec::new();
    let mut kept_targets = Vec::new();
    loop {
        match expr {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                let binding = LiftedLet {
                    name,
                    id,
                    value: value.into_inner(),
                };
                if should_lift(&binding, kept_targets.as_slice()) {
                    lifted.push(binding);
                } else {
                    kept_targets.push(BindingTarget::from(&binding));
                    kept.push(binding);
                }
                expr = body.into_inner();
            }
            other => return (lifted, wrap_lifted_lets(kept, other)),
        }
    }
}
