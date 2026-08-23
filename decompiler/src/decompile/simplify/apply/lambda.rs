use super::Simplifier;
use crate::pseudo::ast::{Binder, PseudoExpr};

impl Simplifier {
    pub(super) fn args_capture_bound_params(args: &[PseudoExpr], params: &[Binder]) -> bool {
        params
            .iter()
            .filter(|param| param.as_str() != "_")
            .any(|param| {
                args.iter()
                    .any(|arg| Self::is_var_used(arg, param.as_str()))
            })
    }

    pub(super) fn immediate_lambda_parts(expr: &PseudoExpr) -> Option<(&[Binder], &PseudoExpr)> {
        let mut current = expr;
        loop {
            match current {
                PseudoExpr::Lambda { params, body } => return Some((params, body.as_ref())),
                // Pretty-printing already renders `Force(Lambda)` as a direct call,
                // so simplify the same shape before it leaks into late cleanup.
                PseudoExpr::Force(inner) => current = inner.as_ref(),
                _ => return None,
            }
        }
    }

    pub(super) fn into_immediate_lambda_parts(
        expr: PseudoExpr,
    ) -> Option<(Vec<Binder>, PseudoExpr)> {
        let mut current = expr;
        loop {
            match current {
                PseudoExpr::Lambda { params, body } => return Some((params, body.into_inner())),
                PseudoExpr::Force(inner) => current = inner.into_inner(),
                _ => return None,
            }
        }
    }
}
