use crate::pseudo::ast::{Binder, PseudoExpr};

#[derive(Clone, Default)]
pub(in crate::decompile::late::normalize) struct ValidatorEnv {
    pub(in crate::decompile::late::normalize) script_context: Option<Binder>,
    pub(in crate::decompile::late::normalize) redeemer: Option<Binder>,
    pub(in crate::decompile::late::normalize) expect_payload_subjects: Vec<Binder>,
}

pub(in crate::decompile::late::normalize) fn infer_root_validator_env(
    expr: &PseudoExpr,
) -> ValidatorEnv {
    let mut current = expr;

    loop {
        match current {
            PseudoExpr::Let { body, .. } => current = body.as_ref(),
            PseudoExpr::Lambda { params, .. } => {
                return match params.as_slice() {
                    [redeemer, script_context] => ValidatorEnv {
                        script_context: Some(script_context.clone()),
                        redeemer: Some(redeemer.clone()),
                        expect_payload_subjects: Vec::new(),
                    },
                    [_, redeemer, script_context] => ValidatorEnv {
                        script_context: Some(script_context.clone()),
                        redeemer: Some(redeemer.clone()),
                        expect_payload_subjects: Vec::new(),
                    },
                    _ => ValidatorEnv::default(),
                };
            }
            _ => return ValidatorEnv::default(),
        }
    }
}
