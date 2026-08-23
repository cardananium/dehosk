use super::Simplifier;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::var_id::VarId;

impl Simplifier {
    pub(super) fn track_boolean_lambda_binding_facts(
        &mut self,
        name: &str,
        var_id: Option<VarId>,
        simplified_value: &PseudoExpr,
        is_and: bool,
        is_or: bool,
    ) {
        // Post-simplification and/or detection: `is_and_definition` only checks the
        // raw pattern, so it misses bodies that simplify to `a && b`, e.g.
        // fn(a, b) { force(force(if_then_else))(a)(b)(delay(False)) }.
        // Only add to and_vars/or_vars for call-site conversion; setting is_and/is_or
        // here would drop the let binding unconditionally.
        if is_and || is_or {
            return;
        }

        let PseudoExpr::Lambda { params, body } = simplified_value else {
            return;
        };

        if params.len() == 2 {
            if let PseudoExpr::BinOp {
                op: BinaryOp::And,
                left,
                right,
            } = body.as_ref()
                && Self::is_param_or_forced(left, &params[0])
                && Self::is_param_or_forced(right, &params[1])
                && let Some(vid) = var_id
            {
                self.booleans.and_vars.insert(vid);
            }
            if let PseudoExpr::BinOp {
                op: BinaryOp::Or,
                left,
                right,
            } = body.as_ref()
                && Self::is_param_or_forced(left, &params[0])
                && Self::is_param_or_forced(right, &params[1])
                && let Some(vid) = var_id
            {
                self.booleans.or_vars.insert(vid);
            }
        }

        // Detect partial-if lambda: fn(x) { if(x, then_val) }.
        // When over-applied as force(f(a, delay(b))), expands to if(a, then_val, b)
        // which simplify_if can then convert to a || b (if then_val=True) etc.
        if params.len() == 1
            && let PseudoExpr::Apply { function, args } = body.as_ref()
        {
            let is_if_builtin = matches!(
                function.as_ref(),
                PseudoExpr::BuiltinCall { name, args: builtin_args }
                    if (name == "if" || name == "if_then_else") && builtin_args.is_empty()
            );
            if is_if_builtin
                && args.len() == 2
                && matches!(&args[0], PseudoExpr::Var { name: n, .. } if n == &params[0])
            {
                self.booleans.partial_if_then_vals.insert_binding(
                    name.to_string(),
                    var_id,
                    args[1].clone(),
                );
            }
        }
    }

    fn is_param_or_forced(expr: &PseudoExpr, param: &str) -> bool {
        match expr {
            PseudoExpr::Var { name, .. } => name == param,
            PseudoExpr::Force(inner) => {
                matches!(inner.as_ref(), PseudoExpr::Var { name, .. } if name == param)
            }
            _ => false,
        }
    }
}
