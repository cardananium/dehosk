use super::Simplifier;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

impl Simplifier {
    pub(super) fn track_partial_binding_facts(
        &mut self,
        name: &str,
        var_id: Option<VarId>,
        simplified_value: &PseudoExpr,
    ) -> bool {
        // Check for partial application (e.g. let c = fn(x) { x == 1 } or let c = Int.eq(1)).
        let is_partial_app =
            if let Some((op, arg, curried_is_left)) = Self::get_partial_app(simplified_value) {
                self.delays.partial_apps.insert_binding(
                    name.to_string(),
                    var_id,
                    (op, arg, curried_is_left),
                );
                true
            } else if let PseudoExpr::BuiltinCall {
                name: builtin_name,
                args: builtin_args,
            } = simplified_value
            {
                if builtin_args.len() == 1 {
                    let op_opt = match builtin_name.as_str() {
                        "Int.eq" | "ByteArray.eq" | "String.eq" | "Data.eq" => Some(BinaryOp::Eq),
                        "Int.lt" => Some(BinaryOp::Lt),
                        "Int.lte" | "Int.le" => Some(BinaryOp::Lte),
                        "Int.gt" => Some(BinaryOp::Gt),
                        "Int.gte" | "Int.ge" => Some(BinaryOp::Gte),
                        "Int.add" => Some(BinaryOp::Add),
                        "Int.sub" => Some(BinaryOp::Sub),
                        "Int.mul" => Some(BinaryOp::Mul),
                        "Int.div" => Some(BinaryOp::Div),
                        "Int.mod" => Some(BinaryOp::Mod),
                        _ => None,
                    };

                    if let Some(op) = op_opt {
                        // For builtins, the curried arg is the first (left) operand.
                        self.delays.partial_apps.insert_binding(
                            name.to_string(),
                            var_id,
                            (op, builtin_args[0].clone(), true),
                        );
                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            };

        // Track partially applied if/choose_list calls to simplify
        // force(force(fixed)(...)) call sites later.
        if let PseudoExpr::Apply { function, args } = simplified_value {
            let partial_target = match function.as_ref() {
                PseudoExpr::Force(inner_force) => match inner_force.as_ref() {
                    PseudoExpr::Var {
                        name: alias_name,
                        id,
                        ..
                    } => self
                        .builtin_alias_for_var(alias_name, id.get())
                        .map(|builtin| builtin.as_str()),
                    PseudoExpr::BuiltinCall {
                        name: builtin_name,
                        args: builtin_args,
                    } if builtin_args.is_empty() => Some(builtin_name.as_str()),
                    _ => None,
                },
                _ => None,
            };
            if args.len() == 1 {
                if matches!(partial_target, Some("if" | "if_then_else")) {
                    self.booleans.partial_if_conds.insert_binding(
                        name.to_string(),
                        var_id,
                        args[0].clone(),
                    );
                } else if matches!(partial_target, Some("choose_list" | "List.fold")) {
                    self.delays.partial_choose_list_subjects.insert_binding(
                        name.to_string(),
                        var_id,
                        args[0].clone(),
                    );
                }
            }
        }

        is_partial_app
    }
}
