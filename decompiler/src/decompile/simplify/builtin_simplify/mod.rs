//! Builtin function and unary operation simplification methods for Simplifier.

use super::Simplifier;
use crate::builtins::BuiltinId;
use crate::decompile::constructor_data::{
    ConstrPairProjection, rewrite_constr_unpack_pair_projection,
};
use crate::decompile::list_traversal::list_subject_and_tail_depth;
use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, UnaryOp};
use crate::pseudo::var_id::VarId;

mod call_analysis;
mod context;

#[cfg(test)]
pub(in crate::decompile::simplify) use self::call_analysis::CallArgObservation;

impl Simplifier {
    fn may_require_large_data_literal_hoist(expr: &PseudoExpr) -> bool {
        match expr {
            PseudoExpr::Data(_)
            | PseudoExpr::List { .. }
            | PseudoExpr::Tuple(_)
            | PseudoExpr::Pair(_, _)
            | PseudoExpr::Constr { .. } => true,
            PseudoExpr::BuiltinCall { name, .. } => *name == crate::BuiltinId::DataConstr,
            _ => false,
        }
    }

    pub(super) fn simplify_unop(&mut self, op: UnaryOp, operand: PseudoExpr) -> PseudoExpr {
        let inner = self.simplify(operand);

        // For Not, try to simplify
        if op != UnaryOp::Not {
            return PseudoExpr::UnOp {
                op,
                operand: PBox::new(inner),
            };
        }

        // !True -> False, !False -> True
        if self.is_true(&inner) {
            return PseudoExpr::Bool(false);
        }
        if self.is_false(&inner) {
            return PseudoExpr::Bool(true);
        }

        match inner {
            // !(a < b) -> a >= b, etc.
            PseudoExpr::BinOp {
                op: bin_op,
                left,
                right,
            } => {
                let flipped = match bin_op {
                    BinaryOp::Lt => Some(BinaryOp::Gte),
                    BinaryOp::Lte => Some(BinaryOp::Gt),
                    BinaryOp::Gt => Some(BinaryOp::Lte),
                    BinaryOp::Gte => Some(BinaryOp::Lt),
                    BinaryOp::Eq => Some(BinaryOp::Neq),
                    BinaryOp::Neq => Some(BinaryOp::Eq),
                    _ => None,
                };

                if let Some(new_op) = flipped {
                    PseudoExpr::BinOp {
                        op: new_op,
                        left,
                        right,
                    }
                } else {
                    PseudoExpr::UnOp {
                        op,
                        operand: PBox::new(PseudoExpr::BinOp {
                            op: bin_op,
                            left,
                            right,
                        }),
                    }
                }
            }
            // !!x -> x
            PseudoExpr::UnOp {
                op: UnaryOp::Not,
                operand: inner2,
            } => inner2.into_inner(),
            inner => PseudoExpr::UnOp {
                op,
                operand: PBox::new(inner),
            },
        }
    }

    /// Simplify a builtin call.
    pub(super) fn simplify_builtin_call(
        &mut self,
        name: crate::builtins::BuiltinId,
        args: Vec<PseudoExpr>,
    ) -> PseudoExpr {
        let mut simplified_args = Vec::with_capacity(args.len());
        for arg in args {
            simplified_args.push(self.simplify(arg));
        }

        if !self.safe_mode {
            if simplified_args
                .iter()
                .any(|arg| matches!(arg, PseudoExpr::Let { .. }))
                && let Some(hoisted) = self.hoist_let_from_builtin_args(name, &simplified_args)
            {
                return hoisted;
            }
            if name != "Data.Constr"
                && name != "constr_data"
                && simplified_args
                    .iter()
                    .any(Self::may_require_large_data_literal_hoist)
                && let Some(hoisted_literals) =
                    self.hoist_large_data_literals_from_builtin_args(name, &mut simplified_args)
            {
                return hoisted_literals;
            }
        }

        // new_pairs(Void) → [], new_list(Void) → []
        if (name == "new_pairs"
            || name == "mk_nil_pair_data"
            || name == "new_list"
            || name == "mk_nil_data")
            && simplified_args.len() == 1
            && matches!(&simplified_args[0], PseudoExpr::Unit)
        {
            return PseudoExpr::list(vec![]);
        }

        // Data pack/unpack round-trip elimination: pack(unpack(x)) → x and
        // unpack(pack(x)) → x. Sound because unpack fails on the wrong constructor:
        // if the program does not crash, x already holds the right one.
        if simplified_args.len() == 1 {
            let inverse = match name.as_str() {
                // pack(unpack(x)) → x
                "Data.ByteArray" | "ByteArray.to_data" | "b_data" => {
                    Some(&["Data.un_bytearray", "Data.to_bytes", "un_b_data"][..])
                }
                "Data.Int" | "Int.to_data" | "i_data" => {
                    Some(&["Data.un_int", "Data.to_int", "un_i_data"][..])
                }
                "Data.List" | "List.to_data" | "list_data" => {
                    Some(&["Data.un_list", "Data.to_list", "un_list_data"][..])
                }
                "Data.Map" | "Map.to_data" | "map_data" => {
                    Some(&["Data.un_map", "Data.to_map", "un_map_data"][..])
                }
                // unpack(pack(x)) → x
                "Data.un_bytearray" | "Data.to_bytes" | "un_b_data" => {
                    Some(&["Data.ByteArray", "ByteArray.to_data", "b_data"][..])
                }
                "Data.un_int" | "Data.to_int" | "un_i_data" => {
                    Some(&["Data.Int", "Int.to_data", "i_data"][..])
                }
                "Data.un_list" | "Data.to_list" | "un_list_data" => {
                    Some(&["Data.List", "List.to_data", "list_data"][..])
                }
                "Data.un_map" | "Data.to_map" | "un_map_data" => {
                    Some(&["Data.Map", "Map.to_data", "map_data"][..])
                }
                _ => None,
            };
            if let Some(inverse_names) = inverse {
                // Check BuiltinCall form: outer(BuiltinCall(inner, [x]))
                if matches!(
                    &simplified_args[0],
                    PseudoExpr::BuiltinCall {
                        name: inner_name,
                        args: inner_args,
                    } if inverse_names.iter().any(|n| n == inner_name) && inner_args.len() == 1
                ) {
                    let PseudoExpr::BuiltinCall { mut args, .. } =
                        simplified_args.pop().expect("round-trip arg should exist")
                    else {
                        unreachable!("round-trip BuiltinCall shape checked above");
                    };
                    return args.pop().expect("round-trip inner arg should exist");
                }
                // Check Apply form: outer(Apply(BuiltinCall(inner, []), [x]))
                if matches!(
                    &simplified_args[0],
                    PseudoExpr::Apply {
                        function,
                        args: apply_args,
                    } if apply_args.len() == 1
                        && matches!(
                            function.as_ref(),
                            PseudoExpr::BuiltinCall {
                                name: inner_name,
                                args: inner_builtin_args,
                            } if inverse_names.iter().any(|n| n == inner_name)
                                && inner_builtin_args.is_empty()
                        )
                ) {
                    let PseudoExpr::Apply { mut args, .. } =
                        simplified_args.pop().expect("round-trip arg should exist")
                    else {
                        unreachable!("round-trip Apply shape checked above");
                    };
                    return args.pop().expect("round-trip apply arg should exist");
                }
            }
        }

        // Constr.pack(tag, fields) / constr_data(tag, fields) / Data.Constr(tag, fields)
        // → Constr<N>(field1, field2, ...) when tag is literal and fields are a list literal.
        // Falls back to Data.Constr(tag, fields) when normalization can't produce a Constr.
        if (name == BuiltinId::ConstrPack || name == BuiltinId::DataConstr)
            && simplified_args.len() == 2
        {
            let mut args = simplified_args;
            let fields_expr = args.pop().unwrap();
            let tag_expr = args.pop().unwrap();
            return Self::normalize_constructor_data_expr(tag_expr, fields_expr);
        }

        // List.head(List.tail^N(x)) → x[N]; a bare List.head(x) becomes x[0].
        if (name == BuiltinId::ListHead) && simplified_args.len() == 1 {
            let (collection, depth) = list_subject_and_tail_depth(&simplified_args[0]);
            return PseudoExpr::IndexAccess {
                collection: PBox::new(collection),
                index: depth,
            };
        }

        // List.prepend(elem, list) → [elem, ..list_elements] when second arg is a List literal
        if (name == BuiltinId::ListPrepend)
            && simplified_args.len() == 2
            && matches!(&simplified_args[1], PseudoExpr::List { .. })
        {
            let mut args = simplified_args;
            let list_expr = args.pop().unwrap();
            let elem = args.pop().unwrap();
            let PseudoExpr::List { mut elements, tail } = list_expr else {
                unreachable!("list-prepend shape checked above");
            };
            let mut new_elements = Vec::with_capacity(elements.len() + 1);
            new_elements.push(elem);
            new_elements.append(&mut elements);
            return PseudoExpr::List {
                elements: new_elements.into(),
                tail,
            };
        }

        // 3-arg if in BuiltinCall form: if(cond, then, else) → simplify_if.
        if (name == "if" || name == "if_then_else") && simplified_args.len() == 3 {
            let mut iter = simplified_args.into_iter();
            let cond = iter.next().unwrap();
            let then_branch = Self::unwrap_delay_owned(iter.next().unwrap());
            let else_branch = Self::unwrap_delay_owned(iter.next().unwrap());
            return self.simplify_if(cond, then_branch, else_branch);
        }

        // Check for if-continuation pattern: if(cond, fn(_) { then }, fn(_) { else }, trigger)
        if !self.safe_mode && (name == "if" || name == "if_then_else") && simplified_args.len() == 4
        {
            // Last arg is trigger (Void, Unit, or any var)
            let is_trigger = Self::is_void(&simplified_args[3])
                || matches!(&simplified_args[3], PseudoExpr::Unit)
                || matches!(&simplified_args[3], PseudoExpr::Var { .. });

            if is_trigger {
                let then_body = Self::extract_continuation_body_ref(&simplified_args[1]);
                let else_body = Self::extract_continuation_body_ref(&simplified_args[2]);

                if let (Some(then_br), Some(else_br)) = (then_body, else_body) {
                    let cond = &simplified_args[0];

                    // Check for && pattern
                    if Self::can_short_circuit_with_boolean(cond)
                        && Self::can_short_circuit_with_boolean(then_br)
                        && self.is_false(else_br)
                        && !Self::is_fail(then_br)
                    {
                        return PseudoExpr::BinOp {
                            op: BinaryOp::And,
                            left: PBox::new(cond.clone()),
                            right: PBox::new(then_br.clone()),
                        };
                    }

                    // Check for || pattern
                    if Self::can_short_circuit_with_boolean(cond)
                        && Self::can_short_circuit_with_boolean(else_br)
                        && self.is_true(then_br)
                    {
                        return PseudoExpr::BinOp {
                            op: BinaryOp::Or,
                            left: PBox::new(cond.clone()),
                            right: PBox::new(else_br.clone()),
                        };
                    }

                    // expect! pattern; fail messages carry into the 3-arg form.
                    // When cond is already `when X is { ... _ -> fail }` it encodes
                    // the fail semantics itself, so fall through to simplify_if and
                    // let the if-when merge collapse it to a bare `when`.
                    if Self::is_fail(else_br)
                        && !Self::is_fail(then_br)
                        && !Self::when_has_guardless_wildcard_fail(cond)
                    {
                        let mut args = vec![cond.clone(), then_br.clone()];
                        if let Some(msg) = Self::fail_message(else_br) {
                            args.push(PseudoExpr::String(msg.to_string()));
                        }
                        return PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::expect_helper()),
                            args: args.into(),
                        };
                    }

                    // Inverted expect!, with the same guard and fail-message
                    // handling as the non-inverted path.
                    if Self::is_fail(then_br)
                        && !Self::is_fail(else_br)
                        && !Self::when_has_guardless_wildcard_fail(cond)
                    {
                        let msg = Self::fail_message(then_br).map(|m| m.to_string());
                        let mut args = vec![
                            PseudoExpr::UnOp {
                                op: UnaryOp::Not,
                                operand: PBox::new(cond.clone()),
                            },
                            else_br.clone(),
                        ];
                        if let Some(msg) = msg {
                            args.push(PseudoExpr::String(msg));
                        }
                        return PseudoExpr::Apply {
                            function: PBox::new(PseudoExpr::expect_helper()),
                            args: args.into(),
                        };
                    }

                    // Regular if expression
                    return self.simplify_if(cond.clone(), then_br.clone(), else_br.clone());
                }

                // Fallback: apply trigger to branches
                let mut iter = simplified_args.into_iter();
                let cond = iter.next().unwrap();
                let then_fn = Self::unwrap_delay_owned(iter.next().unwrap());
                let else_fn = Self::unwrap_delay_owned(iter.next().unwrap());
                let trigger = iter.next().unwrap();
                let then_applied = self.simplify_apply(then_fn, vec![trigger.clone()]);
                let else_applied = self.simplify_apply(else_fn, vec![trigger]);
                return self.simplify_if(cond, then_applied, else_applied);
            }
        }

        // 5-arg CPS-style if: if(cond, fst_sel, snd_sel, then, else).
        // In CPS encoding booleans select between continuations:
        // True = fst_sel = delay(fn(a, _) { a }), False = snd_sel = delay(fn(_, b) { b }),
        // so cond selects then or else. Rewrite to: if cond { then } else { else }
        if !self.safe_mode
            && (name == "if" || name == "if_then_else")
            && simplified_args.len() == 5
            && self.is_known_fst_selector(&simplified_args[1])
            && self.is_known_snd_selector(&simplified_args[2])
        {
            let mut iter = simplified_args.into_iter();
            let cond = iter.next().unwrap();
            let _fst = iter.next().unwrap();
            let _snd = iter.next().unwrap();
            let then_branch = Self::unwrap_delay_owned(iter.next().unwrap());
            let else_branch = Self::unwrap_delay_owned(iter.next().unwrap());
            return self.simplify_if(cond, then_branch, else_branch);
        }

        // Generic over-application fallback for builtin if:
        // if(cond, then, else, a, b, ...) -> if(cond, then, else)(a, b, ...)
        if !self.safe_mode && (name == "if" || name == "if_then_else") && simplified_args.len() > 3
        {
            let mut rest = simplified_args;
            let applied_args = rest.split_off(3);
            let mut iter = rest.into_iter();
            let cond = iter.next().unwrap();
            let then_branch = Self::unwrap_delay_owned(iter.next().unwrap());
            let else_branch = Self::unwrap_delay_owned(iter.next().unwrap());
            let if_result = self.simplify_if(cond, then_branch, else_branch);
            return self.simplify_apply(if_result, applied_args);
        }

        // Check for constructor tag access: Pair.first(Constr.unpack(x)) -> x.tag
        // Also handles Pair.first(var) where var is tracked as Constr.unpack(x)
        if (name == "Pair.first" || name == "fst_pair") && simplified_args.len() == 1 {
            let arg = simplified_args.into_iter().next().unwrap();
            let tracked_subject = if let PseudoExpr::Var {
                name: var_name, id, ..
            } = &arg
            {
                self.tracked_var(
                    &self.constructors.constr_unpack_subjects,
                    var_name,
                    id.get(),
                )
            } else {
                None
            };

            if let Some(expr) = rewrite_constr_unpack_pair_projection(
                &arg,
                tracked_subject,
                ConstrPairProjection::Tag,
            ) {
                return expr;
            }
            // Pair.first(Pair.new(a, b)) -> a
            if let PseudoExpr::BuiltinCall {
                name: inner_name,
                args: inner_args,
            } = arg
            {
                if (inner_name == "Pair.new" || inner_name == "new_pair") && inner_args.len() == 2 {
                    let mut iter = inner_args.into_iter();
                    return iter.next().unwrap();
                }
                return PseudoExpr::field_access(
                    PseudoExpr::BuiltinCall {
                        name: inner_name,
                        args: inner_args,
                    },
                    "fst".to_string(),
                );
            }
            // General: Pair.first(x) -> x.fst
            return PseudoExpr::field_access(arg, "fst".to_string());
        }

        // Check for constructor fields access: Pair.second(Constr.unpack(x)) -> x.fields
        // Also handles Pair.second(var) where var is tracked as Constr.unpack(x)
        if (name == "Pair.second" || name == "snd_pair") && simplified_args.len() == 1 {
            let arg = simplified_args.into_iter().next().unwrap();
            let tracked_subject = if let PseudoExpr::Var {
                name: var_name, id, ..
            } = &arg
            {
                self.tracked_var(
                    &self.constructors.constr_unpack_subjects,
                    var_name,
                    id.get(),
                )
            } else {
                None
            };

            if let Some(expr) = rewrite_constr_unpack_pair_projection(
                &arg,
                tracked_subject,
                ConstrPairProjection::Fields,
            ) {
                return expr;
            }
            // Pair.second(Pair.new(a, b)) -> b
            if let PseudoExpr::BuiltinCall {
                name: inner_name,
                args: inner_args,
            } = arg
            {
                if (inner_name == "Pair.new" || inner_name == "new_pair") && inner_args.len() == 2 {
                    let mut iter = inner_args.into_iter();
                    let _first = iter.next().unwrap();
                    return iter.next().unwrap();
                }
                return PseudoExpr::field_access(
                    PseudoExpr::BuiltinCall {
                        name: inner_name,
                        args: inner_args,
                    },
                    "snd".to_string(),
                );
            }
            // General: Pair.second(x) -> x.snd
            return PseudoExpr::field_access(arg, "snd".to_string());
        }

        // Convert 2-arg comparison builtins to BinOp: Int.eq(x, y) -> x == y
        let nice = Self::nice_builtin_name(name);
        if simplified_args.len() == 2 {
            let op_opt = match nice.as_str() {
                "Int.eq" | "ByteArray.eq" | "String.eq" | "Data.eq" => Some(BinaryOp::Eq),
                "Int.lt" | "ByteArray.lt" => Some(BinaryOp::Lt),
                "Int.lte" | "ByteArray.lte" => Some(BinaryOp::Lte),
                _ => None,
            };
            if let Some(op) = op_opt {
                let mut args = simplified_args;
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                let (left, right) = Self::canonicalize_commutative_binop(op, left, right);
                return PseudoExpr::BinOp {
                    op,
                    left: PBox::new(left),
                    right: PBox::new(right),
                };
            }
        }

        // Convert 2-arg arithmetic builtins to BinOp: Int.add(x, y) -> x + y
        if simplified_args.len() == 2 {
            let op_opt = match nice.as_str() {
                "Int.add" => Some(BinaryOp::Add),
                "Int.sub" => Some(BinaryOp::Sub),
                "Int.mul" => Some(BinaryOp::Mul),
                "Int.div" => Some(BinaryOp::Div),
                "Int.mod" => Some(BinaryOp::Mod),
                _ => None,
            };
            if let Some(op) = op_opt {
                let mut args = simplified_args;
                let right = args.pop().unwrap();
                let left = args.pop().unwrap();
                let (left, right) = Self::canonicalize_commutative_binop(op, left, right);
                return PseudoExpr::BinOp {
                    op,
                    left: PBox::new(left),
                    right: PBox::new(right),
                };
            }
        }

        // Replace certain builtin calls with nicer representations
        PseudoExpr::BuiltinCall {
            name: nice,
            args: simplified_args.into(),
        }
    }

    /// Extract a tag comparison from an equality check: `x.tag == N`,
    /// `N == x.tag`, or either side a var tracked as `x.tag`. Returns
    /// (subject, tag_value).
    pub(super) fn extract_tag_comparison(
        &self,
        left: &PseudoExpr,
        right: &PseudoExpr,
    ) -> Option<(PseudoExpr, usize)> {
        // Try left = tag accessor, right = int
        if let Some((subj, tag)) = self.try_tag_and_int(left, right) {
            return Some((subj, tag));
        }
        // Try right = tag accessor, left = int
        if let Some((subj, tag)) = self.try_tag_and_int(right, left) {
            return Some((subj, tag));
        }
        None
    }

    /// Helper: check if `tag_expr` is a tag accessor and `int_expr` is an integer.
    fn try_tag_and_int(
        &self,
        tag_expr: &PseudoExpr,
        int_expr: &PseudoExpr,
    ) -> Option<(PseudoExpr, usize)> {
        fn try_unpack_subject(expr: &PseudoExpr) -> Option<PseudoExpr> {
            if let PseudoExpr::BuiltinCall { name, args } = expr
                && (*name == BuiltinId::ConstrUnpack || *name == BuiltinId::DataUnConstr)
                && args.len() == 1
            {
                return Some(args[0].clone());
            }
            None
        }

        use num_traits::ToPrimitive;

        let int_val = if let PseudoExpr::Int(n) = int_expr {
            n.to_usize()?
        } else {
            return None;
        };

        // Direct field access: x.tag
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = tag_expr
        {
            if selector.as_pretty_name() == "tag" {
                return Some(((**record).clone(), int_val));
            }
            if selector.is_pair_fst() {
                return try_unpack_subject(record).map(|subject| (subject, int_val));
            }
        }

        // Raw tuple-style access: Constr.unpack(x)[0]
        if let PseudoExpr::IndexAccess {
            collection,
            index: 0,
        } = tag_expr
        {
            return try_unpack_subject(collection).map(|subject| (subject, int_val));
        }

        // Inline builtin form: Pair.first(Constr.unpack(x)) or aliases
        // (Pair.fst). This is the shape that appears for raw V3 purpose
        // dispatch before any naming pass tracks the tag binding.
        if let PseudoExpr::BuiltinCall { name, args } = tag_expr
            && (name == "Pair.first" || name == "Pair.fst" || name == "fst_pair")
            && args.len() == 1
            && let Some(subject) = try_unpack_subject(&args[0])
        {
            return Some((subject, int_val));
        }

        // Var tracked as tag: m where m = x.tag
        if let PseudoExpr::Var { name, id, .. } = tag_expr
            && let Some(subject) =
                self.tracked_var(&self.constructors.constr_tag_subjects, name, id.get())
        {
            return Some((subject, int_val));
        }

        None
    }

    /// Hoist let bindings from builtin args to outer scope.
    ///
    /// `Builtin(let x = v in body, other)` → `let x = v in Builtin(body, other)`
    pub(super) fn hoist_let_from_builtin_args(
        &mut self,
        name: crate::builtins::BuiltinId,
        args: &[PseudoExpr],
    ) -> Option<PseudoExpr> {
        let mut let_indices = Vec::new();
        let mut let_binders = Vec::new();
        let mut let_ids = Vec::new();

        for (index, arg) in args.iter().enumerate() {
            if let PseudoExpr::Let { name, id, .. } = arg {
                let_indices.push(index);
                let_binders.push(Binder::new(
                    name.clone(),
                    id.unwrap_or_else(VarId::fresh_compat_placeholder),
                ));
                let_ids.push(id.get());
            }
        }

        if let_indices.is_empty() {
            return None;
        }

        let mut usage_counts = vec![0usize; let_indices.len()];
        for (arg_index, arg) in args.iter().enumerate() {
            let arg_counts = Self::count_binding_uses_by_id(arg, &let_binders, &let_ids);
            for (target_index, target_arg_index) in let_indices.iter().enumerate() {
                if arg_index != *target_arg_index {
                    usage_counts[target_index] += arg_counts[target_index];
                }
            }
        }

        for (arg_index, usage_count) in let_indices.iter().zip(usage_counts.iter()) {
            if *usage_count > 0 {
                continue;
            }

            let PseudoExpr::Let {
                name: let_name,
                id,
                value,
                body,
            } = &args[*arg_index]
            else {
                continue;
            };

            let mut new_args = args.to_vec();
            new_args[*arg_index] = body.as_ref().clone();
            let inner = PseudoExpr::BuiltinCall {
                name,
                args: new_args.into(),
            };
            return Some(match id.get() {
                Some(let_id) => {
                    self.simplify_let(let_name.clone(), let_id, value.as_ref().clone(), inner)
                }
                None => self.simplify_compat_let(let_name.clone(), value.as_ref().clone(), inner),
            });
        }
        None
    }

    /// Hoist large data literals from builtin args into let bindings.
    pub(super) fn hoist_large_data_literals_from_builtin_args(
        &mut self,
        name: crate::builtins::BuiltinId,
        args: &mut Vec<PseudoExpr>,
    ) -> Option<PseudoExpr> {
        // Don't hoist from Data.Constr - it IS a data literal that gets extracted at the eq level
        if name == BuiltinId::DataConstr {
            return None;
        }
        let i = args.iter().position(|arg| {
            Self::static_data_expr_node_count(arg).is_some_and(|count| count > 8)
        })?;
        let lit_name = format!("data_literal_{}", i);
        let binder = self.fresh_synthetic_binder(&lit_name);
        self.var_kinds.kind_annotations.insert(
            binder.id,
            crate::pseudo::nameless::VarKind::DataLiteralHoist,
        );
        let lifted = std::mem::replace(&mut args[i], self.make_var_for_binder(&binder));
        let inner = PseudoExpr::BuiltinCall {
            name,
            args: std::mem::take(args).into(),
        };
        Some(self.make_let_for_binder(binder, lifted, inner))
    }
}

#[cfg(test)]
mod tests;
