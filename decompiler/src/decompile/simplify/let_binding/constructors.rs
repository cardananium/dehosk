use super::Simplifier;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::{OptionVarIdGet, VarId};

impl Simplifier {
    pub(super) fn track_constructor_binding_facts(
        &mut self,
        name: &str,
        var_id: Option<VarId>,
        simplified_value: &PseudoExpr,
    ) {
        // Track Constr.unpack bindings: let u = Constr.unpack(x) -> store u -> x
        // so Pair.first(u) -> x.tag and Pair.second(u) -> x.fields.
        if let PseudoExpr::BuiltinCall {
            name: builtin_name,
            args: builtin_args,
        } = simplified_value
            && (*builtin_name == crate::BuiltinId::ConstrUnpack
                || *builtin_name == crate::BuiltinId::DataUnConstr)
            && builtin_args.len() == 1
        {
            self.constructors.constr_unpack_subjects.insert_binding(
                name.to_string(),
                var_id,
                builtin_args[0].clone(),
            );
        }

        // Track Constr.pack partial application: let c = Constr.pack(N) -> store c -> N
        // so c(fields) -> Data.Constr(N, fields) at call sites.
        if let PseudoExpr::BuiltinCall {
            name: builtin_name,
            args: builtin_args,
        } = simplified_value
            && (*builtin_name == crate::BuiltinId::ConstrPack
                || *builtin_name == crate::BuiltinId::DataConstr)
            && builtin_args.len() == 1
            && matches!(&builtin_args[0], PseudoExpr::Int(_))
        {
            self.constructors.constr_pack_tags.insert_binding(
                name.to_string(),
                var_id,
                builtin_args[0].clone(),
            );
        }

        // Track constructor-data bindings (possibly wrapped in Let chains):
        // let t = Data.Constr(tag, fields) or let t = Constr<tag>(...) -> store t.
        // Used to fold t.fields -> fields and t.tag -> tag via re-simplification.
        {
            let mut inner = simplified_value;
            while let PseudoExpr::Let { body, .. } = inner {
                inner = body;
            }
            let is_data_constr = match inner {
                PseudoExpr::BuiltinCall {
                    name: builtin_name,
                    args: builtin_args,
                } => *builtin_name == crate::BuiltinId::DataConstr && builtin_args.len() == 2,
                PseudoExpr::Constr { .. } => true,
                _ => false,
            };
            if is_data_constr {
                self.constructors.data_constr_bindings.insert_binding(
                    name.to_string(),
                    var_id,
                    simplified_value.clone(),
                );
            }
        }

        // Track constructor tag bindings: let m = x.tag -> store m -> x
        // so `when m is { 0 -> ... }` can become `when x is { Constr<0> -> ... }`.
        //
        // Also recognize the inline-builtin shape that appears for raw
        // V3 purpose dispatch: `let m = Pair.first(Constr.unpack(x))`.
        let tracked_subject = match simplified_value {
            PseudoExpr::FieldAccess {
                record, selector, ..
            } if selector.as_pretty_name() == "tag" => Some((**record).clone()),
            PseudoExpr::BuiltinCall { name, args }
                if (name == "Pair.first" || name == "Pair.fst" || name == "fst_pair")
                    && args.len() == 1 =>
            {
                if let PseudoExpr::BuiltinCall {
                    name: inner_name,
                    args: inner_args,
                } = &args[0]
                {
                    if (*inner_name == crate::BuiltinId::ConstrUnpack
                        || *inner_name == crate::BuiltinId::DataUnConstr
                        || inner_name == "un_constr_data")
                        && inner_args.len() == 1
                    {
                        Some(inner_args[0].clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(subject) = tracked_subject {
            self.constructors
                .constr_tag_subjects
                .insert_binding(name.to_string(), var_id, subject);
        }

        // Track .fields bindings: let v = x.fields -> store v -> x.
        // Used for when-clause field destructuring.
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = simplified_value
            && selector.as_pretty_name() == "fields"
        {
            self.constructors.fields_bindings.insert_binding(
                name.to_string(),
                var_id,
                (**record).clone(),
            );
        }

        // Track List.tail chain offsets: let v = List.tail(x) -> store v -> (x, 1).
        // When x is already tracked as (base, N), store v -> (base, N+1).
        // Used to convert v[M] -> base[M + offset].
        {
            let tail_arg = Self::extract_tail_arg(simplified_value);
            if let Some(arg) = tail_arg {
                let (base, offset) = if let PseudoExpr::Var {
                    name: var_name, id, ..
                } = arg
                {
                    if let Some((base, existing_offset)) =
                        self.tracked_var(&self.constructors.tail_chain_offsets, var_name, id.get())
                    {
                        (base, existing_offset + 1)
                    } else {
                        (arg.clone(), 1)
                    }
                } else {
                    (arg.clone(), 1)
                };
                self.constructors.tail_chain_offsets.insert_binding(
                    name.to_string(),
                    var_id,
                    (base.clone(), offset),
                );
                // record VarKind::SliceTailAlias at the
                // mint site when the base is a Var and the binder
                // has a concrete VarId (not a compat placeholder).
                // For complex bases (non-Var), defer to
                // kind_inference's name-pattern recognizer.
                if let (
                    PseudoExpr::Var {
                        id: Some(parent_id),
                        ..
                    },
                    Some(binder_id),
                ) = (base, var_id)
                {
                    self.var_kinds.kind_annotations.insert(
                        binder_id,
                        VarKind::SliceTailAlias {
                            parent: parent_id,
                            depth: offset,
                        },
                    );
                }
            }
        }
    }
}
