use super::Simplifier;
use crate::decompile::constructor_data::ConstrPairProjection;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};

impl Simplifier {
    pub(super) fn partial_builtin_comparison_op(name: &str) -> Option<BinaryOp> {
        match name {
            "Int.eq" | "ByteArray.eq" | "String.eq" => Some(BinaryOp::Eq),
            "Int.lt" => Some(BinaryOp::Lt),
            "Int.lte" | "Int.le" => Some(BinaryOp::Lte),
            "Int.gt" => Some(BinaryOp::Gt),
            "Int.gte" | "Int.ge" => Some(BinaryOp::Gte),
            _ => None,
        }
    }

    pub(super) fn apply_form_binop_op(func: &PseudoExpr, apply_arg_len: usize) -> Option<BinaryOp> {
        match func {
            PseudoExpr::BuiltinCall {
                name: bname,
                args: builtin_args,
            } if builtin_args.len() + apply_arg_len == 2 => {
                let nice = Self::nice_builtin_name(*bname);
                match nice.as_str() {
                    "Int.eq" | "ByteArray.eq" | "String.eq" | "Data.eq" => Some(BinaryOp::Eq),
                    "Int.lt" | "ByteArray.lt" => Some(BinaryOp::Lt),
                    "Int.lte" | "ByteArray.lte" => Some(BinaryOp::Lte),
                    "Int.add" => Some(BinaryOp::Add),
                    "Int.sub" => Some(BinaryOp::Sub),
                    "Int.mul" => Some(BinaryOp::Mul),
                    "Int.div" => Some(BinaryOp::Div),
                    "Int.mod" => Some(BinaryOp::Mod),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub(super) fn apply_form_pair_selector(
        name: &str,
    ) -> Option<(bool, ConstrPairProjection, &'static str)> {
        match name {
            "Pair.first" | "fst_pair" => Some((true, ConstrPairProjection::Tag, "fst")),
            "Pair.second" | "snd_pair" => Some((false, ConstrPairProjection::Fields, "snd")),
            _ => None,
        }
    }

    pub(super) fn data_round_trip_inverse_names(name: &str) -> Option<&'static [&'static str]> {
        match name {
            "Data.ByteArray" | "ByteArray.to_data" | "b_data" => {
                Some(&["Data.un_bytearray", "Data.to_bytes", "un_b_data"])
            }
            "Data.Int" | "Int.to_data" | "i_data" => {
                Some(&["Data.un_int", "Data.to_int", "un_i_data"])
            }
            "Data.List" | "List.to_data" | "list_data" => {
                Some(&["Data.un_list", "Data.to_list", "un_list_data"])
            }
            "Data.Map" | "Map.to_data" | "map_data" => {
                Some(&["Data.un_map", "Data.to_map", "un_map_data"])
            }
            "Data.un_bytearray" | "Data.to_bytes" | "un_b_data" => {
                Some(&["Data.ByteArray", "ByteArray.to_data", "b_data"])
            }
            "Data.un_int" | "Data.to_int" | "un_i_data" => {
                Some(&["Data.Int", "Int.to_data", "i_data"])
            }
            "Data.un_list" | "Data.to_list" | "un_list_data" => {
                Some(&["Data.List", "List.to_data", "list_data"])
            }
            "Data.un_map" | "Data.to_map" | "un_map_data" => {
                Some(&["Data.Map", "Map.to_data", "map_data"])
            }
            _ => None,
        }
    }

    pub(super) fn is_apply_form_list_head_builtin(name: &str) -> bool {
        matches!(name, "List.head" | "head_list")
    }

    pub(super) fn is_apply_form_list_prepend_builtin(name: &str) -> bool {
        matches!(name, "List.prepend" | "cons_list" | "mk_cons")
    }
}
