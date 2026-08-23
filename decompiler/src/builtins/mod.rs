//! Canonical builtin identities used across the pseudo AST and decompiler passes.

use std::fmt;
use std::ops::Deref;
use std::rc::Rc;

use serde::{Deserialize, Serialize};

use crate::error::{DecompileError, Result};
use crate::pseudo::ast::PseudoType;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BuiltinId {
    IfThenElse,
    ListHead,
    ListTail,
    ListIsEmpty,
    ListPrepend,
    ListCons,
    ListFold,
    ListEmpty,
    ListEmptyPairs,
    PairFirst,
    PairSecond,
    PairNew,
    MkNilData,
    NewList,
    MkNilPairData,
    NewPairs,
    Seq,
    Trace,
    Error,
    DataCase,
    ConstrUnpack,
    ConstrPack,
    DataConstrIndex,
    DataConstrFields,
    DataUnConstr,
    DataUnInt,
    DataUnByteArray,
    DataUnList,
    DataUnMap,
    DataToInt,
    DataToBytes,
    DataToList,
    DataToMap,
    DataConstr,
    DataInt,
    DataByteArray,
    DataList,
    DataMap,
    IntToData,
    ByteArrayToData,
    ListToData,
    MapToData,
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntQuot,
    IntRem,
    IntMod,
    IntEq,
    IntLt,
    IntLte,
    ByteArrayConcat,
    ByteArrayPush,
    ByteArraySlice,
    ByteArrayLength,
    ByteArrayAt,
    ByteArrayEq,
    ByteArrayLt,
    ByteArrayLte,
    ByteArrayAnd,
    ByteArrayOr,
    ByteArrayXor,
    ByteArrayComplement,
    ByteArrayReadBit,
    ByteArrayWriteBits,
    ByteArrayReplicate,
    ByteArrayShift,
    ByteArrayRotate,
    ByteArrayCountSetBits,
    ByteArrayFindFirstSetBit,
    IntToByteArray,
    ByteArrayToInt,
    HashSha256,
    HashSha3_256,
    HashBlake2b256,
    HashBlake2b224,
    HashKeccak256,
    HashRipemd160,
    CryptoVerifyEd25519,
    CryptoVerifyEcdsa,
    CryptoVerifySchnorr,
    StringConcat,
    StringEq,
    StringToBytes,
    ByteArrayToString,
    DataEq,
    DataSerialize,
    Bls12_381G1Add,
    Bls12_381G1Neg,
    Bls12_381G1ScalarMul,
    Bls12_381G1Equal,
    Bls12_381G1Compress,
    Bls12_381G1Uncompress,
    Bls12_381G1HashToGroup,
    Bls12_381G2Add,
    Bls12_381G2Neg,
    Bls12_381G2ScalarMul,
    Bls12_381G2Equal,
    Bls12_381G2Compress,
    Bls12_381G2Uncompress,
    Bls12_381G2HashToGroup,
    Bls12_381MillerLoop,
    Bls12_381MulMillerLoopResult,
    Bls12_381FinalVerify,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BuiltinDisplayStyle {
    Canonical,
    Pretty,
}

impl BuiltinId {
    pub(crate) fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "if_then_else" | "if" => Self::IfThenElse,
            "head_list" | "List.head" => Self::ListHead,
            "tail_list" | "List.tail" => Self::ListTail,
            "null_list" | "List.is_empty" => Self::ListIsEmpty,
            "cons_list" | "mk_cons" | "List.prepend" => Self::ListPrepend,
            "List.cons" => Self::ListCons,
            "choose_list" | "List.fold" => Self::ListFold,
            "List.empty" => Self::ListEmpty,
            "List.empty_pairs" => Self::ListEmptyPairs,
            "fst_pair" | "Pair.first" => Self::PairFirst,
            "snd_pair" | "Pair.second" => Self::PairSecond,
            "mk_pair_data" | "new_pair" | "Pair.new" => Self::PairNew,
            "mk_nil_data" => Self::MkNilData,
            "new_list" => Self::NewList,
            "mk_nil_pair_data" => Self::MkNilPairData,
            "new_pairs" => Self::NewPairs,
            "choose_unit" | "choose_void" | "seq" => Self::Seq,
            "trace" | "debug" => Self::Trace,
            "error" | "fail" => Self::Error,
            "choose_data" | "Data.case" => Self::DataCase,
            "Constr.unpack" => Self::ConstrUnpack,
            "Constr.pack" => Self::ConstrPack,
            "Data.constr_index" => Self::DataConstrIndex,
            "Data.constr_fields" => Self::DataConstrFields,
            "un_constr_data" | "Data.un_constr" => Self::DataUnConstr,
            "un_i_data" | "Data.un_int" => Self::DataUnInt,
            "un_b_data" | "Data.un_bytearray" => Self::DataUnByteArray,
            "un_list_data" | "Data.un_list" => Self::DataUnList,
            "un_map_data" | "Data.un_map" => Self::DataUnMap,
            "Data.to_int" => Self::DataToInt,
            "Data.to_bytes" => Self::DataToBytes,
            "Data.to_list" => Self::DataToList,
            "Data.to_map" => Self::DataToMap,
            "constr_data" | "Data.Constr" => Self::DataConstr,
            "i_data" | "Data.Int" => Self::DataInt,
            "b_data" | "Data.ByteArray" => Self::DataByteArray,
            "list_data" | "Data.List" => Self::DataList,
            "map_data" | "Data.Map" => Self::DataMap,
            "Int.to_data" => Self::IntToData,
            "ByteArray.to_data" => Self::ByteArrayToData,
            "List.to_data" => Self::ListToData,
            "Map.to_data" => Self::MapToData,
            "add_integer" | "Int.add" => Self::IntAdd,
            "subtract_integer" | "Int.sub" => Self::IntSub,
            "multiply_integer" | "Int.mul" => Self::IntMul,
            "divide_integer" | "Int.div" => Self::IntDiv,
            "quotient_integer" | "Int.quot" => Self::IntQuot,
            "remainder_integer" | "Int.rem" => Self::IntRem,
            "mod_integer" | "Int.mod" => Self::IntMod,
            "equals_integer" | "Int.eq" => Self::IntEq,
            "less_than_integer" | "Int.lt" => Self::IntLt,
            "less_than_equals_integer" | "Int.lte" => Self::IntLte,
            "append_bytestring" | "append_bytearray" | "ByteArray.concat" => Self::ByteArrayConcat,
            "cons_bytearray" | "ByteArray.push" => Self::ByteArrayPush,
            "slice_bytestring" | "slice_bytearray" | "ByteArray.slice" => Self::ByteArraySlice,
            "length_of_bytestring" | "length_of_bytearray" | "ByteArray.length" => {
                Self::ByteArrayLength
            }
            "index_bytestring" | "index_bytearray" | "ByteArray.at" => Self::ByteArrayAt,
            "equals_bytestring" | "equals_bytearray" | "ByteArray.eq" => Self::ByteArrayEq,
            "less_than_bytestring" | "less_than_bytearray" | "ByteArray.lt" => Self::ByteArrayLt,
            "less_than_equals_bytestring" | "less_than_equals_bytearray" | "ByteArray.lte" => {
                Self::ByteArrayLte
            }
            "and_bytearray" | "ByteArray.and" => Self::ByteArrayAnd,
            "or_bytearray" | "ByteArray.or" => Self::ByteArrayOr,
            "xor_bytearray" | "ByteArray.xor" => Self::ByteArrayXor,
            "complement_bytearray" | "ByteArray.complement" => Self::ByteArrayComplement,
            "read_bit" | "ByteArray.read_bit" => Self::ByteArrayReadBit,
            "write_bits" | "ByteArray.write_bits" => Self::ByteArrayWriteBits,
            "replicate_byte" | "ByteArray.replicate" => Self::ByteArrayReplicate,
            "shift_bytearray" | "ByteArray.shift" => Self::ByteArrayShift,
            "rotate_bytearray" | "ByteArray.rotate" => Self::ByteArrayRotate,
            "count_set_bits" | "ByteArray.count_set_bits" => Self::ByteArrayCountSetBits,
            "find_first_set_bit" | "ByteArray.find_first_set_bit" => Self::ByteArrayFindFirstSetBit,
            "integer_to_bytearray" | "int_to_bytearray" | "Int.to_bytearray" => {
                Self::IntToByteArray
            }
            "bytearray_to_integer" | "bytearray_to_int" | "ByteArray.to_int" => {
                Self::ByteArrayToInt
            }
            "sha2_256" | "Hash.sha256" => Self::HashSha256,
            "sha3_256" | "Hash.sha3_256" => Self::HashSha3_256,
            "blake2b_256" | "Hash.blake2b_256" => Self::HashBlake2b256,
            "blake2b_224" | "Hash.blake2b_224" => Self::HashBlake2b224,
            "keccak_256" | "Hash.keccak_256" => Self::HashKeccak256,
            "ripemd_160" | "Hash.ripemd_160" => Self::HashRipemd160,
            "verify_ed25519_signature" | "Crypto.verify_ed25519" => Self::CryptoVerifyEd25519,
            "verify_ecdsa_secp256k1_signature"
            | "verify_ecdsa_secp256k1"
            | "Crypto.verify_ecdsa" => Self::CryptoVerifyEcdsa,
            "verify_schnorr_secp256k1_signature"
            | "verify_schnorr_secp256k1"
            | "Crypto.verify_schnorr" => Self::CryptoVerifySchnorr,
            "append_string" | "String.concat" => Self::StringConcat,
            "equals_string" | "String.eq" => Self::StringEq,
            "encode_utf8" | "String.to_bytes" => Self::StringToBytes,
            "decode_utf8" | "ByteArray.to_string" => Self::ByteArrayToString,
            "equals_data" | "Data.eq" => Self::DataEq,
            "serialise_data" | "Data.serialize" => Self::DataSerialize,
            "bls12_381_g1_add" => Self::Bls12_381G1Add,
            "bls12_381_g1_neg" => Self::Bls12_381G1Neg,
            "bls12_381_g1_scalar_mul" => Self::Bls12_381G1ScalarMul,
            "bls12_381_g1_equal" => Self::Bls12_381G1Equal,
            "bls12_381_g1_compress" => Self::Bls12_381G1Compress,
            "bls12_381_g1_uncompress" => Self::Bls12_381G1Uncompress,
            "bls12_381_g1_hash_to_group" => Self::Bls12_381G1HashToGroup,
            "bls12_381_g2_add" => Self::Bls12_381G2Add,
            "bls12_381_g2_neg" => Self::Bls12_381G2Neg,
            "bls12_381_g2_scalar_mul" => Self::Bls12_381G2ScalarMul,
            "bls12_381_g2_equal" => Self::Bls12_381G2Equal,
            "bls12_381_g2_compress" => Self::Bls12_381G2Compress,
            "bls12_381_g2_uncompress" => Self::Bls12_381G2Uncompress,
            "bls12_381_g2_hash_to_group" => Self::Bls12_381G2HashToGroup,
            "bls12_381_miller_loop" => Self::Bls12_381MillerLoop,
            "bls12_381_mul_miller_loop_result" => Self::Bls12_381MulMillerLoopResult,
            "bls12_381_final_verify" => Self::Bls12_381FinalVerify,
            _ => return None,
        })
    }

    pub(crate) fn parse_known(name: &str, stage: &str) -> Result<Self> {
        Self::from_name(name).ok_or_else(|| DecompileError::unknown_builtin(name, stage))
    }

    pub(crate) fn expect_known(name: &str) -> Self {
        Self::from_name(name).unwrap_or_else(|| panic!("unknown builtin literal `{name}`"))
    }

    pub(crate) fn is_known_name(name: &str) -> bool {
        Self::from_name(name).is_some()
    }

    pub(crate) fn as_str(self) -> &'static str {
        self.canonical_name()
    }

    pub(crate) fn canonical_name(self) -> &'static str {
        match self {
            Self::IfThenElse => "if",
            Self::ListHead => "List.head",
            Self::ListTail => "List.tail",
            Self::ListIsEmpty => "List.is_empty",
            Self::ListPrepend => "List.prepend",
            Self::ListCons => "List.cons",
            Self::ListFold => "List.fold",
            Self::ListEmpty => "List.empty",
            Self::ListEmptyPairs => "List.empty_pairs",
            Self::PairFirst => "Pair.first",
            Self::PairSecond => "Pair.second",
            Self::PairNew => "Pair.new",
            Self::MkNilData => "mk_nil_data",
            Self::NewList => "new_list",
            Self::MkNilPairData => "mk_nil_pair_data",
            Self::NewPairs => "new_pairs",
            Self::Seq => "seq",
            Self::Trace => "trace",
            Self::Error => "fail",
            Self::DataCase => "Data.case",
            Self::ConstrUnpack => "Constr.unpack",
            Self::ConstrPack => "Constr.pack",
            Self::DataConstrIndex => "Data.constr_index",
            Self::DataConstrFields => "Data.constr_fields",
            Self::DataUnConstr => "Data.un_constr",
            Self::DataUnInt => "Data.un_int",
            Self::DataUnByteArray => "Data.un_bytearray",
            Self::DataUnList => "Data.un_list",
            Self::DataUnMap => "Data.un_map",
            Self::DataToInt => "Data.to_int",
            Self::DataToBytes => "Data.to_bytes",
            Self::DataToList => "Data.to_list",
            Self::DataToMap => "Data.to_map",
            Self::DataConstr => "Data.Constr",
            Self::DataInt => "Data.Int",
            Self::DataByteArray => "Data.ByteArray",
            Self::DataList => "Data.List",
            Self::DataMap => "Data.Map",
            Self::IntToData => "Int.to_data",
            Self::ByteArrayToData => "ByteArray.to_data",
            Self::ListToData => "List.to_data",
            Self::MapToData => "Map.to_data",
            Self::IntAdd => "Int.add",
            Self::IntSub => "Int.sub",
            Self::IntMul => "Int.mul",
            Self::IntDiv => "Int.div",
            Self::IntQuot => "Int.quot",
            Self::IntRem => "Int.rem",
            Self::IntMod => "Int.mod",
            Self::IntEq => "Int.eq",
            Self::IntLt => "Int.lt",
            Self::IntLte => "Int.lte",
            Self::ByteArrayConcat => "ByteArray.concat",
            Self::ByteArrayPush => "ByteArray.push",
            Self::ByteArraySlice => "ByteArray.slice",
            Self::ByteArrayLength => "ByteArray.length",
            Self::ByteArrayAt => "ByteArray.at",
            Self::ByteArrayEq => "ByteArray.eq",
            Self::ByteArrayLt => "ByteArray.lt",
            Self::ByteArrayLte => "ByteArray.lte",
            Self::ByteArrayAnd => "ByteArray.and",
            Self::ByteArrayOr => "ByteArray.or",
            Self::ByteArrayXor => "ByteArray.xor",
            Self::ByteArrayComplement => "ByteArray.complement",
            Self::ByteArrayReadBit => "ByteArray.read_bit",
            Self::ByteArrayWriteBits => "ByteArray.write_bits",
            Self::ByteArrayReplicate => "ByteArray.replicate",
            Self::ByteArrayShift => "ByteArray.shift",
            Self::ByteArrayRotate => "ByteArray.rotate",
            Self::ByteArrayCountSetBits => "ByteArray.count_set_bits",
            Self::ByteArrayFindFirstSetBit => "ByteArray.find_first_set_bit",
            Self::IntToByteArray => "Int.to_bytearray",
            Self::ByteArrayToInt => "ByteArray.to_int",
            Self::HashSha256 => "Hash.sha256",
            Self::HashSha3_256 => "Hash.sha3_256",
            Self::HashBlake2b256 => "Hash.blake2b_256",
            Self::HashBlake2b224 => "Hash.blake2b_224",
            Self::HashKeccak256 => "Hash.keccak_256",
            Self::HashRipemd160 => "Hash.ripemd_160",
            Self::CryptoVerifyEd25519 => "Crypto.verify_ed25519",
            Self::CryptoVerifyEcdsa => "Crypto.verify_ecdsa",
            Self::CryptoVerifySchnorr => "Crypto.verify_schnorr",
            Self::StringConcat => "String.concat",
            Self::StringEq => "String.eq",
            Self::StringToBytes => "String.to_bytes",
            Self::ByteArrayToString => "ByteArray.to_string",
            Self::DataEq => "Data.eq",
            Self::DataSerialize => "Data.serialize",
            Self::Bls12_381G1Add => "bls12_381_g1_add",
            Self::Bls12_381G1Neg => "bls12_381_g1_neg",
            Self::Bls12_381G1ScalarMul => "bls12_381_g1_scalar_mul",
            Self::Bls12_381G1Equal => "bls12_381_g1_equal",
            Self::Bls12_381G1Compress => "bls12_381_g1_compress",
            Self::Bls12_381G1Uncompress => "bls12_381_g1_uncompress",
            Self::Bls12_381G1HashToGroup => "bls12_381_g1_hash_to_group",
            Self::Bls12_381G2Add => "bls12_381_g2_add",
            Self::Bls12_381G2Neg => "bls12_381_g2_neg",
            Self::Bls12_381G2ScalarMul => "bls12_381_g2_scalar_mul",
            Self::Bls12_381G2Equal => "bls12_381_g2_equal",
            Self::Bls12_381G2Compress => "bls12_381_g2_compress",
            Self::Bls12_381G2Uncompress => "bls12_381_g2_uncompress",
            Self::Bls12_381G2HashToGroup => "bls12_381_g2_hash_to_group",
            Self::Bls12_381MillerLoop => "bls12_381_miller_loop",
            Self::Bls12_381MulMillerLoopResult => "bls12_381_mul_miller_loop_result",
            Self::Bls12_381FinalVerify => "bls12_381_final_verify",
        }
    }

    pub(crate) fn display_name(self, style: BuiltinDisplayStyle) -> &'static str {
        match style {
            BuiltinDisplayStyle::Canonical => self.canonical_name(),
            BuiltinDisplayStyle::Pretty => match self {
                Self::IfThenElse => "if_then_else",
                // `Data.*` is a pseudonym, not surface syntax — `Data` is a
                // type, not a module. Pretty rendering maps each form to its
                // `builtin` equivalent; `canonical_name` keeps the
                // pseudonym so internal pattern-match callers still match.
                Self::DataUnConstr => "builtin.un_constr_data",
                // `Constr.unpack` unpacks a raw `Data` Constr into its
                // (tag, fields) pair, sharing `DataUnConstr`'s surface.
                Self::ConstrUnpack => "builtin.un_constr_data",
                // List primitives: the raw `builtin` forms keep an
                // un-recovered list spine compilable.
                Self::ListHead => "builtin.head_list",
                Self::ListTail => "builtin.tail_list",
                Self::ListIsEmpty => "builtin.null_list",
                Self::DataUnInt => "builtin.un_i_data",
                Self::DataUnByteArray => "builtin.un_b_data",
                Self::DataUnList => "builtin.un_list_data",
                Self::DataUnMap => "builtin.un_map_data",
                Self::DataConstr => "builtin.constr_data",
                Self::DataInt => "builtin.i_data",
                Self::DataByteArray => "builtin.b_data",
                Self::DataList => "builtin.list_data",
                Self::DataMap => "builtin.map_data",
                Self::DataSerialize => "builtin.serialise_data",
                Self::DataEq => "builtin.equals_data",
                Self::DataCase => "builtin.choose_data",
                // Render as the `Pair(a, b)` literal, matching the
                // `KnownConstructor::Pair` render path.
                Self::PairNew => "Pair",
                _ => self.canonical_name(),
            },
        }
    }

    pub(crate) fn force_count(self) -> u8 {
        match self {
            Self::PairFirst
            | Self::PairSecond
            | Self::ListFold
            | Self::ListPrepend
            | Self::DataCase => 2,
            Self::IfThenElse
            | Self::ListHead
            | Self::ListTail
            | Self::ListIsEmpty
            | Self::Trace
            | Self::PairNew
            | Self::MkNilData
            | Self::NewList
            | Self::MkNilPairData
            | Self::NewPairs
            | Self::Seq => 1,
            _ => 0,
        }
    }

    pub(crate) fn is_projection_wrapper(self) -> bool {
        matches!(
            self,
            Self::ListTail
                | Self::ConstrUnpack
                | Self::DataUnList
                | Self::DataUnMap
                | Self::DataUnConstr
                | Self::DataUnByteArray
                | Self::DataUnInt
        )
    }

    pub(crate) fn starts_projection_chain(self) -> bool {
        matches!(self, Self::ListTail)
    }

    pub(crate) fn is_data_constructor(self) -> bool {
        matches!(self, Self::ConstrPack | Self::DataConstr)
    }

    pub(crate) fn is_fail_builtin(self) -> bool {
        matches!(self, Self::Error)
    }

    /// True for builtins whose return type is structurally `Bool` and whose
    /// result is a boolean predicate, not Plutus `Data` carrying a
    /// constructor tag. The type solver reads it to constrain an `if`
    /// condition to `Bool` (`is_inherently_bool` in `type_solver.rs`).
    ///
    /// Invariant: every variant listed here must also be produced by
    /// [`BuiltinId::monomorphic_return_type`] with `Some(PseudoType::Bool)`.
    pub(crate) fn returns_bool(self) -> bool {
        matches!(
            self,
            Self::ListIsEmpty
                | Self::IntEq
                | Self::IntLt
                | Self::IntLte
                | Self::ByteArrayEq
                | Self::ByteArrayLt
                | Self::ByteArrayLte
                | Self::StringEq
                | Self::DataEq
                | Self::Seq
        )
    }

    /// Return type for builtins whose result type is determined by the
    /// builtin identity alone (no dependency on argument types).
    ///
    /// `None` for genuinely polymorphic builtins
    /// (`ListHead`/`ListTail`/`PairFirst`/`PairSecond`/`ListPrepend`/…)
    /// that need argument types; each caller resolves those.
    pub(crate) fn monomorphic_return_type(self) -> Option<PseudoType> {
        let ty = match self {
            // Bool-returning predicates ---
            Self::ListIsEmpty
            | Self::IntEq
            | Self::IntLt
            | Self::IntLte
            | Self::ByteArrayEq
            | Self::ByteArrayLt
            | Self::ByteArrayLte
            | Self::StringEq
            | Self::DataEq
            | Self::Seq => PseudoType::Bool,

            // Int-returning ---
            Self::IntAdd
            | Self::IntSub
            | Self::IntMul
            | Self::IntDiv
            | Self::IntQuot
            | Self::IntRem
            | Self::IntMod
            | Self::ByteArrayLength
            | Self::ByteArrayAt
            | Self::ByteArrayCountSetBits
            | Self::ByteArrayFindFirstSetBit
            | Self::ByteArrayToInt
            | Self::DataUnInt
            | Self::DataToInt
            | Self::DataConstrIndex => PseudoType::Int,

            // Bool-returning bit predicate ---
            // `ByteArray.read_bit(bytes, index)` is Bool, not Int.
            Self::ByteArrayReadBit => PseudoType::Bool,

            // ByteArray-returning ---
            Self::ByteArrayConcat
            | Self::ByteArrayPush
            | Self::ByteArraySlice
            | Self::ByteArrayAnd
            | Self::ByteArrayOr
            | Self::ByteArrayXor
            | Self::ByteArrayComplement
            | Self::ByteArrayWriteBits
            | Self::ByteArrayReplicate
            | Self::ByteArrayShift
            | Self::ByteArrayRotate
            | Self::IntToByteArray
            | Self::HashSha256
            | Self::HashSha3_256
            | Self::HashBlake2b256
            | Self::HashBlake2b224
            | Self::HashKeccak256
            | Self::HashRipemd160
            | Self::DataUnByteArray
            | Self::DataToBytes
            | Self::StringToBytes
            | Self::DataSerialize => PseudoType::ByteArray,

            // String-returning ---
            Self::StringConcat | Self::ByteArrayToString => PseudoType::String,

            // Data-returning (packers + constructors) ---
            Self::DataConstr
            | Self::DataInt
            | Self::DataByteArray
            | Self::DataList
            | Self::DataMap
            | Self::IntToData
            | Self::ByteArrayToData
            | Self::ListToData
            | Self::MapToData => PseudoType::Data,

            // Unpackers with known shapes ---
            Self::DataUnList | Self::DataToList => PseudoType::List(Rc::new(PseudoType::Data)),
            Self::DataUnMap | Self::DataToMap => PseudoType::List(Rc::new(PseudoType::Pair(
                Rc::new(PseudoType::Data),
                Rc::new(PseudoType::Data),
            ))),
            Self::DataUnConstr | Self::ConstrUnpack => PseudoType::Pair(
                Rc::new(PseudoType::Int),
                Rc::new(PseudoType::List(Rc::new(PseudoType::Data))),
            ),
            Self::DataConstrFields => PseudoType::List(Rc::new(PseudoType::Data)),

            // BLS elements ---
            Self::Bls12_381G1Add
            | Self::Bls12_381G1Neg
            | Self::Bls12_381G1ScalarMul
            | Self::Bls12_381G1Uncompress
            | Self::Bls12_381G1HashToGroup => PseudoType::G1Element,
            Self::Bls12_381G2Add
            | Self::Bls12_381G2Neg
            | Self::Bls12_381G2ScalarMul
            | Self::Bls12_381G2Uncompress
            | Self::Bls12_381G2HashToGroup => PseudoType::G2Element,
            Self::Bls12_381MillerLoop | Self::Bls12_381MulMillerLoopResult => {
                PseudoType::MillerLoopResult
            }
            Self::Bls12_381G1Compress | Self::Bls12_381G2Compress => PseudoType::ByteArray,
            Self::Bls12_381G1Equal
            | Self::Bls12_381G2Equal
            | Self::Bls12_381FinalVerify
            | Self::CryptoVerifyEd25519
            | Self::CryptoVerifyEcdsa
            | Self::CryptoVerifySchnorr => PseudoType::Bool,

            // Empty-list constructors with Unknown element type ---
            // The list itself is certain; only the element type is
            // unresolved statically; callers may refine it from args.
            Self::ListEmpty
            | Self::ListEmptyPairs
            | Self::MkNilData
            | Self::MkNilPairData
            | Self::NewList
            | Self::NewPairs => PseudoType::List(Rc::new(PseudoType::Unknown)),

            // Polymorphic / arg-dependent: caller must resolve ---
            Self::IfThenElse
            | Self::ListHead
            | Self::ListTail
            | Self::ListPrepend
            | Self::ListCons
            | Self::ListFold
            | Self::PairFirst
            | Self::PairSecond
            | Self::PairNew
            | Self::DataCase
            | Self::ConstrPack
            | Self::Trace
            | Self::Error => return None,
        };
        Some(ty)
    }

    /// Monomorphic argument types for builtins whose entire signature is
    /// concrete, position-aligned so callers can refine arg-binder types
    /// via `merge_more_concrete`. Polymorphic / arg-dependent builtins
    /// return `None` — they need type-variable propagation.
    ///
    /// Covers Int / ByteArray / Bool / Data / String arg shapes plus
    /// monomorphic crypto/BLS; List/Pair args are skipped.
    pub(crate) fn monomorphic_arg_types(self) -> Option<Vec<PseudoType>> {
        let args: Vec<PseudoType> = match self {
            // (Int, Int) → ...
            Self::IntAdd
            | Self::IntSub
            | Self::IntMul
            | Self::IntDiv
            | Self::IntQuot
            | Self::IntRem
            | Self::IntMod
            | Self::IntEq
            | Self::IntLt
            | Self::IntLte => vec![PseudoType::Int, PseudoType::Int],

            // (Int,) → ... — `IntToData(value)`.
            Self::IntToData => vec![PseudoType::Int],

            // `IntToByteArray(big_endian: Bool, size: Int, value: Int) -> ByteArray`
            // — per Plutus V3 spec.
            Self::IntToByteArray => vec![PseudoType::Bool, PseudoType::Int, PseudoType::Int],

            // (ByteArray, ByteArray) → ...
            Self::ByteArrayConcat | Self::ByteArrayEq | Self::ByteArrayLt | Self::ByteArrayLte => {
                vec![PseudoType::ByteArray, PseudoType::ByteArray]
            }

            // `andByteString/orByteString/xorByteString(pad_or_no: Bool, a: ByteArray, b: ByteArray)`
            // — per Plutus V3 spec (the `pad_or_no` flag controls
            // length mismatch handling).
            Self::ByteArrayAnd | Self::ByteArrayOr | Self::ByteArrayXor => {
                vec![
                    PseudoType::Bool,
                    PseudoType::ByteArray,
                    PseudoType::ByteArray,
                ]
            }

            // (ByteArray,) → ...
            Self::ByteArrayLength
            | Self::ByteArrayComplement
            | Self::ByteArrayToString
            | Self::HashSha256
            | Self::HashSha3_256
            | Self::HashBlake2b256
            | Self::HashBlake2b224
            | Self::HashKeccak256
            | Self::HashRipemd160
            | Self::ByteArrayCountSetBits
            | Self::ByteArrayFindFirstSetBit
            | Self::ByteArrayToData => vec![PseudoType::ByteArray],

            // `byteStringToInteger(big_endian: Bool, b: ByteArray)`
            // — per Plutus V3 spec.
            Self::ByteArrayToInt => vec![PseudoType::Bool, PseudoType::ByteArray],

            // (ByteArray, Int) → ...
            Self::ByteArrayAt | Self::ByteArrayReadBit => {
                vec![PseudoType::ByteArray, PseudoType::Int]
            }

            // `sliceByteString(start: Int, length: Int, b: ByteArray) -> ByteArray`
            // — per Plutus core spec. ARGS ORDER MATTERS.
            Self::ByteArraySlice => vec![PseudoType::Int, PseudoType::Int, PseudoType::ByteArray],

            // (Int, ByteArray) → ... — `consByteString(byte, bytes)`.
            Self::ByteArrayPush => vec![PseudoType::Int, PseudoType::ByteArray],

            // `shiftByteString(b: ByteArray, amount: Int) -> ByteArray`
            // and `rotateByteString(b: ByteArray, amount: Int) -> ByteArray`
            // — per Plutus V3 spec. NO Bool prefix.
            Self::ByteArrayShift | Self::ByteArrayRotate => {
                vec![PseudoType::ByteArray, PseudoType::Int]
            }

            // `writeBits(b: ByteArray, indices: List<Int>, value: Bool) -> ByteArray`
            // — the middle arg is polymorphic, so skip rather than mis-seed.
            Self::ByteArrayWriteBits => return None,

            // `replicateByteString(count: Int, byte: Int) -> ByteArray`.
            Self::ByteArrayReplicate => vec![PseudoType::Int, PseudoType::Int],

            // (String, String) → ...
            Self::StringConcat => vec![PseudoType::String, PseudoType::String],
            Self::StringEq => vec![PseudoType::String, PseudoType::String],
            Self::StringToBytes => vec![PseudoType::String],

            // (Data, Data) → Bool
            Self::DataEq => vec![PseudoType::Data, PseudoType::Data],

            // (Data,) → various
            Self::DataUnInt
            | Self::DataUnByteArray
            | Self::DataUnList
            | Self::DataUnMap
            | Self::DataUnConstr
            | Self::ConstrUnpack
            | Self::DataConstrFields
            | Self::DataConstrIndex
            | Self::DataToInt
            | Self::DataToBytes
            | Self::DataToList
            | Self::DataToMap
            | Self::DataSerialize => vec![PseudoType::Data],

            // Sequence (any, any) → second: second is polymorphic,
            // first is always evaluated for effect. One vector maps
            // ALL slots, so the first arg cannot be refined alone.
            Self::Seq => return None,

            // Everything else: polymorphic or special-cased; skip.
            _ => return None,
        };
        Some(args)
    }
}

impl Deref for BuiltinId {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.canonical_name()
    }
}

impl fmt::Display for BuiltinId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.canonical_name())
    }
}

impl PartialEq<&str> for BuiltinId {
    fn eq(&self, other: &&str) -> bool {
        Self::from_name(other).is_some_and(|builtin| builtin == *self)
    }
}

impl PartialEq<str> for BuiltinId {
    fn eq(&self, other: &str) -> bool {
        Self::from_name(other).is_some_and(|builtin| builtin == *self)
    }
}

impl PartialEq<BuiltinId> for &str {
    fn eq(&self, other: &BuiltinId) -> bool {
        *other == *self
    }
}

impl PartialEq<BuiltinId> for str {
    fn eq(&self, other: &BuiltinId) -> bool {
        *other == self
    }
}

impl AsRef<str> for BuiltinId {
    fn as_ref(&self) -> &str {
        self.canonical_name()
    }
}

impl From<&str> for BuiltinId {
    fn from(value: &str) -> Self {
        Self::expect_known(value)
    }
}

impl From<String> for BuiltinId {
    fn from(value: String) -> Self {
        Self::expect_known(&value)
    }
}

impl From<&String> for BuiltinId {
    fn from(value: &String) -> Self {
        Self::expect_known(value)
    }
}

#[cfg(test)]
mod tests;
