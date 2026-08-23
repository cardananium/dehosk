//! Abstract value lattice for static analysis of MidExpr.
//!
//! `AbstractValue` describes what is known about a MIR node's runtime
//! value without executing the program.

use num_bigint::BigInt;
use uplc::builtins::DefaultFunction;

use super::var_id::VarId;

/// Abstract values for constant propagation and partial evaluation.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum AbstractValue {
    /// Exact constant value known at analysis time.
    Constant(AbstractLiteral),

    /// Known to be a constructor with known tag but unknown fields.
    Constructor { tag: usize, arity: usize },

    /// Known to be a closure.
    Closure { params: Vec<VarId> },

    /// Known to be a thunk (delayed computation).
    Thunk,

    /// Known to be a specific builtin, possibly partially applied.
    BuiltinPartial {
        fun: DefaultFunction,
        forces: u8,
        args_given: usize,
    },

    /// Known to be a field extracted from a constructor via Case pattern matching.
    ConstructorField { tag: usize, field_index: usize },

    /// Known type but unknown value.
    Typed(AbstractType),

    /// Nothing known.
    Unknown,
}

/// Constant literals that can be determined at analysis time.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum AbstractLiteral {
    Integer(BigInt),
    ByteString(Vec<u8>),
    String(String),
    Bool(bool),
    Unit,
}

/// Abstract types for type-level reasoning.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum AbstractType {
    Int,
    ByteArray,
    String,
    Bool,
    Unit,
    Data,
    List(Box<AbstractType>),
    Pair(Box<AbstractType>, Box<AbstractType>),
    Function {
        arity: usize,
    },
    /// Concrete constructor value with known tag and arity.
    Constructor {
        tag: usize,
        arity: usize,
    },
    /// BLS12-381 G1 element.
    G1Element,
    /// BLS12-381 G2 element.
    G2Element,
    /// BLS12-381 Miller loop result.
    MillerLoopResult,
    /// Unknown type.
    Unknown,
}

impl AbstractValue {
    pub(crate) fn as_constant(&self) -> Option<&AbstractLiteral> {
        match self {
            AbstractValue::Constant(lit) => Some(lit),
            _ => None,
        }
    }

    pub(crate) fn as_bool(&self) -> Option<bool> {
        match self {
            AbstractValue::Constant(AbstractLiteral::Bool(b)) => Some(*b),
            _ => None,
        }
    }

    pub(crate) fn abstract_type(&self) -> AbstractType {
        match self {
            AbstractValue::Constant(lit) => lit.abstract_type(),
            AbstractValue::Constructor { tag, arity } => AbstractType::Constructor {
                tag: *tag,
                arity: *arity,
            },
            AbstractValue::Closure { params } => AbstractType::Function {
                arity: params.len(),
            },
            AbstractValue::Thunk => AbstractType::Unknown,
            AbstractValue::BuiltinPartial {
                fun, args_given, ..
            } => {
                // Remaining arity = total builtin arity - args already given
                let total = fun.arity();
                AbstractType::Function {
                    arity: total.saturating_sub(*args_given),
                }
            }
            AbstractValue::ConstructorField { .. } => AbstractType::Unknown,
            AbstractValue::Typed(t) => t.clone(),
            AbstractValue::Unknown => AbstractType::Unknown,
        }
    }
}

impl AbstractLiteral {
    pub(crate) fn abstract_type(&self) -> AbstractType {
        match self {
            AbstractLiteral::Integer(_) => AbstractType::Int,
            AbstractLiteral::ByteString(_) => AbstractType::ByteArray,
            AbstractLiteral::String(_) => AbstractType::String,
            AbstractLiteral::Bool(_) => AbstractType::Bool,
            AbstractLiteral::Unit => AbstractType::Unit,
        }
    }
}

impl std::fmt::Display for AbstractType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AbstractType::Int => write!(f, "Int"),
            AbstractType::ByteArray => write!(f, "ByteArray"),
            AbstractType::String => write!(f, "String"),
            AbstractType::Bool => write!(f, "Bool"),
            AbstractType::Unit => write!(f, "Void"),
            AbstractType::Data => write!(f, "Data"),
            AbstractType::List(t) => write!(f, "List<{}>", t),
            AbstractType::Pair(a, b) => write!(f, "Pair<{}, {}>", a, b),
            AbstractType::Function { arity } => write!(f, "fn/{}", arity),
            AbstractType::Constructor { tag, arity } => {
                write!(f, "Constructor(tag={}, arity={})", tag, arity)
            }
            AbstractType::G1Element => write!(f, "G1Element"),
            AbstractType::G2Element => write!(f, "G2Element"),
            AbstractType::MillerLoopResult => write!(f, "MillerLoopResult"),
            AbstractType::Unknown => write!(f, "?"),
        }
    }
}

#[cfg(test)]
mod tests;
