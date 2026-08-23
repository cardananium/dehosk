//! Const-fold an `un_*_data` unwrap applied to a literal constant:
//! `builtin.un_b_data(#"ab")` → `#"ab"`, `builtin.un_i_data(42)` → `42`,
//! `builtin.un_list_data([…])` → `[…]`.
//!
//! Compile-time-applied / extracted parameters surface as concrete
//! literals. The decompiler lowers a Plutus `Data` constant
//! `(con data (B b))` to `PseudoExpr::ByteArray(b)` (and
//! `(con data (I n))` to `PseudoExpr::Int(n)`), leaving the program's
//! own `un_*_data` unwrap on top — invalid surface syntax, since
//! `un_b_data` expects `Data` but the literal already reads as a
//! `ByteArray`. The equivalent `Data(ByteString)` / `Data(Integer)`
//! form folds too, should the constant survive as a `Data` node.
//!
//! Provenance comes from the argument position, not the node shape:
//! `un_b_data` has UPLC type `Data -> ByteArray`, so whatever sits in
//! its argument slot is necessarily `Data`. A native `ByteArray`/`Int`
//! literal there can only be the decompiler's normalized rendering of
//! a `Data.B` / `Data.I` scalar constant — a genuine non-`Data` one
//! would be a type error Plutus rejects at compile time, so it cannot
//! occur in the valid on-chain scripts the decompiler consumes.
//! `un_b_data` is the left inverse of the `Data.B` injection, so
//! `un_b_data(Data.B b) == b` never fails at runtime and the folded
//! literal has the same type and value as the unwrap result.
//!
//! The list case is the same equivalence one level up. An extracted
//! parameter carrying `(con data (List […]))` renders its argument as a
//! list literal already, so the unwrap on top read as
//! `builtin.un_list_data([#"7b41…", …])` — a `Data -> List` builtin
//! handed something that already prints as a list. `un_list_data` is
//! the left inverse of the `Data.List` injection, so dropping it keeps
//! both the type and the value.
//!
//! The fold fires only on a literal argument of the matching kind. A
//! `Var`, a field/index access or another call is left untouched, so
//! genuine runtime unwraps such as `un_b_data(x_13[0])` are unaffected;
//! `un_b_data` of an `Int`/`Data(Integer)` literal (a kind mismatch)
//! likewise. A list literal with a `..tail` spread is not a constant and
//! never folds.

use crate::builtins::BuiltinId;
use crate::pseudo::ast::{PseudoData, PseudoExpr};
use num_bigint::BigInt;

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn fold_un_data_scalar_const(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_fold)
}

fn try_fold(expr: PseudoExpr) -> PseudoExpr {
    match &expr {
        PseudoExpr::BuiltinCall {
            name: BuiltinId::DataUnByteArray,
            args,
        } if args.len() == 1 => match as_bytearray_const(&args[0]) {
            Some(bytes) => PseudoExpr::ByteArray(bytes),
            None => expr,
        },
        PseudoExpr::BuiltinCall {
            name: BuiltinId::DataUnInt,
            args,
        } if args.len() == 1 => match as_int_const(&args[0]) {
            Some(n) => PseudoExpr::Int(n),
            None => expr,
        },
        PseudoExpr::BuiltinCall {
            name: BuiltinId::DataUnList,
            args,
        } if args.len() == 1 => match as_list_const(&args[0]) {
            Some(elements) => PseudoExpr::List {
                elements: elements.into(),
                tail: None,
            },
            None => expr,
        },
        _ => expr,
    }
}

/// The elements of a literal list: a native `List` with no spread and
/// only CONSTANT elements, or a `Data(List)` constant.
///
/// `tail: None` alone is not constancy — it only says there is no
/// spread. `un_list_data([x])` with `x` a binder is a runtime unwrap of
/// a runtime value, and folding it away would drop real work.
fn as_list_const(e: &PseudoExpr) -> Option<Vec<PseudoExpr>> {
    match e {
        PseudoExpr::List {
            elements,
            tail: None,
        } if elements.iter().all(is_const_element) => Some((elements.clone()).into_vec()),
        PseudoExpr::Data(d) => match d.as_ref() {
            PseudoData::List(items) => Some(
                items
                    .iter()
                    .map(|i| PseudoExpr::Data(Box::new(i.clone())))
                    .collect(),
            ),
            _ => None,
        },
        _ => None,
    }
}

/// The bytes of a literal `ByteArray` (native) or `Data(ByteString)` constant.
fn as_bytearray_const(e: &PseudoExpr) -> Option<Vec<u8>> {
    match e {
        PseudoExpr::ByteArray(b) => Some(b.clone()),
        PseudoExpr::Data(d) => match d.as_ref() {
            PseudoData::ByteString(b) => Some(b.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// A list element that is a constant: a scalar literal, a `Data` node
/// (always a constant by construction), or a nested constant list.
fn is_const_element(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::ByteArray(_)
            | PseudoExpr::Int(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Data(_) => {}
            PseudoExpr::List {
                elements,
                tail: None,
            } => pending.extend(elements.iter()),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            _ => return false,
        }
    }
    true
}

/// The value of a literal `Int` (native) or `Data(Integer)` constant.
fn as_int_const(e: &PseudoExpr) -> Option<BigInt> {
    match e {
        PseudoExpr::Int(n) => Some(n.clone()),
        PseudoExpr::Data(d) => match d.as_ref() {
            PseudoData::Integer(n) => Some(n.clone()),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests;
