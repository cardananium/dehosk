//! Drop redundant `list_data` round-trips on both sides of an equality:
//! `builtin.list_data(a) == builtin.list_data(b)` → `a == b` (and the same
//! for `!=`).
//!
//! `DataList` (`list_data`) is the injective, deterministic `List<Data> -> Data`
//! encoder, so `list_data(a) == list_data(b)` holds iff `a == b`. Dropping both
//! wrappers is semantics-preserving and yields the native structural comparison.
//!
//! Only the symmetric both-`list_data` form is folded. A one-sided
//! `x == list_data(b)` (where `x` is already `Data`) is a genuine `Data`
//! comparison — unwrapping one side would compare a `Data` against a
//! `List<Data>`. The `… == []` empty-list form is likewise not both-`list_data`
//! and is left alone.

use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr};

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn fold_data_eq_roundtrip(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_rewrite)
}

fn try_rewrite(expr: PseudoExpr) -> PseudoExpr {
    match expr {
        PseudoExpr::BinOp { op, left, right }
            if matches!(op, BinaryOp::Eq | BinaryOp::Neq)
                && is_list_data(&left)
                && is_list_data(&right) =>
        {
            PseudoExpr::BinOp {
                op,
                left: PBox::new(unwrap_list_data(left.into_inner())),
                right: PBox::new(unwrap_list_data(right.into_inner())),
            }
        }
        other => other,
    }
}

/// `builtin.list_data(<single arg>)`.
fn is_list_data(e: &PseudoExpr) -> bool {
    matches!(
        e,
        PseudoExpr::BuiltinCall { name: BuiltinId::DataList, args } if args.len() == 1
    )
}

fn unwrap_list_data(e: PseudoExpr) -> PseudoExpr {
    if let PseudoExpr::BuiltinCall {
        name: BuiltinId::DataList,
        mut args,
    } = e
    {
        args.pop().expect("checked len == 1")
    } else {
        e
    }
}

#[cfg(test)]
mod tests;
