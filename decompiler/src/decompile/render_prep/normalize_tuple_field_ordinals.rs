//! Rewrite numeric tuple-element selectors (`.0`, `.7`) to idiomatic
//! ordinals (`.1st`, `.8th`).
//!
//! The language's tuple access is the 1-based ordinal; a bare numeric `.0`/`.7` is
//! invalid syntax. Several paths mint numeric selectors
//! (`inline_pack_call_use_sites`, the initial tuple-unpack decode), so one
//! late pass normalizes all of them.
//!
//! Soundness: a `FieldSelector::NamedField` whose content is all-digits is
//! always a 0-based tuple element index — Pairs use `PairFst`/`PairSnd`, the
//! Constr accessor is the literal `"fields"`, `head` is `ListHead`, and
//! `field_N`/`item_N` are Var names, not selectors. Index `i` renders as
//! ordinal `i + 1`.

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::field_selector::FieldSelector;

use super::scope_recurse::rewrite_bottom_up;

/// Relabel is node-local: it reads only this node's own selector and moves
/// `record` through untouched, so running it after the children (where
/// `rewrite_bottom_up` calls back) is equivalent. An already-normalized
/// `1st` fails `is_numeric`.
pub(super) fn normalize_tuple_field_ordinals(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, relabel_selector)
}

fn relabel_selector(expr: PseudoExpr) -> PseudoExpr {
    match expr {
        PseudoExpr::FieldAccess {
            record,
            selector: FieldSelector::NamedField(n),
        } if is_numeric(&n) => {
            let idx: usize = n.parse().expect("all-digit selector parses");
            PseudoExpr::FieldAccess {
                record,
                selector: FieldSelector::NamedField(ordinal(idx)),
            }
        }
        other => other,
    }
}

fn is_numeric(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())
}

/// 0-based tuple index → surface 1-based ordinal word (`0 -> "1st"`,
/// `1 -> "2nd"`, `7 -> "8th"`), with the 11–13 exception.
fn ordinal(idx: usize) -> String {
    let n = idx + 1;
    let suffix = match (n % 10, n % 100) {
        (_, 11..=13) => "th",
        (1, _) => "st",
        (2, _) => "nd",
        (3, _) => "rd",
        _ => "th",
    };
    format!("{n}{suffix}")
}

#[cfg(test)]
mod tests;
