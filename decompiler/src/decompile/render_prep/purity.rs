//! Shared purity predicate used by render-prep passes that discard
//! sub-expressions (`church_pair_collapse`, `slice_chain`).
//!
//! A value is **pure** when discarding it doesn't change observable
//! behavior — no force, no allocation, no traces, no side effects,
//! no aborts.
//!
//! The simplifier's synthetic abort sentinel `Var{name:"expect!",
//! id:None}` evaluates to a runtime abort, so it is not pure despite
//! its Var surface shape: without the exception `[expect!, b][1]`
//! could fold to `b` and drop the abort.

use crate::pseudo::ast::PseudoExpr;

/// Returns `true` when `expr` is a pure value: discarding it has no
/// observable evaluation effect.
///
/// Pure: literals; `Var` references EXCEPT the synthetic abort
/// sentinel `Var{name:"expect!", id:None}`; `Lambda`/`RecFn` (UPLC
/// first-class values, body deferred); `Pair`, `Tuple`, `List`,
/// `Constr` iff all components are pure. Everything else refuses.
pub(super) fn is_pure_value(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            // Literals: always pure.
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit => {}
            // Var references: pure — the binding was evaluated before
            // entering the environment. EXCEPT the synthetic abort
            // sentinel: evaluating it aborts the script, so dropping
            // it would lose an observable abort.
            PseudoExpr::Var { name, id: None } if name.as_str() == "expect!" => return false,
            PseudoExpr::Var { .. } => {}
            // Lambda as a value (NOT applied): pure — UPLC lambda is a
            // first-class value, body isn't evaluated until application.
            PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => {}
            // Aggregate values: pure iff all components are pure.
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Tuple(items) => pending.extend(items),
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements);
                if let Some(t) = tail.as_deref() {
                    pending.push(t);
                }
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields),
            // Conservative reject: anything else may evaluate, allocate,
            // throw, or trace.
            PseudoExpr::Apply { .. }
            | PseudoExpr::BuiltinCall { .. }
            | PseudoExpr::Force(_)
            | PseudoExpr::Delay(_)
            | PseudoExpr::Trace { .. }
            | PseudoExpr::Let { .. }
            | PseudoExpr::If { .. }
            | PseudoExpr::When { .. }
            | PseudoExpr::FieldAccess { .. }
            | PseudoExpr::IndexAccess { .. }
            | PseudoExpr::BinOp { .. }
            | PseudoExpr::UnOp { .. }
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests;
