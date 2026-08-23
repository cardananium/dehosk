//! Collapse `let X = trace @"msg": <pure_value>; fail` to `fail @"msg"`.
//!
//! V1 scripts emit this at every "shouldn't happen" site: an unused
//! binder whose value is `trace @"PT1": <pure>` and whose body is
//! bare `fail`. The `trace` exists only to emit the marker before
//! aborting; the compiler writes that as `fail @"PT1"` directly.
//!
//! Recurse first so an inner let ending in `fail` collapses before
//! the outer one sees a bare `Error` body.
//!
//! Fail-closed:
//! - Body is `Error { message: None }` — a bare `fail` with no
//!   message of its own.
//! - The trace's value is pure (Var, literal, Lambda, Unit);
//!   anything else could carry an observable effect this pass
//!   would drop.
//! - The message is a String literal.
//! - The binder is unused by construction: an `Error` body has no
//!   Vars.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

pub(super) fn collapse_trace_fail_let(expr: PseudoExpr) -> PseudoExpr {
    rewrite(expr)
}

// The Let case reads as "recurse first, then look at both results" — but
// that's not a between-children write, it's plain bottom-up: value and
// body are folded independently (neither's folding depends on the other's
// result), only the *node-level* collapse decision after both are done
// needs them together. `ExprFolder`'s `post_let` fires exactly there, once
// both children are already folded, so overriding it is a direct port —
// the "recurse first" comment described is just what bottom-up folding
// does automatically.
fn rewrite(expr: PseudoExpr) -> PseudoExpr {
    struct TraceFailLetCollapser;

    impl ExprFolder for TraceFailLetCollapser {
        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            if matches!(&body, PseudoExpr::Error { message: None })
                && let Some(msg) = extract_trace_msg(&value)
            {
                return PseudoExpr::Error { message: Some(msg) };
            }
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }

        fn fold_pattern(
            &mut self,
            pattern: crate::pseudo::ast::WhenPattern,
        ) -> crate::pseudo::ast::WhenPattern {
            // Original never touches a pattern, so this stays the identity
            // — deliberately not the trait's default, which folds a
            // `Literal` pattern's expression.
            pattern
        }
    }

    TraceFailLetCollapser.fold(expr)
}

/// Extract a String trace-message from `expr` when `expr` fires
/// exactly one trace and then evaluates to a pure result. Two
/// shapes:
///
/// 1. `Trace { message: String(s), value: <pure> }` — direct.
/// 2. `Apply { function: Trace { message: String(s), value: <pure_fn> }, args: [<pure_args>] }`
///    — Trace in the Apply head; renders as `trace @"s": <fn>(<args>)`.
///
/// Dropping the trailing pure computation is safe when the binder
/// is unused and the body is bare `fail`: the log effect survives.
fn extract_trace_msg(expr: &PseudoExpr) -> Option<String> {
    match expr {
        PseudoExpr::Trace { message, value } => {
            if let PseudoExpr::String(s) = message.as_ref() {
                if is_pure(value) {
                    return Some(s.clone());
                }
            }
            None
        }
        PseudoExpr::Apply { function, args } => {
            if let PseudoExpr::Trace { message, value } = function.as_ref() {
                if let PseudoExpr::String(s) = message.as_ref() {
                    if is_pure(value) && args.iter().all(is_pure) {
                        return Some(s.clone());
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Pure values whose evaluation has no observable side effect:
/// literals, Var refs, and function abstractions.
///
/// `Apply` is pure only when the CALLEE is a builtin. A `Var` callee is
/// unknown code — a `Var` is a pure value to REFERENCE, not a pure
/// function to CALL — and UPLC binds strictly, so the discarded value
/// really does run. Same rule as
/// `Simplifier::contains_strict_failpoint` and the sibling
/// `drop_dead_pure_lets`; builtin partiality is judged by none of them.
///
/// What is at stake here is narrower than at those two sites: this
/// pass only fires when the body is a bare `fail`, so the program
/// aborts either way and no rejection can be lost — only trace output
/// the dropped call would have emitted first. That is still a real
/// loss, and the rule costs nothing to get right.
///
/// `Force` executes what it forces: `force(delay b)` runs `b`, and
/// `force(<builtin>)` is the builtin-arity mechanism. Forcing anything
/// else runs code this pass cannot see.
fn is_pure(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Lambda { .. }
            | PseudoExpr::RecFn { .. } => {}
            PseudoExpr::Apply { function, args } => {
                if !head_is_builtin(function) {
                    return false;
                }
                pending.extend(args.iter());
            }
            PseudoExpr::Force(inner) => match inner.as_ref() {
                PseudoExpr::Delay(body) => pending.push(body),
                _ if head_is_builtin(inner) => pending.push(inner),
                _ => return false,
            },
            _ => return false,
        }
    }
    true
}

/// Whether a callee bottoms out in a builtin, through the `force`
/// wrappers and the curried spine the lowering leaves.
fn head_is_builtin(function: &PseudoExpr) -> bool {
    let mut current = function;
    loop {
        match current {
            PseudoExpr::BuiltinCall { .. } => return true,
            PseudoExpr::Force(inner) => current = inner,
            PseudoExpr::Apply { function, .. } => current = function,
            _ => return false,
        }
    }
}

#[cfg(test)]
mod tests;
