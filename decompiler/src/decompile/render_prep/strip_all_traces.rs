//! Opt-in: strip every trace expression (user-facing or not).
//!
//! Unlike `strip_plutustx_trace_pairs`, which strips only the
//! PlutusTx "entering/exiting" instrumentation pattern, this pass
//! removes every `Trace` / `BuiltinCall(Trace, ...)` invocation —
//! including legitimate surface `trace @"msg"` calls. Useful when
//! the log content is noise: analysis of the rendered output, or a
//! visual diff between two scripts.
//!
//! Log-dropping: traces that would have reached the validator logs
//! are silently removed, so the pass is gated behind
//! [`RenderCtx::strip_all_traces`] (`--strip-all-traces`); default off.
//!
//! Both fire unconditionally when enabled:
//! 1. `PseudoExpr::Trace { message: _, value }` → `value`.
//! 2. `BuiltinCall { name: Trace, args: [msg, ...rest] }` → `Unit`
//!    when `rest` is empty, `rest[0]` when it holds one arg, else
//!    `Apply(rest[0], rest[1..])` — the curried `trace(msg)(val)`
//!    and `trace(msg)(lam)(arg)` forms.

use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::ExprFolder;

use super::ctx::RenderCtx;

pub(super) fn strip_all_traces(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    strip_all_traces_with_enabled(expr, ctx.strip_all_traces())
}

/// Entry point with an explicit `enabled` flag, so the child `tests` mod
/// can drive the pass without building a whole [`RenderCtx`].
fn strip_all_traces_with_enabled(expr: PseudoExpr, enabled: bool) -> PseudoExpr {
    if !enabled {
        return expr;
    }
    let mut stripper = Stripper;
    stripper.fold(expr)
}

struct Stripper;

impl ExprFolder for Stripper {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_trace(&mut self, _message: PseudoExpr, value: PseudoExpr) -> PseudoExpr {
        // 2-arg PseudoExpr::Trace — drop the message, keep value.
        value
    }

    fn post_builtin_call(&mut self, name: BuiltinId, args: Vec<PseudoExpr>) -> PseudoExpr {
        if !matches!(name, BuiltinId::Trace) || args.is_empty() {
            return PseudoExpr::BuiltinCall {
                name,
                args: args.into(),
            };
        }
        // BuiltinCall(Trace, [msg, ...rest]) — drop msg, return rest
        // (re-wrapped as Apply if more than one trailing arg, since
        // Trace is eta-expanded into a curried chain).
        let mut owned = args;
        let _msg = owned.remove(0);
        match owned.len() {
            0 => PseudoExpr::Unit,
            1 => owned.pop().unwrap(),
            _ => {
                let function = owned.remove(0);
                PseudoExpr::Apply {
                    function: PBox::new(function),
                    args: owned.into(),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
