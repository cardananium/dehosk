//! Inline let-bound always-fail helpers — Lambdas whose body always
//! diverges: either a literal `fail @"…"` (`PseudoExpr::Error`) or a
//! `trace <param>: fail` that traces one of its parameters then fails.
//!
//! V1 scripts emit helpers whose params are wildcards, so every call
//! site evaluates to the same `fail @"…"`. PlutusTx-compiled scripts
//! instead emit a single fail-label helper that traces its argument
//! (`f_2(@"PT1")`, `f_2(@"PT2")`, …): the tail is always `fail`; only
//! the trace message varies — it is the argument. Left opaque, such a
//! call hides the divergence, and as a `when` subject it leaves an
//! empty `when x is { }`.
//!
//! If every use of the helper is a call site, the let is dropped; a
//! bare ref (the helper itself passed as a value) preserves it.
//!
//! - Body must be exactly `Error { … }` (a bare fail) or `Trace {
//!   message: <param>, value: Error { … } }` (trace-a-param then fail).
//!   Anything else wrapping the fail (Apply, a non-param trace message,
//!   …) disqualifies — the helper must *provably* diverge on every call.
//! - Bare-`Error` case: the body ignores the call args.
//! - `Trace`-param case: the message is the parameter, so the call arg
//!   is threaded into the message position. A string-literal arg over a
//!   message-less inner `fail` folds to `fail @"…"`; anything else stays
//!   as `trace arg: fail`.
//! - The substituted expression is cloned at each site.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

/// How an always-fail helper substitutes at each of its call sites.
#[derive(Clone)]
enum FailHelper {
    /// Body is exactly `fail` (`Error{..}`). Args are discarded; every
    /// call site becomes the cloned `Error`.
    Bare(PseudoExpr),
    /// Body is `trace <param_i>: fail`. The call arg at `param_index`
    /// becomes the trace message.
    TraceParam {
        /// Which parameter flows into the trace message.
        param_index: usize,
        /// The inner `fail` (`Error{..}`), cloned to the call site.
        error: PseudoExpr,
    },
}

pub(super) fn inline_always_fail_helpers(expr: PseudoExpr) -> PseudoExpr {
    InlineAlwaysFailHelpers.fold(expr)
}

struct InlineAlwaysFailHelpers;

impl ExprFolder for InlineAlwaysFailHelpers {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    // The classify-and-substitute logic only needs the already-folded
    // `value`/`body` (no state must be pushed before `body` is folded), so
    // it slots into `post_let` unchanged from the old post-order code.
    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let helper = match (&id, classify_always_fail_helper(&value)) {
            (Some(vid), Some(kind)) => Some((*vid, kind)),
            _ => None,
        };

        if let Some((helper_id, kind)) = helper {
            let (new_body, kept_bare_ref) = rewrite_uses(body, helper_id, &kind);
            if kept_bare_ref {
                return PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(new_body),
                };
            }
            // No bare refs — drop the let.
            return new_body;
        }

        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }
}

/// Classify `value` as an always-fail helper. Returns how to substitute
/// it at each call site, or `None` if the body is not provably-diverging.
fn classify_always_fail_helper(value: &PseudoExpr) -> Option<FailHelper> {
    let PseudoExpr::Lambda { params, body } = value else {
        return None;
    };
    // `fn f(_) { fail }` — bare always-fail; args discarded.
    if let PseudoExpr::Error { .. } = body.as_ref() {
        return Some(FailHelper::Bare((**body).clone()));
    }
    // `fn f(p) { trace p: fail }` — the call arg takes the param's
    // place in the trace message.
    if let PseudoExpr::Trace {
        message,
        value: inner,
    } = body.as_ref()
        && matches!(inner.as_ref(), PseudoExpr::Error { .. })
        && let PseudoExpr::Var { id: Some(mid), .. } = message.as_ref()
        && let Some(param_index) = params.iter().position(|p| p.id == *mid)
    {
        return Some(FailHelper::TraceParam {
            param_index,
            error: (**inner).clone(),
        });
    }
    None
}

/// Build the substitution for a call `helper(args)`.
fn substitute_call(kind: &FailHelper, args: &[PseudoExpr]) -> PseudoExpr {
    match kind {
        // Args discarded — the body is a constant fail.
        FailHelper::Bare(error) => error.clone(),
        FailHelper::TraceParam { param_index, error } => {
            match args.get(*param_index) {
                // Fold `trace @"lit": fail` (message-less inner fail) into
                // the idiomatic `fail @"lit"`.
                Some(PseudoExpr::String(msg))
                    if matches!(error, PseudoExpr::Error { message: None }) =>
                {
                    PseudoExpr::Error {
                        message: Some(msg.clone()),
                    }
                }
                // Non-literal arg — keep the faithful `trace arg: fail`.
                Some(arg) => PseudoExpr::Trace {
                    message: PBox::new(arg.clone()),
                    value: PBox::new(error.clone()),
                },
                // Under-applied (no arg at that position) — the trace
                // message would be lost; keep it honest as a bare fail.
                None => error.clone(),
            }
        }
    }
}

/// Walk `body`, replacing every `Apply { fn: Var(helper_id), args }` with
/// the helper's substitution. Return the new body and whether any bare
/// ref to the helper remained.
fn rewrite_uses(body: PseudoExpr, helper_id: VarId, kind: &FailHelper) -> (PseudoExpr, bool) {
    let mut substituter = SubstituteFailHelper {
        helper_id,
        kind,
        bare_ref: false,
    };
    let new_body = substituter.fold(body);
    (new_body, substituter.bare_ref)
}

struct SubstituteFailHelper<'a> {
    helper_id: VarId,
    kind: &'a FailHelper,
    bare_ref: bool,
}

impl ExprFolder for SubstituteFailHelper<'_> {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        if let PseudoExpr::Apply { function, args } = expr
            && let PseudoExpr::Var { id: Some(vid), .. } = function.as_ref()
            && *vid == self.helper_id
        {
            // Replace the whole Apply with the helper's divergent body,
            // threading the call args (used only for the trace-param case).
            return FoldAction::Replace(substitute_call(self.kind, args));
        }
        if let PseudoExpr::Var { id: Some(vid), .. } = expr
            && *vid == self.helper_id
        {
            self.bare_ref = true;
            return FoldAction::Replace(expr.clone());
        }
        FoldAction::Walk
    }
}

#[cfg(test)]
mod tests;
