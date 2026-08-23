//! Strip PlutusTx "entering/exiting" trace-pair instrumentation.
//!
//! PlutusTx wraps nearly every call in `trace("entering fooBar",
//! fn(_) { trace("exiting fooBar", body, _) }, _)`, which decompiles
//! to a 3-arg `BuiltinCall { name: Trace, args: [msg, lam, _] }`
//! whose `lam` is `Lambda { params: [_], body }`. The trace is a
//! side-effect-only logging hook and the computed value is the
//! lambda body, so the whole call is replaced by that body.
//!
//! The match is this specific PlutusTx shape, not generic `trace` —
//! scripts use traces for user-facing logging and must keep them.
//! All four gates are required: (1) `BuiltinCall` Trace with
//! `args.len() >= 3` — the curried `trace(msg)(lam)(unit)` shape,
//! which the 2-arg `trace(msg, val)` cannot match. A 4+-arg form is
//! a flattened Apply chain whose CPS continuation took further
//! runtime args (`trace(msg, lam, Void, x, y)` = `lam(Void)(x)(y)`);
//! that residual Apply is rebuilt after the strip. (2) `args[0]` is
//! a `String` starting with `"entering "`, the instrumentation
//! prefix that compiler never emits. (3) `args[1]` is a `Lambda`
//! with exactly one param whose display name starts with `"_"`
//! (PlutusTx unused-arg convention, typically `"__N"`), and whose
//! body does not free-reference that param's VarId — that is what
//! makes dropping `args[2]` sound. (4) `args[2]` is exactly
//! `PseudoExpr::Unit` (`Void`), so nothing carrying side effects
//! (`trace`, `error`) is discarded. The call then becomes
//! `lambda_body`, minus a head `Trace` whose message is
//! `"exiting <same X>"` — that pairing rules out a user-trace whose
//! message merely starts with `"exiting "`. Idempotent.

use crate::builtins::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

const ENTERING_PREFIX: &str = "entering ";
const EXITING_PREFIX: &str = "exiting ";

/// True if any descendant `Var { id: Some(target) }` references
/// the binder. Gates the trace-pair strip: replacing the lambda
/// with its body would turn such a reference into a free variable.
fn body_references_var(expr: &PseudoExpr, target: VarId) -> bool {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Var { id: Some(id), .. } => {
                if *id == target {
                    return true;
                }
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                    if let Some(g) = c.guard.as_ref() {
                        pending.push(g);
                    }
                }
                pending.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail.as_ref() {
                    pending.push(t);
                }
                for e in elements.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Tuple(items) => {
                for e in items.iter().rev() {
                    pending.push(e);
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push(f);
                }
            }
            // Leaves
            PseudoExpr::Var { id: None, .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
    false
}

/// Returns the identifier portion of a PlutusTx instrumentation
/// message — e.g. `"entering fooBar"` returns `"fooBar"`.
fn instrumentation_identifier<'a>(msg: &'a str, prefix: &str) -> Option<&'a str> {
    msg.strip_prefix(prefix)
}

pub(super) fn strip_plutustx_trace_pairs(expr: PseudoExpr) -> PseudoExpr {
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
    fn post_builtin_call(&mut self, name: BuiltinId, args: Vec<PseudoExpr>) -> PseudoExpr {
        // Gate 1: builtin must be Trace, with at least 3 args.
        if !matches!(name, BuiltinId::Trace) || args.len() < 3 {
            return PseudoExpr::BuiltinCall {
                name,
                args: args.into(),
            };
        }
        // Gate 2: args[0] is a String starting with "entering "; the
        // identifier after the prefix match-pairs against the inner
        // exit-trace.
        let enter_ident = match &args[0] {
            PseudoExpr::String(s) => match instrumentation_identifier(s, ENTERING_PREFIX) {
                Some(ident) => ident.to_string(),
                None => {
                    return PseudoExpr::BuiltinCall {
                        name,
                        args: args.into(),
                    };
                }
            },
            _ => {
                return PseudoExpr::BuiltinCall {
                    name,
                    args: args.into(),
                };
            }
        };
        // Gate 3: args[1] must be a Lambda with a single param whose
        // display name starts with `_` AND whose body does NOT
        // free-reference that param's VarId.
        let lam_ok = match &args[1] {
            PseudoExpr::Lambda { params, body }
                if params.len() == 1 && params[0].as_str().starts_with('_') =>
            {
                let param_id = params[0].var_id();
                !body_references_var(body, param_id)
            }
            _ => false,
        };
        if !lam_ok {
            return PseudoExpr::BuiltinCall {
                name,
                args: args.into(),
            };
        }
        // Gate 4: args[2] must be exactly `Unit` (`Void`) — refuse to
        // drop arbitrary side-effecting expressions.
        if !matches!(&args[2], PseudoExpr::Unit) {
            return PseudoExpr::BuiltinCall {
                name,
                args: args.into(),
            };
        }
        // All gates passed — take the lambda's body, dropping a head
        // `Trace` whose message is `"exiting <same ident>"` — the
        // pairing rules out an user-facing
        // `trace @"exiting foo"`.
        let mut owned = args;
        // Split off any trailing args (args[3..]) — these get re-Applied
        // to the stripped body to preserve the original Apply chain.
        let trailing_args: Vec<PseudoExpr> = if owned.len() > 3 {
            owned.split_off(3)
        } else {
            Vec::new()
        };
        // Drop args[2] (the Unit) from the tail; remove args[1] (lam).
        let _unit_arg = owned.swap_remove(2);
        let lam = owned.swap_remove(1);
        let PseudoExpr::Lambda { body, .. } = lam else {
            unreachable!("lam_ok matched, but extraction expected Lambda")
        };
        let body_expr = body.into_inner();
        // Try to strip the matching inner exit-trace.
        let stripped_body = if let PseudoExpr::Trace {
            message: ref inner_msg,
            value: ref inner_value,
        } = body_expr
            && let PseudoExpr::String(ref s) = **inner_msg
            && let Some(exit_ident) = instrumentation_identifier(s, EXITING_PREFIX)
            && exit_ident == enter_ident.as_str()
        {
            (**inner_value).clone()
        } else {
            body_expr
        };
        // If there were trailing args, rebuild Apply(stripped_body, trailing_args).
        if trailing_args.is_empty() {
            stripped_body
        } else {
            PseudoExpr::Apply {
                function: PBox::new(stripped_body),
                args: trailing_args.into(),
            }
        }
    }
}

#[cfg(test)]
mod tests;
