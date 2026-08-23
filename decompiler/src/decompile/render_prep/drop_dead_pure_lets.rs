//! Drop `Let { id: Some(vid), value: <pure>, body }` when vid is
//! unreferenced in body.
//!
//! All simplification is done by this point, so a `let` whose binder
//! the body never mentions is noise. Only values with no side effect
//! when evaluated may be dropped; trace/error cases stay for other
//! passes.
//!
//! Safe to drop when unused: literals (`Int`, `ByteArray`, `String`,
//! `Bool`, `Unit`); `Var`; `FieldAccess`/`IndexAccess` over a pure
//! record/collection (chooseList/headList/tailList might fail, but
//! Plutus already evaluated them when the original Var was bound);
//! `Tuple`/`List`/`Pair`/`Constr` if all components are pure;
//! `BinOp`/`UnOp` if operands are pure; `Force`/`Delay` of a pure
//! inner; `Apply` of a pure function on pure args, and `BuiltinCall`
//! with pure args other than `Trace`/`Error`; a `Lambda` whose body
//! carries no `Trace`/`Error` — a dead `fn` is never called, so the
//! only reason to keep it is a `trace`/`fail` the reader would
//! otherwise lose.
//!
//! Refuse: `Trace`, `Error`, `When`, `If`, `Let` (own body might
//! contain effects), the `Trace`/`Error` builtins, and a bare
//! `RecFn` value not wrapped in a `Lambda` — dropping a recursive
//! helper risks a use site reached by inlining/hoisting outside this
//! binding's body.
//!
//! Skips when no `decompiled` validator marker exists in the chain
//! (defence against cascade-drops that would eat the validator on
//! non-wrapped scripts).

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

pub(super) fn drop_dead_pure_lets(expr: PseudoExpr) -> PseudoExpr {
    if !contains_decompiled_marker(&expr) {
        return expr;
    }
    rewrite(expr)
}

/// Marker-ungated variant for fragment callers: a handler-body fragment
/// deliberately lacks the `decompiled` wrapper but still wants the sweep.
pub(crate) fn drop_dead_pure_lets_unchecked(expr: PseudoExpr) -> PseudoExpr {
    rewrite(expr)
}

/// The inner expression of a `WhenPattern::Literal` clause pattern, if any.
///
/// The walkers below must scan it like any other child: otherwise a binder
/// referenced ONLY from a literal pattern looks unused, and a `trace`/`fail`
/// hidden there evades the gate.
fn literal_pattern_expr(p: &WhenPattern) -> Option<&PseudoExpr> {
    match p {
        WhenPattern::Literal(e) => Some(e),
        _ => None,
    }
}

pub(super) fn contains_decompiled_marker(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Let {
                name, value, body, ..
            } => {
                if name == "decompiled" {
                    return true;
                }
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Lambda { body, .. } => pending.push(body),
            PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                pending.extend(clauses.iter().map(|c| &c.body));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            _ => {}
        }
    }
    false
}

fn rewrite(expr: PseudoExpr) -> PseudoExpr {
    struct DeadLetRewriter;
    impl ExprFolder for DeadLetRewriter {
        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            if let Some(vid) = id
                && name != "decompiled"
                && is_pure(&value)
                && !contains_var_id(&body, vid)
                && !contains_var_name(&body, &name)
            {
                return body;
            }
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }

        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            pattern
        }
    }
    DeadLetRewriter.fold(expr)
}

fn is_pure(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. } => {}
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
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
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            // `Delay` suspends: a dead binding never forces it.
            PseudoExpr::Delay(_) => {}
            // Forcing EXECUTES the suspended body: `force(delay b)` runs `b`,
            // and `force(<builtin>)` is the builtin-arity mechanism. Forcing
            // anything else runs code this pass cannot see.
            PseudoExpr::Force(inner) => match inner.as_ref() {
                PseudoExpr::Delay(body) => pending.push(body),
                _ if apply_head_is_builtin(inner) => pending.push(inner),
                _ => return false,
            },
            // Most Plutus builtins are pure; Trace (log side-effect) and Error
            // (runtime abort) are not — deleting a dead strict
            // `let x = <builtin error>` would silently un-fail the program.
            PseudoExpr::BuiltinCall { name, args } => {
                if matches!(name, crate::BuiltinId::Trace | crate::BuiltinId::Error) {
                    return false;
                }
                pending.extend(args);
            }
            // Apply: pure only when the CALLEE is a builtin (e.g. headList
            // applied to a Var). A non-builtin head — a `Var`, a lambda, a
            // helper symbol — is code this pass cannot see, and UPLC binds
            // strictly, so `let _ = f(a, b)` RUNS `f`. Calling the head pure
            // because it is a `Var` reads the wrong thing off it: a `Var` is
            // a pure value to REFERENCE, not a pure function to CALL. That
            // mistake deleted the entire body of an OpShin validator, whose
            // whole program is one discarded call to a looked-up function.
            //
            // Same rule the pipeline's dead-let gate already applies
            // (`Simplifier::contains_strict_failpoint`). Neither judges
            // BUILTIN partiality, and that is the standing boundary, not an
            // oversight: `head_list([])` does fail when strictly bound, so a
            // dead `let _ = head_list(xs)` is dropped here even though the
            // bytecode could reject on it. Deciding that needs a value proof
            // (is `xs` non-empty?) rather than a shape test, and every
            // builtin-headed decode in a PlutusTx script would otherwise be
            // retained. Move the line only with such a proof in hand.
            PseudoExpr::Apply { function, args } => {
                if !apply_head_is_builtin(function) {
                    return false;
                }
                pending.push(function);
                pending.extend(args);
            }
            // `Lambda` is pure: constructing an abstraction has no effect, and
            // the drop site fires only when the binder is unused, so the body
            // never runs — whatever it holds (`RecFn`, `If`, `When`, …). Refuse
            // only when the body carries a `trace`/`fail` the reader would lose:
            // keep `fn f() { trace @"m" … }`, drop
            // `fn match_subject_44(v) { rec fn self(x) { v(self, x) } }`.
            // A bare `RecFn` VALUE is refused below, so a recursive helper bound
            // directly to a let is left alone. No further recursion needed:
            // once the trace/error check passes, the Lambda itself is pure
            // regardless of anything else in its body.
            PseudoExpr::Lambda { body, .. } => {
                if contains_trace_or_error(body) {
                    return false;
                }
            }
            // Refuse: Trace, Error, When, If, Let, bare RecFn.
            _ => return false,
        }
    }
    true
}

/// Whether an `Apply`'s callee bottoms out in a builtin, looking through
/// the `force` wrappers and the curried spine the lowering leaves.
fn apply_head_is_builtin(function: &PseudoExpr) -> bool {
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

/// `true` if `expr` holds a `Trace` or `Error` node (either the
/// `PseudoExpr` or the `BuiltinCall` form) anywhere in its subtree — the
/// diagnostics that dropping a dead function would silently remove.
fn contains_trace_or_error(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Trace { .. } | PseudoExpr::Error { .. } => return true,
            PseudoExpr::BuiltinCall { name, args } => {
                // `fail` survives both as `PseudoExpr::Error` and as the builtin
                // form `BuiltinCall(Error)`; `trace` as `Trace`/`BuiltinCall(Trace)`.
                if matches!(name, crate::BuiltinId::Trace | crate::BuiltinId::Error) {
                    return true;
                }
                pending.extend(args);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Lambda { body, .. } => pending.push(body),
            PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for c in clauses {
                    if let Some(e) = literal_pattern_expr(&c.pattern) {
                        pending.push(e);
                    }
                    if let Some(g) = c.guard.as_ref() {
                        pending.push(g);
                    }
                    pending.push(&c.body);
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Constr { fields, .. } => pending.extend(fields),
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements);
                if let Some(t) = tail.as_deref() {
                    pending.push(t);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            _ => {}
        }
    }
    false
}

fn contains_var_id(expr: &PseudoExpr, target: VarId) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Var { id: Some(v), .. } => {
                if *v == target {
                    return true;
                }
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Lambda { body, .. } => pending.push(body),
            PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for c in clauses {
                    if let Some(e) = literal_pattern_expr(&c.pattern) {
                        pending.push(e);
                    }
                    if let Some(g) = c.guard.as_ref() {
                        pending.push(g);
                    }
                    pending.push(&c.body);
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Constr { fields, .. } => pending.extend(fields),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args),
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements);
                if let Some(t) = tail.as_deref() {
                    pending.push(t);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            _ => {}
        }
    }
    false
}

fn contains_var_name(expr: &PseudoExpr, target: &str) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(cur) = pending.pop() {
        match cur {
            PseudoExpr::Var { name, .. } => {
                if name == target {
                    return true;
                }
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Lambda { body, .. } => pending.push(body),
            PseudoExpr::RecFn { body, .. } => pending.push(body),
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args);
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                pending.push(subject);
                for c in clauses {
                    if let Some(e) = literal_pattern_expr(&c.pattern) {
                        pending.push(e);
                    }
                    if let Some(g) = c.guard.as_ref() {
                        pending.push(g);
                    }
                    pending.push(&c.body);
                }
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::Constr { fields, .. } => pending.extend(fields),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args),
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements);
                if let Some(t) = tail.as_deref() {
                    pending.push(t);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests;
