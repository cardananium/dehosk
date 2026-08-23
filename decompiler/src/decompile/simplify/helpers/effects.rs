use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

use super::Simplifier;

/// `replace_void_markers`'s `ExprFolder`: swaps a `__VOID__`-named `Var` for
/// `Unit`. Does not descend into `FieldAccess`/`IndexAccess`/`Tuple` — see
/// the `pre_expr`/`fold_pattern` overrides below.
struct ReplaceVoidMarkers;

impl ExprFolder for ReplaceVoidMarkers {
    // Leave `FieldAccess`/`IndexAccess`/`Tuple` untouched: the default walk
    // would otherwise descend into them and silently widen what gets rewritten.
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        match expr {
            PseudoExpr::FieldAccess { .. }
            | PseudoExpr::IndexAccess { .. }
            | PseudoExpr::Tuple(_) => FoldAction::Replace(expr.clone()),
            _ => FoldAction::Walk,
        }
    }

    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        if name == "__VOID__" {
            PseudoExpr::Unit
        } else {
            PseudoExpr::Var { name, id }
        }
    }

    // Same reasoning as `pre_expr` above: the old recursion walked a `when`
    // clause's guard/body but never its pattern, so a `__VOID__` sitting
    // inside a `Literal` pattern must stay untouched.
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }
}

impl Simplifier {
    /// Extract side effects from a let chain that ends with Void.
    /// Pattern: let x = { let y = trace f; g; Void } -> Some(trace f)
    pub(crate) fn extract_side_effects_before_void(expr: &PseudoExpr) -> Option<Vec<PseudoExpr>> {
        enum Frame<'a> {
            Let(&'a PseudoExpr),   // the bound `value`
            Trace(&'a PseudoExpr), // the `message`
        }

        let mut frames: Vec<Frame> = Vec::new();
        let mut current = expr;
        let mut result: Option<Vec<PseudoExpr>> = loop {
            match current {
                // Direct Void - no side effects
                PseudoExpr::Unit => break Some(vec![]),
                PseudoExpr::Constr { shape, fields, .. }
                    if *shape == ConstructorShape::Known(KnownConstructor::Void)
                        && fields.is_empty() =>
                {
                    break Some(vec![]);
                }
                PseudoExpr::Let { value, body, .. } => {
                    frames.push(Frame::Let(value));
                    current = body;
                }
                PseudoExpr::Trace { message, value } => {
                    frames.push(Frame::Trace(message));
                    current = value;
                }
                _ => break None,
            }
        };

        for frame in frames.into_iter().rev() {
            result = match frame {
                // Extract from `value` only when `body` itself ends with Void.
                Frame::Let(value) => result.and_then(|mut effects| {
                    Self::extract_trace_side_effect(value).map(|value_effects| {
                        let mut all_effects = value_effects;
                        all_effects.append(&mut effects);
                        all_effects
                    })
                }),
                // Trace is a side effect
                Frame::Trace(message) => {
                    let mut effects = vec![PseudoExpr::Trace {
                        message: PBox::new(message.clone()),
                        value: PBox::new(PseudoExpr::Unit),
                    }];
                    if let Some(mut more_effects) = result {
                        effects.append(&mut more_effects);
                    }
                    Some(effects)
                }
            };
        }

        result
    }

    /// Lift a top-level `Trace` into a standalone message-only effect.
    pub(crate) fn extract_trace_side_effect(expr: &PseudoExpr) -> Option<Vec<PseudoExpr>> {
        match expr {
            PseudoExpr::Trace { message, .. } => Some(vec![PseudoExpr::Trace {
                message: message.clone(),
                value: PBox::new(PseudoExpr::Unit),
            }]),
            _ => None,
        }
    }

    /// Create a sequence of side effects followed by fail
    pub(crate) fn sequence_before_fail(
        effects: Vec<PseudoExpr>,
        fail_expr: PseudoExpr,
    ) -> PseudoExpr {
        if effects.is_empty() {
            return fail_expr;
        }

        // `Trace` sequences: `trace msg; value` evaluates `msg` then `value`,
        // so folding the effects in reverse nests them ahead of `fail`.
        let mut result = fail_expr;
        for effect in effects.into_iter().rev() {
            if let PseudoExpr::Trace { message, .. } = effect {
                result = PseudoExpr::Trace {
                    message,
                    value: PBox::new(result),
                };
            }
        }
        result
    }

    /// Replace __VOID__ marker variables with actual Unit expressions.
    pub(crate) fn replace_void_markers(expr: PseudoExpr) -> PseudoExpr {
        ReplaceVoidMarkers.fold(expr)
    }

    /// Check if an expression is side-effect-free for the purposes of
    /// dropping a redundant `if cond { x } else { x }` -> `x`.
    pub(crate) fn is_side_effect_free_if_condition(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Var { .. }
                | PseudoExpr::Bool(_)
                | PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Unit => {}
                PseudoExpr::UnOp { operand, .. } => pending.push(operand),
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(left);
                    pending.push(right);
                }
                PseudoExpr::FieldAccess { record, .. } => pending.push(record),
                PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
                _ => return false,
            }
        }
        true
    }

    /// True when the expression contains a literal `Error` that dropping the
    /// binding would lose. Narrow by design: it vetoes only `let x = error in
    /// body` and Errors nested in strictly-evaluated wrappers, leaving
    /// dead-let elimination permissive elsewhere.
    pub(crate) fn contains_explicit_error(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                // Direct failure
                PseudoExpr::Error { .. } => return true,
                // Wrappers whose contents the strict let-binding would evaluate.
                PseudoExpr::Trace { message, value } => {
                    pending.push(message);
                    pending.push(value);
                }
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(value);
                    pending.push(body);
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
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    pending.push(subject);
                    pending.extend(clauses.iter().map(|c| &c.body));
                }
                PseudoExpr::Apply { function, args } => {
                    pending.push(function);
                    pending.extend(args.iter());
                }
                PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(left);
                    pending.push(right);
                }
                PseudoExpr::UnOp { operand, .. } => pending.push(operand),
                PseudoExpr::FieldAccess { record, .. } => pending.push(record),
                PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
                PseudoExpr::Force(inner) => pending.push(inner),
                // Delay suspends its body: an unforced error never fires, and a dead let
                // is never forced.
                PseudoExpr::Delay(_) => {}
                // Lambda/RecFn bodies run only on call, not on the strict bind.
                PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => {}
                // Constructors / tuples / lists / pairs: errors in fields are evaluated strictly
                PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
                PseudoExpr::Tuple(items) => pending.extend(items.iter()),
                PseudoExpr::Pair(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                PseudoExpr::List { elements, tail } => {
                    pending.extend(elements.iter());
                    if let Some(tail) = tail.as_deref() {
                        pending.push(tail);
                    }
                }
                // Leaf values - no Error
                PseudoExpr::Var { .. }
                | PseudoExpr::Bool(_)
                | PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
                | PseudoExpr::Raw { .. }
                | PseudoExpr::HelperSymbol(_) => {}
            }
        }
        false
    }

    /// Strict-evaluation failpoint scan for dead-let elimination.
    ///
    /// UPLC binds strictly: `[(lam x body) value]` evaluates `value` even
    /// when `x` is unused, so dropping a `value` that can FAIL makes the
    /// render ACCEPT inputs the bytecode REJECTS. `contains_explicit_error`
    /// catches only a literal `Error`, missing a non-builtin call in strict
    /// position — a helper call, `expect!(...)`, a beta-redex — that fails
    /// at runtime with no `Error` in the tree.
    ///
    /// A strict superset of `contains_explicit_error`: it additionally
    /// treats any **non-builtin-headed `Apply` in strict position** as a
    /// potential failpoint. It deliberately does NOT judge builtin
    /// partiality (`headList []` fails); a builtin-headed apply recurses
    /// into its arguments only. Retention is always sound — it can only
    /// keep a side effect that turns out absent — and costs at most one
    /// extra anonymous `let _ =`.
    pub(crate) fn contains_strict_failpoint(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                // Direct failure.
                PseudoExpr::Error { .. } => return true,
                PseudoExpr::Apply { function, args } => {
                    // A non-builtin callee (Var/Lambda/RecFn/HelperSymbol head)
                    // applied in strict position is a potential failpoint; a
                    // builtin callee counts as total, so recurse into the spine
                    // and args instead of flagging the apply.
                    if !Self::apply_head_is_builtin(function) {
                        return true;
                    }
                    pending.push(function);
                    pending.extend(args.iter());
                }
                // Same strict-position recursion shape as contains_explicit_error.
                PseudoExpr::Trace { message, value } => {
                    pending.push(message);
                    pending.push(value);
                }
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(value);
                    pending.push(body);
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
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    pending.push(subject);
                    pending.extend(clauses.iter().map(|c| &c.body));
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(left);
                    pending.push(right);
                }
                PseudoExpr::UnOp { operand, .. } => pending.push(operand),
                PseudoExpr::FieldAccess { record, .. } => pending.push(record),
                PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
                // Forcing EXECUTES the suspended body strictly: `force(delay b)`
                // runs `b`; `force(<builtin>)` is the builtin-arity mechanism,
                // total but with strict operands. Forcing anything else
                // (`force(var)`, `force(helper)`) runs unknown code that can
                // fail → retain.
                PseudoExpr::Force(inner) => match inner.as_ref() {
                    PseudoExpr::Delay(body) => pending.push(body),
                    _ if Self::apply_head_is_builtin(inner) => pending.push(inner),
                    _ => return true,
                },
                // Suspended: only runs when forced/called, not by the let's bind.
                PseudoExpr::Delay(_) | PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => {}
                // Strict aggregate positions.
                PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
                PseudoExpr::Tuple(items) => pending.extend(items.iter()),
                PseudoExpr::Pair(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                PseudoExpr::List { elements, tail } => {
                    pending.extend(elements.iter());
                    if let Some(tail) = tail.as_deref() {
                        pending.push(tail);
                    }
                }
                // A builtin call's operands are strict — a non-builtin failpoint
                // can hide in one — but the builtin itself counts as total.
                PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
                // Raw is opaque, undecompiled UPLC that may hide an error or a
                // user call; retain-on-doubt keeps the binding, which also keeps
                // the only trace of an unrecognized region.
                PseudoExpr::Raw { .. } => return true,
                // Leaves — a bare Var/HelperSymbol is a VALUE (not a call/force).
                PseudoExpr::Var { .. }
                | PseudoExpr::Bool(_)
                | PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
                | PseudoExpr::HelperSymbol(_) => {}
            }
        }
        false
    }

    /// True iff an apply-spine's head resolves to a `BuiltinCall`, peeling
    /// the curried `Apply` spine and any `Force` wrappers (as in
    /// `(force choose_list)(xs)`). `Delay` is NOT peeled: a delayed value
    /// cannot be applied before being forced, so a head under a bare
    /// `Delay` is degenerate — non-builtin, retain-on-doubt.
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

    /// True when the expression holds a `Trace` whose log-message side
    /// effect would vanish with the enclosing unused let-binding.
    ///
    /// Mirrors `contains_explicit_error`, including its evaluation-order
    /// assumptions: Delay/Lambda/RecFn suspend their body, so traces inside
    /// them are not triggered by the let's strict evaluation.
    pub(crate) fn contains_explicit_trace(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Trace { .. } => return true,
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(value);
                    pending.push(body);
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
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    pending.push(subject);
                    pending.extend(clauses.iter().map(|c| &c.body));
                }
                PseudoExpr::Apply { function, args } => {
                    pending.push(function);
                    pending.extend(args.iter());
                }
                PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(left);
                    pending.push(right);
                }
                PseudoExpr::UnOp { operand, .. } => pending.push(operand),
                PseudoExpr::FieldAccess { record, .. } => pending.push(record),
                PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
                PseudoExpr::Force(inner) => pending.push(inner),
                PseudoExpr::Delay(_) => {}
                PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => {}
                PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
                PseudoExpr::Tuple(items) => pending.extend(items.iter()),
                PseudoExpr::Pair(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                PseudoExpr::List { elements, tail } => {
                    pending.extend(elements.iter());
                    if let Some(tail) = tail.as_deref() {
                        pending.push(tail);
                    }
                }
                PseudoExpr::Var { .. }
                | PseudoExpr::Bool(_)
                | PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
                | PseudoExpr::Error { .. }
                | PseudoExpr::Raw { .. }
                | PseudoExpr::HelperSymbol(_) => {}
            }
        }
        false
    }
}
