//! Line-breaking / complexity heuristics used by `pretty.rs`.
//!
//! The renderer consults these predicates when deciding whether to
//! inline a let-binding, force a multi-argument call onto separate
//! lines, or spread a `delay`/`force` body across multiple lines.

use crate::pseudo::ast::PseudoExpr;

use super::traversal::is_expect_bang;

/// True if `expr` renders as a SEQUENCE of statements — a `let …`
/// chain, an `expect …` chain, or a `seq` — not a single expression.
/// Such a value needs `{ … }` in a position requiring one expression
/// (a `let` value, a `when` subject), else the text is unparseable
/// Surface: `let c1 = expect …  when … is { … }`.
///
/// `if`/`when`/`fn`/`rec fn` are single (if multi-line) expressions,
/// legal unbraced in both positions, so they are excluded to keep
/// brace-wrapping minimal.
pub(in crate::decompile::render) fn renders_as_statement_sequence(expr: &PseudoExpr) -> bool {
    match expr {
        // `let X = v; body` — a binding followed by a continuation.
        PseudoExpr::Let { .. } => true,
        PseudoExpr::Apply { function, args } => {
            // `expect cond; body` chain — `Apply(expect!, [cond, msg?, body])`.
            // Match the renderer's arity (2 or 3) so a malformed/partial
            // `expect!` application isn't needlessly block-wrapped.
            (is_expect_bang(function.as_ref()) && (args.len() == 2 || args.len() == 3))
                // `a; b` sequencing — `Apply(seq, [a, b])`.
                || (args.len() == 2
                    && matches!(
                        function.as_ref(),
                        PseudoExpr::BuiltinCall { name, args: ba }
                            if *name == crate::BuiltinId::Seq && ba.is_empty()
                    ))
        }
        // Direct `seq` builtin form: `seq(a, b)`.
        PseudoExpr::BuiltinCall { name, args } => *name == crate::BuiltinId::Seq && args.len() == 2,
        // `delay`/`force` are transparent wrappers around the sequence.
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => renders_as_statement_sequence(inner),
        _ => false,
    }
}

pub(in crate::decompile::render) fn is_block_style_expr(expr: &PseudoExpr) -> bool {
    match expr {
        PseudoExpr::Let { .. }
        | PseudoExpr::If { .. }
        | PseudoExpr::When { .. }
        | PseudoExpr::Lambda { .. }
        | PseudoExpr::RecFn { .. }
        | PseudoExpr::Trace { .. } => true,
        PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => is_block_style_expr(inner),
        _ => false,
    }
}

pub(in crate::decompile::render) fn should_inline_let_value(expr: &PseudoExpr) -> bool {
    !is_block_style_expr(expr) && expr_complexity_for_call(expr) <= 6
}

/// Returns `true` if `expr` ultimately renders as a function value —
/// directly (`Lambda`, `RecFn`) or via a `Let` chain whose
/// terminal-evaluated form is a function. The let-renderer uses it to
/// suppress the use-site-inferred type annotation on `let X: T = …`
/// when X is bound to a function.
///
/// **Semantics.** Walks through nested `Let { id, value, body, ... }`:
///
/// - `body` is `Var(id)` for THIS let's binder: the let evaluates to
///   the value — descend into `value`.
/// - Otherwise the let evaluates to `body` — descend into `body`.
///
/// This keeps an intermediate Lambda-valued let from over-suppressing:
/// `let X = (let f = fn(...) {...} in 42)` returns `false` (X is bound
/// to 42), while the same chain ending `in f` returns `true`.
pub(in crate::decompile::render) fn value_renders_as_function(expr: &PseudoExpr) -> bool {
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => return true,
            PseudoExpr::Let {
                id: Some(let_id),
                value,
                body,
                ..
            } => {
                if let PseudoExpr::Var {
                    id: Some(body_id), ..
                } = body.as_ref()
                    && *body_id == *let_id
                {
                    current = value;
                } else {
                    current = body;
                }
            }
            PseudoExpr::Let { body, .. } => {
                // No id — can't match body=Var(let_id); just descend into body.
                current = body;
            }
            // Y-combinator application:
            // `(fn(v) { rec fn self(x) { v(self, x) } })(arg)` evaluates
            // to a function: the outer Lambda's body is a RecFn that
            // captures `arg` as the recursion driver. Only a
            // single-Lambda head qualifies (not a generic Apply chain),
            // and only one peel per Apply — recursing into the arg
            // could mislead.
            PseudoExpr::Apply { function, .. } => {
                if let PseudoExpr::Lambda { body, .. } = function.as_ref() {
                    current = body;
                } else if let PseudoExpr::Var { name, .. } = function.as_ref() {
                    // Calls to the Church-pack helpers hoisted by render-prep
                    // (`pair_pack`, `pack_N`, `church_cons`, `church_true`,
                    // `church_false`) return Lambda values. Without this
                    // by-name hint, `let x: fn(_) -> _ = pair_pack(...)` keeps
                    // its uninformative annotation — the call's result type is
                    // not visible from the Apply's structure.
                    if name == "pair_pack"
                        || name == "church_cons"
                        || name == "church_true"
                        || name == "church_false"
                        || name.starts_with("pack_")
                    {
                        return true;
                    }
                    return false;
                } else {
                    return false;
                }
            }
            // The type system makes all `when` arms share a result
            // type, so the FIRST non-fail clause decides whether the
            // `when` is function-valued; `fail`/`Error` clauses abort
            // instead of producing a value and are skipped. No
            // non-fail clause at all: not a function.
            PseudoExpr::When { clauses, .. } => {
                let first_non_fail = clauses
                    .iter()
                    .find(|c| !matches!(c.body, PseudoExpr::Error { .. }));
                let Some(c) = first_non_fail else {
                    return false;
                };
                current = &c.body;
            }
            // `if` branches agree by typing: pick whichever side is not
            // `fail`, and when neither is, the `then` branch decides.
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                let pick = if matches!(then_branch.as_ref(), PseudoExpr::Error { .. }) {
                    else_branch.as_ref()
                } else {
                    then_branch.as_ref()
                };
                current = pick;
            }
            _ => return false,
        }
    }
}

pub(in crate::decompile::render) fn should_multiline_delay_force_body(inner: &PseudoExpr) -> bool {
    is_block_style_expr(inner)
}

pub(in crate::decompile::render) fn should_force_multiline_call_args(args: &[PseudoExpr]) -> bool {
    if args.len() >= 3 {
        // Exception: if every arg is a simple identifier (Var), defer to the
        // pretty printer's width-based wrapping, so an all-Var call like
        // `x(a, b, c, d, e, f, g, h, i, j)` (a pack_N body) fits one line.
        let all_simple_vars = args.iter().all(|a| matches!(a, PseudoExpr::Var { .. }));
        if !all_simple_vars {
            return true;
        }
    }

    let total_complexity: usize = args.iter().map(expr_complexity_for_call).sum();
    let has_complex_arg = args.iter().any(|arg| {
        matches!(
            arg,
            PseudoExpr::If { .. }
                | PseudoExpr::When { .. }
                | PseudoExpr::Let { .. }
                | PseudoExpr::Trace { .. }
        ) || expr_complexity_for_call(arg) >= 8
    });

    has_complex_arg || total_complexity >= 14
}

pub(in crate::decompile::render) fn expr_complexity_for_call(expr: &PseudoExpr) -> usize {
    let mut total = 0usize;
    let mut stack = vec![expr];

    while let Some(current) = stack.pop() {
        total += 1;

        match current {
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Var { .. }
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}

            PseudoExpr::Lambda { body, .. }
            | PseudoExpr::RecFn { body, .. }
            | PseudoExpr::Delay(body)
            | PseudoExpr::Force(body)
            | PseudoExpr::UnOp { operand: body, .. }
            | PseudoExpr::FieldAccess { record: body, .. }
            | PseudoExpr::IndexAccess {
                collection: body, ..
            } => {
                stack.push(body);
            }

            PseudoExpr::Apply { function, args } => {
                stack.push(function);
                for arg in args {
                    stack.push(arg);
                }
            }

            PseudoExpr::BuiltinCall { args, .. } => {
                for arg in args {
                    stack.push(arg);
                }
            }

            PseudoExpr::Let { value, body, .. } => {
                stack.push(value);
                stack.push(body);
            }

            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                stack.push(condition);
                stack.push(then_branch);
                stack.push(else_branch);
            }

            PseudoExpr::When {
                subject, clauses, ..
            } => {
                stack.push(subject);
                for clause in clauses {
                    if let Some(guard) = &clause.guard {
                        stack.push(guard);
                    }
                    stack.push(&clause.body);
                }
            }

            PseudoExpr::List { elements, tail } => {
                for element in elements {
                    stack.push(element);
                }
                if let Some(tail_expr) = tail {
                    stack.push(tail_expr);
                }
            }

            PseudoExpr::Tuple(items) => {
                for item in items {
                    stack.push(item);
                }
            }

            PseudoExpr::Pair(a, b)
            | PseudoExpr::BinOp {
                left: a, right: b, ..
            } => {
                stack.push(a);
                stack.push(b);
            }

            PseudoExpr::Constr { fields, .. } => {
                for field in fields {
                    stack.push(field);
                }
            }

            PseudoExpr::Trace { message, value } => {
                stack.push(message);
                stack.push(value);
            }
        }
    }

    total
}

#[cfg(test)]
mod tests;
