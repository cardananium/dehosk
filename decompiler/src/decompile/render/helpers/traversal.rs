//! Chain flattening and self-reference analysis helpers.
//!
//! These traverse `PseudoExpr` shapes to expose flat views of common
//! nested patterns (if-else-if chains, seq chains, expect!-chains,
//! List.tail chains, logical chains, nested lets) so the renderer in
//! `pretty.rs` can emit them as multi-line blocks instead of deeply
//! nested expressions. `expr_has_obvious_self_root_reference` is the
//! readability guard used when flattening let-bindings.

use crate::pseudo::ast::{BinaryOp, PseudoExpr, WhenPattern};
use crate::pseudo::var_id::VarId;

pub(in crate::decompile::render) fn flatten_if_chain<'a>(
    condition: &'a PseudoExpr,
    then_branch: &'a PseudoExpr,
    else_branch: &'a PseudoExpr,
) -> (Vec<(&'a PseudoExpr, &'a PseudoExpr)>, &'a PseudoExpr) {
    let mut branches = vec![(condition, then_branch)];
    let mut final_else = else_branch;
    while let PseudoExpr::If {
        condition: next_cond,
        then_branch: next_then,
        else_branch: next_else,
    } = final_else
    {
        branches.push((next_cond.as_ref(), next_then.as_ref()));
        final_else = next_else.as_ref();
    }

    (branches, final_else)
}

/// Detect obvious "self-root" shapes like:
/// `x`
/// `x[0]`
/// `x.fst`
/// `force(x)`
/// `x(...)`
///
/// A narrow readability guard for let-flattening — it avoids emitting
/// bindings that look directly self-referential.
pub(in crate::decompile::render) fn expr_has_obvious_self_root_reference(
    expr: &PseudoExpr,
    target: &str,
) -> bool {
    match expr {
        PseudoExpr::Var { name, .. } => name == target,
        PseudoExpr::Let {
            name, value, body, ..
        } => {
            expr_has_obvious_self_root_reference(value, target)
                || (name != target && expr_has_obvious_self_root_reference(body, target))
        }
        PseudoExpr::Lambda { params, body } => {
            !params.iter().any(|param| param == target)
                && expr_has_obvious_self_root_reference(body, target)
        }
        PseudoExpr::RecFn {
            name, params, body, ..
        } => {
            name != target
                && !params.iter().any(|param| param == target)
                && expr_has_obvious_self_root_reference(body, target)
        }
        PseudoExpr::Apply { function, args } => {
            expr_has_obvious_self_root_reference(function, target)
                || args
                    .iter()
                    .any(|arg| expr_has_obvious_self_root_reference(arg, target))
        }
        PseudoExpr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expr_has_obvious_self_root_reference(condition, target)
                || expr_has_obvious_self_root_reference(then_branch, target)
                || expr_has_obvious_self_root_reference(else_branch, target)
        }
        PseudoExpr::When {
            subject, clauses, ..
        } => {
            expr_has_obvious_self_root_reference(subject, target)
                || clauses.iter().any(|clause| {
                    !pattern_binds_var(&clause.pattern, target)
                        && clause.guard.as_ref().is_some_and(|guard| {
                            expr_has_obvious_self_root_reference(guard, target)
                        })
                        || !pattern_binds_var(&clause.pattern, target)
                            && expr_has_obvious_self_root_reference(&clause.body, target)
                })
        }
        PseudoExpr::FieldAccess { record, .. } => {
            expr_has_obvious_self_root_reference(record, target)
        }
        PseudoExpr::IndexAccess { collection, .. } => {
            expr_has_obvious_self_root_reference(collection, target)
        }
        PseudoExpr::Force(inner)
        | PseudoExpr::Delay(inner)
        | PseudoExpr::UnOp { operand: inner, .. } => {
            expr_has_obvious_self_root_reference(inner, target)
        }
        PseudoExpr::BinOp { left, right, .. } => {
            expr_has_obvious_self_root_reference(left, target)
                || expr_has_obvious_self_root_reference(right, target)
        }
        PseudoExpr::Trace { message, value } => {
            expr_has_obvious_self_root_reference(message, target)
                || expr_has_obvious_self_root_reference(value, target)
        }
        PseudoExpr::List { elements, tail } => {
            elements
                .iter()
                .any(|element| expr_has_obvious_self_root_reference(element, target))
                || tail
                    .as_ref()
                    .is_some_and(|tail| expr_has_obvious_self_root_reference(tail, target))
        }
        PseudoExpr::Tuple(elements) => elements
            .iter()
            .any(|element| expr_has_obvious_self_root_reference(element, target)),
        PseudoExpr::Pair(first, second) => {
            expr_has_obvious_self_root_reference(first, target)
                || expr_has_obvious_self_root_reference(second, target)
        }
        PseudoExpr::Constr { fields, .. } => fields
            .iter()
            .any(|field| expr_has_obvious_self_root_reference(field, target)),
        PseudoExpr::BuiltinCall { args, .. } => args
            .iter()
            .any(|arg| expr_has_obvious_self_root_reference(arg, target)),
        _ => false,
    }
}

pub(in crate::decompile::render) fn pattern_binds_var(pattern: &WhenPattern, target: &str) -> bool {
    match pattern {
        WhenPattern::Var(name) => name == target,
        WhenPattern::List { elements, tail } => {
            elements.iter().any(|element| element == target)
                || tail.as_ref().is_some_and(|tail| tail == target)
        }
        WhenPattern::Tuple(elements) => elements.iter().any(|element| element == target),
        WhenPattern::Pair(first, second) => first == target || second == target,
        WhenPattern::Constructor { fields, .. } => fields.iter().any(|field| field == target),
        WhenPattern::Literal(_) | WhenPattern::Wildcard => false,
    }
}

/// Collect nested Let bindings from a value expression for flattening.
///
/// `Let { b, Let { c, E, D }, F }` collects
///   bindings = [(c, id_c, E), (b, id_b, D)]
/// and returns F. Unwraps Let in the value position, stopping at
/// Lambda/RecFn values (custom rendering) or where flattening would
/// produce self-referential bindings (`let x = x[...]`).
pub(in crate::decompile::render) fn collect_nested_let_bindings<'a>(
    expr: &'a PseudoExpr,
    bindings: &mut Vec<(&'a str, VarId, &'a PseudoExpr)>,
) -> &'a PseudoExpr {
    let mut chain: Vec<(&'a str, VarId, &'a PseudoExpr)> = Vec::new();

    let mut current = expr;
    loop {
        let PseudoExpr::Let {
            name: inner_name,
            id: inner_id,
            value: inner_value,
            body: inner_body,
        } = current
        else {
            break;
        };

        // Keep lambda/rec-fn lets intact because they use custom rendering.
        let is_special = matches!(
            inner_value.as_ref(),
            PseudoExpr::RecFn { name: fn_name, .. }
                if fn_name == inner_name
        ) || matches!(inner_value.as_ref(), PseudoExpr::Lambda { .. });

        if is_special {
            break;
        }

        // Unresolved (compat) Lets carry `id: None`; synthesize a fresh
        // compat placeholder so type-resolution sites consuming the
        // binding tuple still get an id.
        let resolved_id = inner_id.unwrap_or_else(VarId::fresh_compat_placeholder);
        chain.push((inner_name.as_str(), resolved_id, inner_body.as_ref()));
        current = inner_value.as_ref();
    }

    // Build the flattened bindings in a temporary buffer: if any would
    // become syntactically self-referential, keep the nested structure.
    let mut resolved = current;
    let mut computed: Vec<(&'a str, VarId, &'a PseudoExpr)> = Vec::with_capacity(chain.len());

    for (name, var_id, body) in chain.iter().rev() {
        if expr_has_obvious_self_root_reference(resolved, name) {
            return expr;
        }
        computed.push((*name, *var_id, resolved));
        resolved = *body;
    }

    bindings.extend(computed);
    resolved
}

/// Collect a chain of nested `seq` calls into a flat list of statements:
/// `seq(A, seq(B, seq(C, D)))` becomes `[A, B, C, D]`.
///
/// Both spellings count: `BuiltinCall("seq", [A, B])` and
/// `Apply(BuiltinCall("seq", []), [A, B])`.
pub(in crate::decompile::render) fn collect_seq_chain(expr: &PseudoExpr) -> Vec<&PseudoExpr> {
    let mut stmts = Vec::new();
    let mut current = expr;
    loop {
        match current {
            // Direct form: BuiltinCall("seq", [A, B])
            PseudoExpr::BuiltinCall { name, args }
                if *name == crate::BuiltinId::Seq && args.len() == 2 =>
            {
                stmts.push(&args[0]);
                current = &args[1];
            }
            // Apply form: Apply(BuiltinCall("seq", []), [A, B])
            PseudoExpr::Apply { function, args }
                if args.len() == 2
                    && matches!(
                        function.as_ref(),
                        PseudoExpr::BuiltinCall { name, args: ba } if *name == crate::BuiltinId::Seq && ba.is_empty()
                    ) =>
            {
                stmts.push(&args[0]);
                current = &args[1];
            }
            // Not a seq -- this is the final expression in the chain
            other => {
                stmts.push(other);
                break;
            }
        }
    }
    stmts
}

/// Check if an expression is `Var("expect!")`.
pub(in crate::decompile::render) fn is_expect_bang(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Var { name, .. } if name == "expect!")
}

/// Collect a chain of nested `expect!(cond, expect!(cond2, ... value))` calls.
///
/// Returns `(entries, final_value)`. Each entry is `(cond, message)`: a
/// 3-arg `expect!` contributes the message, a 2-arg one `None`;
/// `final_value` is the innermost non-expect! expression (usually `Void`
/// for statement-position assertion chains).
pub(in crate::decompile::render) fn collect_expect_chain(
    expr: &PseudoExpr,
) -> (Vec<(&PseudoExpr, Option<&PseudoExpr>)>, &PseudoExpr) {
    let mut entries = Vec::new();
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Apply { function, args }
                if is_expect_bang(function.as_ref()) && (args.len() == 2 || args.len() == 3) =>
            {
                let msg = if args.len() == 3 {
                    Some(&args[2])
                } else {
                    None
                };
                entries.push((&args[0], msg));
                current = &args[1];
            }
            other => {
                return (entries, other);
            }
        }
    }
}

/// Count nested `List.tail` calls and return the innermost expression.
/// Handles both `BuiltinCall("List.tail", [arg])` and `Apply(BuiltinCall("List.tail", []), [arg])`.
///
/// `List.tail(List.tail(x))` → `(x, 2)`, `List.tail(x)` → `(x, 1)`, `x` → `(x, 0)`.
pub(in crate::decompile::render) fn count_tail_chain_any(
    expr: &PseudoExpr,
) -> (&PseudoExpr, usize) {
    let mut current = expr;
    let mut depth = 0;
    loop {
        match current {
            // Direct form: BuiltinCall("List.tail", [arg])
            PseudoExpr::BuiltinCall { name, args }
                if *name == crate::BuiltinId::ListTail && args.len() == 1 =>
            {
                depth += 1;
                current = &args[0];
            }
            // Apply form: Apply(BuiltinCall("List.tail", []), [arg])
            PseudoExpr::Apply { function, args }
                if args.len() == 1
                    && matches!(
                        function.as_ref(),
                        PseudoExpr::BuiltinCall { name, args: ba } if *name == crate::BuiltinId::ListTail && ba.is_empty()
                    ) =>
            {
                depth += 1;
                current = &args[0];
            }
            _ => return (current, depth),
        }
    }
}

pub(in crate::decompile::render) fn collect_logical_chain<'a>(
    op: BinaryOp,
    expr: &'a PseudoExpr,
    out: &mut Vec<&'a PseudoExpr>,
) {
    let mut stack = vec![expr];
    while let Some(current) = stack.pop() {
        if let PseudoExpr::BinOp {
            op: inner_op,
            left,
            right,
        } = current
            && *inner_op == op
        {
            // Push right first so left is processed first.
            stack.push(right);
            stack.push(left);
            continue;
        }
        out.push(current);
    }
}
