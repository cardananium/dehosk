//! Rewrite `True`/`False` literals into explicit Church-encoded
//! lambdas where they sit in the nil position of a list eliminator
//! whose cons position returns a non-Bool value — either a
//! `Nil`/`Cons` `when` or a `ListFold` (UPLC `chooseList`) call.
//!
//! After `curry_split_partial_helpers` the cons arm is often a
//! 2-arg lambda (a Church-pair-pack), so the arms look like
//! `Bool` vs `fn(_, _) -> _`. At the UPLC level both are 2-arg
//! lambdas: `True` is structurally `Constr 1 []`, named `True`
//! because that is the canonical name, but here it is a Church
//! selector `fn(t, _) { t }` (pair-discard-snd).
//!
//! `Bool(true)` becomes `fn(t, _) { t }` (pick-first);
//! `Bool(false)` becomes `fn(_, f) { f }` (pick-second).
//!
//! The `when` must have exactly two arms, one `Nil` and one `Cons`
//! constructor pattern; a wildcard fall-through is left alone. The
//! cons side must not evaluate to Bool — if both sides are Bool the
//! eliminator is a genuine Bool computation and the rewrite would
//! be wrong. The nil side must be exactly `Bool(true)` or
//! `Bool(false)`; trace-wrapped or computed Bools genuinely return
//! Bool.

use crate::BuiltinId;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::rewrite_bottom_up;

/// Both arms that do work of their own — the `When` clause rewrite and the
/// `ListFold` argument rewrite — ran it AFTER their children were rewritten,
/// which is exactly where [`rewrite_bottom_up`] calls back.
pub(super) fn rewrite_church_bool_in_list_fold(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, |expr| match expr {
        PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        } => {
            let clauses = maybe_rewrite_clauses(clauses);
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            }
        }
        PseudoExpr::BuiltinCall { name, args } => {
            let args = maybe_rewrite_list_fold_args(name, args.into_vec());
            PseudoExpr::BuiltinCall {
                name,
                args: args.into(),
            }
        }
        other => other,
    })
}

/// `ListFold` (UPLC `chooseList`) with a `Bool` literal in the
/// nil-case slot (arg 1) and a cons-case slot (arg 2) that does NOT
/// evaluate to Bool is a Church-encoded list match: rewrite the
/// nil-case Bool to a Church selector Lambda.
fn maybe_rewrite_list_fold_args(name: BuiltinId, args: Vec<PseudoExpr>) -> Vec<PseudoExpr> {
    if name != BuiltinId::ListFold {
        return args;
    }
    if args.len() < 3 {
        return args;
    }
    // args[0] = list, args[1] = nil_case, args[2] = cons_case, args[3..] = trailing continuations
    let nil_bool = match &args[1] {
        PseudoExpr::Bool(b) => *b,
        _ => return args,
    };
    if evaluates_to_bool(&args[2]) {
        return args;
    }
    let mut new_args = args;
    new_args[1] = build_church_bool_selector(nil_bool);
    new_args
}

/// Nil/Cons clauses with a `Bool` leaf in the Nil arm and a
/// non-Bool-evaluating Cons arm: rewrite the Nil arm's Bool to a
/// Church-encoded selector Lambda.
fn maybe_rewrite_clauses(clauses: Vec<WhenClause>) -> Vec<WhenClause> {
    if clauses.len() != 2 {
        return clauses;
    }
    let nil_index = clauses.iter().position(|c| is_nil_pattern(&c.pattern));
    let cons_index = clauses.iter().position(|c| is_cons_pattern(&c.pattern));
    let (Some(ni), Some(ci)) = (nil_index, cons_index) else {
        return clauses;
    };
    if ni == ci {
        return clauses;
    }
    let nil_bool = match &clauses[ni].body {
        PseudoExpr::Bool(b) => *b,
        _ => return clauses,
    };
    // A Bool-evaluating Cons arm means the When is a genuine Bool
    // computation, where the rewrite would be wrong.
    if evaluates_to_bool(&clauses[ci].body) {
        return clauses;
    }
    let mut new_clauses = clauses;
    new_clauses[ni].body = build_church_bool_selector(nil_bool);
    new_clauses
}

fn is_nil_pattern(pattern: &WhenPattern) -> bool {
    matches!(
        pattern,
        WhenPattern::Constructor {
            shape: ConstructorShape::Known(KnownConstructor::Nil),
            ..
        }
    )
}

fn is_cons_pattern(pattern: &WhenPattern) -> bool {
    matches!(
        pattern,
        WhenPattern::Constructor {
            shape: ConstructorShape::Known(KnownConstructor::Cons),
            ..
        }
    )
}

/// True ONLY for shapes whose result is unambiguously a Bool literal
/// or Bool-valued computation. Deliberately narrower than the
/// `boolean_cleanup` predicate, since under-rewriting is safer than
/// rewriting a genuine Bool match.
fn evaluates_to_bool(expr: &PseudoExpr) -> bool {
    use crate::pseudo::ast::{BinaryOp, UnaryOp};

    // First visit expands a node's children onto the stack; second visit
    // (after those children's results are on `results`) combines them.
    enum Frame<'a> {
        Expand(&'a PseudoExpr),
        Combine(&'a PseudoExpr),
    }

    let mut stack = vec![Frame::Expand(expr)];
    let mut results: Vec<bool> = Vec::new();

    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Expand(e) => match e {
                PseudoExpr::BinOp { left, right, .. } => {
                    stack.push(Frame::Combine(e));
                    stack.push(Frame::Expand(right));
                    stack.push(Frame::Expand(left));
                }
                PseudoExpr::UnOp { operand, .. } => {
                    stack.push(Frame::Combine(e));
                    stack.push(Frame::Expand(operand));
                }
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    stack.push(Frame::Combine(e));
                    stack.push(Frame::Expand(else_branch));
                    stack.push(Frame::Expand(then_branch));
                }
                PseudoExpr::Trace { value, .. } => {
                    stack.push(Frame::Combine(e));
                    stack.push(Frame::Expand(value));
                }
                // Apply, Var, Lambda, RecFn, Let, When, FieldAccess, IndexAccess,
                // BuiltinCall — none are statically Bool without further analysis.
                _ => results.push(matches!(e, PseudoExpr::Bool(_))),
            },
            Frame::Combine(e) => match e {
                PseudoExpr::BinOp { op, .. } => {
                    let right = results.pop().expect("right pushed by Expand");
                    let left = results.pop().expect("left pushed by Expand");
                    // Comparison + boolean operators always return Bool.
                    let is_bool_op = matches!(
                        op,
                        BinaryOp::Eq
                            | BinaryOp::Neq
                            | BinaryOp::Lt
                            | BinaryOp::Lte
                            | BinaryOp::Gt
                            | BinaryOp::Gte
                            | BinaryOp::And
                            | BinaryOp::Or
                    );
                    results.push(is_bool_op || (left && right));
                }
                PseudoExpr::UnOp { op, .. } => {
                    let operand = results.pop().expect("operand pushed by Expand");
                    results.push(matches!(op, UnaryOp::Not) || operand);
                }
                PseudoExpr::If { .. } => {
                    let else_r = results.pop().expect("else_branch pushed by Expand");
                    let then_r = results.pop().expect("then_branch pushed by Expand");
                    results.push(then_r && else_r);
                }
                // Trace is a pure passthrough of its value's result, already
                // sitting on top of `results` — nothing to combine.
                PseudoExpr::Trace { .. } => {}
                _ => unreachable!("Combine only pushed for BinOp/UnOp/If/Trace"),
            },
        }
    }

    results
        .pop()
        .expect("root always pushes exactly one result")
}

/// Build the Church-encoded selector Lambda for a Bool value:
///   true  → `fn(t, _) { t }`  (Church-True: pick first arm)
///   false → `fn(_, f) { f }`  (Church-False: pick second arm)
fn build_church_bool_selector(value: bool) -> PseudoExpr {
    let t_id = VarId::fresh_binding();
    let f_id = VarId::fresh_binding();
    let body = if value {
        PseudoExpr::var_with_id("t", t_id)
    } else {
        PseudoExpr::var_with_id("f", f_id)
    };
    PseudoExpr::Lambda {
        params: vec![
            Binder::new(if value { "t" } else { "_" }, t_id),
            Binder::new(if value { "_" } else { "f" }, f_id),
        ],
        body: PBox::new(body),
    }
}

#[cfg(test)]
mod tests;
