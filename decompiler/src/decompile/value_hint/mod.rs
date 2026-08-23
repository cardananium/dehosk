//! Structural type hinting for expressions.
//!
//! `infer_value_type_hint` returns the type determined purely by an
//! expression's shape — literals, operators, builtin calls, if-branch
//! unification. It reads no solver state or `TypeEnvironment`.

use crate::pseudo::ast::{BinaryOp, PseudoExpr, PseudoType, UnaryOp};

use super::type_solver::infer_builtin_return_type;

/// Infer a type hint for `expr` from its syntactic structure alone.
///
/// Returns `Some(ty)` when the expression's own shape determines the type
/// (literals, arithmetic/comparison ops, builtin calls with known return
/// types, if-branches that agree); otherwise falls back to
/// `expr.type_resolution()`, which is set only for literal kinds.
pub(crate) fn infer_value_type_hint(expr: &PseudoExpr) -> Option<PseudoType> {
    enum Frame<'a> {
        Enter(&'a PseudoExpr),
        CombineIf,
    }
    let mut stack = vec![Frame::Enter(expr)];
    let mut results: Vec<Option<PseudoType>> = Vec::new();
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Enter(cur) => match cur {
                PseudoExpr::Let { body, .. } => stack.push(Frame::Enter(body)),
                PseudoExpr::Trace { value, .. } => stack.push(Frame::Enter(value)),
                PseudoExpr::Int(_) => results.push(Some(PseudoType::Int)),
                PseudoExpr::ByteArray(_) => results.push(Some(PseudoType::ByteArray)),
                PseudoExpr::String(_) => results.push(Some(PseudoType::String)),
                PseudoExpr::Bool(_) => results.push(Some(PseudoType::Bool)),
                PseudoExpr::Unit => results.push(Some(PseudoType::Unit)),
                PseudoExpr::BinOp { op, .. } => results.push(match op {
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod => Some(PseudoType::Int),
                    BinaryOp::Eq
                    | BinaryOp::Neq
                    | BinaryOp::Lt
                    | BinaryOp::Lte
                    | BinaryOp::Gt
                    | BinaryOp::Gte
                    | BinaryOp::And
                    | BinaryOp::Or => Some(PseudoType::Bool),
                    BinaryOp::Cons | BinaryOp::Concat => None,
                }),
                PseudoExpr::UnOp { op, .. } => results.push(match op {
                    UnaryOp::Not => Some(PseudoType::Bool),
                    UnaryOp::Negate | UnaryOp::Length => Some(PseudoType::Int),
                }),
                PseudoExpr::BuiltinCall { name, args } => {
                    results.push(infer_builtin_return_type(name, args))
                }
                PseudoExpr::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    // Push in reverse so `then_branch` (visited first
                    // originally) is processed before `else_branch`, and
                    // `CombineIf` runs only once both results are ready.
                    stack.push(Frame::CombineIf);
                    stack.push(Frame::Enter(else_branch));
                    stack.push(Frame::Enter(then_branch));
                }
                _ => results.push(cur.type_resolution().as_deref().cloned()),
            },
            Frame::CombineIf => {
                let else_type = results.pop().expect("else_branch result");
                let then_type = results.pop().expect("then_branch result");
                results.push(match (then_type, else_type) {
                    (Some(t), Some(e)) if t == e => Some(t),
                    _ => None,
                });
            }
        }
    }
    results
        .pop()
        .expect("worklist always leaves exactly one result")
}

#[cfg(test)]
mod tests;
