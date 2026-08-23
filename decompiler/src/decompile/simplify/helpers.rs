//! Helper predicates and utility functions for simplification.

mod access;
mod effects;
mod force_chain;
mod force_tracking;
mod naming;
mod readability;
mod scope;
mod shape;

use crate::pseudo::ast::{BinaryOp, PseudoExpr};

use super::Simplifier;

impl Simplifier {
    /// Clone `expr` with fresh binder VarIds from the per-instance
    /// `identity.next_synthetic_var_id` counter: inlined copies get
    /// deterministic, locally-unique VarIds.
    pub(crate) fn clone_with_fresh_ids(&mut self, expr: &PseudoExpr) -> PseudoExpr {
        let counter = &mut self.identity.next_synthetic_var_id;
        super::clone_hygiene::clone_with_fresh_binder_ids(expr, || {
            let id = crate::pseudo::var_id::VarId::from_raw(*counter);
            *counter = counter.saturating_add(1);
            id
        })
    }

    /// Check if two expressions are structurally equal.
    pub(crate) fn exprs_equal(a: &PseudoExpr, b: &PseudoExpr) -> bool {
        let mut pending: Vec<(&PseudoExpr, &PseudoExpr)> = vec![(a, b)];
        while let Some((a, b)) = pending.pop() {
            match (a, b) {
                // Literals
                (PseudoExpr::Int(i1), PseudoExpr::Int(i2)) => {
                    if i1 != i2 {
                        return false;
                    }
                }
                (PseudoExpr::Bool(b1), PseudoExpr::Bool(b2)) => {
                    if b1 != b2 {
                        return false;
                    }
                }
                (PseudoExpr::String(s1), PseudoExpr::String(s2)) => {
                    if s1 != s2 {
                        return false;
                    }
                }
                (PseudoExpr::ByteArray(b1), PseudoExpr::ByteArray(b2)) => {
                    if b1 != b2 {
                        return false;
                    }
                }
                (PseudoExpr::Unit, PseudoExpr::Unit) => {}

                // Variables
                (PseudoExpr::Var { name: n1, .. }, PseudoExpr::Var { name: n2, .. }) => {
                    if n1 != n2 {
                        return false;
                    }
                }

                // Force/Delay
                (PseudoExpr::Force(inner1), PseudoExpr::Force(inner2)) => {
                    pending.push((inner1, inner2));
                }
                (PseudoExpr::Delay(inner1), PseudoExpr::Delay(inner2)) => {
                    pending.push((inner1, inner2));
                }

                // Applications
                (
                    PseudoExpr::Apply {
                        function: f1,
                        args: a1,
                    },
                    PseudoExpr::Apply {
                        function: f2,
                        args: a2,
                    },
                ) => {
                    if a1.len() != a2.len() {
                        return false;
                    }
                    pending.push((f1, f2));
                    pending.extend(a1.iter().zip(a2.iter()));
                }

                // Builtins
                (
                    PseudoExpr::BuiltinCall { name: n1, args: a1 },
                    PseudoExpr::BuiltinCall { name: n2, args: a2 },
                ) => {
                    if n1 != n2 || a1.len() != a2.len() {
                        return false;
                    }
                    pending.extend(a1.iter().zip(a2.iter()));
                }

                // Binary/Unary ops
                (
                    PseudoExpr::BinOp {
                        op: op1,
                        left: l1,
                        right: r1,
                    },
                    PseudoExpr::BinOp {
                        op: op2,
                        left: l2,
                        right: r2,
                    },
                ) => {
                    if op1 != op2 {
                        return false;
                    }
                    pending.push((l1, l2));
                    pending.push((r1, r2));
                }
                (
                    PseudoExpr::UnOp {
                        op: op1,
                        operand: o1,
                    },
                    PseudoExpr::UnOp {
                        op: op2,
                        operand: o2,
                    },
                ) => {
                    if op1 != op2 {
                        return false;
                    }
                    pending.push((o1, o2));
                }

                // Field/Index access
                (
                    PseudoExpr::FieldAccess {
                        record: r1,
                        selector: s1,
                        ..
                    },
                    PseudoExpr::FieldAccess {
                        record: r2,
                        selector: s2,
                        ..
                    },
                ) => {
                    if s1 != s2 {
                        return false;
                    }
                    pending.push((r1, r2));
                }
                (
                    PseudoExpr::IndexAccess {
                        collection: c1,
                        index: i1,
                    },
                    PseudoExpr::IndexAccess {
                        collection: c2,
                        index: i2,
                    },
                ) => {
                    if i1 != i2 {
                        return false;
                    }
                    pending.push((c1, c2));
                }

                // Constructors
                (
                    PseudoExpr::Constr {
                        tag: t1,
                        fields: f1,
                        ..
                    },
                    PseudoExpr::Constr {
                        tag: t2,
                        fields: f2,
                        ..
                    },
                ) => {
                    if t1 != t2 || f1.len() != f2.len() {
                        return false;
                    }
                    pending.extend(f1.iter().zip(f2.iter()));
                }

                // Pairs/Lists/Tuples
                (PseudoExpr::Pair(a1, b1), PseudoExpr::Pair(a2, b2)) => {
                    pending.push((a1, a2));
                    pending.push((b1, b2));
                }
                (
                    PseudoExpr::List {
                        elements: e1,
                        tail: t1,
                    },
                    PseudoExpr::List {
                        elements: e2,
                        tail: t2,
                    },
                ) => {
                    if e1.len() != e2.len() {
                        return false;
                    }
                    pending.extend(e1.iter().zip(e2.iter()));
                    match (t1, t2) {
                        (None, None) => {}
                        (Some(x), Some(y)) => pending.push((x, y)),
                        _ => return false,
                    }
                }
                (PseudoExpr::Tuple(e1), PseudoExpr::Tuple(e2)) => {
                    if e1.len() != e2.len() {
                        return false;
                    }
                    pending.extend(e1.iter().zip(e2.iter()));
                }

                // Error
                (PseudoExpr::Error { message: m1 }, PseudoExpr::Error { message: m2 }) => {
                    if m1 != m2 {
                        return false;
                    }
                }

                // Different types are never equal
                _ => return false,
            }
        }
        true
    }

    /// Try to collapse a chain of cons_bytearray calls into a single ByteArray.
    ///
    /// Pattern: cons_bytearray(byte1, cons_bytearray(byte2, ... cons_bytearray(byteN, #"")...))
    /// Result: #"byte1 byte2 ... byteN"
    pub(crate) fn try_collapse_cons_bytestring(expr: &PseudoExpr) -> Option<Vec<u8>> {
        let is_cons = match expr {
            PseudoExpr::BuiltinCall { name, .. } => {
                name == "cons_bytearray" || name == "ByteArray.push"
            }
            _ => false,
        };

        if !is_cons {
            return None;
        }

        let mut bytes = Vec::new();
        let mut current = expr;

        loop {
            match current {
                PseudoExpr::BuiltinCall { name, args }
                    if (name == "cons_bytearray" || name == "ByteArray.push")
                        && args.len() == 2 =>
                {
                    // First arg should be an integer (the byte)
                    if let PseudoExpr::Int(n) = &args[0] {
                        use num_traits::ToPrimitive;
                        {
                            let byte = n.to_u8()?;
                            bytes.push(byte);
                            current = &args[1];
                        }
                    } else {
                        // First arg is not an integer, can't collapse
                        return None;
                    }
                }

                PseudoExpr::ByteArray(existing) => {
                    // End of chain.
                    bytes.extend(existing);
                    return Some(bytes);
                }

                _ => {
                    // Tail is neither a cons call nor a literal ByteArray, so the
                    // bytes collected so far cannot be collapsed either.
                    return None;
                }
            }
        }
    }

    /// Check for the Y-combinator self-call `self_name(self_name, ...)`.
    pub(crate) fn has_self_call(expr: &PseudoExpr, self_name: &str) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Apply { function, args } => {
                    if let PseudoExpr::Var { name, .. } = function.as_ref()
                        && name == self_name
                        && !args.is_empty()
                        && let PseudoExpr::Var { name: arg_name, .. } = &args[0]
                        && arg_name == self_name
                    {
                        return true;
                    }
                    pending.push(function);
                    pending.extend(args.iter());
                }
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(value);
                    pending.push(body);
                }
                PseudoExpr::Lambda { params, body } => {
                    if !params.iter().any(|param| param == self_name) {
                        pending.push(body);
                    }
                }
                PseudoExpr::RecFn {
                    name, params, body, ..
                } => {
                    if name != self_name && !params.iter().any(|param| param == self_name) {
                        pending.push(body);
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
                PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => pending.push(inner),
                PseudoExpr::Trace { message, value } => {
                    pending.push(message);
                    pending.push(value);
                }
                PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
                PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
                PseudoExpr::List { elements, tail } => {
                    pending.extend(elements.iter());
                    if let Some(t) = tail.as_ref() {
                        pending.push(t);
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// Check whether an expression calls the self parameter directly,
    /// `self_name(...)` — the shape of a partially-normalized recursive
    /// wrapper whose body lost `self(self, ...)` while its entry call
    /// still seeds recursion via `__y_comb_rec_fn`.
    pub(crate) fn has_direct_self_call(expr: &PseudoExpr, self_name: &str) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Apply { function, args } => {
                    if matches!(function.as_ref(), PseudoExpr::Var { name, .. } if name == self_name)
                    {
                        return true;
                    }
                    pending.push(function);
                    pending.extend(args.iter());
                }
                PseudoExpr::Let { value, body, .. } => {
                    pending.push(value);
                    pending.push(body);
                }
                PseudoExpr::Lambda { params, body } => {
                    if !params.iter().any(|param| param == self_name) {
                        pending.push(body);
                    }
                }
                PseudoExpr::RecFn {
                    name, params, body, ..
                } => {
                    if name != self_name && !params.iter().any(|param| param == self_name) {
                        pending.push(body);
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
                PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => pending.push(inner),
                PseudoExpr::Trace { message, value } => {
                    pending.push(message);
                    pending.push(value);
                }
                PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
                PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
                PseudoExpr::List { elements, tail } => {
                    pending.extend(elements.iter());
                    if let Some(t) = tail.as_ref() {
                        pending.push(t);
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// Canonicalize operand order for commutative binary ops.
    ///
    /// For ==, !=, +, *, && and ||, literals go on the right, so output
    /// reads `x == 1` rather than `1 == x`.
    pub(crate) fn canonicalize_commutative_binop(
        op: BinaryOp,
        left: PseudoExpr,
        right: PseudoExpr,
    ) -> (PseudoExpr, PseudoExpr) {
        let commutative = matches!(
            op,
            BinaryOp::Eq
                | BinaryOp::Neq
                | BinaryOp::Add
                | BinaryOp::Mul
                | BinaryOp::And
                | BinaryOp::Or
        );
        if !commutative {
            return (left, right);
        }
        // Swap if left is a literal/constant and right is not
        let left_is_literal = matches!(
            left,
            PseudoExpr::Int(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
        );
        let right_is_literal = matches!(
            right,
            PseudoExpr::Int(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
        );
        if left_is_literal && !right_is_literal {
            (right, left)
        } else {
            (left, right)
        }
    }

    /// Canonicalize comparison and commutative operand order.
    ///
    /// Commutative ops (==, !=, +, *, &&, ||): literals go on the right.
    /// Comparison ops (<, <=, >, >=): a literal on the left flips both the
    /// operands and the operator, so `10 < z` becomes `z > 10`.
    pub(crate) fn canonicalize_comparison_order(
        op: BinaryOp,
        left: PseudoExpr,
        right: PseudoExpr,
    ) -> (BinaryOp, PseudoExpr, PseudoExpr) {
        // First handle commutative ops (no op change needed)
        let (left, right) = Self::canonicalize_commutative_binop(op, left, right);

        // Then handle non-commutative comparisons: flip lit < var → var > lit
        let flippable = matches!(
            op,
            BinaryOp::Lt | BinaryOp::Lte | BinaryOp::Gt | BinaryOp::Gte
        );
        if !flippable {
            return (op, left, right);
        }
        let left_is_literal = matches!(
            left,
            PseudoExpr::Int(_) | PseudoExpr::ByteArray(_) | PseudoExpr::String(_)
        );
        let right_is_literal = matches!(
            right,
            PseudoExpr::Int(_) | PseudoExpr::ByteArray(_) | PseudoExpr::String(_)
        );
        if left_is_literal && !right_is_literal {
            let flipped_op = match op {
                BinaryOp::Lt => BinaryOp::Gt,
                BinaryOp::Lte => BinaryOp::Gte,
                BinaryOp::Gt => BinaryOp::Lt,
                BinaryOp::Gte => BinaryOp::Lte,
                _ => unreachable!(),
            };
            (flipped_op, right, left)
        } else {
            (op, left, right)
        }
    }

    /// Check if an expression is the integer literal -1.
    pub(crate) fn is_neg_one(expr: &PseudoExpr) -> bool {
        matches!(expr, PseudoExpr::Int(n) if *n == num_bigint::BigInt::from(-1))
    }

    /// Check if an expression contains control flow sub-expressions (If, When, Let).
    ///
    /// Used to decide whether a complex condition should be extracted into a let binding.
    pub(crate) fn contains_control_flow_expr(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::If { .. } | PseudoExpr::When { .. } | PseudoExpr::Let { .. } => {
                    return true;
                }
                PseudoExpr::UnOp { operand, .. } => pending.push(operand),
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(left);
                    pending.push(right);
                }
                PseudoExpr::Apply { function, args } => {
                    pending.push(function);
                    pending.extend(args.iter());
                }
                PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
                _ => {}
            }
        }
        false
    }
}
