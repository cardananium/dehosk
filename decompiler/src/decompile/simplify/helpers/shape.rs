use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, PseudoType, UnaryOp};
use crate::pseudo::constructor::{ConstructorOrigin, ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::OptionVarIdGet;

use super::Simplifier;

impl Simplifier {
    pub(crate) fn normalize_constructor_data_expr(
        tag_expr: PseudoExpr,
        fields_expr: PseudoExpr,
    ) -> PseudoExpr {
        crate::decompile::constructor_data::normalize_constructor_data_expr(tag_expr, fields_expr)
    }

    /// Extract branch from Scott-encoded case analysis, returning (field_params, body):
    /// Delay(body) → ([], body) — fieldless constructor
    /// Lambda(params, Delay(body)) → (params, body) — constructor with fields
    /// Lambda(params, body) → (params, body) — same, delay already stripped
    /// Error → ([], Error) — fail branch, since force(fail) = fail
    /// non-thunk value → ([], value) — since force(value) = value
    pub(crate) fn extract_scott_branch(expr: &PseudoExpr) -> Option<(Vec<Binder>, PseudoExpr)> {
        if let PseudoExpr::Delay(inner) = expr {
            return Some((vec![], (**inner).clone()));
        }
        // Checked before the bare Lambda so the delay is stripped.
        if let PseudoExpr::Lambda { params, body } = expr
            && let PseudoExpr::Delay(inner) = body.as_ref()
        {
            return Some((params.clone(), (**inner).clone()));
        }
        // Some compilers omit the delay in Lambda branches when the outer force
        // on the Scott value already supplies the evaluation.
        if let PseudoExpr::Lambda { params, body } = expr {
            return Some((params.clone(), (**body).clone()));
        }
        if matches!(expr, PseudoExpr::Error { .. }) {
            return Some((vec![], expr.clone()));
        }
        // Such values were delay-wrapped at the source; an earlier pass stripped it
        // (constructor recognition turns delay(fn(_,y){y(a,b)}) into Constr<1>(a,b)).
        if Self::is_non_thunk_value(expr) {
            return Some((vec![], expr.clone()));
        }
        None
    }

    /// Fallback for when `extract_scott_branch` finds no inline Delay: the
    /// delay sits behind a variable known to be delayed.
    /// Var → ([], var) — fieldless constructor; the outer force peels the delay
    /// Lambda(params, delayed var) → (params, var) — constructor with fields
    pub(crate) fn extract_scott_branch_from_delayed(
        &self,
        expr: &PseudoExpr,
    ) -> Option<(Vec<Binder>, PseudoExpr)> {
        if let PseudoExpr::Var { name, id, .. } = expr
            && self
                .tracked_var(&self.delays.delayed_value_depths, name, id.get())
                .is_some()
        {
            return Some((vec![], expr.clone()));
        }
        if let PseudoExpr::Lambda { params, body } = expr
            && let PseudoExpr::Var { name, id, .. } = body.as_ref()
            && self
                .tracked_var(&self.delays.delayed_value_depths, name, id.get())
                .is_some()
        {
            return Some((params.clone(), body.as_ref().clone()));
        }
        None
    }

    pub(crate) fn unwrap_delay(expr: &PseudoExpr) -> PseudoExpr {
        if let PseudoExpr::Delay(inner) = expr {
            (**inner).clone()
        } else {
            expr.clone()
        }
    }

    /// Unwrap delay when the expression is already owned.
    pub(crate) fn unwrap_delay_owned(expr: PseudoExpr) -> PseudoExpr {
        if let PseudoExpr::Delay(inner) = expr {
            inner.into_inner()
        } else {
            expr
        }
    }

    /// Borrow the inner expression, unwrapping one delay layer when present.
    pub(crate) fn unwrap_delay_ref(expr: &PseudoExpr) -> &PseudoExpr {
        if let PseudoExpr::Delay(inner) = expr {
            inner.as_ref()
        } else {
            expr
        }
    }

    /// Borrow body from continuation lambda: fn(_) { body } -> body
    /// Also handles: fn(_) { delay(body) } -> body
    pub(crate) fn extract_continuation_body_ref(expr: &PseudoExpr) -> Option<&PseudoExpr> {
        if let PseudoExpr::Lambda { params, body } = expr
            && params.len() == 1
        {
            return Some(Self::unwrap_delay_ref(body));
        }
        None
    }

    /// Move body from continuation lambda: fn(_) { body } -> body
    /// Also handles: fn(_) { delay(body) } -> body
    pub(crate) fn extract_continuation_body_owned(expr: PseudoExpr) -> Option<PseudoExpr> {
        if let PseudoExpr::Lambda { params, body } = expr
            && params.len() == 1
        {
            return Some(Self::unwrap_delay_owned(body.into_inner()));
        }
        None
    }

    /// Check list-cons continuation shape from lazy Plutus wrapper:
    /// fn(head, tail, _) { body }. The 3rd parameter must be unused in body.
    pub(crate) fn is_list_cons_continuation(expr: &PseudoExpr) -> bool {
        if let PseudoExpr::Lambda { params, body } = expr {
            if params.len() != 3 {
                return false;
            }
            let third = &params[2];
            if Self::is_binder_used(body, third) {
                return false;
            }
            return true;
        }
        false
    }

    /// Move list-cons continuation from lazy Plutus wrapper:
    /// fn(head, tail, _) { body } -> (head, tail, body)
    pub(crate) fn extract_list_cons_continuation_owned(
        expr: PseudoExpr,
    ) -> Option<(Binder, Binder, PseudoExpr)> {
        if let PseudoExpr::Lambda { params, body } = expr {
            if params.len() != 3 {
                return None;
            }
            let mut params = params.into_iter();
            let head = params.next().expect("list-cons head param should exist");
            let tail = params.next().expect("list-cons tail param should exist");
            let third = params.next().expect("list-cons third param should exist");
            if Self::is_binder_used(&body, &third) {
                return None;
            }
            return Some((head, tail, Self::unwrap_delay_owned(body.into_inner())));
        }
        None
    }

    pub(crate) fn is_delay(expr: &PseudoExpr) -> bool {
        matches!(expr, PseudoExpr::Delay(_))
    }

    pub(crate) fn is_false(&self, expr: &PseudoExpr) -> bool {
        // The nullary `Constr` meaning `False` is read PER-BOOL: with a
        // `church_true` witness on the leaf, `false` is its sibling tag;
        // otherwise `false_tag_for_shape` applies the program-scoped
        // convention (CIP → 0, inverse-CIP → 1). A `DataTag` leaf is always
        // eligible; a `ScottPositional` leaf is a church-continuation
        // position of unknown convention, decoded only with a witness.
        match expr {
            PseudoExpr::Bool(false) => true,
            PseudoExpr::Constr { shape, fields, .. } if fields.is_empty() => {
                if matches!(shape, ConstructorShape::Known(KnownConstructor::False)) {
                    return true;
                }
                matches!(
                    shape,
                    ConstructorShape::Unknown { tag, origin, church_true, .. }
                        if (*origin == ConstructorOrigin::DataTag || church_true.is_some())
                            && *tag
                                == crate::decompile::church_polarity::false_tag_for_shape(
                                    shape,
                                    self.church_polarity,
                                )
                )
            }
            _ => false,
        }
    }

    pub(crate) fn is_true(&self, expr: &PseudoExpr) -> bool {
        // Per-bool dual of `is_false`: `true` is the leaf's own
        // `church_true` witness when present, else the program convention
        // (`true_tag_for_shape`: CIP → 1, inverse-CIP → 0).
        match expr {
            PseudoExpr::Bool(true) => true,
            PseudoExpr::Constr { shape, fields, .. } if fields.is_empty() => {
                if matches!(shape, ConstructorShape::Known(KnownConstructor::True)) {
                    return true;
                }
                matches!(
                    shape,
                    ConstructorShape::Unknown { tag, origin, church_true, .. }
                        if (*origin == ConstructorOrigin::DataTag || church_true.is_some())
                            && *tag
                                == crate::decompile::church_polarity::true_tag_for_shape(
                                    shape,
                                    self.church_polarity,
                                )
                )
            }
            _ => false,
        }
    }

    /// If `expr` is a nullary church-bool constructor (a fieldless `Constr`
    /// with tag 0 or 1 and a `DataTag`/`Known(True|False)` bool shape), return
    /// its raw tag. Used by the bool→bool-map recognizer, which
    /// decides identity-vs-negation from the raw scrutinee/body tag ORDER, so
    /// this returns the tag WITHOUT applying any True/False value convention.
    pub(crate) fn nullary_bool_constr_tag(expr: &PseudoExpr) -> Option<usize> {
        let PseudoExpr::Constr {
            shape, fields, tag, ..
        } = expr
        else {
            return None;
        };
        if !fields.is_empty() {
            return None;
        }
        match shape {
            ConstructorShape::Known(KnownConstructor::True) if *tag == 1 => Some(1),
            ConstructorShape::Known(KnownConstructor::False) if *tag == 0 => Some(0),
            ConstructorShape::Unknown {
                tag: shape_tag,
                arity: 0,
                origin: ConstructorOrigin::DataTag,
                ..
            } if (*shape_tag == 0 || *shape_tag == 1) && *shape_tag == *tag => Some(*tag),
            _ => None,
        }
    }

    /// True when an expression is *known* to carry a non-Bool type. Vetoes
    /// rewrites that would otherwise emit nonsense like `if data {…}` or
    /// `data && bool`.
    pub(crate) fn has_known_non_boolean_type(expr: &PseudoExpr) -> bool {
        matches!(
            expr.type_resolution().as_deref(),
            Some(
                PseudoType::Int
                    | PseudoType::ByteArray
                    | PseudoType::String
                    | PseudoType::Unit
                    | PseudoType::List(_)
                    | PseudoType::Tuple(_)
                    | PseudoType::Pair(_, _)
                    | PseudoType::Option(_)
                    | PseudoType::Result(_, _)
                    | PseudoType::Function { .. }
                    | PseudoType::Data
                    | PseudoType::G1Element
                    | PseudoType::G2Element
                    | PseudoType::MillerLoopResult
                    | PseudoType::Named(_)
            )
        )
    }

    /// Check whether an expression can safely participate in `&&` / `||`
    /// readability rewrites with a boolean sentinel branch.
    ///
    /// A bare `Var` of unknown type is allowed, to keep the useful
    /// collapses; anything already known to be non-boolean is rejected.
    pub(crate) fn can_short_circuit_with_boolean(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(cur) = pending.pop() {
            if Self::has_known_non_boolean_type(cur) {
                return false;
            }
            match cur {
                PseudoExpr::Bool(_) => {}
                PseudoExpr::Int(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::String(_)
                | PseudoExpr::Unit
                | PseudoExpr::Data(_)
                | PseudoExpr::List { .. }
                | PseudoExpr::Tuple(_)
                | PseudoExpr::Pair(_, _)
                | PseudoExpr::Raw { .. }
                | PseudoExpr::Lambda { .. }
                | PseudoExpr::RecFn { .. }
                | PseudoExpr::HelperSymbol(_) => return false,
                PseudoExpr::Var { .. } => {}
                PseudoExpr::Let { body, .. } => pending.push(body),
                // A nullary `Constr` may short-circuit only as the church-bool
                // encoding (tag 0 = False, tag 1 = True), mirroring `is_false` /
                // `is_true`. Any other tag is a different nullary sum variant —
                // `Ordering::Less`/`Greater`, say — and folding one into `&&`/`||`
                // collapses the sum into a Bool, destroying the distinction a
                // downstream `when … is { Less|Equal|Greater }` needs.
                PseudoExpr::Constr { shape, fields, .. } => {
                    let ok = fields.is_empty()
                        && matches!(
                            shape,
                            ConstructorShape::Known(
                                KnownConstructor::True | KnownConstructor::False
                            ) | ConstructorShape::Unknown {
                                tag: 0 | 1,
                                origin: ConstructorOrigin::DataTag,
                                ..
                            }
                        );
                    if !ok {
                        return false;
                    }
                }
                PseudoExpr::BuiltinCall { name, .. } if name.is_data_constructor() => {
                    return false;
                }
                PseudoExpr::BuiltinCall { .. } => return false,
                PseudoExpr::Apply { .. } => return false,
                PseudoExpr::FieldAccess { .. } => return false,
                PseudoExpr::IndexAccess { .. } => return false,
                PseudoExpr::Trace { value, .. } => pending.push(value),
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
                PseudoExpr::BinOp { op, left, right } => match op {
                    BinaryOp::Eq
                    | BinaryOp::Neq
                    | BinaryOp::Lt
                    | BinaryOp::Lte
                    | BinaryOp::Gt
                    | BinaryOp::Gte => {}
                    BinaryOp::And | BinaryOp::Or => {
                        pending.push(right);
                        pending.push(left);
                    }
                    _ => return false,
                },
                PseudoExpr::UnOp {
                    op: UnaryOp::Not,
                    operand,
                } => pending.push(operand),
                PseudoExpr::UnOp { .. } => return false,
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(else_branch);
                    pending.push(then_branch);
                    pending.push(condition);
                }
                PseudoExpr::When { clauses, .. } => {
                    for clause in clauses.iter().rev() {
                        pending.push(&clause.body);
                    }
                }
                PseudoExpr::Error { .. } => return false,
            }
        }
        true
    }

    pub(crate) fn is_fail(expr: &PseudoExpr) -> bool {
        matches!(expr, PseudoExpr::Error { .. })
            || matches!(
                expr,
                PseudoExpr::BuiltinCall { name, .. } if name.is_fail_builtin()
            )
    }

    /// Check if an expression is a `when` with a guardless wildcard clause
    /// whose body is `fail`. The scope guard in `force.rs` uses it to skip
    /// a redundant `expect!` around such a `when` sitting in the condition
    /// position of `if cond { Void } else { fail }`.
    pub(crate) fn when_has_guardless_wildcard_fail(expr: &PseudoExpr) -> bool {
        let PseudoExpr::When { clauses, .. } = expr else {
            return false;
        };
        clauses.iter().any(|clause| {
            matches!(clause.pattern, crate::pseudo::ast::WhenPattern::Wildcard)
                && clause.guard.is_none()
                && Self::is_fail(&clause.body)
        })
    }

    /// Check if the fail expression carries a message that should be preserved.
    pub(crate) fn has_fail_message(expr: &PseudoExpr) -> bool {
        matches!(expr, PseudoExpr::Error { message: Some(_) })
    }

    pub(crate) fn fail_message(expr: &PseudoExpr) -> Option<&str> {
        if let PseudoExpr::Error {
            message: Some(msg), ..
        } = expr
        {
            Some(msg.as_str())
        } else {
            None
        }
    }

    /// Check if expr is a positional selector function: fn(a,b,c,...) { <nth-param> }
    /// Returns the selected parameter's 0-indexed position when the arity matches.
    pub(crate) fn is_nth_selector(expr: &PseudoExpr, arity: usize) -> Option<usize> {
        if let PseudoExpr::Lambda { params, body } = expr
            && let Some((selector_arity, index)) = Self::selector_signature(params, body)
        {
            return (selector_arity == arity).then_some(index);
        }
        None
    }

    pub(crate) fn is_void(expr: &PseudoExpr) -> bool {
        matches!(expr, PseudoExpr::Unit)
            || matches!(expr, PseudoExpr::Constr { shape, fields, .. }
                if *shape == ConstructorShape::Known(KnownConstructor::Void)
                    && fields.is_empty())
            // An unnamed `Constr { tag: 0, fields: [] }` also counts as Void. The
            // shape is ambiguous — it could be False or None — but in `is_void`
            // callers such as CPS trigger detection it usually reads as Void.
            || matches!(expr, PseudoExpr::Constr { tag: 0, fields, shape: ConstructorShape::Unknown { .. }, type_hint: None, .. }
                if fields.is_empty())
    }
}
