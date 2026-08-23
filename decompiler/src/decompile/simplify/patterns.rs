//! Pattern recognition for simplification:
//! Y/Z-combinators, and/or function definitions,
//! if-chain to `when` conversion.

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{BinaryOp, PseudoExpr, UnaryOp, WhenClause, WhenPattern};
use crate::pseudo::var_id::VarId;

use super::Simplifier;

impl Simplifier {
    pub(crate) fn may_build_when_from_if_chain(cond: &PseudoExpr, else_br: &PseudoExpr) -> bool {
        matches!(
            cond,
            PseudoExpr::BinOp {
                op: BinaryOp::Eq,
                left,
                right,
            } if matches!(left.as_ref(), PseudoExpr::Int(_))
                || matches!(right.as_ref(), PseudoExpr::Int(_))
        ) && matches!(
            else_br,
            PseudoExpr::If { .. }
                | PseudoExpr::When { .. }
                | PseudoExpr::BinOp {
                    op: BinaryOp::And | BinaryOp::Or,
                    ..
                }
        )
    }

    /// Unwrap delay wrappers from an expression.
    /// Delay(delay(delay(x))) -> &x
    fn unwrap_delays(expr: &PseudoExpr) -> &PseudoExpr {
        let mut current = expr;
        while let PseudoExpr::Delay(inner) = current {
            current = inner;
        }
        current
    }

    /// Delay-wrapped Y-combinator; returns the delay count (>= 2).
    /// Pattern: delay(delay(fn(b) { fn c(d, e) { b(d(d), e) }; c(c) }))
    /// Common in old Plutus compiled code.
    pub(crate) fn is_delayed_y_combinator(expr: &PseudoExpr) -> Option<u8> {
        let mut count = 0u8;
        let mut current = expr;

        while let PseudoExpr::Delay(inner) = current {
            count += 1;
            current = inner;
        }

        if count >= 2 && Self::is_y_combinator_inner(current) {
            Some(count)
        } else {
            None
        }
    }

    /// Check if inner expression is a Y-combinator pattern (without delay wrappers).
    fn is_y_combinator_inner(expr: &PseudoExpr) -> bool {
        if let PseudoExpr::Lambda { params, body } = expr
            && params.len() == 1
        {
            // Pattern 1: fn(b) { fn c(d, e) { b(d(d), e) }; c(c) } - a Let
            // whose inner function calls itself
            if let PseudoExpr::Let {
                value,
                body: let_body,
                ..
            } = body.as_ref()
            {
                if let PseudoExpr::Lambda {
                    params: inner_params,
                    body: inner_body,
                } = value.as_ref()
                    && inner_params.len() >= 2
                {
                    if Self::contains_self_application(inner_body) {
                        return true;
                    }
                }
                if Self::contains_self_application(let_body) {
                    return true;
                }
            }

            // Pattern 2: fn(b) { fn c(...) { ... }; c(c) } - immediate definition + self-call
            if Self::contains_self_application(body) && Self::is_var_used(body, &params[0]) {
                return true;
            }
        }
        false
    }

    /// Check if a function definition is an "and" wrapper: fn(a,b) { f(a, b, delay(False)) }
    pub(crate) fn is_and_definition(&self, value: &PseudoExpr) -> bool {
        if let PseudoExpr::Lambda { params, body } = value
            && params.len() == 2
        {
            if let PseudoExpr::Apply { function, args } = body.as_ref()
                && let PseudoExpr::Var { name, .. } = function.as_ref()
                && name == "f"
                && args.len() == 3
            {
                if let PseudoExpr::Delay(inner) = &args[2] {
                    return self.is_false(inner);
                }
            }
        }
        false
    }

    /// Check if a function definition is an "or" wrapper.
    /// Patterns:
    /// Fn(a,b) { f(a, delay(True), b) }
    /// fn(a) { if(a, True) } - curried ||
    pub(crate) fn is_or_definition(&self, value: &PseudoExpr) -> bool {
        if let PseudoExpr::Lambda { params, body } = value {
            // Pattern 1: fn(a, b) { f(a, delay(True), b) }
            if params.len() == 2
                && let PseudoExpr::Apply { function, args } = body.as_ref()
                && let PseudoExpr::Var { name, .. } = function.as_ref()
                && name == "f"
                && args.len() == 3
            {
                let second_is_true = match &args[1] {
                    PseudoExpr::Delay(inner) => self.is_true(inner),
                    other => self.is_true(other),
                };
                if second_is_true {
                    return true;
                }
            }

            // Pattern 2: fn(a) { if(a, True) } - curried ||
            if params.len() == 1 {
                let param_name = &params[0];
                if let PseudoExpr::Apply { function, args } = body.as_ref() {
                    if let PseudoExpr::Var { name, .. } = function.as_ref()
                        && (name == "if" || name == "f" || name == "if_then_else")
                        && args.len() == 2
                    {
                        if let PseudoExpr::Var { name: arg_name, .. } = &args[0]
                            && arg_name == param_name
                        {
                            let second_is_true = match &args[1] {
                                PseudoExpr::Delay(inner) => self.is_true(inner),
                                other => self.is_true(other),
                            };
                            if second_is_true {
                                return true;
                            }
                        }
                    }
                }
                if let PseudoExpr::If {
                    condition,
                    then_branch,
                    ..
                } = body.as_ref()
                    && let PseudoExpr::Var {
                        name: cond_name, ..
                    } = condition.as_ref()
                    && cond_name == param_name
                    && self.is_true(then_branch)
                {
                    return true;
                }
            }
        }
        false
    }

    /// Check if expression is a Y/Z-combinator (fixed-point combinator for recursion).
    ///
    /// Classic Y: λf. (λx. f(x x))(λx. f(x x))
    /// Z (strict): λf. (λx. f(λv. x x v))(λx. f(λv. x x v))
    ///
    /// In Compiled output, it looks like:
    /// fn(k) { let l = fn(m) { k(fn(n) { m(m, n) }) } in k(fn(o) { l(l, o) }) }
    ///
    /// Or with delay wrappers (common in old Plutus compiled code):
    /// Delay(delay(fn(b) { fn c(d, e) { b(d(d), e) }; c(c) }))
    pub(crate) fn is_y_combinator(expr: &PseudoExpr) -> bool {
        let inner_expr = Self::unwrap_delays(expr);

        if let PseudoExpr::Lambda { params, body } = inner_expr
            && params.len() == 1
        {
            if let PseudoExpr::Let {
                value,
                body: let_body,
                name: let_name,
                id,
            } = body.as_ref()
            {
                if let PseudoExpr::Lambda {
                    params: inner_params,
                    body: inner_body,
                } = value.as_ref()
                    && inner_params.len() == 1
                {
                    let has_self_app = Self::contains_self_application(inner_body);
                    let has_var_call = Self::contains_var_call_by_id(let_body, let_name, id.get());
                    if has_self_app && has_var_call {
                        return true;
                    }
                }

                if Self::contains_self_application(let_body) {
                    return true;
                }
            }

            // Alternative pattern: direct application like inner(inner)
            if let PseudoExpr::Apply { function, args } = body.as_ref() {
                if args.len() == 1
                    && let (
                        PseudoExpr::Var {
                            name: fn_name,
                            id: fn_id,
                        },
                        PseudoExpr::Var {
                            name: arg_name,
                            id: arg_id,
                        },
                    ) = (function.as_ref(), &args[0])
                    && Self::same_var_ref(fn_name, *fn_id, arg_name, *arg_id)
                {
                    return true;
                }
                if Self::contains_self_application(body) {
                    return true;
                }
            }
        }
        false
    }

    fn contains_var_call_by_id(expr: &PseudoExpr, var_name: &str, var_id: Option<VarId>) -> bool {
        let binder_shadow = |name: &str, id: Option<VarId>| {
            (
                crate::decompile::var_match::ids_match_strict(var_id, id.get()),
                name == var_name,
            )
        };

        let mut pending: Vec<(&PseudoExpr, bool, bool)> = vec![(expr, false, false)];
        while let Some((current, exact_blocked, fallback_blocked)) = pending.pop() {
            let ref_matches = |name: &str, id: Option<VarId>| match (var_id, id.get()) {
                (Some(target), Some(candidate)) => !exact_blocked && target == candidate,
                _ => !fallback_blocked && name == var_name,
            };

            match current {
                PseudoExpr::Apply { function, args } => {
                    if let PseudoExpr::Var { name, id } = function.as_ref()
                        && ref_matches(name, *id)
                    {
                        return true;
                    }
                    for a in args.iter().rev() {
                        pending.push((a, exact_blocked, fallback_blocked));
                    }
                    pending.push((function, exact_blocked, fallback_blocked));
                }
                PseudoExpr::Lambda { params, body } => {
                    let exact_shadowed = params
                        .iter()
                        .any(|p| crate::decompile::var_match::ids_match_strict(var_id, p.id.get()));
                    let fallback_shadowed = params.iter().any(|p| p == var_name);
                    pending.push((
                        body,
                        exact_blocked || exact_shadowed,
                        fallback_blocked || fallback_shadowed,
                    ));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                    ..
                } => {
                    let (exact_shadowed, fallback_shadowed) = binder_shadow(name, *id);
                    pending.push((
                        body,
                        exact_blocked || exact_shadowed,
                        fallback_blocked || fallback_shadowed,
                    ));
                    pending.push((value, exact_blocked, fallback_blocked));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    let (name_exact_shadowed, name_fallback_shadowed) =
                        binder_shadow(name.as_str(), Some(name.id));
                    let exact_param_shadowed = params
                        .iter()
                        .any(|p| crate::decompile::var_match::ids_match_strict(var_id, p.id.get()));
                    let fallback_param_shadowed = params.iter().any(|p| p == var_name);
                    pending.push((
                        body,
                        exact_blocked || name_exact_shadowed || exact_param_shadowed,
                        fallback_blocked || name_fallback_shadowed || fallback_param_shadowed,
                    ));
                }
                _ => {}
            }
        }
        false
    }

    /// Check if expression contains self-application x(x,...) where first arg is same
    /// as function.
    pub(crate) fn contains_self_application(expr: &PseudoExpr) -> bool {
        let mut pending: Vec<&PseudoExpr> = vec![expr];
        while let Some(current) = pending.pop() {
            match current {
                PseudoExpr::Apply { function, args } => {
                    // Compat refs carry `id: None`, so `same_var_ref` falls back
                    // to name matching via `refs_match`.
                    if !args.is_empty()
                        && let PseudoExpr::Var {
                            name: fn_name,
                            id: fn_id,
                        } = function.as_ref()
                        && let PseudoExpr::Var {
                            name: arg_name,
                            id: arg_id,
                        } = &args[0]
                        && Self::same_var_ref(fn_name, *fn_id, arg_name, *arg_id)
                    {
                        return true;
                    }
                    pending.push(function);
                    pending.extend(args.iter());
                }
                PseudoExpr::Lambda { body, .. } => pending.push(body),
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
                _ => {}
            }
        }
        false
    }

    fn same_var_ref(
        left_name: &str,
        left_id: Option<VarId>,
        right_name: &str,
        right_id: Option<VarId>,
    ) -> bool {
        crate::decompile::var_match::refs_match(
            left_name,
            left_id.get(),
            right_name,
            right_id.get(),
        )
    }

    /// Try to build a when expression from a chain of if conditions comparing the same subject.
    /// Pattern: if subject == N { body } else { if subject == M { ... } else { fallback } }
    pub(crate) fn try_build_when_from_if_chain(
        cond: &PseudoExpr,
        then_br: &PseudoExpr,
        else_br: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        let (subject, value) = Self::extract_eq_comparison(cond)?;

        let mut clauses = vec![];

        clauses.push(WhenClause::new(
            WhenPattern::Literal(value),
            then_br.clone(),
        ));

        // Walk through else branch to find more conditions on the same subject
        let mut current_else = else_br;
        let mut owned_else_tails = Vec::new();
        loop {
            if let PseudoExpr::When {
                subject: when_subject,
                clauses: when_clauses,
                ..
            } = current_else
                && Self::if_chain_subjects_equal(&subject, when_subject)
            {
                clauses.extend(when_clauses.iter().cloned());
                return Some(PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name: None,
                    clauses,
                });
            }

            if let PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } = current_else
            {
                if let Some((else_subject, else_value)) = Self::extract_eq_comparison(condition)
                    && Self::if_chain_subjects_equal(&subject, &else_subject)
                {
                    clauses.push(WhenClause::new(
                        WhenPattern::Literal(else_value),
                        then_branch.as_ref().clone(),
                    ));
                    current_else = else_branch.as_ref();
                    continue;
                }
            }

            // Recognize a final tail already collapsed by boolean simplification:
            // `subject == N && body` => `if subject == N { body } else { False }`
            // `subject == N || body` => `if subject == N { True } else { body }`
            // `!(subject == N) && b` => `if subject == N { False } else { b }`
            // `!(subject == N) || b` => `if subject == N { b } else { True }`
            if let Some((else_value, collapsed_then, collapsed_else)) =
                Self::extract_collapsed_if_for_subject(current_else, &subject)
            {
                clauses.push(WhenClause::new(
                    WhenPattern::Literal(else_value),
                    collapsed_then,
                ));
                owned_else_tails.push(collapsed_else);
                current_else = owned_else_tails
                    .last()
                    .expect("collapsed else tail stored for if-chain walker");
                continue;
            }
            // Not a matching if - this is the final else (wildcard case)
            break;
        }

        // Need at least 2 clauses to make when worthwhile
        if clauses.len() < 2 {
            return None;
        }

        clauses.push(WhenClause::new(WhenPattern::Wildcard, current_else.clone()));

        Some(PseudoExpr::When {
            subject: PBox::new(subject),
            subject_name: None,
            clauses,
        })
    }

    fn extract_collapsed_if_for_subject(
        expr: &PseudoExpr,
        subject: &PseudoExpr,
    ) -> Option<(PseudoExpr, PseudoExpr, PseudoExpr)> {
        let PseudoExpr::BinOp { op, left, right } = expr else {
            return None;
        };

        match op {
            BinaryOp::And => {
                if let Some(value) = Self::extract_eq_value_for_subject(left, subject) {
                    return Some((value, right.as_ref().clone(), PseudoExpr::Bool(false)));
                }
                if let Some(value) = Self::extract_eq_value_for_subject(right, subject) {
                    return Some((value, left.as_ref().clone(), PseudoExpr::Bool(false)));
                }
                if let Some(value) = Self::extract_negated_eq_value_for_subject(left, subject) {
                    return Some((value, PseudoExpr::Bool(false), right.as_ref().clone()));
                }
                if let Some(value) = Self::extract_negated_eq_value_for_subject(right, subject) {
                    return Some((value, PseudoExpr::Bool(false), left.as_ref().clone()));
                }
                None
            }
            BinaryOp::Or => {
                if let Some(value) = Self::extract_eq_value_for_subject(left, subject) {
                    return Some((value, PseudoExpr::Bool(true), right.as_ref().clone()));
                }
                if let Some(value) = Self::extract_eq_value_for_subject(right, subject) {
                    return Some((value, PseudoExpr::Bool(true), left.as_ref().clone()));
                }
                if let Some(value) = Self::extract_negated_eq_value_for_subject(left, subject) {
                    return Some((value, right.as_ref().clone(), PseudoExpr::Bool(true)));
                }
                if let Some(value) = Self::extract_negated_eq_value_for_subject(right, subject) {
                    return Some((value, left.as_ref().clone(), PseudoExpr::Bool(true)));
                }
                None
            }
            _ => None,
        }
    }

    fn extract_eq_value_for_subject(expr: &PseudoExpr, subject: &PseudoExpr) -> Option<PseudoExpr> {
        let (candidate_subject, value) = Self::extract_eq_comparison(expr)?;
        Self::if_chain_subjects_equal(subject, &candidate_subject).then_some(value)
    }

    fn if_chain_subjects_equal(a: &PseudoExpr, b: &PseudoExpr) -> bool {
        let mut a = a;
        let mut b = b;
        loop {
            match (a, b) {
                (
                    PseudoExpr::Var {
                        name: left,
                        id: Some(left_id),
                    },
                    PseudoExpr::Var {
                        name: right,
                        id: Some(right_id),
                    },
                ) => {
                    return crate::decompile::var_match::refs_match(
                        left,
                        left_id.get(),
                        right,
                        right_id.get(),
                    );
                }
                (PseudoExpr::Force(left), PseudoExpr::Force(right))
                | (PseudoExpr::Delay(left), PseudoExpr::Delay(right)) => {
                    a = left;
                    b = right;
                }
                (
                    PseudoExpr::FieldAccess {
                        record: left,
                        selector: left_selector,
                    },
                    PseudoExpr::FieldAccess {
                        record: right,
                        selector: right_selector,
                    },
                ) => {
                    if left_selector != right_selector {
                        return false;
                    }
                    a = left;
                    b = right;
                }
                (
                    PseudoExpr::IndexAccess {
                        collection: left,
                        index: left_index,
                    },
                    PseudoExpr::IndexAccess {
                        collection: right,
                        index: right_index,
                    },
                ) => {
                    if left_index != right_index {
                        return false;
                    }
                    a = left;
                    b = right;
                }
                _ => return Self::exprs_equal(a, b),
            }
        }
    }

    fn extract_negated_eq_value_for_subject(
        expr: &PseudoExpr,
        subject: &PseudoExpr,
    ) -> Option<PseudoExpr> {
        let PseudoExpr::UnOp {
            op: UnaryOp::Not,
            operand,
        } = expr
        else {
            return None;
        };

        Self::extract_eq_value_for_subject(operand, subject)
    }

    /// Extract subject and value from an equality comparison: subject == value
    pub(crate) fn extract_eq_comparison(expr: &PseudoExpr) -> Option<(PseudoExpr, PseudoExpr)> {
        if let PseudoExpr::BinOp {
            op: BinaryOp::Eq,
            left,
            right,
        } = expr
        {
            if matches!(right.as_ref(), PseudoExpr::Int(_)) {
                return Some(((**left).clone(), (**right).clone()));
            }
            if matches!(left.as_ref(), PseudoExpr::Int(_)) {
                return Some(((**right).clone(), (**left).clone()));
            }
        }
        None
    }
}
