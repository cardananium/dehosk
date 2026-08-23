use std::collections::{HashMap, HashSet};

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::{BinaryOp, Binder, PseudoExpr, PseudoType, UnaryOp};
use crate::pseudo::var_id::VarId;

#[derive(Clone, Default)]
pub(super) struct KnownBindings {
    pub(super) authoritative_ids: HashSet<VarId>,
    pub(super) compat_names: HashSet<String>,
}

impl KnownBindings {
    pub(super) fn insert_binding(&mut self, name: &str, id: Option<VarId>) {
        if let Some(vid) = id.get() {
            self.authoritative_ids.insert(vid);
        } else {
            self.compat_names.insert(name.to_string());
        }
    }

    pub(super) fn contains_var(&self, name: &str, id: Option<VarId>) -> bool {
        if let Some(vid) = id.get() {
            self.authoritative_ids.contains(&vid)
        } else {
            self.compat_names.contains(name)
        }
    }

    pub(super) fn contains_binding(&self, name: &str, id: Option<VarId>) -> bool {
        self.contains_var(name, id)
    }

    pub(super) fn intersect_with(&mut self, other: &Self) {
        self.authoritative_ids
            .retain(|id| other.authoritative_ids.contains(id));
        self.compat_names
            .retain(|name| other.compat_names.contains(name));
    }
}

#[derive(Clone)]
pub(super) struct CpsClassification {
    pub(super) param_count: usize,
}

#[derive(Default)]
pub(super) struct ClassifiedBindings {
    pub(super) authoritative: HashMap<VarId, CpsClassification>,
    pub(super) compat: HashMap<String, CpsClassification>,
}

impl ClassifiedBindings {
    pub(super) fn is_empty(&self) -> bool {
        self.authoritative.is_empty() && self.compat.is_empty()
    }

    pub(super) fn insert_binding(
        &mut self,
        name: &str,
        id: Option<VarId>,
        classification: CpsClassification,
    ) {
        if let Some(vid) = id.get() {
            self.authoritative.insert(vid, classification);
        } else {
            self.compat.insert(name.to_string(), classification);
        }
    }

    pub(super) fn get_var(&self, name: &str, id: Option<VarId>) -> Option<&CpsClassification> {
        if let Some(vid) = id.get() {
            self.authoritative.get(&vid)
        } else {
            self.compat.get(name)
        }
    }

    pub(super) fn contains_binding(&self, name: &str, id: Option<VarId>) -> bool {
        self.get_var(name, id).is_some()
    }

    pub(super) fn remove_all(&mut self, bindings: &KnownBindings) {
        for id in &bindings.authoritative_ids {
            self.authoritative.remove(id);
        }
        for name in &bindings.compat_names {
            self.compat.remove(name);
        }
    }

    fn extend_known_bindings(&self, known: &mut KnownBindings) {
        known
            .authoritative_ids
            .extend(self.authoritative.keys().copied());
        known.compat_names.extend(self.compat.keys().cloned());
    }
}

/// Walk the AST to collect let bindings that are pure fst/snd selectors.
pub(super) fn collect_selector_names(expr: &PseudoExpr) -> (KnownBindings, KnownBindings) {
    let mut fst = KnownBindings::default();
    let mut snd = KnownBindings::default();
    collect_selectors_inner(expr, &mut fst, &mut snd);
    (fst, snd)
}

fn collect_selectors_inner(expr: &PseudoExpr, fst: &mut KnownBindings, snd: &mut KnownBindings) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                let inner = unwrap_delay_ref(value);
                if is_fst_selector(inner) {
                    fst.insert_binding(name, *id);
                } else if is_snd_selector(inner) {
                    snd.insert_binding(name, *id);
                }
                // Also include well-known names.
                if name == "choose_fst" {
                    fst.insert_binding(name, *id);
                } else if name == "choose_snd" {
                    snd.insert_binding(name, *id);
                }
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. }
            | PseudoExpr::RecFn { body, .. }
            | PseudoExpr::Delay(body)
            | PseudoExpr::Force(body) => {
                pending.push(body);
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
                }
                pending.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => {
                pending.push(operand);
            }
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            _ => {}
        }
    }
}

/// Collect selector names that participate in CPS-style patterns.
/// A selector participates if it is referenced (directly or via a function body)
/// from any call site that has >= 2 delay-wrapped args.
pub(super) fn collect_cps_used_selectors(
    expr: &PseudoExpr,
    fst_names: &KnownBindings,
    snd_names: &KnownBindings,
) -> KnownBindings {
    let mut cps_callers = KnownBindings::default();
    collect_cps_call_targets(expr, &mut cps_callers);

    let mut used = KnownBindings::default();
    collect_cps_direct_selector_refs(expr, fst_names, snd_names, &mut used);
    collect_selectors_in_func_bodies(expr, &cps_callers, fst_names, snd_names, &mut used);
    used
}

/// Collect names of functions/variables called with >= 2 delay-wrapped args.
fn collect_cps_call_targets(expr: &PseudoExpr, targets: &mut KnownBindings) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Apply { function, args } => {
                let delay_count = args
                    .iter()
                    .filter(|a| matches!(a, PseudoExpr::Delay(_)))
                    .count();
                if delay_count >= 2 {
                    // Walk the function expression to find the root Var name.
                    let mut cur = function.as_ref();
                    while let PseudoExpr::Apply {
                        function: inner, ..
                    } = cur
                    {
                        cur = inner.as_ref();
                    }
                    if let PseudoExpr::Var { name, id } = cur {
                        targets.insert_binding(name, *id);
                    }
                }
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. }
            | PseudoExpr::RecFn { body, .. }
            | PseudoExpr::Delay(body)
            | PseudoExpr::Force(body) => {
                pending.push(body);
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
                }
                pending.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => {
                pending.push(operand);
            }
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            _ => {}
        }
    }
}

/// Collect selector names directly referenced in function position of CPS-style calls.
fn collect_cps_direct_selector_refs(
    expr: &PseudoExpr,
    fst_names: &KnownBindings,
    snd_names: &KnownBindings,
    used: &mut KnownBindings,
) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Apply { function, args } => {
                let delay_count = args
                    .iter()
                    .filter(|a| matches!(a, PseudoExpr::Delay(_)))
                    .count();
                if delay_count >= 2 {
                    collect_selector_refs(function, fst_names, snd_names, used);
                }
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. }
            | PseudoExpr::RecFn { body, .. }
            | PseudoExpr::Delay(body)
            | PseudoExpr::Force(body) => {
                pending.push(body);
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
                }
                pending.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => {
                pending.push(operand);
            }
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            _ => {}
        }
    }
}

/// Walk the AST looking for Let bindings whose name is a CPS caller.
/// Collect selector references from the value (function body) of those bindings.
fn collect_selectors_in_func_bodies(
    expr: &PseudoExpr,
    cps_callers: &KnownBindings,
    fst_names: &KnownBindings,
    snd_names: &KnownBindings,
    used: &mut KnownBindings,
) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
                ..
            } => {
                if cps_callers.contains_binding(name, *id) {
                    collect_selector_refs(value, fst_names, snd_names, used);
                }
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. }
            | PseudoExpr::RecFn { body, .. }
            | PseudoExpr::Delay(body)
            | PseudoExpr::Force(body) => {
                pending.push(body);
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
                }
                pending.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => {
                pending.push(operand);
            }
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            _ => {}
        }
    }
}

/// Collect selector Var references from an expression (for checking if a
/// function body references known selectors).
fn collect_selector_refs(
    expr: &PseudoExpr,
    fst_names: &KnownBindings,
    snd_names: &KnownBindings,
    used: &mut KnownBindings,
) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Var { name, id } => {
                if fst_names.contains_var(name, *id) || snd_names.contains_var(name, *id) {
                    used.insert_binding(name, *id);
                }
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
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
            PseudoExpr::When { clauses, .. } => {
                for c in clauses.iter().rev() {
                    pending.push(&c.body);
                }
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                pending.push(inner);
            }
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push(a);
                }
                pending.push(function);
            }
            _ => {}
        }
    }
}

/// Check if an expression is a fst selector: `fn(x, _) { x }`
pub(super) fn is_fst_selector(expr: &PseudoExpr) -> bool {
    if let PseudoExpr::Lambda { params, body } = expr
        && params.len() == 2
    {
        return root_var_matches_binder(body, &params[0])
            && (params[1] == "_" || !is_var_at_root(body, &params[1]));
    }
    false
}

/// Check if an expression is a snd selector: `fn(_, y) { y }`
pub(super) fn is_snd_selector(expr: &PseudoExpr) -> bool {
    if let PseudoExpr::Lambda { params, body } = expr
        && params.len() == 2
    {
        return root_var_matches_binder(body, &params[1])
            && (params[0] == "_" || !is_var_at_root(body, &params[0]));
    }
    false
}

fn root_var_matches_binder(expr: &PseudoExpr, binder: &Binder) -> bool {
    match expr {
        PseudoExpr::Var { name, id } => {
            crate::decompile::var_match::ref_matches_binder(name, id.get(), binder)
        }
        _ => false,
    }
}

/// True when the expression is directly a Var matching `binder`.
fn is_var_at_root(expr: &PseudoExpr, binder: &Binder) -> bool {
    root_var_matches_binder(expr, binder)
}

/// Unwrap nested Delay wrappers to get at the inner expression.
fn unwrap_delay_ref(expr: &PseudoExpr) -> &PseudoExpr {
    let mut current = expr;
    while let PseudoExpr::Delay(inner) = current {
        current = inner;
    }
    current
}

fn unwrap_lambda_value_ref(expr: &PseudoExpr) -> &PseudoExpr {
    let mut current = expr;
    while let PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) = current {
        current = inner;
    }
    current
}

/// Recognise selector-valued expressions as booleans.
/// `choose_fst` / `fn(x, _) { x }` -> `Some(true)`
/// `choose_snd` / `fn(_, y) { y }` -> `Some(false)`
pub(super) fn selector_bool_value(
    expr: &PseudoExpr,
    fst_names: &KnownBindings,
    snd_names: &KnownBindings,
) -> Option<bool> {
    let mut current = expr;
    loop {
        match current {
            PseudoExpr::Var { name, id } if fst_names.contains_var(name, *id) => {
                return Some(true);
            }
            PseudoExpr::Var { name, id } if snd_names.contains_var(name, *id) => {
                return Some(false);
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                current = inner;
            }
            other if is_fst_selector(other) => return Some(true),
            other if is_snd_selector(other) => return Some(false),
            _ => return None,
        }
    }
}

/// Check whether every return path of `expr` yields a known selector or Bool.
pub(super) fn is_all_selector_returns(
    expr: &PseudoExpr,
    fst_names: &KnownBindings,
    snd_names: &KnownBindings,
) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if selector_bool_value(current, fst_names, snd_names).is_some() {
            continue;
        }

        match current {
            PseudoExpr::Bool(_) => {}
            PseudoExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::When { clauses, .. } => {
                pending.extend(clauses.iter().map(|c| &c.body));
            }
            PseudoExpr::Let { body, .. } => pending.push(body),
            PseudoExpr::Trace { value, .. } => pending.push(value),
            PseudoExpr::Error { .. } => {}
            _ => return false,
        }
    }
    true
}

pub(super) fn can_rewrite_selector_condition_as_if(expr: &PseudoExpr) -> bool {
    fn has_known_non_boolean_type(expr: &PseudoExpr) -> bool {
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

    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if has_known_non_boolean_type(current) {
            return false;
        }

        match current {
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
            | PseudoExpr::BuiltinCall { .. }
            | PseudoExpr::Apply { .. }
            | PseudoExpr::FieldAccess { .. }
            | PseudoExpr::IndexAccess { .. }
            | PseudoExpr::HelperSymbol(_)
            | PseudoExpr::Error { .. } => return false,
            PseudoExpr::Var { .. } => {
                // Var.type_resolution() is Unknown, so Bool cannot be ruled out.
            }
            PseudoExpr::Let { body, .. } => pending.push(body),
            PseudoExpr::Constr { fields, .. } => {
                if !fields.is_empty() {
                    return false;
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Trace { value, .. } => pending.push(value),
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
        }
    }
    true
}

/// Walk the AST to classify functions whose bodies return selectors.
pub(super) fn classify_functions(
    expr: &PseudoExpr,
    fst_names: &KnownBindings,
    snd_names: &KnownBindings,
) -> ClassifiedBindings {
    let mut result = ClassifiedBindings::default();
    classify_inner(expr, fst_names, snd_names, &mut result);
    result
}

fn classify_inner(
    expr: &PseudoExpr,
    fst_names: &KnownBindings,
    snd_names: &KnownBindings,
    out: &mut ClassifiedBindings,
) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
                ..
            } => {
                // Check if value is a Lambda, possibly wrapped in delay/force.
                if let PseudoExpr::Lambda {
                    params,
                    body: lam_body,
                } = unwrap_lambda_value_ref(value.as_ref())
                {
                    // Count params (flatten curried lambdas).
                    let mut param_count = params.len();
                    let mut inner_body = lam_body.as_ref();
                    while let PseudoExpr::Lambda {
                        params: inner_params,
                        body: next_body,
                    } = inner_body
                    {
                        param_count += inner_params.len();
                        inner_body = next_body.as_ref();
                    }

                    // Include already-classified functions so CPS functions that
                    // return another CPS function's result are recognised too.
                    let mut all_known_fst = fst_names.clone();
                    let mut all_known_snd = snd_names.clone();
                    out.extend_known_bindings(&mut all_known_fst);
                    out.extend_known_bindings(&mut all_known_snd);

                    if is_all_selector_returns(inner_body, &all_known_fst, &all_known_snd) {
                        out.insert_binding(name, *id, CpsClassification { param_count });
                    }
                }
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::Lambda { body, .. }
            | PseudoExpr::RecFn { body, .. }
            | PseudoExpr::Delay(body)
            | PseudoExpr::Force(body) => {
                pending.push(body);
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
                }
                pending.push(subject);
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(right);
                pending.push(left);
            }
            PseudoExpr::UnOp { operand, .. } => {
                pending.push(operand);
            }
            PseudoExpr::Trace { message, value } => {
                pending.push(value);
                pending.push(message);
            }
            _ => {}
        }
    }
}

/// Safety check: find classified function names that appear as values
/// (i.e. Var references NOT in the function position of an Apply).
pub(super) fn find_value_uses(
    expr: &PseudoExpr,
    classifications: &ClassifiedBindings,
) -> KnownBindings {
    let mut result = KnownBindings::default();
    find_value_uses_inner(expr, classifications, false, &mut result);
    result
}

fn find_value_uses_inner(
    expr: &PseudoExpr,
    classifications: &ClassifiedBindings,
    in_apply_fn_position: bool,
    result: &mut KnownBindings,
) {
    let mut pending: Vec<(&PseudoExpr, bool)> = vec![(expr, in_apply_fn_position)];
    while let Some((current, in_fn_pos)) = pending.pop() {
        match current {
            PseudoExpr::Var { name, id } => {
                if !in_fn_pos && classifications.get_var(name, *id).is_some() {
                    result.insert_binding(name, *id);
                }
            }
            PseudoExpr::Apply { function, args } => {
                // The function position is okay - it's a call, not a value use.
                for a in args.iter().rev() {
                    pending.push((a, false));
                }
                pending.push((function, true));
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push((body, false));
                pending.push((value, false));
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push((body, false));
            }
            PseudoExpr::Delay(body) | PseudoExpr::Force(body) => {
                pending.push((body, in_fn_pos));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push((else_branch, false));
                pending.push((then_branch, false));
                pending.push((condition, false));
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    pending.push((&c.body, false));
                }
                pending.push((subject, false));
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push((right, false));
                pending.push((left, false));
            }
            PseudoExpr::UnOp { operand, .. } => {
                pending.push((operand, false));
            }
            PseudoExpr::Trace { message, value } => {
                pending.push((value, false));
                pending.push((message, false));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    pending.push((t, false));
                }
                for e in elements.iter().rev() {
                    pending.push((e, false));
                }
            }
            PseudoExpr::Tuple(elements) => {
                for e in elements.iter().rev() {
                    pending.push((e, false));
                }
            }
            PseudoExpr::Pair(a, b) => {
                pending.push((b, false));
                pending.push((a, false));
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    pending.push((f, false));
                }
            }
            PseudoExpr::FieldAccess { record, .. } => {
                pending.push((record, false));
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                pending.push((collection, false));
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push((a, false));
                }
            }
            _ => {}
        }
    }
}
