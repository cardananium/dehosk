//! Inline fully-applied CPS-identity helpers.
//!
//! Direct shape: `fn(p₀, …, pₙ₋₁, k) { k(p₀, …, pₙ₋₁) }` — the body
//! applies the last param (`k`) to the preceding params in declaration
//! order. The curried shape puts callbacks in a second lambda
//! (`fn(p₀, …) { fn(k₀, …) { kⱼ(p₀, …) } }`): one inner param for a
//! church pair, several for a church Either/Option, where `kⱼ` is the
//! arm that fires.
//!
//! At a fully-applied call site (args equal `params.len()`),
//! `helper(arg₀, …, argₙ₋₁, callback)` becomes
//! `callback(arg₀, …, argₙ₋₁)`. Params that never reach the callback
//! are dead arg slots: the rewrite drops their call-site args, so
//! those args must be pure. Partial applications stay — a church-pair
//! value cannot be reduced away before its consumer projects it.
//!
//! The helper let is dropped when every reference was a rewritten
//! call site; a surviving bare reference keeps it alive.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause};
use crate::pseudo::fold::{ExprFolder, ExprVisitor};
use crate::pseudo::var_id::VarId;

pub(super) fn inline_cps_identity_helpers(expr: PseudoExpr) -> PseudoExpr {
    let mut inliner = Inliner;
    inliner.fold(expr)
}

struct Inliner;

impl ExprFolder for Inliner {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        if let PseudoExpr::Lambda {
            params,
            body: lam_body,
        } = &value
        {
            if let Some(shape) = match_cps_identity_helper(params, lam_body) {
                return run_inlining(&name, id, value, body, shape, HelperKind::Direct);
            }
            if let Some(shape) = match_curried_cps_pair(params, lam_body) {
                return run_inlining(&name, id, value, body, shape, HelperKind::Curried);
            }
        }
        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum HelperKind {
    /// `fn(p₀, ..., pₙ₋₁, k) { k(p₀, ..., pₙ₋₁) }` — one Apply at call site.
    Direct,
    /// `fn(p₀, ..., pₙ₋₁) { fn(k) { k(p₀, ..., pₙ₋₁) } }` — two-stage call.
    Curried,
}

fn run_inlining(
    name: &str,
    id: Option<VarId>,
    value: PseudoExpr,
    body: PseudoExpr,
    shape: HelperShape,
    kind: HelperKind,
) -> PseudoExpr {
    let total_refs = count_refs(&body, id, name);
    if total_refs == 0 {
        return PseudoExpr::Let {
            name: name.to_string(),
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        };
    }
    let (rewritten, inlined_count) = inline_calls(body, id, name, &shape, kind);
    if inlined_count == total_refs {
        return rewritten;
    }
    PseudoExpr::Let {
        name: name.to_string(),
        id,
        value: PBox::new(value),
        body: PBox::new(rewritten),
    }
}

/// Returns `Some(HelperShape)` if the outer `params` and `body`
/// form a curried CPS constructor: `Lambda(params, Lambda(inner,
/// Apply(Var(kⱼ), [Vars matching a subset of `params`])))`, `kⱼ`
/// being one of the inner params — one of them for a church pair,
/// two or more for a church Either/Option whose other arms stay
/// dead. Flowing indices must ascend, as in the direct form.
fn match_curried_cps_pair(params: &[Binder], body: &PseudoExpr) -> Option<HelperShape> {
    let PseudoExpr::Lambda {
        params: inner_params,
        body: inner_body,
    } = body
    else {
        return None;
    };
    if inner_params.is_empty() {
        return None;
    }
    let PseudoExpr::Apply { function, args } = inner_body.as_ref() else {
        return None;
    };
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        return None;
    };
    let active_inner_index = inner_params.iter().position(|p| p.id == *fn_id)?;
    // Track flowing OUTER param indices (strictly ascending order).
    let mut flowing_indices = Vec::with_capacity(args.len());
    let mut last_idx: Option<usize> = None;
    for arg in args {
        let PseudoExpr::Var {
            id: Some(arg_id), ..
        } = arg
        else {
            return None;
        };
        let pos = params.iter().position(|p| p.id == *arg_id)?;
        if let Some(prev) = last_idx
            && pos <= prev
        {
            return None;
        }
        last_idx = Some(pos);
        flowing_indices.push(pos);
    }
    Some(HelperShape {
        arity: params.len(),
        flowing_indices,
        inner_arity: inner_params.len(),
        active_inner_index,
    })
}

/// Result of helper-shape matching.
///
/// `arity` = total OUTER param count. `flowing_indices` = outer
/// positions whose Vars reach the active callback, in ascending
/// declaration order; the rest (excluding `Direct`'s trailing
/// callback param) are dead slots, allowed at a call site only
/// when the arg there is pure.
///
/// Curried form only: `inner_arity` = inner-projection param count
/// (1 for a church pair, 2 for a church Either/Option) and
/// `active_inner_index` = which of them takes the flowing args.
/// The other inner params are dead and must be pure at call sites
/// too — typically a Lambda literal, the alternative arm.
#[derive(Debug, Clone)]
struct HelperShape {
    arity: usize,
    flowing_indices: Vec<usize>,
    inner_arity: usize,
    active_inner_index: usize,
}

/// Match `Lambda(params, Apply(Var(last_param), [Var(p_{i₀}), Var(p_{i₁}), ..., Var(p_{iₘ})]))`
/// where `last_param` is the callback and each `Var(p_{iⱼ})` matches
/// some non-callback param's VarId. The `iⱼ` indices must be in
/// strictly ascending order (each param flows at most once, in
/// declaration order) so the rewrite preserves arg-evaluation order.
/// Non-callback positions missing from `flowing_indices` are dead
/// arg slots (`KP3`-extended).
fn match_cps_identity_helper(params: &[Binder], body: &PseudoExpr) -> Option<HelperShape> {
    if params.len() < 2 {
        return None;
    }
    let PseudoExpr::Apply { function, args } = body else {
        return None;
    };
    let last_param = params.last()?;
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        return None;
    };
    if *fn_id != last_param.id {
        return None;
    }
    let mut flowing_indices = Vec::with_capacity(args.len());
    let mut last_idx: Option<usize> = None;
    let last_pos = params.len() - 1;
    for arg in args {
        let PseudoExpr::Var {
            id: Some(arg_id), ..
        } = arg
        else {
            return None;
        };
        let pos = params[..last_pos].iter().position(|p| p.id == *arg_id)?;
        if let Some(prev) = last_idx
            && pos <= prev
        {
            return None;
        }
        last_idx = Some(pos);
        flowing_indices.push(pos);
    }
    Some(HelperShape {
        arity: params.len(),
        flowing_indices,
        // Direct form: no inner-projection layer.
        inner_arity: 0,
        active_inner_index: 0,
    })
}

/// Walk `expr` and rewrite each fully-applied call of the
/// binder into a direct call of the callback on the flowing
/// args: for `Direct`, `args.len() == arity`; for `Curried`,
/// an outer Apply of `arity` args consumed by an inner Apply
/// of `inner_arity` args. Returns the rewritten expr plus the
/// number of call sites inlined.
fn inline_calls(
    expr: PseudoExpr,
    binder_id: Option<VarId>,
    binder_name: &str,
    shape: &HelperShape,
    kind: HelperKind,
) -> (PseudoExpr, usize) {
    struct CallInliner<'a> {
        binder_id: Option<VarId>,
        binder_name: &'a str,
        shape: &'a HelperShape,
        kind: HelperKind,
        inlined_count: usize,
        shadow_depth: usize,
    }
    impl ExprFolder for CallInliner<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn enter_lambda(&mut self, params: &[Binder]) -> Vec<Binder> {
            if params.iter().any(|p| p.as_str() == self.binder_name) {
                self.shadow_depth += 1;
            }
            params.to_vec()
        }
        fn exit_lambda(&mut self, params: &[Binder]) {
            if params.iter().any(|p| p.as_str() == self.binder_name) {
                self.shadow_depth -= 1;
            }
        }
        fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
            if name.as_str() == self.binder_name
                || params.iter().any(|p| p.as_str() == self.binder_name)
            {
                self.shadow_depth += 1;
            }
            (name.clone(), params.to_vec())
        }
        fn exit_recfn(&mut self, name: &Binder, params: &[Binder]) {
            if name.as_str() == self.binder_name
                || params.iter().any(|p| p.as_str() == self.binder_name)
            {
                self.shadow_depth -= 1;
            }
        }
        fn enter_let(&mut self, name: &str, _id: &Option<VarId>, _value: &PseudoExpr) -> String {
            if name == self.binder_name {
                self.shadow_depth += 1;
            }
            name.to_string()
        }
        fn exit_let(&mut self, name: &str) {
            if name == self.binder_name {
                self.shadow_depth -= 1;
            }
        }

        fn post_apply(&mut self, function: PseudoExpr, mut args: Vec<PseudoExpr>) -> PseudoExpr {
            match self.kind {
                HelperKind::Direct => {
                    // `helper(arg₀, ..., argₙ₋₁, callback)` becomes
                    // `callback(arg_{i₀}, ..., arg_{iₘ})` at the
                    // flowing indices; args at dead indices are
                    // dropped, so they must be pure.
                    if args.len() == self.shape.arity
                        && let PseudoExpr::Var { name, id } = &function
                        && matches_binder(
                            self.binder_id,
                            self.binder_name,
                            self.shadow_depth,
                            name,
                            id,
                        )
                        && is_pure_callback(args.last().expect("arity >= 2"))
                        && dead_args_are_pure_with_callback_at_end(
                            &args,
                            &self.shape.flowing_indices,
                        )
                    {
                        self.inlined_count += 1;
                        let callback = args.pop().expect("arity >= 2 guarantees at least 2 args");
                        let flowing_args = pick_flowing_args(args, &self.shape.flowing_indices);
                        return PseudoExpr::Apply {
                            function: PBox::new(callback),
                            args: flowing_args.into(),
                        };
                    }
                }
                HelperKind::Curried => {
                    // `helper(arg₀, ..., argₙ₋₁)(cb₀, ..., cb_{m-1})` with
                    // m = inner_arity: 1 for a church pair (`KP1`), ≥2 for
                    // a church Either/Option (`KP2`), where
                    // `active_inner_index` picks the callback that fires;
                    // the other inner args are dead (must be pure).
                    if args.len() == self.shape.inner_arity
                        && let PseudoExpr::Apply {
                            function: inner_fn,
                            args: outer_args,
                        } = &function
                        && outer_args.len() == self.shape.arity
                        && let PseudoExpr::Var { name, id } = inner_fn.as_ref()
                        && matches_binder(
                            self.binder_id,
                            self.binder_name,
                            self.shadow_depth,
                            name,
                            id,
                        )
                        && is_pure_callback(&args[self.shape.active_inner_index])
                        && inner_dead_args_are_pure(&args, self.shape.active_inner_index)
                        && dead_args_are_pure(outer_args, &self.shape.flowing_indices)
                    {
                        self.inlined_count += 1;
                        let active_idx = self.shape.active_inner_index;
                        let callback = args.swap_remove(active_idx);
                        let flowing_args = pick_flowing_args(
                            (outer_args.clone()).into_vec(),
                            &self.shape.flowing_indices,
                        );
                        return PseudoExpr::Apply {
                            function: PBox::new(callback),
                            args: flowing_args.into(),
                        };
                    }
                }
            }
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
    }
    let mut inliner = CallInliner {
        binder_id,
        binder_name,
        shape,
        kind,
        inlined_count: 0,
        shadow_depth: 0,
    };
    let rewritten = inliner.fold(expr);
    (rewritten, inliner.inlined_count)
}

/// Count references to the binder in `expr`, skipping scopes that
/// shadow it.
fn count_refs(expr: &PseudoExpr, target_id: Option<VarId>, target_name: &str) -> usize {
    struct RefCounter<'a> {
        target_id: Option<VarId>,
        target_name: &'a str,
        count: usize,
        shadow_depth: usize,
    }
    impl ExprVisitor for RefCounter<'_> {
        fn visit_var(&mut self, name: &str, id: &Option<VarId>) {
            if matches_binder(
                self.target_id,
                self.target_name,
                self.shadow_depth,
                name,
                id,
            ) {
                self.count += 1;
            }
        }
        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            if params.iter().any(|p| p.as_str() == self.target_name) {
                self.shadow_depth += 1;
            }
        }
        fn visit_lambda_post(&mut self, params: &[Binder]) {
            if params.iter().any(|p| p.as_str() == self.target_name) {
                self.shadow_depth -= 1;
            }
        }
        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            if name.as_str() == self.target_name
                || params.iter().any(|p| p.as_str() == self.target_name)
            {
                self.shadow_depth += 1;
            }
        }
        fn visit_recfn_post(&mut self, name: &Binder, params: &[Binder]) {
            if name.as_str() == self.target_name
                || params.iter().any(|p| p.as_str() == self.target_name)
            {
                self.shadow_depth -= 1;
            }
        }
        fn visit_let_pre(&mut self, name: &str) {
            if name == self.target_name {
                self.shadow_depth += 1;
            }
        }
        fn visit_let_post(&mut self, name: &str) {
            if name == self.target_name {
                self.shadow_depth -= 1;
            }
        }
        fn visit_when_clause_pre(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            if shadows_target(subject_name, &clause.pattern, self.target_name) {
                self.shadow_depth += 1;
            }
        }
        fn visit_when_clause_post(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            if shadows_target(subject_name, &clause.pattern, self.target_name) {
                self.shadow_depth -= 1;
            }
        }
    }
    let mut c = RefCounter {
        target_id,
        target_name,
        count: 0,
        shadow_depth: 0,
    };
    c.walk(expr);
    c.count
}

/// The rewrite moves the callback from arg position to function
/// position, and Plutus's strict `Apply` evaluates the function
/// before its args, so the two swap evaluation order. Equivalent
/// only when evaluating the callback has no observable effect:
/// `Var` (no eval cost) and `Lambda` / `RecFn` literals (eval
/// just packs a closure).
fn is_pure_callback(expr: &PseudoExpr) -> bool {
    matches!(
        expr,
        PseudoExpr::Var { .. } | PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. }
    )
}

/// KP2 (curried form) purity guard: the inner-projection args at
/// the non-active positions are evaluated by the original chain
/// (`pack(args)(cb_active, cb_dead)` evaluates both callbacks)
/// but DROPPED by the rewrite. Refuse unless they're all pure.
fn inner_dead_args_are_pure(inner_args: &[PseudoExpr], active_index: usize) -> bool {
    for (i, arg) in inner_args.iter().enumerate() {
        if i == active_index {
            continue;
        }
        if !super::purity::is_pure_value(arg) {
            return false;
        }
    }
    true
}

/// Purity guard for the Direct form, where the LAST `call_args`
/// element is the callback (checked separately by
/// `is_pure_callback`). The remaining positions not in
/// `flowing_indices` are dead arg slots: the original evaluates
/// them, the rewrite drops them — refuse unless they are all
/// pure.
///
/// The Curried form uses `dead_args_are_pure` instead, its
/// callback living in a separate inner Apply rather than the
/// outer args list.
fn dead_args_are_pure_with_callback_at_end(
    call_args: &[PseudoExpr],
    flowing_indices: &[usize],
) -> bool {
    let last_pos = call_args.len() - 1;
    for (i, arg) in call_args.iter().enumerate() {
        if i == last_pos {
            continue;
        }
        if flowing_indices.contains(&i) {
            continue;
        }
        if !super::purity::is_pure_value(arg) {
            return false;
        }
    }
    true
}

fn dead_args_are_pure(call_args: &[PseudoExpr], flowing_indices: &[usize]) -> bool {
    for (i, arg) in call_args.iter().enumerate() {
        if flowing_indices.contains(&i) {
            continue;
        }
        if !super::purity::is_pure_value(arg) {
            return false;
        }
    }
    true
}

/// Select call-site args at the flowing-index positions, in the
/// matcher's ascending (= declaration) order.
///
/// `call_args` holds the NON-callback args: for `Direct` mode,
/// `args` after the callback has been popped; for `Curried`, the
/// outer-Apply args. `flowing_indices` carry positions in
/// `0..call_args.len()`.
fn pick_flowing_args(call_args: Vec<PseudoExpr>, flowing_indices: &[usize]) -> Vec<PseudoExpr> {
    // Identity case (no dead args): return as-is, no cloning.
    let identity = flowing_indices.len() == call_args.len()
        && flowing_indices.iter().enumerate().all(|(i, &p)| i == p);
    if identity {
        return call_args;
    }
    // Dead-arg case: cherry-pick by index.
    flowing_indices
        .iter()
        .map(|&i| call_args[i].clone())
        .collect()
}

fn matches_binder(
    target_id: Option<VarId>,
    target_name: &str,
    shadow_depth: usize,
    var_name: &str,
    var_id: &Option<VarId>,
) -> bool {
    if let Some(target) = target_id {
        if let Some(other) = var_id {
            return *other == target;
        }
        return false;
    }
    if var_id.is_some() {
        return false;
    }
    shadow_depth == 0 && var_name == target_name
}

fn shadows_target(
    subject_name: Option<&Binder>,
    pattern: &crate::pseudo::ast::WhenPattern,
    target_name: &str,
) -> bool {
    if let Some(sn) = subject_name {
        if sn.as_str() == target_name {
            return true;
        }
    }
    pattern_binds_name(pattern, target_name)
}

fn pattern_binds_name(pattern: &crate::pseudo::ast::WhenPattern, target_name: &str) -> bool {
    use crate::pseudo::ast::WhenPattern;
    match pattern {
        WhenPattern::Var(b) => b.as_str() == target_name,
        WhenPattern::Pair(a, b) => a.as_str() == target_name || b.as_str() == target_name,
        WhenPattern::Tuple(binders) => binders.iter().any(|b| b.as_str() == target_name),
        WhenPattern::Constructor { fields, .. } => fields.iter().any(|b| b.as_str() == target_name),
        WhenPattern::List { elements, tail } => {
            elements.iter().any(|b| b.as_str() == target_name)
                || tail.as_ref().is_some_and(|t| t.as_str() == target_name)
        }
        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
    }
}

#[cfg(test)]
mod tests;
