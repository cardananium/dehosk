//! Pre-computation passes for MidExpr:
//!
//! Force/Thunk resolution (Force(Thunk(x)) → x)
//! Inverse operation cancellation (un_i_data(i_data(x)) → x)
//! Dead-let elimination (use_count == 0)
//! Trivial-let inlining and immediate-app folding
//! Y-combinator → recursive closure conversion

use std::collections::HashMap;

use uplc::builtins::DefaultFunction;

use crate::pseudo::mid::expr::MidExpr;
use crate::pseudo::mid::expr_id::{ProvenanceBuilder, refresh_mid_ids};
use crate::pseudo::var_id::VarId;

use super::fold::{
    Descend, MidCollector, Rewritten, rewrite_bottom_up, rewrite_bottom_up_fixpoint,
    rewrite_bottom_up_selective, substitute_var,
};

/// Run all pre-computation passes on a MidExpr tree, after
/// use_count/abstract-evaluation analysis has updated the interpreter's env.
///
/// Ordering invariants:
/// Pattern recognition runs first so later passes see structured nodes
///   (If, Case, Trace) instead of builtins.
/// Recursive marking must run before Y-comb conversion.
/// Force/thunk resolution must run before dead-let elimination — resolved
///   thunks may reduce use counts.
/// Dead-let elimination must run before inlining.
/// Inlining creates Apply(Closure) → fold converts to Let.
/// Y-comb conversion creates new Let/Closure → re-inline cleans up.
/// The final re-fold catches Apply(Builtin) in closure bodies from re-inlining.
pub(crate) fn run_precompute(
    expr: &mut MidExpr,
    provenance: &mut ProvenanceBuilder,
    safe_mode: bool,
) {
    super::patterns::recognize_patterns(expr, provenance);

    // Y-combinator marking on Let bindings
    if !safe_mode {
        mark_recursive_lets(expr);
    }

    resolve_force_thunk(expr);

    // Cancel inverse operations (skip in safe mode — some cancellations are heuristic)
    if !safe_mode {
        cancel_inverses(expr, provenance);
    }

    // Refresh use counts — the preceding passes drop nodes, so EliminateDeadLets
    // would otherwise work on stale counts.
    super::use_count::apply_use_counts(expr);

    eliminate_dead_lets(expr, provenance);

    // Inline trivial bindings (zero-arg builtins, variable aliases, literals)
    inline_trivial_lets(expr, provenance);

    // Fold immediate lambda applications: Apply(Closure(p, body), [arg]) → Let(p=arg, body)
    fold_immediate_apps(expr, provenance);

    // Convert Y-combinator self-application pattern to recursive closures
    // fn(__self, x) { ...__self(__self, y)... } + f(f, input) → rec fn f(x) { ...f(y)... }
    if !safe_mode {
        let converted = convert_y_comb(expr, provenance);

        // Clean up remaining f(f) / f(f, args) sites, only for the closures
        // `ConvertYComb` converted — see `cleanup_recursive_call_sites`.
        cleanup_recursive_call_sites(expr, provenance, &converted);

        // Re-inline trivial let bindings created by Y-comb conversion.
        inline_trivial_lets(expr, provenance);
    }

    // Re-fold Apply(Builtin) patterns inside Closure bodies.
    fold_immediate_apps(expr, provenance);

    // Rewrite passes clone and substitute whole subtrees, so refresh ids once at
    // the end to restore the global MidExprId uniqueness invariant while keeping
    // provenance attached to the final tree.
    refresh_mid_ids(expr, provenance);
}

fn collect_mid_subtree_ids(expr: &MidExpr) -> Vec<crate::pseudo::mid::expr_id::MidExprId> {
    let mut ids = Vec::new();
    let mut stack = vec![expr];

    while let Some(current) = stack.pop() {
        ids.push(current.id());
        let mut children = current.children();
        children.reverse();
        stack.extend(children);
    }

    ids.sort_unstable();
    ids.dedup();
    ids
}

fn absorb_mid_subtree(
    target_id: crate::pseudo::mid::expr_id::MidExprId,
    subtree: &MidExpr,
    provenance: &mut ProvenanceBuilder,
) {
    for mid_id in collect_mid_subtree_ids(subtree) {
        if mid_id != target_id {
            provenance.absorb_mid(target_id, mid_id);
        }
    }
}

// =============================================================================
// Mark Recursive Lets
// =============================================================================

/// Tag every `let` whose value refers to the binder itself as recursive.
///
/// Pre-order and iterative: the work touches only the node, so no ownership
/// dance is needed — unlike the bottom-up passes below, which act on a node
/// after its children and therefore go through [`rewrite_bottom_up`].
fn mark_recursive_lets(expr: &mut MidExpr) {
    let mut pending: Vec<&mut MidExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let MidExpr::Let { var, value, .. } = current {
            super::patterns::try_mark_recursive(*var, value);
        }
        pending.extend(current.children_mut().into_iter().rev());
    }
}

// =============================================================================
// Force/Thunk Resolution
// =============================================================================

/// Resolve Force(Thunk(body)) → body throughout the tree.
/// Also resolves Force(Var(v)) where v is known to be a Thunk by inlining the thunk body.
/// Uses multi-pass resolution to handle chained thunks (thunk A referencing thunk B).
fn resolve_force_thunk(expr: &mut MidExpr) {
    // Collect thunk bindings: VarId → thunk body (cloned)
    let mut thunk_bodies: HashMap<VarId, MidExpr> = HashMap::new();
    let mut collector = ThunkBodyCollector {
        thunks: &mut thunk_bodies,
    };
    collector.walk(expr);

    // Transitively resolve thunk bodies.
    // If thunk A's body is Force(Var(B)) and B is also a thunk,
    // replace A's body with B's resolved body.
    let max_iters = thunk_bodies.len();
    for _ in 0..max_iters {
        let mut changed = false;
        let snapshot = thunk_bodies.clone();
        for body in thunk_bodies.values_mut() {
            // Resolve Force(Var(v)) patterns within thunk bodies
            if resolve_force_thunks(body, &snapshot) {
                changed = true;
            }
            // Also resolve Var(v) where v is a thunk → thunk body directly
            if let MidExpr::Var { var, .. } = body
                && let Some(resolved) = snapshot.get(var)
            {
                *body = resolved.clone();
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Resolve Force(Thunk) and Force(Var(thunk)) in main tree
    resolve_force_thunks(expr, &thunk_bodies);
}

struct ThunkBodyCollector<'a> {
    thunks: &'a mut HashMap<VarId, MidExpr>,
}

impl MidCollector for ThunkBodyCollector<'_> {
    fn inspect_expr(&mut self, expr: &MidExpr) {
        if let MidExpr::Let { var, value, .. } = expr
            && let MidExpr::Thunk { body, .. } = value.as_ref()
        {
            self.thunks.insert(*var, (**body).clone());
        }
    }
}

/// Resolve `Force(Thunk(inner))` → `resolved = inner`, and `Force(Var(v))`
/// where `v` is a known thunk → `resolved = <that thunk's body>`.
fn resolve_force_thunks(expr: &mut MidExpr, thunk_bodies: &HashMap<VarId, MidExpr>) -> bool {
    let mut changed = false;
    let placeholder = MidExpr::Error { id: expr.id() };
    let taken = std::mem::replace(expr, placeholder);
    *expr = rewrite_bottom_up(taken, &mut |mut node| {
        if let MidExpr::Force {
            id,
            ref mut body,
            ref mut resolved,
        } = node
// Skip if already resolved — idempotent across fix-point iterations
            && resolved.is_none()
        {
            // Rule 1: Force(Thunk(inner)) → resolved = inner
            if let MidExpr::Thunk {
                body: thunk_body, ..
            } = body.as_mut()
            {
                let inner = std::mem::replace(thunk_body.as_mut(), MidExpr::Error { id });
                *resolved = Some(Box::new(inner));
                changed = true;
            // Rule 2: Force(Var(v)) where v is a known thunk variable.
            // Inline the thunk body into resolved so the lowerer can use it
            // directly.
            } else if let MidExpr::Var { var, .. } = body.as_ref()
                && let Some(thunk_body) = thunk_bodies.get(var)
            {
                *resolved = Some(Box::new(thunk_body.clone()));
                changed = true;
            }
        }
        node
    });
    changed
}

/// Cancel inverse operations: `un_i_data(i_data(x))` → `x`, etc.
///
/// Bottom-up, so a chain of inverses collapses in one pass. Runs on the owned
/// rewriter rather than a `&mut` visitor: acting on a node AFTER its children
/// needs the node while the children are out of it, which only ownership
/// allows — see [`rewrite_bottom_up`].
fn cancel_inverses(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    let placeholder = MidExpr::Error { id: expr.id() };
    let taken = std::mem::replace(expr, placeholder);
    *expr = rewrite_bottom_up(taken, &mut |node| {
        let MidExpr::Builtin {
            id: outer_id,
            fun,
            ref args,
            ..
        } = node
        else {
            return node;
        };
        if args.len() != 1 {
            return node;
        }
        let MidExpr::Builtin {
            id: inner_id,
            fun: inner_fun,
            args: ref inner_args,
            ..
        } = args[0]
        else {
            return node;
        };
        if inner_args.len() != 1 || !is_inverse_pair(fun, inner_fun) {
            return node;
        }
        // Safe: if inner(x) would error on a type mismatch, the original
        // program errors too, so cancellation preserves observable behavior.
        let inner_arg = inner_args[0].clone();
        let target_id = inner_arg.id();
        provenance.absorb_mid(target_id, outer_id);
        provenance.absorb_mid(target_id, inner_id);
        inner_arg
    });
}

fn is_inverse_pair(outer: DefaultFunction, inner: DefaultFunction) -> bool {
    matches!(
        (outer, inner),
        (DefaultFunction::UnIData, DefaultFunction::IData)
            | (DefaultFunction::IData, DefaultFunction::UnIData)
            | (DefaultFunction::UnBData, DefaultFunction::BData)
            | (DefaultFunction::BData, DefaultFunction::UnBData)
            | (DefaultFunction::UnListData, DefaultFunction::ListData)
            | (DefaultFunction::ListData, DefaultFunction::UnListData)
            | (DefaultFunction::UnMapData, DefaultFunction::MapData)
            | (DefaultFunction::MapData, DefaultFunction::UnMapData) // NOTE: DecodeUtf8/EncodeUtf8 are NOT inverse-safe because
                                                                     // DecodeUtf8 validates UTF-8 — cancellation would remove that check.
    )
}

// =============================================================================
// Dead Code Elimination
// =============================================================================

/// Drop `let`s that are never used and whose value cannot have an effect.
///
/// Bottom-up so an inner elimination can make an outer binding dead in the same
/// pass. On the owned rewriter — see [`rewrite_bottom_up`].
fn eliminate_dead_lets(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    let taken = std::mem::replace(expr, MidExpr::Error { id: expr.id() });
    *expr = rewrite_bottom_up(taken, &mut |node| {
        if let MidExpr::Let {
            id,
            use_count,
            ref value,
            ..
        } = node
            && use_count == 0
            && is_side_effect_free(value)
        {
            // Dead binding — return just the body
            if let MidExpr::Let { body, value, .. } = node {
                let body = *body;
                let target_id = body.id();
                provenance.absorb_mid(target_id, id);
                absorb_mid_subtree(target_id, &value, provenance);
                return body;
            }
        }
        node
    });
}

fn is_side_effect_free(expr: &MidExpr) -> bool {
    match expr {
        MidExpr::Lit { .. }
        | MidExpr::Var { .. }
        | MidExpr::Closure { .. }
        | MidExpr::Thunk { .. }
        | MidExpr::Constr { .. }
        | MidExpr::Data { .. } => true,
        MidExpr::Builtin { args, .. } if args.is_empty() => true,
        _ => false,
    }
}

// =============================================================================
// Inline Trivial Let Bindings
// =============================================================================

/// Inline `let`s whose value is trivial (a literal, an alias, a nullary builtin).
///
/// Bottom-up, on the owned rewriter — see [`rewrite_bottom_up`].
fn inline_trivial_lets(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    let taken = std::mem::replace(expr, MidExpr::Error { id: expr.id() });
    *expr = rewrite_bottom_up(taken, &mut |node| {
        if let MidExpr::Let {
            id,
            ref var,
            ref value,
            use_count,
            ..
        } = node
            && is_trivially_inlinable(value, use_count)
        {
            let target = *var;
            let replacement = value.clone();
            if let MidExpr::Let { body, .. } = node {
                let result = substitute_var(*body, target, &replacement, provenance);
                let target_id = result.id();
                provenance.absorb_mid(target_id, id);
                absorb_mid_subtree(target_id, &replacement, provenance);
                return result;
            }
        }
        node
    });
}

fn is_trivially_inlinable(expr: &MidExpr, _use_count: u32) -> bool {
    match expr {
        // Zero-arg builtin: always inline (just a function reference, no eval)
        MidExpr::Builtin { args, .. } if args.is_empty() => true,
        // Strictly partial-applied builtin with literal args: still a function
        // value (no evaluation yet) — safe to inline.
        MidExpr::Builtin { fun, args, .. }
            if args.iter().all(|a| matches!(a, MidExpr::Lit { .. }))
                && args.len() < fun.arity() =>
        {
            true
        }
        // Variable alias: let x = y
        MidExpr::Var { .. } => true,
        MidExpr::Lit { .. } => true,
        _ => false,
    }
}

// =============================================================================
// Fold Immediate Lambda Applications
// =============================================================================

/// Fold applications that can be resolved structurally: hoist a `let` out of
/// function position, merge args into a partially-applied builtin, and turn
/// `Apply(Closure(ps, body), args)` into a chain of `let`s.
fn fold_immediate_apps(expr: &mut MidExpr, provenance: &mut ProvenanceBuilder) {
    let taken = std::mem::replace(expr, MidExpr::Error { id: expr.id() });
    *expr = rewrite_bottom_up_fixpoint(taken, &mut |_| Descend::All, &mut |node| {
        let MidExpr::Apply { id, function, args } = node else {
            return Rewritten::Done(node);
        };
        let function = *function;

        // Hoist Let from Apply function position:
        // Apply(Let(v, val, inner_fn), args) → Let(v, val, Apply(inner_fn, args))
        if let MidExpr::Let {
            id: let_id,
            var,
            value,
            body,
            use_count,
        } = function
        {
            return Rewritten::Again(MidExpr::Let {
                id: let_id,
                var,
                value,
                body: Box::new(MidExpr::Apply {
                    id,
                    function: body,
                    args,
                }),
                use_count,
            });
        }

        // Merge partial-applied builtins
        if let MidExpr::Builtin { args: ba, fun, .. } = &function {
            let should_merge = if ba.is_empty() {
                is_data_constructor_builtin(fun)
            } else {
                true
            };
            if should_merge
                && let MidExpr::Builtin {
                    id: b_id,
                    fun,
                    forces,
                    args: mut existing,
                    folded,
                } = function
            {
                provenance.absorb_mid(b_id, id);
                existing.extend(args);
                return Rewritten::Done(MidExpr::Builtin {
                    id: b_id,
                    fun,
                    forces,
                    args: existing,
                    folded,
                });
            }
        }

        // Check: Apply(Closure(params, body), args) with matching length.
        // The body needs no further folding: it was already rewritten as a
        // descendant of this node, and the walk is bottom-up.
        if let MidExpr::Closure {
            id: closure_id,
            params,
            body,
            ..
        } = &function
            && params.len() == args.len()
            && !args.is_empty()
        {
            let mut result = (**body).clone();
            for (param, arg) in params.iter().zip(args.iter()).rev() {
                result = MidExpr::Let {
                    id, // temporary duplicate — refresh_mid_ids fixes at end of precompute
                    var: *param,
                    value: Box::new(arg.clone()),
                    body: Box::new(result),
                    use_count: 0,
                };
            }
            provenance.absorb_mid(result.id(), *closure_id);
            return Rewritten::Done(result);
        }

        Rewritten::Done(MidExpr::Apply {
            id,
            function: Box::new(function),
            args,
        })
    });
}

fn is_data_constructor_builtin(fun: &DefaultFunction) -> bool {
    matches!(
        fun,
        DefaultFunction::ConstrData
            | DefaultFunction::MkCons
            | DefaultFunction::IData
            | DefaultFunction::BData
            | DefaultFunction::ListData
            | DefaultFunction::MapData
            | DefaultFunction::MkNilData
            | DefaultFunction::MkNilPairData
            | DefaultFunction::MkPairData
    )
}

// =============================================================================
// Y-Combinator → Recursive Conversion
// =============================================================================

/// Convert the Y-combinator self-application shape into a real recursive
/// closure: `fn(__self, x) { …__self(__self, y)… }` + `f(f, input)` becomes
/// `rec fn f(x) { …f(y)… }`.
///
/// Bottom-up, on the owned rewriter — see [`rewrite_bottom_up`]. Returns the
/// vars it ACTUALLY converted; only those satisfy the `RecFn` contract, so only
/// their `var(var)` knots are safe for `cleanup_recursive_call_sites`.
fn convert_y_comb(
    expr: &mut MidExpr,
    provenance: &mut ProvenanceBuilder,
) -> std::collections::HashSet<VarId> {
    let mut converted: std::collections::HashSet<VarId> = std::collections::HashSet::new();
    let taken = std::mem::replace(expr, MidExpr::Error { id: expr.id() });
    *expr = rewrite_bottom_up(taken, &mut |expr| {
        if let MidExpr::Let {
            id,
            var,
            value,
            body,
            use_count,
        } = expr
        {
            if let MidExpr::Closure {
                id: c_id,
                ref params,
                body: ref closure_body,
                recursive,
            } = *value
                && params.len() >= 2
                && recursive.is_none()
            {
                let self_param = params[0];
                if contains_self_app_pattern(closure_body, self_param) {
                    let mut real_params: Vec<VarId> = params[1..].to_vec();
                    let mut actual_body = (**closure_body).clone();
                    let mut removed_body_ids = Vec::new();

                    // Flatten nested Lambdas (including through Thunk wrappers)
                    loop {
                        match actual_body {
                            MidExpr::Closure {
                                id: inner_id,
                                params: inner_params,
                                body: inner_body,
                                ..
                            } => {
                                removed_body_ids.push(inner_id);
                                real_params.extend(inner_params);
                                actual_body = *inner_body;
                            }
                            MidExpr::Thunk {
                                id: thunk_id,
                                body: inner,
                                ..
                            } => {
                                removed_body_ids.push(thunk_id);
                                actual_body = *inner;
                            }
                            _ => break,
                        }
                    }

                    // Rewrite closure body: replace self_param(self_param, args) → var(args)
                    let new_body = rewrite_self_calls(actual_body, self_param, var, provenance);

                    let new_closure = MidExpr::Closure {
                        id: c_id,
                        params: real_params,
                        body: Box::new(new_body),
                        recursive: Some(var),
                    };
                    converted.insert(var);
                    for removed_id in removed_body_ids {
                        provenance.absorb_mid(c_id, removed_id);
                    }

                    // Rewrite call sites: var(var, args) → var(args)
                    let body = rewrite_call_sites(*body, var, provenance);

                    return MidExpr::Let {
                        id,
                        var,
                        value: Box::new(new_closure),
                        body: Box::new(body),
                        use_count,
                    };
                }
            }

            return MidExpr::Let {
                id,
                var,
                value,
                body,
                use_count,
            };
        }

        expr
    });
    converted
}

/// Check if expression contains Apply(Var(self_param), [Var(self_param), ...]) pattern.
fn contains_self_app_pattern(expr: &MidExpr, self_param: VarId) -> bool {
    struct Checker {
        self_param: VarId,
        found: bool,
    }
    impl MidCollector for Checker {
        fn inspect_expr(&mut self, expr: &MidExpr) {
            if let MidExpr::Apply { function, args, .. } = expr
                && let MidExpr::Var { var, .. } = function.as_ref()
                && *var == self.self_param
                && !args.is_empty()
                && let MidExpr::Var { var: first_arg, .. } = &args[0]
                && *first_arg == self.self_param
            {
                self.found = true;
            }
        }
    }
    let mut checker = Checker {
        self_param,
        found: false,
    };
    checker.walk(expr);
    checker.found
}

/// Rewrite self-application calls: self_param(self_param, args) → rec_var(args)
fn rewrite_self_calls(
    expr: MidExpr,
    self_param: VarId,
    rec_var: VarId,
    provenance: &mut ProvenanceBuilder,
) -> MidExpr {
    // Which children to walk. The special `self(self, …)` shape deliberately
    // does NOT descend into the callee or the first argument: both must stay
    // `Var(self_param)` for the shape check that runs when the node is
    // reassembled. A `let`/`Closure` binder that rebinds `self_param` shadows
    // it, so its body is left alone.
    rewrite_bottom_up_selective(
        expr,
        &mut |node| match node {
            MidExpr::Apply { function, args, .. }
                if is_self_self_call(function.as_ref(), args, self_param) =>
            {
                // Children are `[function, arg0, arg1, …]`; keep 0 and 1 intact.
                Descend::Only((2..=args.len()).collect())
            }
            MidExpr::Let { var, .. } if *var == self_param => Descend::Only(vec![0]),
            MidExpr::Closure { params, .. } if params.contains(&self_param) => Descend::None,
            _ => Descend::All,
        },
        &mut |node| match node {
            MidExpr::Apply { id, function, args }
                if is_self_self_call(&function, &args, self_param) =>
            {
                let (function_id, first_arg_id) = (function.id(), args[0].id());
                let real_args: Vec<MidExpr> = args.into_iter().skip(1).collect();
                provenance.absorb_mid(id, function_id);
                provenance.absorb_mid(id, first_arg_id);
                MidExpr::Apply {
                    id,
                    function: Box::new(MidExpr::Var {
                        id, // temporary duplicate — refresh_mid_ids fixes
                        var: rec_var,
                    }),
                    args: real_args,
                }
            }
            MidExpr::Var { id, var } if var == self_param => MidExpr::Var { id, var: rec_var },
            other => other,
        },
    )
}

/// `self_param(self_param, …)` — the Y-combinator knot at a call site.
fn is_self_self_call(function: &MidExpr, args: &[MidExpr], self_param: VarId) -> bool {
    matches!(function, MidExpr::Var { var, .. } if *var == self_param)
        && matches!(args.first(), Some(MidExpr::Var { var, .. }) if *var == self_param)
}

/// Rewrite call sites: var(var, args) → var(args) (drop first self-arg)
fn rewrite_call_sites(
    expr: MidExpr,
    rec_var: VarId,
    provenance: &mut ProvenanceBuilder,
) -> MidExpr {
    // Same descent rule as `rewrite_self_calls`: the callee and the first
    // argument of a `rec_var(rec_var, …)` knot are left untouched so the shape
    // check still sees them when the node is reassembled. No shadowing arm here
    // — `rec_var` is the closure's own name, not a parameter anything rebinds.
    rewrite_bottom_up_selective(
        expr,
        &mut |node| match node {
            MidExpr::Apply { function, args, .. }
                if is_self_self_call(function.as_ref(), args, rec_var) =>
            {
                Descend::Only((2..=args.len()).collect())
            }
            _ => Descend::All,
        },
        &mut |node| match node {
            MidExpr::Apply { id, function, args }
                if is_self_self_call(&function, &args, rec_var) =>
            {
                let (function_id, first_arg_id) = (function.id(), args[0].id());
                let real_args: Vec<MidExpr> = args.into_iter().skip(1).collect();
                provenance.absorb_mid(id, function_id);
                provenance.absorb_mid(id, first_arg_id);
                if real_args.is_empty() {
                    return MidExpr::Var { id, var: rec_var };
                }
                MidExpr::Apply {
                    id,
                    function: Box::new(MidExpr::Var {
                        id, // temporary duplicate — refresh_mid_ids fixes
                        var: rec_var,
                    }),
                    args: real_args,
                }
            }
            other => other,
        },
    )
}

// =============================================================================
// Recursive Call Site Cleanup
// =============================================================================

/// After Y-comb conversion, clean up any remaining f(f) or f(f, args) patterns
/// in the entire tree, for the closures `ConvertYComb` actually CONVERTED. Collects
/// their rec fn VarIds (intersected with `converted`), then rewrites globally.
///
/// The `converted` gate is load-bearing: `MarkRecursiveLets` also sets
/// `recursive: Some` on un-restructured 1-param closures (the eta-expanded Z
/// half, whose body still self-applies a PARAM). Collapsing those `v(v)` knots
/// deletes the fixpoint and leaves a body that seats a non-function in its self
/// slot — a valid-looking-wrong render. Only vars converted by `ConvertYComb` have
/// had their self-calls rewritten to the `var(args)` RecFn form.
fn cleanup_recursive_call_sites(
    expr: &mut MidExpr,
    provenance: &mut ProvenanceBuilder,
    converted: &std::collections::HashSet<VarId>,
) {
    struct RecVarCollector<'a> {
        rec_vars: Vec<VarId>,
        converted: &'a std::collections::HashSet<VarId>,
    }
    impl MidCollector for RecVarCollector<'_> {
        fn inspect_expr(&mut self, expr: &MidExpr) {
            if let MidExpr::Closure {
                recursive: Some(var),
                ..
            } = expr
                && self.converted.contains(var)
            {
                self.rec_vars.push(*var);
            }
        }
    }

    let mut collector = RecVarCollector {
        rec_vars: Vec::new(),
        converted,
    };
    collector.walk(expr);

    if collector.rec_vars.is_empty() {
        return;
    }

    let sentinel = MidExpr::Error {
        id: crate::pseudo::mid::expr_id::MidExprId::new(0),
    };
    let mut result = std::mem::replace(expr, sentinel);
    for var in collector.rec_vars {
        result = rewrite_call_sites(result, var, provenance);
    }
    *expr = result;
}

#[cfg(test)]
mod tests;
