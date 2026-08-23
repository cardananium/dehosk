//! Hoist multi-arg function calls whose arguments are all "stable" (free
//! vars are entry-Lambda parameters or top-level let ids) and which
//! appear ≥3 times in the validator-entry body.
//!
//! V1 scripts emit the same multi-arg call many times with identical
//! argument lists. Hoisting to a single `let X = f(...)` at the entry
//! top collapses every use-site to a bare `Var`.
//!
//! Restricted to `Apply { Var(f, Some(f_id)), args }` with
//! `args.len() >= 2`. Every arg is "stable": its free vars ⊆ entry
//! params + top let ids, counting the binders the arg itself introduces.
//! Any shape not known to be pure counts as unstable. At least one arg
//! must be non-trivial (not just a bare `Var`) — bare 1-arg calls are
//! already handled by `hoist_entry_param_chain_calls`. Threshold: ≥3
//! occurrences with the same structural arg list.
//!
//! A hoisted call's free vars are stable at entry body top, so
//! evaluation there is well-defined. Plutus calls are pure, so eager
//! evaluation matches semantics.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

pub(super) fn hoist_pure_multi_arg_calls(expr: PseudoExpr) -> PseudoExpr {
    super::scope_recurse::run_with_scope_fn(
        expr,
        // Seed the stable set with top-level let ids (helpers and consts)
        // so calls like `helper_20(top_const, ...)` qualify.
        |top_lets| {
            top_lets
                .iter()
                .filter_map(|(_, lid, _)| lid.as_ref().copied())
                .collect()
        },
        |body, stable| run_scope_until_fixed_point(body, stable.clone()),
    )
}

/// Iterate the per-scope hoist to a fixed point: a freshly minted `_args`
/// let is itself a stable Var, which can unblock a wrapping call.
fn run_scope_until_fixed_point(body: PseudoExpr, stable: HashSet<VarId>) -> PseudoExpr {
    let mut body = body;
    let mut rounds = 0;
    loop {
        let (next_body, hoists_produced) = process_scope(body, &stable);
        body = next_body;
        if hoists_produced == 0 {
            break;
        }
        rounds += 1;
        if rounds >= 8 {
            debug_assert!(
                false,
                "hoist_pure_multi_arg_calls: per-scope fixed-point exceeded 8 rounds"
            );
            break;
        }
    }
    body
}

/// Run the hoist on a single scope's body. The stable set is `outer` plus
/// the ids of the body's outer let chain; each hoist is inserted just after
/// the last chain let its callee or args depend on. Returns the rewritten
/// body and the number of hoists produced.
fn process_scope(body: PseudoExpr, outer_stable: &HashSet<VarId>) -> (PseudoExpr, usize) {
    let (body_chain, body_terminal) = super::scope_recurse::peel_top_lets(body);

    let mut chain_id_pos: HashMap<VarId, usize> = HashMap::new();
    for (i, (_, lid, _)) in body_chain.iter().enumerate() {
        if let Some(vid) = lid {
            chain_id_pos.insert(*vid, i);
        }
    }

    let mut stable = outer_stable.clone();
    for (_, lid, _) in &body_chain {
        if let Some(vid) = lid {
            stable.insert(*vid);
        }
    }

    let mut counts: HashMap<(VarId, u64), CandidateInfo> = HashMap::new();
    let mut next_seen = 0usize;
    for (_, _, v) in &body_chain {
        count_calls(v, &stable, &mut counts, &mut next_seen);
    }
    count_calls(&body_terminal, &stable, &mut counts, &mut next_seen);

    // Order by first occurrence, then mint the hoists' VarIds. Both halves
    // matter: `counts` is a HashMap, so draining it yields the plans in an
    // arbitrary order, and minting during the drain would tie each plan's
    // id to that order.
    let mut ordered: Vec<((VarId, u64), CandidateInfo)> = counts
        .into_iter()
        .filter(|(_, info)| info.count >= 3)
        .collect();
    ordered.sort_by_key(|(_, info)| info.first_seen);

    let plans: Vec<HoistPlan> = ordered
        .into_iter()
        .map(|((fn_id, args_hash), info)| {
            let mut max_pos: Option<usize> = None;
            collect_chain_dep(&info.canonical_args, &chain_id_pos, &mut max_pos);
            if let Some(pos) = chain_id_pos.get(&fn_id) {
                max_pos = Some(max_pos.map_or(*pos, |m| m.max(*pos)));
            }
            let insertion_depth = max_pos.map(|p| p + 1).unwrap_or(0);
            HoistPlan {
                fn_id,
                args_hash,
                fn_name: info.fn_name,
                canonical_args: info.canonical_args,
                new_id: VarId::fresh_binding(),
                insertion_depth,
            }
        })
        .collect();

    if plans.is_empty() {
        return (
            super::scope_recurse::reassemble_top(body_chain, body_terminal),
            0,
        );
    }

    let mut name_counts: HashMap<String, usize> = HashMap::new();
    let mut new_names: Vec<String> = Vec::with_capacity(plans.len());
    for p in &plans {
        let stem = p
            .fn_name
            .strip_suffix("_call")
            .or_else(|| p.fn_name.strip_suffix("_result"))
            .unwrap_or(&p.fn_name);
        let base = format!("{}_args", stem);
        let n = name_counts.entry(stem.to_string()).or_insert(0);
        *n += 1;
        if *n == 1 {
            new_names.push(base);
        } else {
            new_names.push(format!("{}_{}", base, n));
        }
    }

    let body_chain: Vec<_> = body_chain
        .into_iter()
        .map(|(n, i, v)| (n, i, rewrite_calls(v, &plans, &new_names)))
        .collect();
    let body_terminal = rewrite_calls(body_terminal, &plans, &new_names);

    let chain_len = body_chain.len();
    let mut by_depth: Vec<Vec<usize>> = vec![Vec::new(); chain_len + 1];
    for (i, p) in plans.iter().enumerate() {
        let d = p.insertion_depth.min(chain_len);
        by_depth[d].push(i);
    }

    let mut new_chain: Vec<(String, Option<VarId>, PseudoExpr)> = Vec::new();
    for (pos, (lname, lid, lvalue)) in body_chain.into_iter().enumerate() {
        for &plan_idx in &by_depth[pos] {
            new_chain.push(build_hoist_let(&plans[plan_idx], &new_names[plan_idx]));
        }
        new_chain.push((lname, lid, lvalue));
    }
    for &plan_idx in &by_depth[chain_len] {
        new_chain.push(build_hoist_let(&plans[plan_idx], &new_names[plan_idx]));
    }

    let new_body = super::scope_recurse::reassemble_top(new_chain, body_terminal);
    let hoists_produced = plans.len();
    (
        super::scope_recurse::fold_identity_aliases(new_body),
        hoists_produced,
    )
}

fn build_hoist_let(plan: &HoistPlan, name: &str) -> (String, Option<VarId>, PseudoExpr) {
    let value = PseudoExpr::Apply {
        function: PBox::new(PseudoExpr::Var {
            name: plan.fn_name.clone(),
            id: Some(plan.fn_id),
        }),
        args: (plan.canonical_args.clone()).into(),
    };
    (name.to_string(), Some(plan.new_id), value)
}

fn collect_chain_dep(
    args: &[PseudoExpr],
    chain_id_pos: &HashMap<VarId, usize>,
    max_pos: &mut Option<usize>,
) {
    for a in args {
        walk_collect_dep(a, chain_id_pos, max_pos);
    }
}

fn walk_collect_dep(
    expr: &PseudoExpr,
    chain_id_pos: &HashMap<VarId, usize>,
    max_pos: &mut Option<usize>,
) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Var { id: Some(vid), .. } = cur
            && let Some(pos) = chain_id_pos.get(vid)
        {
            *max_pos = Some(max_pos.map_or(*pos, |m| m.max(*pos)));
        }
        pending.extend(children(cur).into_iter().rev());
    }
}

struct CandidateInfo {
    fn_name: String,
    canonical_args: Vec<PseudoExpr>,
    count: usize,
    /// Traversal index of this candidate's FIRST occurrence in the scope.
    ///
    /// Plan order decides the hoisted lets' emission order and which of two
    /// same-callee hoists keeps the plain `<fn>_args` name, so it must be a
    /// property of the program, not of the run. Ordering by
    /// `(fn_id, args_hash)` fails that: `args_hash` hashes the arguments' free
    /// `VarId`s, drawn from a thread-local counter that keeps climbing across
    /// decompiles, so the same script rendered twice in one process swaps the
    /// two names. First occurrence in a deterministic walk cannot drift, and
    /// it lists the hoists in reading order.
    first_seen: usize,
}

struct HoistPlan {
    fn_id: VarId,
    args_hash: u64,
    fn_name: String,
    canonical_args: Vec<PseudoExpr>,
    new_id: VarId,
    /// Position in the entry body's outer let chain after which this hoist
    /// must be inserted (0 = entry body top; chain_len = after all chain lets).
    insertion_depth: usize,
}

fn count_calls(
    expr: &PseudoExpr,
    stable: &HashSet<VarId>,
    counts: &mut HashMap<(VarId, u64), CandidateInfo>,
    next_seen: &mut usize,
) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let Some((fn_id, fn_name, args)) = match_multi_arg(cur, stable) {
            let h = hash_args(args);
            let entry = counts.entry((fn_id, h)).or_insert_with(|| {
                let first_seen = *next_seen;
                *next_seen += 1;
                CandidateInfo {
                    fn_name: fn_name.to_string(),
                    canonical_args: args.to_vec(),
                    count: 0,
                    first_seen,
                }
            });
            entry.count += 1;
        }
        pending.extend(children(cur).into_iter().rev());
    }
}

fn match_multi_arg<'a>(
    expr: &'a PseudoExpr,
    stable: &HashSet<VarId>,
) -> Option<(VarId, &'a str, &'a [PseudoExpr])> {
    let PseudoExpr::Apply { function, args } = expr else {
        return None;
    };
    if args.len() < 2 {
        return None;
    }
    let PseudoExpr::Var {
        id: Some(fn_id),
        name: fn_name,
    } = function.as_ref()
    else {
        return None;
    };
    let bound_in_arg = HashSet::new();
    if !args.iter().all(|a| is_stable_arg(a, stable, &bound_in_arg)) {
        return None;
    }
    let has_non_trivial = args.iter().any(|a| !matches!(a, PseudoExpr::Var { .. }));
    if !has_non_trivial {
        return None;
    }
    Some((*fn_id, fn_name, args.as_slice()))
}

fn is_stable_arg(expr: &PseudoExpr, stable: &HashSet<VarId>, bound: &HashSet<VarId>) -> bool {
    use std::rc::Rc;

    let mut pending: Vec<(&PseudoExpr, Rc<HashSet<VarId>>)> = vec![(expr, Rc::new(bound.clone()))];
    while let Some((cur, bound)) = pending.pop() {
        match cur {
            PseudoExpr::Var { id: Some(vid), .. } => {
                if !(stable.contains(vid) || bound.contains(vid)) {
                    return false;
                }
            }
            PseudoExpr::Var { id: None, .. } => {}
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_)
            | PseudoExpr::Error { .. } => {}
            PseudoExpr::FieldAccess { record, .. } => pending.push((record, bound)),
            PseudoExpr::IndexAccess { collection, .. } => pending.push((collection, bound)),
            PseudoExpr::Apply { function, args } => {
                for a in args.iter().rev() {
                    pending.push((a, bound.clone()));
                }
                pending.push((function, bound));
            }
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    pending.push((a, bound.clone()));
                }
            }
            PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => pending.push((inner, bound)),
            PseudoExpr::Lambda { params, body } => {
                let mut inner = bound.as_ref().clone();
                for p in params {
                    inner.insert(p.id);
                }
                pending.push((body, Rc::new(inner)));
            }
            PseudoExpr::RecFn { name, params, body } => {
                let mut inner = bound.as_ref().clone();
                inner.insert(name.id);
                for p in params {
                    inner.insert(p.id);
                }
                pending.push((body, Rc::new(inner)));
            }
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                let mut inner = bound.as_ref().clone();
                if let Some(vid) = id {
                    inner.insert(*vid);
                }
                pending.push((body, Rc::new(inner)));
                pending.push((value, bound));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push((else_branch, bound.clone()));
                pending.push((then_branch, bound.clone()));
                pending.push((condition, bound));
            }
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push((right, bound.clone()));
                pending.push((left, bound));
            }
            PseudoExpr::UnOp { operand, .. } => pending.push((operand, bound)),
            // Conservative: anything else, treat as not stable.
            _ => return false,
        }
    }
    true
}

/// Alpha-aware structural hash for an arg list. A binder reference
/// inside a Lambda/RecFn/Let body hashes by de-Bruijn depth, so two
/// `fn(x) { fail }` Lambdas hash alike whatever their params' VarIds.
fn hash_args(args: &[PseudoExpr]) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut h = DefaultHasher::new();
    args.len().hash(&mut h);
    let mut bound_depths: HashMap<VarId, usize> = HashMap::new();
    let mut depth_counter: usize = 0;
    for a in args {
        hash_expr(a, &mut h, &mut bound_depths, &mut depth_counter);
    }
    h.finish()
}

fn hash_expr<H: std::hash::Hasher>(
    expr: &PseudoExpr,
    h: &mut H,
    bound: &mut HashMap<VarId, usize>,
    depth: &mut usize,
) {
    use std::hash::Hash;

    enum Step<'a> {
        Visit(&'a PseudoExpr),
        // `args.len()` is hashed after `function` but before any `args` —
        // its own step so that byte order into the hasher survives.
        ApplyArgsLen(usize),
        // The selector/index is hashed only once its single child is
        // fully hashed, so each needs a step after that child's `Visit`.
        PostFieldAccess(&'a crate::pseudo::field_selector::FieldSelector),
        PostIndexAccess(usize),
        // Lambda/RecFn bind their names+params before descending into the
        // body and unwind them (in reverse) after; the unwind hashes
        // nothing, it only restores `bound`/`depth`.
        PopScope(Vec<VarId>),
        // `Let`'s bound id (if any) comes into scope AFTER the value is
        // hashed but BEFORE the body is.
        EnterLetBody {
            id: Option<VarId>,
            body: &'a PseudoExpr,
        },
        PopLet(Option<VarId>),
    }

    let mut steps = vec![Step::Visit(expr)];
    while let Some(step) = steps.pop() {
        match step {
            Step::Visit(expr) => {
                std::mem::discriminant(expr).hash(h);
                match expr {
                    PseudoExpr::Var {
                        id: Some(vid),
                        name,
                    } => {
                        if let Some(d) = bound.get(vid) {
                            "BOUND".hash(h);
                            d.hash(h);
                        } else {
                            "FREE".hash(h);
                            vid.hash(h);
                        }
                        let _ = name; // ignore name for alpha-equiv
                    }
                    PseudoExpr::Var { id: None, name } => {
                        "SYMBOLIC".hash(h);
                        name.hash(h);
                    }
                    PseudoExpr::Int(n) => n.hash(h),
                    PseudoExpr::ByteArray(b) => b.hash(h),
                    PseudoExpr::String(s) => s.hash(h),
                    PseudoExpr::Bool(b) => b.hash(h),
                    PseudoExpr::Unit => {}
                    PseudoExpr::Error { .. } => {}
                    PseudoExpr::Apply { function, args } => {
                        for a in args.iter().rev() {
                            steps.push(Step::Visit(a));
                        }
                        steps.push(Step::ApplyArgsLen(args.len()));
                        steps.push(Step::Visit(function));
                    }
                    PseudoExpr::BuiltinCall { name, args } => {
                        format!("{:?}", name).hash(h);
                        for a in args.iter().rev() {
                            steps.push(Step::Visit(a));
                        }
                    }
                    PseudoExpr::FieldAccess { record, selector } => {
                        steps.push(Step::PostFieldAccess(selector));
                        steps.push(Step::Visit(record));
                    }
                    PseudoExpr::IndexAccess { collection, index } => {
                        steps.push(Step::PostIndexAccess(*index));
                        steps.push(Step::Visit(collection));
                    }
                    PseudoExpr::Force(inner) | PseudoExpr::Delay(inner) => {
                        steps.push(Step::Visit(inner));
                    }
                    PseudoExpr::Lambda { params, body } => {
                        params.len().hash(h);
                        let pushed: Vec<VarId> = params.iter().map(|p| p.id).collect();
                        for vid in &pushed {
                            bound.insert(*vid, *depth);
                            *depth += 1;
                        }
                        steps.push(Step::PopScope(pushed));
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        params.len().hash(h);
                        let mut pushed = vec![name.id];
                        for p in params {
                            pushed.push(p.id);
                        }
                        for vid in &pushed {
                            bound.insert(*vid, *depth);
                            *depth += 1;
                        }
                        steps.push(Step::PopScope(pushed));
                        steps.push(Step::Visit(body));
                    }
                    PseudoExpr::Let {
                        id, value, body, ..
                    } => {
                        steps.push(Step::EnterLetBody { id: *id, body });
                        steps.push(Step::Visit(value));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        steps.push(Step::Visit(else_branch));
                        steps.push(Step::Visit(then_branch));
                        steps.push(Step::Visit(condition));
                    }
                    PseudoExpr::BinOp { op, left, right } => {
                        format!("{:?}", op).hash(h);
                        steps.push(Step::Visit(right));
                        steps.push(Step::Visit(left));
                    }
                    PseudoExpr::UnOp { op, operand } => {
                        format!("{:?}", op).hash(h);
                        steps.push(Step::Visit(operand));
                    }
                    // Conservative: rare/complex shapes hash on discriminant only.
                    _ => {}
                }
            }
            Step::ApplyArgsLen(n) => {
                n.hash(h);
            }
            Step::PostFieldAccess(selector) => {
                selector.as_pretty_name().hash(h);
            }
            Step::PostIndexAccess(index) => {
                format!("{:?}", index).hash(h);
            }
            Step::PopScope(pushed) => {
                for vid in pushed.iter().rev() {
                    *depth -= 1;
                    bound.remove(vid);
                }
            }
            Step::EnterLetBody { id, body } => {
                if let Some(vid) = id {
                    bound.insert(vid, *depth);
                    *depth += 1;
                }
                steps.push(Step::PopLet(id));
                steps.push(Step::Visit(body));
            }
            Step::PopLet(id) => {
                if let Some(vid) = id {
                    *depth -= 1;
                    bound.remove(&vid);
                }
            }
        }
    }
}

fn rewrite_calls(expr: PseudoExpr, plans: &[HoistPlan], new_names: &[String]) -> PseudoExpr {
    struct CallRewriter<'a> {
        plans: &'a [HoistPlan],
        new_names: &'a [String],
    }

    impl ExprFolder for CallRewriter<'_> {
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            if let PseudoExpr::Apply { function, args } = expr
                && let PseudoExpr::Var {
                    id: Some(fn_id), ..
                } = function.as_ref()
                && args.len() >= 2
            {
                let args_h = hash_args(args);
                for (i, p) in self.plans.iter().enumerate() {
                    if p.fn_id == *fn_id && p.args_hash == args_h {
                        return FoldAction::Replace(PseudoExpr::Var {
                            name: self.new_names[i].clone(),
                            id: Some(p.new_id),
                        });
                    }
                }
            }
            FoldAction::Walk
        }

        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            pattern
        }
    }

    CallRewriter { plans, new_names }.fold(expr)
}

#[cfg(test)]
mod tests;
