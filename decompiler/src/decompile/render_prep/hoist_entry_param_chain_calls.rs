//! Hoist `f(p)` calls — where `p` is a validator-entry parameter and
//! the call appears ≥3 times — to a single `let` at the top of the
//! entry body.
//!
//! V1 scripts often project from the script-context Pair via a
//! helper chain (`f_33(script_context)().snd` repeated). Hoisting
//! `f_33(script_context)` to `let f_33_result = …` at the entry
//! body's top turns each occurrence into a single `Var` ref.
//!
//! Recognised argument shapes (each may be wrapped in `Force(...)`
//! or a 0-arg `Apply` — the `f(p)()` form): `Var(p)` — `f(p)` or
//! `f(p)()`; `FieldAccess(Var(p), sel)` — `f(p.sel)` or
//! `f(p.sel)()`. `p` must be in the stable set — initially the
//! enclosing scope's binders, expanded each iteration with the
//! lets this pass hoisted. The pass iterates to a fixed point, so
//! once iter-1 hoists `let f_33_call = f_33(script_context)()`,
//! iter-2 can match `f_31(f_33_call.fst)()`. The wider `Called`
//! shape (with the trailing `()`) is preferred over the bare
//! shape for the same target, so use-sites end as plain Var refs
//! (not `var()`).
//!
//! The hoisted expression's free vars are a single entry param,
//! which is in scope at the body's top. The call is pure (Plutus
//! builtins/Lambdas have no side effects). Eager evaluation
//! matches the original because the same call already executes
//! ≥3 times in the body.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

pub(super) fn hoist_entry_param_chain_calls(expr: PseudoExpr) -> PseudoExpr {
    super::scope_recurse::run_with_scope_fn(
        expr,
        |_top_lets| Vec::new(), // single-arg pass doesn't seed with top-let ids
        |body, stable| process_scope(body, stable.clone()),
    )
}

/// Iterate-to-fixed-point single-arg hoist on `body` using `stable` as the
/// stable VarId set.
fn process_scope(body: PseudoExpr, mut stable: std::collections::HashSet<VarId>) -> PseudoExpr {
    let mut body = body;
    let mut all_hoists: Vec<HoistPlan> = Vec::new();

    loop {
        let mut counts: HashMap<CandidateKey, CandidateInfo> = HashMap::new();
        count_calls(&body, &stable, &mut counts);

        let mut called_keys = std::collections::HashSet::new();
        for (key, info) in &counts {
            if key.shape == CandidateShape::Called && info.count >= 3 {
                called_keys.insert((key.fn_id, key.target_id, key.selector.clone()));
            }
        }

        let mut round_hoists: Vec<HoistPlan> = counts
            .into_iter()
            .filter(|(k, info)| {
                if info.count < 3 {
                    return false;
                }
                if k.shape == CandidateShape::Bare
                    && called_keys.contains(&(k.fn_id, k.target_id, k.selector.clone()))
                {
                    return false;
                }
                true
            })
            .map(|(k, info)| HoistPlan {
                fn_id: k.fn_id,
                target_id: k.target_id,
                selector: k.selector,
                fn_name: info.fn_name,
                target_name: info.target_name,
                new_id: VarId::fresh_binding(),
                shape: k.shape,
            })
            .collect();
        round_hoists.sort_by(|a, b| {
            let sel_a = a.selector.as_ref().map(|s| s.as_pretty_name().to_string());
            let sel_b = b.selector.as_ref().map(|s| s.as_pretty_name().to_string());
            (a.fn_id, a.target_id, sel_a, a.shape as u8).cmp(&(
                b.fn_id,
                b.target_id,
                sel_b,
                b.shape as u8,
            ))
        });

        if round_hoists.is_empty() {
            break;
        }

        body = rewrite_calls(body, &round_hoists);
        for h in &round_hoists {
            stable.insert(h.new_id);
        }
        all_hoists.extend(round_hoists);

        // Safety cap: a well-behaved program reaches fixed point in 1-2
        // rounds, so hitting it means a round keeps minting fresh candidates.
        // Assert in debug, break in release rather than hang the pipeline.
        if all_hoists.len() > 64 {
            debug_assert!(
                false,
                "hoist_entry_param_chain_calls: exceeded 64-hoist safety cap in a single scope; suspected non-monotonic iteration"
            );
            break;
        }
    }

    let restored_body = if all_hoists.is_empty() {
        body
    } else {
        let mut wrapped = body;
        for h in all_hoists.iter().rev() {
            let suffix = match h.shape {
                CandidateShape::Bare => "_result",
                CandidateShape::Called => "_call",
            };
            let new_name = match &h.selector {
                Some(sel) => format!(
                    "{}_{}_{}",
                    h.fn_name,
                    sanitize_sel(sel),
                    trim_underscore(suffix)
                ),
                None => format!("{}{}", h.fn_name, suffix),
            };
            let target_var = PseudoExpr::Var {
                name: h.target_name.clone(),
                id: Some(h.target_id),
            };
            let arg = match h.selector.clone() {
                Some(sel) => PseudoExpr::FieldAccess {
                    record: PBox::new(target_var),
                    selector: sel,
                },
                None => target_var,
            };
            let inner_apply = PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: h.fn_name.clone(),
                    id: Some(h.fn_id),
                }),
                args: vec![arg].into(),
            };
            let value = match h.shape {
                CandidateShape::Bare => inner_apply,
                CandidateShape::Called => PseudoExpr::Force(PBox::new(inner_apply)),
            };
            wrapped = PseudoExpr::Let {
                name: new_name,
                id: Some(h.new_id),
                value: PBox::new(value),
                body: PBox::new(wrapped),
            };
        }
        wrapped
    };

    super::scope_recurse::fold_identity_aliases(restored_body)
}

fn sanitize_sel(sel: &FieldSelector) -> String {
    let name = sel.as_pretty_name();
    // Selectors like "fst"/"snd" pass through; numerics like "0" → "n0".
    if name.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        format!("n{}", name)
    } else {
        name.to_string()
    }
}

fn trim_underscore(s: &str) -> &str {
    s.strip_prefix('_').unwrap_or(s)
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum CandidateShape {
    /// `Apply { Var(f), [arg] }` — bare `f(arg)`.
    Bare,
    /// `Force(Apply { Var(f), [arg] })` or 0-arg-Apply wrap — `f(arg)()`.
    Called,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct CandidateKey {
    fn_id: VarId,
    target_id: VarId,
    /// `None` for arg=`Var(target)`, `Some(sel)` for `FieldAccess(Var(target), sel)`.
    selector: Option<FieldSelector>,
    shape: CandidateShape,
}

struct CandidateInfo {
    fn_name: String,
    target_name: String,
    count: usize,
}

struct HoistPlan {
    fn_id: VarId,
    target_id: VarId,
    selector: Option<FieldSelector>,
    fn_name: String,
    target_name: String,
    new_id: VarId,
    shape: CandidateShape,
}

fn count_calls(
    expr: &PseudoExpr,
    stable: &std::collections::HashSet<VarId>,
    counts: &mut HashMap<CandidateKey, CandidateInfo>,
) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        if let Some(m) = match_candidate(expr, stable) {
            let entry = counts
                .entry(CandidateKey {
                    fn_id: m.fn_id,
                    target_id: m.target_id,
                    selector: m.selector.clone(),
                    shape: m.shape,
                })
                .or_insert_with(|| CandidateInfo {
                    fn_name: m.fn_name,
                    target_name: m.target_name,
                    count: 0,
                });
            entry.count += 1;
        }
        pending.extend(children(expr));
    }
}

struct MatchedCandidate {
    fn_id: VarId,
    fn_name: String,
    target_id: VarId,
    target_name: String,
    selector: Option<FieldSelector>,
    shape: CandidateShape,
}

fn match_candidate(
    expr: &PseudoExpr,
    stable: &std::collections::HashSet<VarId>,
) -> Option<MatchedCandidate> {
    // Try the wider Called shape first: Force(Apply{Var(f), [arg]}) or
    // 0-arg-Apply wrap. Falls through to Bare otherwise.
    let inner_apply = match expr {
        PseudoExpr::Force(inner) => Some(inner.as_ref()),
        PseudoExpr::Apply { function, args } if args.is_empty() => Some(function.as_ref()),
        _ => None,
    };
    if let Some(inner) = inner_apply
        && let Some(matched) = match_apply_arg(inner, stable, CandidateShape::Called)
    {
        return Some(matched);
    }
    match_apply_arg(expr, stable, CandidateShape::Bare)
}

fn match_apply_arg(
    expr: &PseudoExpr,
    stable: &std::collections::HashSet<VarId>,
    shape: CandidateShape,
) -> Option<MatchedCandidate> {
    let PseudoExpr::Apply { function, args } = expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let PseudoExpr::Var {
        id: Some(fn_id),
        name: fn_name,
    } = function.as_ref()
    else {
        return None;
    };
    let (target_id, target_name, selector) = match &args[0] {
        PseudoExpr::Var {
            id: Some(p_id),
            name: p_name,
        } if stable.contains(p_id) => (*p_id, p_name.clone(), None),
        PseudoExpr::FieldAccess { record, selector } => match record.as_ref() {
            PseudoExpr::Var {
                id: Some(p_id),
                name: p_name,
            } if stable.contains(p_id) => (*p_id, p_name.clone(), Some(selector.clone())),
            _ => return None,
        },
        _ => return None,
    };
    Some(MatchedCandidate {
        fn_id: *fn_id,
        fn_name: fn_name.clone(),
        target_id,
        target_name,
        selector,
        shape,
    })
}

struct HoistCallRewriter<'a> {
    hoists: &'a [HoistPlan],
}

impl ExprFolder for HoistCallRewriter<'_> {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
        // Try the wider Called shape first: Force(Apply{Var(f), [arg]}) or
        // 0-arg-Apply wrap.
        let inner_apply_ref = match expr {
            PseudoExpr::Force(inner) => Some(inner.as_ref()),
            PseudoExpr::Apply { function, args } if args.is_empty() => Some(function.as_ref()),
            _ => None,
        };
        if let Some(inner) = inner_apply_ref
            && let Some((fn_id, target_id, sel)) = peek_apply_arg(inner)
            && let Some(h) = find_hoist(self.hoists, fn_id, target_id, &sel, CandidateShape::Called)
        {
            return FoldAction::Replace(PseudoExpr::Var {
                name: hoist_name(h),
                id: Some(h.new_id),
            });
        }
        // Then the Bare shape.
        if let Some((fn_id, target_id, sel)) = peek_apply_arg(expr)
            && let Some(h) = find_hoist(self.hoists, fn_id, target_id, &sel, CandidateShape::Bare)
        {
            return FoldAction::Replace(PseudoExpr::Var {
                name: hoist_name(h),
                id: Some(h.new_id),
            });
        }
        FoldAction::Walk
    }
}

fn rewrite_calls(expr: PseudoExpr, hoists: &[HoistPlan]) -> PseudoExpr {
    HoistCallRewriter { hoists }.fold(expr)
}

fn peek_apply_arg(expr: &PseudoExpr) -> Option<(VarId, VarId, Option<FieldSelector>)> {
    let PseudoExpr::Apply { function, args } = expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let PseudoExpr::Var {
        id: Some(fn_id), ..
    } = function.as_ref()
    else {
        return None;
    };
    match &args[0] {
        PseudoExpr::Var { id: Some(p_id), .. } => Some((*fn_id, *p_id, None)),
        PseudoExpr::FieldAccess { record, selector } => {
            if let PseudoExpr::Var { id: Some(p_id), .. } = record.as_ref() {
                Some((*fn_id, *p_id, Some(selector.clone())))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn find_hoist<'a>(
    hoists: &'a [HoistPlan],
    fn_id: VarId,
    target_id: VarId,
    selector: &Option<FieldSelector>,
    shape: CandidateShape,
) -> Option<&'a HoistPlan> {
    hoists.iter().find(|h| {
        h.fn_id == fn_id && h.target_id == target_id && h.selector == *selector && h.shape == shape
    })
}

fn hoist_name(h: &HoistPlan) -> String {
    let suffix = match h.shape {
        CandidateShape::Bare => "_result",
        CandidateShape::Called => "_call",
    };
    match &h.selector {
        Some(sel) => format!(
            "{}_{}_{}",
            h.fn_name,
            sanitize_sel(sel),
            trim_underscore(suffix)
        ),
        None => format!("{}{}", h.fn_name, suffix),
    }
}

#[cfg(test)]
mod tests;
