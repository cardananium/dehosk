//! Unfold a textbook-Z fixpoint that is seeded through the driver's argument.
//!
//! `unfold_y_comb_apply` and `unfold_y_comb_helper_apply` both key on the
//! half-Z standing in FUNCTION position — the shape aiken and plutus-tx
//! emit. A compiler that emits the textbook Z instead,
//! `λf. (λx. f(λv. x x v)) (λx. f(λv. x x v))`, seeds recursion the other
//! way round: the driver is applied TO the half-Z, as an argument. Once
//! the lowering folds the two identical copies onto one binding, the tree
//! reads
//!
//! ```text
//! let d = fn(self, x) { … self(…) … }
//! let s = fn(w) { d(fn(u) { w(w, u) }) }
//! … d(fn(v) { s(s, v) }, arg) …
//! ```
//!
//! which is `fix(d)(arg)`. Neither sibling pass matches it, so the
//! fixpoint survives into the render as a two-parameter helper whose
//! first parameter is its own self-reference, called with a seed the
//! reader has to run the Z by hand to recognize.
//!
//! `d` becomes `rec fn d(x) { … }` — self param substituted by a
//! self-reference — and every call drops its seed argument. That leaves
//! `s` with no uses, and this pass drops its binding itself rather than
//! leaving it for `drop_dead_pure_lets`, which is gated on a validator
//! marker a plain script does not carry. The gates below have already
//! established that every use of `s` was a seed this pass removed.
//!
//! Fail-closed. Both `d` and `s` are `Let`-bound with their `VarId` bound
//! exactly once program-wide (a collided id is ambiguous); `s`'s value is
//! literally `fn(w) { d(fn(u) { w(w, u) }) }` for that same `d`; `d`'s
//! value is a literal 2-param `Lambda`; every seed argument is literally
//! `fn(v) { s(s, v) }`; and the use counts must account for every
//! reference — `d` appears once per seeded call plus once inside `s`, and
//! `s` only in the seeds. A use anywhere else means something reads `d`
//! at its two-parameter arity, or reads `s` other than to seed, and the
//! rewrite would change what that use denotes, so it is declined whole.

use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PBox, PseudoExpr, WhenClause};
use crate::pseudo::fold::ExprVisitor;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{rewrite_bottom_up, substitute_var};

/// What one driver's unfold needs: the seed binding to strand, and the
/// driver's own two parameters.
struct Unfold {
    /// `s` — kept only to match seed arguments against the right binding.
    seed: VarId,
    /// The driver's first parameter, its self-reference.
    self_param: VarId,
    /// The driver's second parameter, which the `rec fn` keeps.
    arg_param: Binder,
}

pub(super) fn unfold_y_comb_seed_applications(expr: PseudoExpr) -> PseudoExpr {
    let plan = plan_unfolds(&expr);
    if plan.is_empty() {
        return expr;
    }
    rewrite(expr, &plan)
}

/// Driver `VarId` → its unfold, for every driver that clears every gate.
fn plan_unfolds(expr: &PseudoExpr) -> HashMap<VarId, Unfold> {
    #[derive(Default)]
    struct Scan {
        binder_seen: HashMap<VarId, usize>,
        var_uses: HashMap<VarId, usize>,
        /// `s` → the driver its half-Z body applies.
        half_z: HashMap<VarId, VarId>,
        /// `d` → its 2-param lambda's parameters.
        drivers: HashMap<VarId, (VarId, Binder)>,
        /// Every `d(fn(v) { s(s, v) }, …)` site as `(d, s)`, unfiltered.
        /// The half-Z's own body applies its driver to a lambda of the
        /// same shape over its own parameter, so a site is only real once
        /// `half_z` confirms `s` is a let-bound half-Z for that `d` —
        /// which the walk cannot know at the moment it sees the call.
        seed_sites: Vec<(VarId, VarId)>,
    }
    impl Scan {
        fn record_binder(&mut self, id: VarId) {
            *self.binder_seen.entry(id).or_insert(0) += 1;
        }
    }
    impl ExprVisitor for Scan {
        fn visit_var(&mut self, _name: &str, id: &Option<VarId>) {
            if let Some(id) = id {
                *self.var_uses.entry(*id).or_insert(0) += 1;
            }
        }
        fn visit_let_value_post(&mut self, _name: &str, id: &Option<VarId>, value: &PseudoExpr) {
            let Some(vid) = id else { return };
            self.record_binder(*vid);
            if let Some(driver) = half_z_driver(value) {
                self.half_z.insert(*vid, driver);
            }
            if let PseudoExpr::Lambda { params, body: _ } = value
                && let [self_param, arg_param] = params.as_slice()
            {
                self.drivers
                    .insert(*vid, (self_param.var_id(), arg_param.clone()));
            }
        }
        fn visit_apply(&mut self, _expr: &PseudoExpr, function: &PseudoExpr, args: &[PseudoExpr]) {
            let PseudoExpr::Var {
                id: Some(driver), ..
            } = function
            else {
                return;
            };
            let Some(first) = args.first() else { return };
            let Some(seed) = seed_binding(first) else {
                return;
            };
            self.seed_sites.push((*driver, seed));
        }
        fn visit_lambda_pre(&mut self, params: &[Binder]) {
            for param in params {
                self.record_binder(param.var_id());
            }
        }
        fn visit_recfn_pre(&mut self, name: &Binder, params: &[Binder]) {
            self.record_binder(name.var_id());
            for param in params {
                self.record_binder(param.var_id());
            }
        }
        fn visit_when_clause_pre(&mut self, subject_name: Option<&Binder>, clause: &WhenClause) {
            if let Some(binder) = subject_name {
                self.record_binder(binder.var_id());
            }
            for id in clause.pattern.bound_ids() {
                self.record_binder(id);
            }
        }
    }

    let mut scan = Scan::default();
    scan.walk(expr);

    // Group the real sites per driver. A driver seeded from two different
    // bindings is not a shape this pass can name — poison it so the use
    // accounting below cannot balance.
    let mut sites: HashMap<VarId, (usize, VarId)> = HashMap::new();
    for (driver, seed) in &scan.seed_sites {
        if scan.half_z.get(seed) != Some(driver) {
            continue;
        }
        match sites.get_mut(driver) {
            Some((count, known)) if known == seed => *count += 1,
            Some((count, _)) => *count = usize::MAX,
            None => {
                sites.insert(*driver, (1, *seed));
            }
        }
    }

    let bound_once = |id: &VarId| scan.binder_seen.get(id) == Some(&1);
    let uses = |id: &VarId| scan.var_uses.get(id).copied().unwrap_or(0);

    sites
        .iter()
        .filter_map(|(driver, (sites, seed))| {
            let (self_param, arg_param) = scan.drivers.get(driver)?;
            if !bound_once(driver) || !bound_once(seed) {
                return None;
            }
            // Every reference accounted for: `d` once per seeded call plus
            // the one inside `s`; `s` twice per seed and nowhere else.
            if uses(driver) != sites.checked_add(1)? || uses(seed) != sites.checked_mul(2)? {
                return None;
            }
            Some((
                *driver,
                Unfold {
                    seed: *seed,
                    self_param: *self_param,
                    arg_param: arg_param.clone(),
                },
            ))
        })
        .collect()
}

/// The half-Z body `fn(w) { d(fn(u) { w(w, u) }) }`, returning `d`.
fn half_z_driver(expr: &PseudoExpr) -> Option<VarId> {
    let PseudoExpr::Lambda { params, body } = expr else {
        return None;
    };
    let [w] = params.as_slice() else { return None };
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        return None;
    };
    let PseudoExpr::Var {
        id: Some(driver), ..
    } = function.as_ref()
    else {
        return None;
    };
    let [inner] = args.as_slice() else {
        return None;
    };
    self_application(inner, w.var_id()).then_some(*driver)
}

/// The seed `fn(v) { s(s, v) }`, returning `s`.
fn seed_binding(expr: &PseudoExpr) -> Option<VarId> {
    let PseudoExpr::Lambda { params, body } = expr else {
        return None;
    };
    let [v] = params.as_slice() else { return None };
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        return None;
    };
    let PseudoExpr::Var { id: Some(seed), .. } = function.as_ref() else {
        return None;
    };
    let matches = matches!(
        args.as_slice(),
        [
            PseudoExpr::Var { id: Some(a), .. },
            PseudoExpr::Var { id: Some(b), .. },
        ] if a == seed && *b == v.var_id()
    );
    matches.then_some(*seed)
}

/// `fn(u) { f(f, u) }` for the given `f`.
fn self_application(expr: &PseudoExpr, f: VarId) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    let [u] = params.as_slice() else { return false };
    let PseudoExpr::Apply { function, args } = body.as_ref() else {
        return false;
    };
    if !matches!(function.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == f) {
        return false;
    }
    matches!(
        args.as_slice(),
        [
            PseudoExpr::Var { id: Some(a), .. },
            PseudoExpr::Var { id: Some(b), .. },
        ] if *a == f && *b == u.var_id()
    )
}

fn rewrite(expr: PseudoExpr, plan: &HashMap<VarId, Unfold>) -> PseudoExpr {
    let seeds: HashSet<VarId> = plan.values().map(|unfold| unfold.seed).collect();
    rewrite_bottom_up(expr, |node| match node {
        // `d(fn(v) { s(s, v) }, rest…)` → `d(rest…)`.
        PseudoExpr::Apply { function, args } => {
            let seeded = match (function.as_ref(), args.first()) {
                (
                    PseudoExpr::Var {
                        id: Some(driver), ..
                    },
                    Some(first),
                ) => plan
                    .get(driver)
                    .is_some_and(|unfold| seed_binding(first) == Some(unfold.seed)),
                _ => false,
            };
            if !seeded {
                return PseudoExpr::Apply { function, args };
            }
            let rest: Vec<PseudoExpr> = args.into_vec().into_iter().skip(1).collect();
            if rest.is_empty() {
                function.into_inner()
            } else {
                PseudoExpr::Apply {
                    function,
                    args: rest.into(),
                }
            }
        }
        // `let d = fn(self, x) { … }` → `let d = rec fn d(x) { … }`, with
        // `self` reading as the recursive function itself. The let is
        // kept: `ExitLetRecFnSameName` collapses `let d = rec fn d`.
        PseudoExpr::Let {
            name,
            id: Some(vid),
            value,
            body,
        } => {
            // The half-Z binding, now that its every use is gone.
            if seeds.contains(&vid) {
                return body.into_inner();
            }
            let Some(unfold) = plan.get(&vid) else {
                return PseudoExpr::Let {
                    name,
                    id: Some(vid),
                    value,
                    body,
                };
            };
            let PseudoExpr::Lambda {
                params,
                body: driver_body,
            } = value.into_inner()
            else {
                unreachable!("planned driver was verified to be a 2-param lambda")
            };
            debug_assert_eq!(params.len(), 2, "planned driver arity");
            let rec_body = substitute_var(driver_body.into_inner(), unfold.self_param, vid, &name);
            PseudoExpr::Let {
                name: name.clone(),
                id: Some(vid),
                value: PBox::new(PseudoExpr::RecFn {
                    name: Binder::new(name, vid),
                    params: vec![unfold.arg_param.clone()],
                    body: PBox::new(rec_body),
                }),
                body,
            }
        }
        other => other,
    })
}

#[cfg(test)]
mod tests;
