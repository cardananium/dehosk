//! Interprocedural identity-parameter inlining.
//!
//! Companion to [`super::inline_identity_helper`] (let-bound `fn(x){x}`)
//! for an identity that arrives as a call argument and is applied as
//! `param(arg)`. Rewrite `param(arg) → arg`, drop the param and the
//! slot's argument, and keep the dropped argument's `fail` as a
//! statement-position guard.
//!
//! Fail-closed — any miss leaves the tree unchanged:
//! 1. Enumerable + one `let r = f(…)` call site (id never a value).
//! 2. Every param use is a 1-arg `param(arg)` head.
//! 3. Slot arg is `fn(x){x}` (pure, dropped) or
//!    `when s is { Ctor(_) -> fn(x){x}; _ -> fail }`.
//! 4. No sibling argument carries `trace` (traces are never reordered).
//! 5. Impure preceding slots are pre-bound before the guard so
//!    left-to-right order, including `fail`s, is preserved.
//! 6. Plain `let f = fn(…)` only — not RecFn, not multi-call.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::inline_identity_helper::{count_refs, var_refers_to_binder};
use super::purity::is_pure_value;
use super::scope_recurse::children;

pub(super) fn inline_identity_params(expr: PseudoExpr) -> PseudoExpr {
    let Some(fold) = find_fold(&expr) else {
        return expr;
    };
    // Names already in the tree — the pass runs after the late
    // naming/disambiguation, so a fresh `arg_<j>` pre-bind must avoid them
    // (the renderer prints binder names directly).
    let mut used_names: HashSet<String> = HashSet::new();
    collect_all_names(&expr, &mut used_names);
    let mut rewriter = Rewriter { fold, used_names };
    rewriter.fold(expr)
}

/// Every binder / reference name in the tree (to keep a fresh pre-bind unique).
fn collect_all_names(expr: &PseudoExpr, out: &mut HashSet<String>) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Let { name, .. } => {
                out.insert(name.clone());
            }
            PseudoExpr::Var { name, .. } => {
                out.insert(name.clone());
            }
            PseudoExpr::Lambda { params, .. } => {
                out.extend(params.iter().map(|p| p.as_str().to_string()));
            }
            PseudoExpr::RecFn { name, params, .. } => {
                out.insert(name.as_str().to_string());
                out.extend(params.iter().map(|p| p.as_str().to_string()));
            }
            PseudoExpr::When {
                subject_name,
                clauses,
                ..
            } => {
                if let Some(sn) = subject_name {
                    out.insert(sn.as_str().to_string());
                }
                for c in clauses {
                    out.extend(c.pattern.bound_names());
                }
            }
            _ => {}
        }
        pending.extend(children(current));
    }
}

// ===== Analysis =====

struct FuncInfo {
    params: Vec<Binder>,
    body: PseudoExpr,
}

#[derive(Default)]
struct Scan {
    /// `let f = fn(…)` (non-recursive Lambda) → its params + body.
    funcs: HashMap<VarId, FuncInfo>,
    /// VarIds reached as anything other than an `Apply` head (value-use).
    value_used: HashSet<VarId>,
    /// fn id → slot-0..n args at each call site (cloned).
    call_sites: HashMap<VarId, Vec<Vec<PseudoExpr>>>,
    /// fn ids whose call appears as a `let r = f(…)` value (continuation known).
    let_value_call: HashSet<VarId>,
}

/// The shape of the dropped slot argument.
enum DroppedShape {
    /// A bare identity lambda — pure, dropped outright (no guard).
    Bare,
    /// `when <subject> is { <pattern> -> fn(x){x}; _ -> <fail> }` — the fail must
    /// be preserved as a statement-position guard.
    Selector {
        subject: PseudoExpr,
        pattern: WhenPattern,
        fail: PseudoExpr,
    },
}

struct Fold {
    func_id: VarId,
    slot: usize,
    param: Binder,
    shape: DroppedShape,
}

fn find_fold(expr: &PseudoExpr) -> Option<Fold> {
    let mut scan = Scan::default();
    collect(expr, &mut scan);
    // Deterministic iteration: a HashMap's order is unspecified, so sort the
    // candidate function ids and return the lowest-id eligible fold. One fold
    // is applied per pass; multi-fold is not handled.
    let mut fids: Vec<VarId> = scan.funcs.keys().copied().collect();
    fids.sort();
    for fid in &fids {
        let info = &scan.funcs[fid];
        // Gate 1: enumerable + exactly one let-value call site of matching arity.
        if scan.value_used.contains(fid) || !scan.let_value_call.contains(fid) {
            continue;
        }
        let Some(calls) = scan.call_sites.get(fid) else {
            continue;
        };
        if calls.len() != 1 || calls[0].len() != info.params.len() {
            continue;
        }
        let args = &calls[0];
        for (slot, param) in info.params.iter().enumerate() {
            // Gate 2: the param is used ONLY as a 1-arg application `param(arg)`.
            let total = count_refs(&info.body, Some(param.id), param.as_str());
            if total == 0 {
                continue;
            }
            let (_, inlined) = inline_param_apps(info.body.clone(), param.id);
            if inlined != total {
                continue; // some bare / over-applied use survived → not foldable
            }
            // Gate 3: the slot arg is a foldable identity (Shape A or B).
            let Some(shape) = classify_dropped_arg(&args[slot]) else {
                continue;
            };
            // Gate 4: no Trace in any sibling arg (never-reorder-traces).
            if args
                .iter()
                .enumerate()
                .any(|(j, a)| j != slot && contains_trace(a))
            {
                continue;
            }
            return Some(Fold {
                func_id: *fid,
                slot,
                param: param.clone(),
                shape,
            });
        }
    }
    None
}

/// One-pass enumeration: record let-bound lambdas, value-used ids, call sites,
/// and which calls are `let r = f(…)` values. A `Var` reached as anything but an
/// `Apply` head is a value-use (fail-closed enumerability).
fn collect(expr: &PseudoExpr, scan: &mut Scan) {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Apply { function, args } => {
                let recurse_function =
                    if let PseudoExpr::Var { id: Some(fid), .. } = function.as_ref() {
                        scan.call_sites
                            .entry(*fid)
                            .or_default()
                            .push((args.clone()).into_vec());
                        // function head is a CALL, not a value-use — do not scan it.
                        false
                    } else {
                        true
                    };
                for a in args.iter().rev() {
                    pending.push(a);
                }
                if recurse_function {
                    pending.push(function);
                }
            }
            PseudoExpr::Var { id: Some(vid), .. } => {
                scan.value_used.insert(*vid);
            }
            PseudoExpr::Let {
                id: Some(lid),
                value,
                body,
                ..
            } => {
                if let PseudoExpr::Lambda {
                    params,
                    body: lbody,
                } = value.as_ref()
                {
                    scan.funcs.insert(
                        *lid,
                        FuncInfo {
                            params: params.clone(),
                            body: (**lbody).clone(),
                        },
                    );
                }
                if let PseudoExpr::Apply { function, .. } = value.as_ref()
                    && let PseudoExpr::Var { id: Some(fid), .. } = function.as_ref()
                {
                    scan.let_value_call.insert(*fid);
                }
                pending.push(body);
                pending.push(value);
            }
            _ => {
                pending.extend(children(current).into_iter().rev());
            }
        }
    }
}

/// Replace every 1-arg application of the param `p_id` — bare
/// `Apply{ Var(p), [arg] }` or `force`d `Apply{ Force(Var(p)), [arg] }` —
/// with `arg`. The `force` is decompiler noise the renderer elides, and `p`
/// is the identity, so `force(p)(arg) ≡ p(arg) ≡ arg`. Matched by `VarId`,
/// so shadowing is irrelevant. Returns `(rewritten, inlined_count)`.
fn inline_param_apps(expr: PseudoExpr, p_id: VarId) -> (PseudoExpr, usize) {
    struct Inliner {
        p_id: VarId,
        inlined: usize,
    }
    impl ExprFolder for Inliner {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_apply(&mut self, function: PseudoExpr, mut args: Vec<PseudoExpr>) -> PseudoExpr {
            if args.len() == 1 {
                let head = match &function {
                    PseudoExpr::Var { id: Some(v), .. } => Some(*v),
                    PseudoExpr::Force(inner) => match inner.as_ref() {
                        PseudoExpr::Var { id: Some(v), .. } => Some(*v),
                        _ => None,
                    },
                    _ => None,
                };
                if head == Some(self.p_id) {
                    self.inlined += 1;
                    return args.remove(0);
                }
            }
            PseudoExpr::Apply {
                function: PBox::new(function),
                args: args.into(),
            }
        }
    }
    let mut inliner = Inliner { p_id, inlined: 0 };
    let out = inliner.fold(expr);
    (out, inliner.inlined)
}

/// `fn(p) { p }` — exactly one param, body a Var to it.
fn is_identity_lambda(e: &PseudoExpr) -> bool {
    matches!(e, PseudoExpr::Lambda { params, body }
        if params.len() == 1
            && matches!(body.as_ref(),
                PseudoExpr::Var { name, id } if var_refers_to_binder(name, id, &params[0])))
}

/// `Error{..}` / `builtin Error` — a fail expression.
fn is_fail_expr(e: &PseudoExpr) -> bool {
    matches!(e, PseudoExpr::Error { .. })
        || matches!(e, PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::Error)
}

fn classify_dropped_arg(arg: &PseudoExpr) -> Option<DroppedShape> {
    if is_identity_lambda(arg) && is_pure_value(arg) {
        return Some(DroppedShape::Bare);
    }
    // Shape B: `when <bare Var> is { Ctor(P) -> fn(x){x}; _ -> fail }`.
    // Clause ORDER is load-bearing (first match wins): the constructor clause
    // MUST precede the wildcard-fail, else the original always fails and
    // emitting `Ctor -> …; _ -> fail` would change behavior. Enforce positionally.
    let PseudoExpr::When {
        subject, clauses, ..
    } = arg
    else {
        return None;
    };
    if !matches!(subject.as_ref(), PseudoExpr::Var { id: Some(_), .. }) || clauses.len() != 2 {
        return None;
    }
    let ctor = &clauses[0];
    let failc = &clauses[1];
    if !matches!(ctor.pattern, WhenPattern::Constructor { .. })
        || ctor.guard.is_some()
        || !is_identity_lambda(&ctor.body)
        || !matches!(failc.pattern, WhenPattern::Wildcard)
        || failc.guard.is_some()
        || !is_fail_expr(&failc.body)
    {
        return None;
    }
    Some(DroppedShape::Selector {
        subject: (**subject).clone(),
        // Wildcard the constructor's field binders: the non-fail branch is
        // the closed identity `fn(x){x}`, which references none of them, and
        // the guard now scopes the whole continuation, where a named binder
        // could capture a same-named continuation reference (the renderer
        // prints names directly).
        pattern: wildcard_ctor_fields(ctor.pattern.clone()),
        fail: failc.body.clone(),
    })
}

/// Replace a constructor pattern's field binders with `_` (display-discarded).
fn wildcard_ctor_fields(pattern: WhenPattern) -> WhenPattern {
    match pattern {
        WhenPattern::Constructor {
            type_hint,
            tag,
            fields,
            shape,
        } => WhenPattern::Constructor {
            type_hint,
            tag,
            shape,
            fields: fields
                .into_iter()
                .map(|b| Binder::new("_", b.var_id()))
                .collect(),
        },
        other => other,
    }
}

fn contains_trace(e: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![e];
    while let Some(current) = pending.pop() {
        if matches!(current, PseudoExpr::Trace { .. }) {
            return true;
        }
        pending.extend(children(current));
    }
    false
}

// ===== Rewrite =====

struct Rewriter {
    fold: Fold,
    /// Names already in the tree + pre-binds allocated so far (collision guard).
    used_names: HashSet<String>,
}

/// `base` if free, else `base_2`, `base_3`, … — guaranteed not in `used`.
fn fresh_name(base: &str, used: &HashSet<String>) -> String {
    if !used.contains(base) {
        return base.to_string();
    }
    let mut n = 2;
    loop {
        let cand = format!("{base}_{n}");
        if !used.contains(&cand) {
            return cand;
        }
        n += 1;
    }
}

impl ExprFolder for Rewriter {
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
        // (a) The function definition: inline `param(arg) → arg` in the body and
        //     drop the param from the signature.
        if id == Some(self.fold.func_id)
            && let PseudoExpr::Lambda {
                params,
                body: lbody,
            } = value
        {
            let (rewritten_body, _) = inline_param_apps(lbody.into_inner(), self.fold.param.id);
            let new_params: Vec<Binder> = params
                .into_iter()
                .enumerate()
                .filter(|(i, _)| *i != self.fold.slot)
                .map(|(_, p)| p)
                .collect();
            return PseudoExpr::Let {
                name,
                id,
                value: PBox::new(PseudoExpr::Lambda {
                    params: new_params,
                    body: PBox::new(rewritten_body),
                }),
                body: PBox::new(body),
            };
        }
        // (b) The call site `let r = f(args)`: drop the slot arg, pre-bind impure
        //     preceding slots, and (Shape B) splice the fail guard.
        if let PseudoExpr::Apply { function, .. } = &value
            && matches!(function.as_ref(), PseudoExpr::Var { id: Some(fid), .. } if *fid == self.fold.func_id)
        {
            return self.rewrite_call_let(name, id, value, body);
        }
        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }
}

impl Rewriter {
    fn rewrite_call_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let PseudoExpr::Apply { function, args } = value else {
            unreachable!("guarded by caller");
        };
        let slot = self.fold.slot;
        // Pre-bind impure preceding slots; build the reduced (slot-dropped) args.
        let mut prebinds: Vec<(String, VarId, PseudoExpr)> = Vec::new();
        let mut reduced: Vec<PseudoExpr> = Vec::new();
        for (j, a) in args.into_iter().enumerate() {
            if j == slot {
                continue; // the identity slot is dropped
            }
            if j < slot && !is_pure_value(&a) {
                // Impure preceding slot: pre-bind so its effect (incl. a fail)
                // still precedes the hoisted guard — order-exact. Name is kept
                // unique against the whole tree + earlier pre-binds (no capture).
                let vid = VarId::fresh_binding();
                let pname = fresh_name(&format!("arg_{j}"), &self.used_names);
                self.used_names.insert(pname.clone());
                reduced.push(PseudoExpr::Var {
                    name: pname.clone(),
                    id: Some(vid),
                });
                prebinds.push((pname, vid, a));
            } else {
                reduced.push(a);
            }
        }
        let inner = PseudoExpr::Let {
            name,
            id,
            value: PBox::new(PseudoExpr::Apply {
                function,
                args: reduced.into(),
            }),
            body: PBox::new(body),
        };
        // Shape A drops outright; Shape B wraps the continuation in the fail guard
        // (the renderer turns this single-real-clause When into `expect P = s`,
        // and `or fail @msg` under --expect-or-fail).
        let guarded = match &self.fold.shape {
            DroppedShape::Bare => inner,
            DroppedShape::Selector {
                subject,
                pattern,
                fail,
            } => PseudoExpr::When {
                subject: PBox::new(subject.clone()),
                subject_name: None,
                clauses: vec![
                    WhenClause {
                        pattern: pattern.clone(),
                        guard: None,
                        body: inner,
                    },
                    WhenClause {
                        pattern: WhenPattern::Wildcard,
                        guard: None,
                        body: fail.clone(),
                    },
                ],
            },
        };
        // Wrap the pre-binds outside the guard, outermost = lowest slot index.
        let mut result = guarded;
        for (pname, vid, pval) in prebinds.into_iter().rev() {
            result = PseudoExpr::Let {
                name: pname,
                id: Some(vid),
                value: PBox::new(pval),
                body: PBox::new(result),
            };
        }
        result
    }
}

#[cfg(test)]
mod tests;
