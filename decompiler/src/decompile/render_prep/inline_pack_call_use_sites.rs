//! Inline church-pack-N use-site calls into native field-access form.
//!
//! `decode_church_to_native` rewrites the pack *value* to a native
//! `Tuple`/`Pair`, but use sites stay `Apply(pack_var, cont, …)` —
//! invalid surface, because tuples are not callable.
//!
//! Rewrite `Apply(Var(pack), [lambda, …extras])` to
//! `let p_i = pack.<i> in cont_body`, then re-wrap extras. The
//! continuation's params become the new `Let` binders (capture-safe:
//! the lambda already shadowed those VarIds). Dead-let cleanup drops
//! unused ones.
//!
//! Fires only when `pack` is a let-bound literal `Tuple`/`Pair` (or a
//! known pack-constructor apply). Function-valued bindings stay —
//! they may be callable. Continuation must be a literal `Lambda`.
//! The pack `let` itself is kept (other access sites still need it).
//!
//! A zero-arity `Constr` sentinel (V1 church-bool) decodes to
//! `.fst`/`.snd`; any other non-lambda continuation is left alone.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children as scope_children;

#[derive(Debug, Clone, Copy)]
enum PackShape {
    Pair,
    Tuple(usize),
}

impl PackShape {
    fn arity(self) -> usize {
        match self {
            PackShape::Pair => 2,
            PackShape::Tuple(n) => n,
        }
    }
}

pub(super) fn inline_pack_call_use_sites(expr: PseudoExpr) -> PseudoExpr {
    // Pass 1: pack-constructor helpers (`fn(a, b) { Pair(a, b) }`).
    let mut pack_ctors: HashMap<VarId, PackShape> = HashMap::new();
    collect_pack_ctors(&expr, &mut pack_ctors);
    // Pass 2: pack-VALUED bindings — a literal Tuple/Pair, or a
    // call to a known pack constructor.
    let mut helpers: HashMap<VarId, PackShape> = HashMap::new();
    collect_pack_helpers(&expr, &pack_ctors, &mut helpers);
    // Pass 3: church-bool sentinel bindings (zero-arity `Constr`
    // lets), which let the sentinel-call decoder fold
    // `pair_var(Var(s), extras…)` into `.fst`/`.snd` field access.
    let mut sentinels: HashMap<VarId, usize> = HashMap::new();
    collect_sentinel_consts(&expr, &mut sentinels);
    if helpers.is_empty() && sentinels.is_empty() {
        return expr;
    }
    rewrite(expr, &helpers, &sentinels)
}

/// The pretty-printer absorbs `Apply(Force(f), args) → f(args)`,
/// so a use site of a let-bound pack value can still carry a
/// `Force` wrapper at AST level that renders as nothing.
fn strip_force(expr: &PseudoExpr) -> &PseudoExpr {
    let mut cur = expr;
    while let PseudoExpr::Force(inner) = cur {
        cur = inner.as_ref();
    }
    cur
}

/// Map each let-binder VarId whose value is a zero-arity `Constr`
/// to its tag. Walks the FULL expr tree, unlike
/// `recover_church_booleans::collect_constr_tag_consts` (validator
/// entry let-chain only), so inner-scope sentinels are caught too.
fn collect_sentinel_consts(expr: &PseudoExpr, out: &mut HashMap<VarId, usize>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            body,
            ..
        } = cur
        {
            if let PseudoExpr::Constr { tag, fields, .. } = value.as_ref() {
                if fields.is_empty() {
                    out.insert(*vid, *tag);
                }
            }
            // Push body then value so value (visited first originally) pops first.
            pending.push(body.as_ref());
            pending.push(value.as_ref());
            continue;
        }
        pending.extend(scope_children(cur).into_iter().rev());
    }
}

/// Pack-constructor helpers — let-bound functions whose body is
/// `Pair(p0, p1)` or `Tuple([p0, …, pN-1])` of their own params.
/// `inline_constructor_helpers` leaves one at module top when a
/// bare-reference use site keeps it alive.
fn collect_pack_ctors(expr: &PseudoExpr, out: &mut HashMap<VarId, PackShape>) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            body,
            ..
        } = cur
        {
            if let Some(shape) = classify_pack_ctor(value.as_ref()) {
                out.insert(*vid, shape);
            }
            // Push body then value so value (visited first originally) pops first.
            pending.push(body.as_ref());
            pending.push(value.as_ref());
            continue;
        }
        pending.extend(scope_children(cur).into_iter().rev());
    }
}

/// Does `value` (a `Let`'s bound expression) evaluate to a pack-N
/// value? Peels inner Let chains — module-level "consts" often wrap
/// the pack construction in a small helper-binding let-chain.
fn classify_pack_value(
    value: &PseudoExpr,
    pack_ctors: &HashMap<VarId, PackShape>,
) -> Option<PackShape> {
    let mut cur = value;
    while let PseudoExpr::Let { body, .. } = cur {
        cur = body.as_ref();
    }
    match cur {
        PseudoExpr::Pair(_, _) => Some(PackShape::Pair),
        PseudoExpr::Tuple(items) if items.len() >= 3 => Some(PackShape::Tuple(items.len())),
        PseudoExpr::Apply { function, args } => {
            let PseudoExpr::Var {
                id: Some(ctor_id), ..
            } = function.as_ref()
            else {
                return None;
            };
            let &shape = pack_ctors.get(ctor_id)?;
            if args.len() == shape.arity() {
                Some(shape)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn classify_pack_ctor(value: &PseudoExpr) -> Option<PackShape> {
    let PseudoExpr::Lambda { params, body } = value else {
        return None;
    };
    match body.as_ref() {
        PseudoExpr::Pair(a, b) if params.len() == 2 => {
            let a_ok =
                matches!(a.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == params[0].id);
            let b_ok =
                matches!(b.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == params[1].id);
            if a_ok && b_ok {
                Some(PackShape::Pair)
            } else {
                None
            }
        }
        PseudoExpr::Tuple(items) if items.len() == params.len() && items.len() >= 3 => {
            for (i, item) in items.iter().enumerate() {
                let ok = matches!(item, PseudoExpr::Var { id: Some(v), .. } if *v == params[i].id);
                if !ok {
                    return None;
                }
            }
            Some(PackShape::Tuple(items.len()))
        }
        _ => None,
    }
}

/// Collect `let`-bindings whose value is pack-N data. Two shapes
/// qualify:
/// - Literal `Tuple` (arity ≥ 3) or `Pair`.
/// - `Apply(Var(pack_ctor), args)` for a known pack-constructor
///   helper from `pack_ctors`, with `args` of matching arity.
fn collect_pack_helpers(
    expr: &PseudoExpr,
    pack_ctors: &HashMap<VarId, PackShape>,
    out: &mut HashMap<VarId, PackShape>,
) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            body,
            ..
        } = cur
        {
            if let Some(shape) = classify_pack_value(value.as_ref(), pack_ctors) {
                out.insert(*vid, shape);
            }
            // Push body then value so value (visited first originally) pops first.
            pending.push(body.as_ref());
            pending.push(value.as_ref());
            continue;
        }
        pending.extend(scope_children(cur).into_iter().rev());
    }
}

struct PackCallRewriter<'a> {
    helpers: &'a HashMap<VarId, PackShape>,
    sentinels: &'a HashMap<VarId, usize>,
}

impl ExprFolder for PackCallRewriter<'_> {
    fn post_expr(&mut self, expr: PseudoExpr) -> PseudoExpr {
        let expr = try_rewrite_sentinel_call(expr, self.helpers, self.sentinels);
        try_rewrite_apply(expr, self.helpers)
    }

    // `map_children` never recursed into a `when` clause's literal
    // pattern expression (only subject/guard/body) — match that exactly
    // rather than the default's descent into `WhenPattern::Literal`.
    fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
        pattern
    }
}

fn rewrite(
    expr: PseudoExpr,
    helpers: &HashMap<VarId, PackShape>,
    sentinels: &HashMap<VarId, usize>,
) -> PseudoExpr {
    PackCallRewriter { helpers, sentinels }.fold(expr)
}

/// Church-pair sentinel-call decoder.
///
/// Pattern: `Apply(Var(pair_var), [Var(sentinel), …extras])` where
/// `pair_var` is a known church-pair binding and `sentinel` a known
/// zero-arity `Constr`.
///
/// Church-pair encoding is `pair(k) = k(fst, snd)`, so a church-bool
/// selector `k` picks `fst` (church-true) or `snd` (church-false),
/// and `extras` apply to that result.
///
/// Polarity: tag 0 → church-true → `.fst`, tag 1 → church-false →
/// `.snd`. Higher tags are not church-bool and are left alone.
fn try_rewrite_sentinel_call(
    expr: PseudoExpr,
    helpers: &HashMap<VarId, PackShape>,
    sentinels: &HashMap<VarId, usize>,
) -> PseudoExpr {
    let PseudoExpr::Apply { function, args } = expr else {
        return expr;
    };
    let effective = strip_force(function.as_ref());
    let PseudoExpr::Var {
        name: pair_name,
        id: Some(pair_id),
    } = effective
    else {
        return PseudoExpr::Apply { function, args };
    };
    let (pair_name, pair_id) = (pair_name.clone(), *pair_id);
    if !matches!(helpers.get(&pair_id), Some(PackShape::Pair)) {
        return PseudoExpr::Apply { function, args };
    }
    if args.is_empty() {
        return PseudoExpr::Apply { function, args };
    }
    let PseudoExpr::Var {
        id: Some(sentinel_id),
        ..
    } = &args[0]
    else {
        return PseudoExpr::Apply { function, args };
    };
    let Some(&tag) = sentinels.get(sentinel_id) else {
        return PseudoExpr::Apply { function, args };
    };
    let selector = match tag {
        0 => FieldSelector::PairFst,
        1 => FieldSelector::PairSnd,
        _ => return PseudoExpr::Apply { function, args },
    };
    let pair_field = PseudoExpr::FieldAccess {
        record: PBox::new(PseudoExpr::Var {
            name: pair_name,
            id: Some(pair_id),
        }),
        selector,
    };
    let extras: Vec<PseudoExpr> = args.into_iter().skip(1).collect();
    if extras.is_empty() {
        pair_field
    } else {
        PseudoExpr::Apply {
            function: PBox::new(pair_field),
            args: extras.into(),
        }
    }
}

fn try_rewrite_apply(expr: PseudoExpr, helpers: &HashMap<VarId, PackShape>) -> PseudoExpr {
    let PseudoExpr::Apply { function, args } = expr else {
        return expr;
    };
    // Must call a Var that resolves to a tracked pack binding.
    let effective = strip_force(function.as_ref());
    let PseudoExpr::Var {
        id: Some(pack_id), ..
    } = effective
    else {
        return PseudoExpr::Apply { function, args };
    };
    let Some(&shape) = helpers.get(pack_id) else {
        return PseudoExpr::Apply { function, args };
    };
    if args.is_empty() {
        return PseudoExpr::Apply { function, args };
    }
    // First arg must be a Lambda literal of the pack's arity;
    // a Var helper ref or partial app is out of scope.
    let PseudoExpr::Lambda {
        params,
        body: cont_body,
    } = &args[0]
    else {
        return PseudoExpr::Apply { function, args };
    };
    if params.len() != shape.arity() {
        return PseudoExpr::Apply { function, args };
    }
    let pack_name = if let PseudoExpr::Var { name, .. } = strip_force(function.as_ref()) {
        name.clone()
    } else {
        return PseudoExpr::Apply { function, args };
    };
    let pack_id_copy = *pack_id;
    let inlined = build_inlined_body(
        pack_name,
        pack_id_copy,
        shape,
        params.clone(),
        (**cont_body).clone(),
    );
    let remaining: Vec<PseudoExpr> = args.into_iter().skip(1).collect();
    if remaining.is_empty() {
        inlined
    } else {
        PseudoExpr::Apply {
            function: PBox::new(inlined),
            args: remaining.into(),
        }
    }
}

fn build_inlined_body(
    pack_name: String,
    pack_id: VarId,
    shape: PackShape,
    params: Vec<Binder>,
    cont_body: PseudoExpr,
) -> PseudoExpr {
    // Wildcard params (`_`) mark unused continuation positions; skip
    // them rather than bind `let _ = x_652.0; let _ = x_652.1; …`.
    let mut acc = cont_body;
    for (i, p) in params.into_iter().enumerate().rev() {
        if p.name == "_" {
            continue;
        }
        let field = build_field_access(&pack_name, pack_id, shape, i);
        acc = PseudoExpr::Let {
            name: p.name,
            id: Some(p.id),
            value: PBox::new(field),
            body: PBox::new(acc),
        };
    }
    acc
}

fn build_field_access(pack_name: &str, pack_id: VarId, shape: PackShape, idx: usize) -> PseudoExpr {
    let record = PseudoExpr::Var {
        name: pack_name.to_string(),
        id: Some(pack_id),
    };
    let selector = match shape {
        PackShape::Pair if idx == 0 => FieldSelector::PairFst,
        PackShape::Pair if idx == 1 => FieldSelector::PairSnd,
        PackShape::Pair => unreachable!("Pair idx > 1 rejected upstream by arity check"),
        // Bare 0-based index — `normalize_tuple_field_ordinals` runs late
        // in prepare_for_render and rewrites every numeric tuple selector
        // to the ordinal (`.1st`/`.8th`) across all sources.
        PackShape::Tuple(_) => FieldSelector::NamedField(idx.to_string()),
    };
    PseudoExpr::FieldAccess {
        record: PBox::new(record),
        selector,
    }
}

#[cfg(test)]
mod tests;
