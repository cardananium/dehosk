//! Share a large expression that appears several times and differs only in
//! WHICH variables it reads.
//!
//! PlutusTx unrolls a fold's first iteration at every use, so one
//! multi-scalar sum shows up as three near-identical `when` blocks that differ
//! in a single list argument (and in the name of a private helper they each
//! carry). Exact-duplicate extraction cannot see that, and a general
//! cross-scope hoist has twice been reverted for what it does to naming. This
//! pass stays local on purpose:
//!
//! 1. A closed `rec fn` that is alpha-equivalent to one bound in an enclosing
//!    scope is replaced by a reference to that one.
//! 2. A big `when` that recurs, with the same shape, is turned into a call to
//!    a `let lifted = fn(...)` placed directly inside the scope of the
//!    innermost variable it shares across all copies. Only the variables that
//!    differ between copies become parameters; the rest stay free in the
//!    helper, so nothing is hoisted past a binding it uses.
//!
//! Every copy is replaced by a call at the same position with plain variable
//! arguments, so evaluation order and effects are unchanged.

use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PBox, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::extract_repeated_subexpr::{
    Facts, abstract_signature, collect_free_vars, pattern_binders, push_children_mut,
};
use super::scope_recurse::{children, rewrite_bottom_up, substitute_var};

/// Smallest `when` worth turning into a helper call.
const MIN_NODES: usize = 30;
const MAX_ROUNDS: usize = 6;

pub(super) fn lift_parametric_duplicates(expr: PseudoExpr) -> PseudoExpr {
    let mut current = dedupe_closed_rec_fns(expr);
    for _ in 0..MAX_ROUNDS {
        match lift_one_group(current) {
            Ok(next) => current = next,
            Err(unchanged) => return unchanged,
        }
    }
    current
}

// ---- 1. closed rec fns ------------------------------------------------

enum Walk<'a> {
    Enter(&'a PseudoExpr),
    /// A closed rec fn's body is about to be walked / was walked: record the
    /// span of node numbers it covers.
    OpenBody(usize),
    CloseBody(usize),
}

struct ClosedRecFn<'a> {
    id: VarId,
    name: String,
    value: &'a PseudoExpr,
    /// The node number of its `let`.
    at: usize,
    /// The node numbers its `let`'s body covers. Kept instead of the list of
    /// enclosing `let`s, which costs as much as the nesting depth — a depth
    /// the script chooses — for every `let` that has one.
    body: (usize, usize),
}

fn dedupe_closed_rec_fns(expr: PseudoExpr) -> PseudoExpr {
    let facts = Facts::of(&expr);
    let mut found: Vec<ClosedRecFn<'_>> = Vec::new();
    let mut numbered = 0usize;
    let mut stack = vec![Walk::Enter(&expr)];
    while let Some(step) = stack.pop() {
        match step {
            Walk::OpenBody(index) => found[index].body.0 = numbered,
            Walk::CloseBody(index) => found[index].body.1 = numbered,
            Walk::Enter(node) => {
                numbered += 1;
                if let PseudoExpr::Let {
                    name,
                    id: Some(id),
                    value,
                    body,
                } = node
                {
                    let closed = matches!(value.as_ref(), PseudoExpr::RecFn { .. })
                        && collect_free_vars(value).is_empty();
                    if closed {
                        found.push(ClosedRecFn {
                            id: *id,
                            name: name.clone(),
                            value,
                            at: numbered,
                            body: (0, 0),
                        });
                        let index = found.len() - 1;
                        stack.push(Walk::CloseBody(index));
                        stack.push(Walk::Enter(body));
                        stack.push(Walk::OpenBody(index));
                    } else {
                        stack.push(Walk::Enter(body));
                    }
                    stack.push(Walk::Enter(value));
                } else {
                    stack.extend(children(node).into_iter().map(Walk::Enter));
                }
            }
        }
    }

    // Only rec fns sharing a shape can share a signature; nobody else's is
    // built.
    let mut per_shape: HashMap<(u64, usize), usize> = HashMap::new();
    for f in &found {
        *per_shape.entry(facts.get(f.value).key()).or_insert(0) += 1;
    }
    let sigs: Vec<Option<String>> = found
        .iter()
        .map(|f| {
            (per_shape[&facts.get(f.value).key()] >= 2).then(|| abstract_signature(f.value).0)
        })
        .collect();
    let encloses = |outer: &ClosedRecFn<'_>, inner: &ClosedRecFn<'_>| {
        outer.body.0 <= inner.at && inner.at < outer.body.1
    };

    let mut redirect: HashMap<VarId, (VarId, String)> = HashMap::new();
    let mut by_sig: HashMap<&str, Vec<&ClosedRecFn<'_>>> = HashMap::new();
    for (f, sig) in found.iter().zip(&sigs) {
        if let Some(sig) = sig {
            by_sig.entry(sig.as_str()).or_default().push(f);
        }
    }
    for group in by_sig.values().filter(|g| g.len() >= 2) {
        let Some(keeper) = group
            .iter()
            .find(|k| group.iter().all(|f| f.id == k.id || encloses(k, f)))
        else {
            continue;
        };
        for f in group.iter().filter(|f| f.id != keeper.id) {
            redirect.insert(f.id, (keeper.id, keeper.name.clone()));
        }
    }
    if redirect.is_empty() {
        return expr;
    }

    struct Redirect<'a>(&'a HashMap<VarId, (VarId, String)>);
    impl ExprFolder for Redirect<'_> {
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            match id.and_then(|i| self.0.get(&i)) {
                Some((to, to_name)) => PseudoExpr::Var {
                    name: to_name.clone(),
                    id: Some(*to),
                },
                None => PseudoExpr::Var { name, id },
            }
        }
    }
    let expr = Redirect(&redirect).fold(expr);
    rewrite_bottom_up(expr, |node| match node {
        PseudoExpr::Let {
            id: Some(id), body, ..
        } if redirect.contains_key(&id) => body.into_inner(),
        other => other,
    })
}

// ---- 2. parametric duplicates ------------------------------------------

type FreeVars = Vec<(VarId, String)>;

fn lift_one_group(expr: PseudoExpr) -> Result<PseudoExpr, PseudoExpr> {
    // Not moved again from here: the copies are replaced in place, at the
    // addresses the facts below were taken at.
    let mut expr = expr;
    // Every big `when`, by shape. A `when` whose shape no other big `when`
    // has cannot share its signature, so its signature — as long as its
    // subtree — is never built: nested `when`s would otherwise cost time
    // quadratic in a depth the script chooses.
    let facts = Facts::of(&expr);
    let mut big: Vec<&PseudoExpr> = Vec::new();
    let mut stack = vec![&expr];
    while let Some(node) = stack.pop() {
        if matches!(node, PseudoExpr::When { .. }) && facts.get(node).key().1 >= MIN_NODES {
            big.push(node);
        }
        stack.extend(children(node));
    }
    let mut per_shape: HashMap<(u64, usize), usize> = HashMap::new();
    for node in &big {
        *per_shape.entry(facts.get(node).key()).or_insert(0) += 1;
    }
    let mut groups: HashMap<String, Vec<FreeVars>> = HashMap::new();
    let mut sizes: HashMap<String, usize> = HashMap::new();
    // Where a copy lives, to read how it uses its differing variables.
    let mut witnesses: HashMap<String, &PseudoExpr> = HashMap::new();
    for node in &big {
        let key = facts.get(node).key();
        if per_shape[&key] < 2 {
            continue;
        }
        let (sig, free) = abstract_signature(node);
        sizes.entry(sig.clone()).or_insert(key.1);
        witnesses.entry(sig.clone()).or_insert(node);
        groups.entry(sig).or_default().push(free);
    }

    let mut best: Option<(usize, &String, Vec<usize>)> = None;
    for (sig, copies) in groups.iter().filter(|(_, c)| c.len() >= 2) {
        let first = &copies[0];
        let differing: Vec<usize> = (0..first.len())
            .filter(|&k| copies.iter().any(|c| c[k].0 != first[k].0))
            .collect();
        // A parameter must be an ordinary variable: helper symbols such as
        // `expect!` are distinct per use but are not values to pass around.
        let ordinary = |name: &str| name.chars().all(|c| c.is_alphanumeric() || c == '_');
        if differing.is_empty() || differing.iter().any(|&k| !ordinary(&first[k].1)) {
            continue;
        }
        // The helper's parameter carries no type of its own.
        let typed_by_patterns = witnesses.get(sig).is_some_and(|w| {
            let ids: HashSet<VarId> = copies
                .iter()
                .flat_map(|c| differing.iter().map(|&k| c[k].0))
                .collect();
            only_list_scrutinee_uses(w, &ids)
        });
        if !typed_by_patterns {
            continue;
        }
        let score = sizes[sig] * (copies.len() - 1);
        let better = match &best {
            None => true,
            Some((s, b, _)) => score > *s || (score == *s && sig < *b),
        };
        if better {
            best = Some((score, sig, differing));
        }
    }
    let Some((_, target, differing)) = best else {
        return Err(expr);
    };
    let target = target.clone();
    let first_free = groups[&target][0].clone();
    let shared: Vec<VarId> = (0..first_free.len())
        .filter(|k| !differing.contains(k))
        .map(|k| first_free[k].0)
        .collect();

    let binders = binder_order(&expr);
    if shared.iter().any(|v| binders.unsupported.contains(v)) {
        return Err(expr);
    }
    // The helper may only be defined where everything it shares is visible:
    // inside the scope of the innermost shared binding.
    let scope_of: Option<VarId> = shared
        .iter()
        .filter_map(|v| binders.order.get(v).map(|i| (*i, *v)))
        .max()
        .map(|(_, v)| v);

    let helper_id = VarId::fresh_binding();
    let helper_name = "lifted".to_string();

    // Replace every copy with a call, in place — where the copies were found —
    // and keep the first one met in pre-order, before it is replaced, as the
    // helper's body. Copies never nest (one signature, one size).
    let target_key = facts.get(witnesses[&target]).key();
    drop(witnesses);
    let mut representative: Option<(PseudoExpr, FreeVars)> = None;
    {
        let mut pending: Vec<&mut PseudoExpr> = vec![&mut expr];
        while let Some(node) = pending.pop() {
            let is_copy = matches!(node, PseudoExpr::When { .. })
                && facts.get(node).key() == target_key
                && abstract_signature(node).0 == target;
            if !is_copy {
                let mut kids = Vec::new();
                push_children_mut(node, &mut kids);
                pending.extend(kids.into_iter().rev());
                continue;
            }
            let (_, free) = abstract_signature(node);
            let args: Vec<PseudoExpr> = differing
                .iter()
                .map(|&k| PseudoExpr::Var {
                    name: free[k].1.clone(),
                    id: Some(free[k].0),
                })
                .collect();
            let call = PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: helper_name.clone(),
                    id: Some(helper_id),
                }),
                args: args.into(),
            };
            let copy = std::mem::replace(node, call);
            if representative.is_none() {
                representative = Some((copy, free));
            }
        }
    }
    let rewritten = expr;
    let (mut body, rep_free) = representative.expect("a group has at least two copies");

    let mut params = Vec::with_capacity(differing.len());
    for (position, &k) in differing.iter().enumerate() {
        let param = Binder::new(param_name(&rep_free[k].1, position), VarId::fresh_binding());
        body = substitute_var(body, rep_free[k].0, param.id, &param.name);
        params.push(param);
    }
    let helper = PseudoExpr::Lambda {
        params,
        body: PBox::new(body),
    };

    let mut pending = Some(helper);
    let wrap = |body: PseudoExpr, pending: &mut Option<PseudoExpr>| -> PseudoExpr {
        match pending.take() {
            Some(value) => PseudoExpr::Let {
                name: helper_name.clone(),
                id: Some(helper_id),
                value: PBox::new(value),
                body: PBox::new(body),
            },
            None => body,
        }
    };
    let Some(scope_var) = scope_of else {
        return Ok(wrap(rewritten, &mut pending));
    };
    let wrapped = rewrite_bottom_up(rewritten, |node| {
        if pending.is_none() {
            return node;
        }
        match node {
            PseudoExpr::Let {
                name,
                id: Some(id),
                value,
                body,
            } if id == scope_var => PseudoExpr::Let {
                name,
                id: Some(id),
                value,
                body: PBox::new(wrap(body.into_inner(), &mut pending)),
            },
            PseudoExpr::Lambda { params, body } if params.iter().any(|p| p.id == scope_var) => {
                PseudoExpr::Lambda {
                    params,
                    body: PBox::new(wrap(body.into_inner(), &mut pending)),
                }
            }
            PseudoExpr::RecFn { name, params, body }
                if name.id == scope_var || params.iter().any(|p| p.id == scope_var) =>
            {
                PseudoExpr::RecFn {
                    name,
                    params,
                    body: PBox::new(wrap(body.into_inner(), &mut pending)),
                }
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } if clauses
                .iter()
                .any(|c| pattern_binders(&c.pattern).contains(&scope_var)) =>
            {
                let clauses = clauses
                    .into_iter()
                    .map(|c| {
                        if pending.is_some() && pattern_binders(&c.pattern).contains(&scope_var) {
                            WhenClause {
                                body: wrap(c.body, &mut pending),
                                ..c
                            }
                        } else {
                            c
                        }
                    })
                    .collect();
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                }
            }
            other => other,
        }
    });
    Ok(wrapped)
}

/// A generated `v_332` says nothing, and keeping it would sit next to the
/// original of the same name; anything the author named is kept.
fn param_name(original: &str, position: usize) -> String {
    let generated = original
        .strip_prefix("v_")
        .is_some_and(|rest| !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit()));
    match (generated, position) {
        (true, 0) => "arg".to_string(),
        (true, n) => format!("arg_{}", n + 1),
        (false, _) => format!("{original}_arg"),
    }
}

/// Whether every use of `vars` in a copy is as the subject of a `when` over
/// list patterns. Then the list patterns fix the variable's type, so a helper
/// parameter standing in for it renders exactly as the variable did. Any other
/// use (called, projected, compared, passed on) can depend on a type the
/// parameter does not carry, and later passes read it differently.
fn only_list_scrutinee_uses(expr: &PseudoExpr, vars: &HashSet<VarId>) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node {
            PseudoExpr::Var { id: Some(v), .. } if vars.contains(v) => return false,
            PseudoExpr::When {
                subject, clauses, ..
            } if matches!(subject.as_ref(), PseudoExpr::Var { id: Some(v), .. } if vars.contains(v)) =>
            {
                let list_typed = clauses.iter().all(|c| match &c.pattern {
                    WhenPattern::List { .. } | WhenPattern::Wildcard => true,
                    WhenPattern::Constructor { shape, .. } => matches!(
                        shape,
                        ConstructorShape::Known(KnownConstructor::Cons | KnownConstructor::Nil)
                    ),
                    _ => false,
                });
                if !list_typed {
                    return false;
                }
                for c in clauses {
                    stack.extend(c.guard.iter());
                    stack.push(&c.body);
                }
            }
            other => stack.extend(children(other)),
        }
    }
    true
}

struct Binders {
    /// Pre-order position of each supported binder.
    order: HashMap<VarId, usize>,
    /// Binders whose scope this pass does not model (`when` subject names).
    unsupported: HashSet<VarId>,
}

fn binder_order(expr: &PseudoExpr) -> Binders {
    let mut order = HashMap::new();
    let mut unsupported = HashSet::new();
    let mut counter = 0usize;
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        counter += 1;
        match node {
            PseudoExpr::Let { id: Some(id), .. } => {
                order.insert(*id, counter);
            }
            PseudoExpr::Lambda { params, .. } => {
                for p in params {
                    order.insert(p.id, counter);
                }
            }
            PseudoExpr::RecFn { name, params, .. } => {
                order.insert(name.id, counter);
                for p in params {
                    order.insert(p.id, counter);
                }
            }
            PseudoExpr::When {
                subject_name,
                clauses,
                ..
            } => {
                if let Some(b) = subject_name {
                    unsupported.insert(b.id);
                }
                for c in clauses {
                    for v in pattern_binders(&c.pattern) {
                        order.insert(v, counter);
                    }
                    if let WhenPattern::Literal(_) = c.pattern {}
                }
            }
            _ => {}
        }
        stack.extend(children(node));
    }
    Binders { order, unsupported }
}

#[cfg(test)]
mod tests;
