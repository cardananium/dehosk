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
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

use super::extract_repeated_subexpr::{
    abstract_signature, collect_free_vars, count_nodes, pattern_binders,
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
    PushScope(VarId),
    PopScope,
}

struct ClosedRecFn {
    id: VarId,
    name: String,
    sig: String,
    /// Let ids whose BODY contains this one.
    enclosing: Vec<VarId>,
}

fn dedupe_closed_rec_fns(expr: PseudoExpr) -> PseudoExpr {
    let mut found: Vec<ClosedRecFn> = Vec::new();
    let mut scope: Vec<VarId> = Vec::new();
    let mut stack = vec![Walk::Enter(&expr)];
    while let Some(step) = stack.pop() {
        match step {
            Walk::PushScope(id) => scope.push(id),
            Walk::PopScope => {
                scope.pop();
            }
            Walk::Enter(node) => {
                if let PseudoExpr::Let {
                    name,
                    id: Some(id),
                    value,
                    body,
                } = node
                {
                    if matches!(value.as_ref(), PseudoExpr::RecFn { .. })
                        && collect_free_vars(value).is_empty()
                    {
                        found.push(ClosedRecFn {
                            id: *id,
                            name: name.clone(),
                            sig: abstract_signature(value).0,
                            enclosing: scope.clone(),
                        });
                    }
                    stack.push(Walk::PopScope);
                    stack.push(Walk::Enter(body));
                    stack.push(Walk::PushScope(*id));
                    stack.push(Walk::Enter(value));
                } else {
                    stack.extend(children(node).into_iter().map(Walk::Enter));
                }
            }
        }
    }

    let mut redirect: HashMap<VarId, (VarId, String)> = HashMap::new();
    let mut by_sig: HashMap<&str, Vec<&ClosedRecFn>> = HashMap::new();
    for f in &found {
        by_sig.entry(f.sig.as_str()).or_default().push(f);
    }
    for group in by_sig.values().filter(|g| g.len() >= 2) {
        let Some(keeper) = group
            .iter()
            .find(|k| group.iter().all(|f| f.id == k.id || f.enclosing.contains(&k.id)))
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

fn at_least(expr: &PseudoExpr, n: usize) -> bool {
    let mut seen = 0;
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        seen += 1;
        if seen >= n {
            return true;
        }
        pending.extend(children(cur));
    }
    false
}

fn lift_one_group(expr: PseudoExpr) -> Result<PseudoExpr, PseudoExpr> {
    // Every big `when`, by shape.
    let mut groups: HashMap<String, Vec<FreeVars>> = HashMap::new();
    let mut sizes: HashMap<String, usize> = HashMap::new();
    let mut stack = vec![&expr];
    while let Some(node) = stack.pop() {
        if matches!(node, PseudoExpr::When { .. }) && at_least(node, MIN_NODES) {
            let (sig, free) = abstract_signature(node);
            sizes.entry(sig.clone()).or_insert_with(|| count_nodes(node));
            groups.entry(sig).or_default().push(free);
        }
        stack.extend(children(node));
    }

    let mut best: Option<(usize, &String, Vec<usize>)> = None;
    // Where a copy lives, to read how it uses its differing variables.
    let mut witnesses: HashMap<&String, &PseudoExpr> = HashMap::new();
    {
        let mut stack = vec![&expr];
        while let Some(node) = stack.pop() {
            if matches!(node, PseudoExpr::When { .. }) && at_least(node, MIN_NODES) {
                let (sig, _) = abstract_signature(node);
                if let Some((key, _)) = groups.get_key_value(&sig) {
                    witnesses.entry(key).or_insert(node);
                }
            }
            stack.extend(children(node));
        }
    }
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

    struct Replace<'a> {
        target: &'a str,
        differing: &'a [usize],
        helper_id: VarId,
        helper_name: &'a str,
        representative: Option<(PseudoExpr, FreeVars)>,
        replaced: usize,
    }
    impl ExprFolder for Replace<'_> {
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            if !matches!(expr, PseudoExpr::When { .. }) || !at_least(expr, MIN_NODES) {
                return FoldAction::Walk;
            }
            let (sig, free) = abstract_signature(expr);
            if sig != self.target {
                return FoldAction::Walk;
            }
            let args: Vec<PseudoExpr> = self
                .differing
                .iter()
                .map(|&k| PseudoExpr::Var {
                    name: free[k].1.clone(),
                    id: Some(free[k].0),
                })
                .collect();
            if self.representative.is_none() {
                self.representative = Some((expr.clone(), free));
            }
            self.replaced += 1;
            FoldAction::Replace(PseudoExpr::Apply {
                function: PBox::new(PseudoExpr::Var {
                    name: self.helper_name.to_string(),
                    id: Some(self.helper_id),
                }),
                args: args.into(),
            })
        }
    }
    let mut replace = Replace {
        target: &target,
        differing: &differing,
        helper_id,
        helper_name: &helper_name,
        representative: None,
        replaced: 0,
    };
    let rewritten = replace.fold(expr);
    let (mut body, rep_free) = replace
        .representative
        .take()
        .expect("a group has at least two copies");

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
