//! CSE for Y-combinator-defining lambdas.
//!
//! Collapsing `Lambda(acc){ rec fn inner(x) { acc(inner, x) } }` to a
//! bare `Var("fix")` is not an option: the surrounding context is
//! often a `when` subject, which such a collapse leaves orphaned. The
//! explicit Y-comb structure is kept.
//!
//! A script can bind a dozen structurally equivalent (modulo VarIds)
//! copies to distinct lets, each referenced once. This pass keeps the
//! first occurrence in a Let chain as canonical, redirects the other
//! binders' references to its VarId, and drops their Lets. A transient
//! binder name (e.g. `match_subject_5`) is replaced with a neutral
//! one so the shared helper is not named after its first use.
//!
//! Shape: `Lambda { params: [outer], body: RecFn { name: self,
//! params: [inner], body: Apply { function: Var(outer), args:
//! [Var(self), Var(inner)] } } }`. Only internal agreement of the
//! three VarIds is checked, so every match is alpha-equivalent.
//!
//! Only top-level Let-chain bindings. Inner / lambda-body lets are
//! already scoped narrowly enough that they do not warrant this CSE.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;
use std::collections::HashMap;

pub(super) fn cse_y_comb_consts(expr: PseudoExpr) -> PseudoExpr {
    let mut chain: Vec<LetEntry> = Vec::new();
    let tail = peel_let_chain(expr, &mut chain);

    // Identify Y-comb entries.
    let y_comb_entries: Vec<(usize, &LetEntry)> = chain
        .iter()
        .enumerate()
        .filter(|(_, e)| is_y_comb_defining_lambda(&e.value))
        .collect();
    if y_comb_entries.len() <= 1 {
        // Nothing to dedupe.
        return rewrap_let_chain(chain, tail);
    }

    // Pick canonical = first Y-comb in chain order.
    let canonical_id_opt = y_comb_entries[0].1.id;
    let Some(canonical_id) = canonical_id_opt else {
        // Without a stable id, refs cannot be redirected.
        return rewrap_let_chain(chain, tail);
    };

    // A transient binder name (e.g. `match_subject_5`) is taken
    // from a surrounding use site and would leave the shared
    // helper misleadingly named after its first use, so the
    // canonical is renamed to a neutral one.
    let canonical_name = canonicalize_helper_name(&y_comb_entries[0].1.name);

    // Build redirect map: every non-canonical Y-comb let's id → canonical id.
    let mut redirect: HashMap<VarId, VarId> = HashMap::new();
    let mut drop_indices: Vec<usize> = Vec::new();
    for &(idx, entry) in y_comb_entries.iter().skip(1) {
        if let Some(eid) = entry.id {
            redirect.insert(eid, canonical_id);
            drop_indices.push(idx);
        }
    }
    if redirect.is_empty() {
        return rewrap_let_chain(chain, tail);
    }
    // Map canonical_id to itself after a rename — the id is
    // unchanged, but refs must pick up the new display name.
    if canonical_name != y_comb_entries[0].1.name {
        redirect.insert(canonical_id, canonical_id);
    }

    // Scan the ENTIRE surviving AST (chain + tail) for binder
    // ids that overlap the redirect map, minus the canonical
    // self-mapping: a nested binder reusing a dropped Y-comb id
    // (a lambda param, an inner let) would have refs wrongly
    // redirected.
    debug_assert!(
        invariant_check_no_redirected_binder_in_survivors(
            &chain,
            &drop_indices,
            &tail,
            &redirect,
            canonical_id,
        ),
        "P2.1.A CSE: a surviving non-canonical binder reuses an id in the redirect map — \
         pipeline VarId-unique invariant violated; refs could be wrongly redirected"
    );

    // Rewrite the tail and each remaining entry's value/body refs.
    let mut rewriter = VarRedirect {
        redirect,
        canonical_name: canonical_name.clone(),
    };
    let tail = rewriter.fold(tail);
    let mut new_chain: Vec<LetEntry> = Vec::with_capacity(chain.len() - drop_indices.len());
    for (idx, entry) in chain.into_iter().enumerate() {
        if drop_indices.contains(&idx) {
            continue;
        }
        let entry_name = if entry.id == Some(canonical_id) {
            canonical_name.clone()
        } else {
            entry.name
        };
        new_chain.push(LetEntry {
            name: entry_name,
            id: entry.id,
            value: rewriter.fold(entry.value),
        });
    }
    rewrap_let_chain(new_chain, tail)
}

struct LetEntry {
    name: String,
    id: Option<VarId>,
    value: PseudoExpr,
}

fn peel_let_chain(mut expr: PseudoExpr, out: &mut Vec<LetEntry>) -> PseudoExpr {
    loop {
        match expr {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                out.push(LetEntry {
                    name,
                    id,
                    value: value.into_inner(),
                });
                expr = body.into_inner();
            }
            other => return other,
        }
    }
}

/// True if NO surviving binder has an id in the redirect map
/// (modulo the canonical_id self-mapping).
fn invariant_check_no_redirected_binder_in_survivors(
    chain: &[LetEntry],
    drop_indices: &[usize],
    tail: &PseudoExpr,
    redirect: &HashMap<VarId, VarId>,
    canonical_id: VarId,
) -> bool {
    let targets: std::collections::HashSet<VarId> = redirect
        .keys()
        .copied()
        .filter(|id| *id != canonical_id)
        .collect();
    if targets.is_empty() {
        return true;
    }
    for (idx, entry) in chain.iter().enumerate() {
        if drop_indices.contains(&idx) {
            continue;
        }
        if let Some(eid) = entry.id
            && targets.contains(&eid)
        {
            return false;
        }
        if has_binder_in(&entry.value, &targets) {
            return false;
        }
    }
    !has_binder_in(tail, &targets)
}

/// True if any binder (Let, Lambda param, RecFn name/params, When
/// subject_name, When clause pattern binders) in `expr` has an id
/// in `targets`.
fn has_binder_in(expr: &PseudoExpr, targets: &std::collections::HashSet<VarId>) -> bool {
    use crate::pseudo::ast::WhenPattern;
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                if let Some(vid) = id
                    && targets.contains(vid)
                {
                    return true;
                }
                pending.push(value);
                pending.push(body);
            }
            PseudoExpr::Lambda { params, body } => {
                if params.iter().any(|p| targets.contains(&p.var_id())) {
                    return true;
                }
                pending.push(body);
            }
            PseudoExpr::RecFn { name, params, body } => {
                if targets.contains(&name.var_id())
                    || params.iter().any(|p| targets.contains(&p.var_id()))
                {
                    return true;
                }
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                pending.push(function);
                pending.extend(args.iter());
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(condition);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                if subject_name
                    .as_ref()
                    .is_some_and(|sn| targets.contains(&sn.var_id()))
                {
                    return true;
                }
                pending.push(subject);
                for c in clauses {
                    let pattern_binders_hit = match &c.pattern {
                        WhenPattern::Constructor { fields, .. } => {
                            fields.iter().any(|f| targets.contains(&f.var_id()))
                        }
                        WhenPattern::List { elements, tail } => {
                            elements.iter().any(|e| targets.contains(&e.var_id()))
                                || tail.as_ref().is_some_and(|t| targets.contains(&t.var_id()))
                        }
                        WhenPattern::Tuple(items) => {
                            items.iter().any(|i| targets.contains(&i.var_id()))
                        }
                        WhenPattern::Pair(a, b) => {
                            targets.contains(&a.var_id()) || targets.contains(&b.var_id())
                        }
                        WhenPattern::Var(b) => targets.contains(&b.var_id()),
                        WhenPattern::Wildcard | WhenPattern::Literal(_) => false,
                    };
                    if pattern_binders_hit {
                        return true;
                    }
                    if let Some(g) = c.guard.as_ref() {
                        pending.push(g);
                    }
                    pending.push(&c.body);
                }
            }
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(t) = tail.as_ref() {
                    pending.push(t);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items.iter()),
            PseudoExpr::Pair(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
            PseudoExpr::FieldAccess { record, .. } => pending.push(record),
            PseudoExpr::IndexAccess { collection, .. } => pending.push(collection),
            PseudoExpr::BinOp { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            PseudoExpr::UnOp { operand, .. } => pending.push(operand),
            PseudoExpr::BuiltinCall { args, .. } => pending.extend(args.iter()),
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => pending.push(inner),
            PseudoExpr::Trace { message, value } => {
                pending.push(message);
                pending.push(value);
            }
            // Leaves
            PseudoExpr::Var { .. }
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
        }
    }
    false
}

/// A stable name for the canonical Y-comb helper: a binder name
/// matching a transient synthetic-rename pattern is replaced with
/// a neutral one; any other name is kept — it may be meaningful.
///
/// **Allowlist.** A name is transient iff it matches one of:
///
/// - `match_subject_<N>` where `<N>` is non-empty digits (e.g.
///   `match_subject_5`, NOT `match_subject_user`).
/// - `x_<N>` where `<N>` is non-empty digits (e.g. `x_3`, NOT
///   `x_squared`).
/// - `v_<N>` where `<N>` is non-empty digits.
///
/// Single-letter names (`f`, `x`, `a`) are not transient — they
/// may be user-given short helpers.
fn canonicalize_helper_name(name: &str) -> String {
    const NEUTRAL: &str = "y_combinator";
    fn is_digits_suffix(name: &str, prefix: &str) -> bool {
        if let Some(rest) = name.strip_prefix(prefix) {
            !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
        } else {
            false
        }
    }
    let looks_transient = is_digits_suffix(name, "match_subject_")
        || is_digits_suffix(name, "x_")
        || is_digits_suffix(name, "v_");
    if looks_transient {
        NEUTRAL.to_string()
    } else {
        name.to_string()
    }
}

fn rewrap_let_chain(chain: Vec<LetEntry>, tail: PseudoExpr) -> PseudoExpr {
    let mut acc = tail;
    for entry in chain.into_iter().rev() {
        acc = PseudoExpr::Let {
            name: entry.name,
            id: entry.id,
            value: PBox::new(entry.value),
            body: PBox::new(acc),
        };
    }
    acc
}

/// Returns `true` if `expr` matches the Y-comb-defining Lambda shape.
fn is_y_comb_defining_lambda(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let outer_id = params[0].var_id();
    let PseudoExpr::RecFn {
        name: self_name,
        params: inner_params,
        body: rec_body,
    } = body.as_ref()
    else {
        return false;
    };
    let self_id = self_name.var_id();
    if inner_params.len() != 1 {
        return false;
    }
    let inner_id = inner_params[0].var_id();
    let PseudoExpr::Apply { function, args } = rec_body.as_ref() else {
        return false;
    };
    // function == Var(outer_id)
    let outer_match = matches!(
        function.as_ref(),
        PseudoExpr::Var { id: Some(vid), .. } if *vid == outer_id
    );
    if !outer_match {
        return false;
    }
    // args == [Var(self_id), Var(inner_id)]
    matches!(
        args.as_slice(),
        [
            PseudoExpr::Var { id: Some(s_vid), .. },
            PseudoExpr::Var { id: Some(i_vid), .. },
        ] if *s_vid == self_id && *i_vid == inner_id
    )
}

struct VarRedirect {
    redirect: HashMap<VarId, VarId>,
    canonical_name: String,
}

impl ExprFolder for VarRedirect {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        if let Some(vid) = id
            && let Some(target) = self.redirect.get(&vid)
        {
            return PseudoExpr::Var {
                name: self.canonical_name.clone(),
                id: Some(*target),
            };
        }
        PseudoExpr::Var { name, id }
    }
}

#[allow(unused_imports)]
use Binder as _BinderImport;

#[cfg(test)]
mod tests;
