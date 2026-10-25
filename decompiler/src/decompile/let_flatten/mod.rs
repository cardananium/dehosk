use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{PseudoExpr, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;
use std::collections::HashSet;

use super::helper::hoist::var_is_referenced_id_aware;

/// Flatten nested let chains for readability.
///
/// Transforms:
/// ```text
/// let x = (let y = use_z in use_y) in
/// use_x
/// ```
/// Into (when safe):
/// ```text
/// let z = very_deep
/// let y = use_z
/// let x = use_y
/// use_x
/// ```
///
/// Safe only when the inner binder is not referenced in the outer
/// body, the outer binder appears in neither the inner value nor the
/// inner body, and the inner value is not a `Lambda`/`RecFn`.
pub(crate) fn flatten_let_chains(expr: PseudoExpr) -> PseudoExpr {
    let mut folder = LetFlattener::default();
    folder.fold(expr)
}

/// What a reference scan over a folded subtree depends on.
///
/// A chain of nested `let`s is as long as the script makes it, and each
/// `let` asks whether its parts reference a binder; scanning the parts each
/// time would cost the square of the chain. Instead every finished subtree
/// carries this summary up, merged into its parent's.
#[derive(Default)]
struct Refs {
    /// The id of every `Var` in the subtree.
    ids: HashSet<VarId>,
    /// Whether the subtree holds an id-less `Var`, which a scan matches by
    /// name, or an id-less `let`, whose scan mints a placeholder id. Either
    /// way the summary cannot stand in for the scan.
    needs_scan: bool,
}

impl Refs {
    fn merge(mut self, mut other: Refs) -> Refs {
        if self.ids.len() < other.ids.len() {
            std::mem::swap(&mut self, &mut other);
        }
        self.ids.extend(other.ids);
        self.needs_scan |= other.needs_scan;
        self
    }
}

/// How many children the fold machine folds for `expr`: the summaries it
/// pushed for them sit on top of [`LetFlattener::refs`].
fn folded_child_count(expr: &PseudoExpr) -> usize {
    match expr {
        PseudoExpr::Lambda { .. }
        | PseudoExpr::RecFn { .. }
        | PseudoExpr::FieldAccess { .. }
        | PseudoExpr::IndexAccess { .. }
        | PseudoExpr::UnOp { .. }
        | PseudoExpr::Delay(_)
        | PseudoExpr::Force(_) => 1,
        PseudoExpr::Let { .. }
        | PseudoExpr::Pair(..)
        | PseudoExpr::BinOp { .. }
        | PseudoExpr::Trace { .. } => 2,
        PseudoExpr::If { .. } => 3,
        PseudoExpr::Apply { args, .. } => 1 + args.len(),
        PseudoExpr::List { elements, tail } => elements.len() + usize::from(tail.is_some()),
        PseudoExpr::Tuple(elements) => elements.len(),
        PseudoExpr::Constr { fields, .. } => fields.len(),
        PseudoExpr::BuiltinCall { args, .. } => args.len(),
        PseudoExpr::When { clauses, .. } => {
            1 + clauses
                .iter()
                .map(|clause| {
                    usize::from(matches!(clause.pattern, WhenPattern::Literal(_)))
                        + usize::from(clause.guard.is_some())
                        + 1
                })
                .sum::<usize>()
        }
        PseudoExpr::Var { .. }
        | PseudoExpr::Int(_)
        | PseudoExpr::ByteArray(_)
        | PseudoExpr::String(_)
        | PseudoExpr::Bool(_)
        | PseudoExpr::Unit
        | PseudoExpr::Error { .. }
        | PseudoExpr::Raw { .. }
        | PseudoExpr::Data(_)
        | PseudoExpr::HelperSymbol(_) => 0,
    }
}

#[derive(Default)]
struct LetFlattener {
    /// One summary per subtree the fold machine has finished and not yet
    /// put into its parent, in the same order as the machine's own results.
    refs: Vec<Refs>,
    /// `post_let` has already pushed the summary of the node `post_expr`
    /// sees next.
    let_summarized: bool,
}

impl ExprFolder for LetFlattener {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }

    fn post_expr(&mut self, expr: PseudoExpr) -> PseudoExpr {
        if std::mem::take(&mut self.let_summarized) {
            return expr;
        }
        let at = self.refs.len() - folded_child_count(&expr);
        let mut summary = self
            .refs
            .split_off(at)
            .into_iter()
            .fold(Refs::default(), Refs::merge);
        if let PseudoExpr::Var { id, .. } = &expr {
            if let Some(id) = id {
                summary.ids.insert(*id);
            }
            summary.needs_scan |= id.get().is_none();
        }
        self.refs.push(summary);
        expr
    }

    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let body_refs = self.refs.pop().expect("let body summary");
        let value_refs = self.refs.pop().expect("let value summary");
        let outer_id = id.unwrap_or_else(VarId::fresh_compat_placeholder);
        let should_hoist = if let PseudoExpr::Let {
            name: ref inner_name,
            id: Some(inner_id),
            value: ref inner_value,
            body: ref inner_body,
            ..
        } = value
        {
            let inner_is_func = matches!(
                inner_value.as_ref(),
                PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. }
            );
            if value_refs.needs_scan || body_refs.needs_scan {
                // Hoisting only preserves scope ownership if the moved inner binder is
                // not referenced outside its current body and the outer binder does
                // not leak into the inner subtree being lifted above it.
                let inner_id_concrete = inner_id;
                let inner_not_in_outer =
                    !var_is_referenced_id_aware(&body, inner_id_concrete, inner_name);
                let no_circular = !var_is_referenced_id_aware(inner_value, outer_id, &name);
                let inner_body_not_outer_self_ref =
                    !var_is_referenced_id_aware(inner_body, outer_id, &name);
                inner_not_in_outer && no_circular && inner_body_not_outer_self_ref && !inner_is_func
            } else {
                // The same three scans, read off the summaries: with no id-less
                // reference or `let` in either part, a scan finds exactly the
                // `Var`s carrying the binder's id. The inner value and body
                // together make up the outer value.
                !body_refs.ids.contains(&inner_id)
                    && !value_refs.ids.contains(&outer_id)
                    && !inner_is_func
            }
        } else {
            false
        };
        let mut summary = value_refs.merge(body_refs);
        summary.needs_scan |= id.is_none();
        self.refs.push(summary);
        self.let_summarized = true;

        if should_hoist
            && let PseudoExpr::Let {
                name: inner_name,
                id: Some(inner_id),
                value: inner_value,
                body: inner_body,
            } = value
        {
            return PseudoExpr::Let {
                name: inner_name,
                id: Some(inner_id),
                value: inner_value,
                body: PBox::new(PseudoExpr::Let {
                    name,
                    id,
                    value: inner_body,
                    body: PBox::new(body),
                }),
            };
        }

        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }
}

#[cfg(test)]
mod tests;
