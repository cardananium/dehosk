use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

use super::helpers::is_orphan_generated_payload_ref;

/// The shared driver behind the three collectors below.
///
/// `visit` fires once per node in source order (children are pushed in
/// REVERSE so they pop in source order), with the `bound` set that was live
/// at that node. `Let` extends `bound` for its BODY only, each `When` clause
/// extends it with the subject name and the clause pattern's binders,
/// `Lambda`/`RecFn` bodies are not entered, and everything else descends
/// into `provenance_children()`.
///
/// The scope travels WITH the node (`Rc`, so a scope is shared by its whole
/// subtree) rather than as a call argument.
fn walk_scoped<'a>(
    root: &'a PseudoExpr,
    bound: &HashSet<VarId>,
    mut visit: impl FnMut(&'a PseudoExpr, &HashSet<VarId>),
) {
    let mut pending: Vec<(&'a PseudoExpr, Rc<HashSet<VarId>>)> =
        vec![(root, Rc::new(bound.clone()))];

    while let Some((expr, bound)) = pending.pop() {
        visit(expr, &bound);
        match expr {
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                let mut next_bound = (*bound).clone();
                if let Some(id_val) = *id {
                    next_bound.insert(id_val);
                }
                // Reversed: the value under the outer scope, then the body
                // under the extended one.
                pending.push((body, Rc::new(next_bound)));
                pending.push((value, bound));
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                // Reversed: the subject under the outer scope, then the
                // clauses in source order.
                for clause in clauses.iter().rev() {
                    let mut next_bound = (*bound).clone();
                    if let Some(subject_name) = subject_name {
                        next_bound.insert(subject_name.id);
                    }
                    next_bound.extend(clause.pattern.bound_ids());
                    let next_bound = Rc::new(next_bound);
                    pending.push((&clause.body, Rc::clone(&next_bound)));
                    if let Some(guard) = &clause.guard {
                        pending.push((guard, next_bound));
                    }
                }
                pending.push((subject, bound));
            }
            PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. } => {}
            _ => {
                for child in expr.provenance_children().into_iter().rev() {
                    pending.push((child, Rc::clone(&bound)));
                }
            }
        }
    }
}

/// Collect refs that look like generated constructor payload
/// carriers and are free at this point. `Lambda`/`RecFn` bodies
/// are not entered.
pub(in crate::decompile::late::normalize) fn collect_local_generated_payload_binders(
    expr: &PseudoExpr,
    bound: &HashSet<VarId>,
    out: &mut Vec<Binder>,
    kind_annotations: &HashMap<VarId, VarKind>,
    use_varkind_recovery: bool,
) {
    walk_scoped(expr, bound, |expr, bound| {
        if let PseudoExpr::Var { name, id } = expr {
            let id_opt = *id;
            let id_concrete = id_opt.unwrap_or_else(VarId::fresh_compat_placeholder);
            if !bound.contains(&id_concrete)
                && is_orphan_generated_payload_ref(
                    name,
                    id_opt,
                    kind_annotations,
                    use_varkind_recovery,
                )
                && !out.iter().any(|existing| Some(existing.id) == id_opt)
            {
                out.push(Binder::new(name.clone(), id_concrete));
            }
        }
    });
}

pub(in crate::decompile::late::normalize) fn collect_nested_generated_field_record_binders(
    expr: &PseudoExpr,
    bound: &HashSet<VarId>,
    out: &mut Vec<Binder>,
    kind_annotations: &HashMap<VarId, VarKind>,
    use_varkind_recovery: bool,
) {
    walk_scoped(expr, bound, |expr, bound| {
        if let PseudoExpr::FieldAccess {
            record, selector, ..
        } = expr
            && selector.as_pretty_name() == "fields"
            && let PseudoExpr::Var { name, id } = record.as_ref()
        {
            let id_opt = *id;
            let id_concrete = id_opt.unwrap_or_else(VarId::fresh_compat_placeholder);
            if !bound.contains(&id_concrete)
                && is_orphan_generated_payload_ref(
                    name,
                    id_opt,
                    kind_annotations,
                    use_varkind_recovery,
                )
                && !out.iter().any(|existing| Some(existing.id) == id_opt)
            {
                out.push(Binder::new(name.clone(), id_concrete));
            }
        }
    });
}

pub(in crate::decompile::late::normalize) fn recovered_generated_payload_binder(
    source: &Binder,
) -> Binder {
    let id = source.id.get().unwrap_or_else(VarId::fresh_binding);
    Binder::new(source.name.clone(), id)
}

pub(in crate::decompile::late::normalize) fn collect_subject_field_access_indices(
    expr: &PseudoExpr,
    subject_id: VarId,
    bound: &HashSet<VarId>,
    out: &mut BTreeSet<usize>,
) {
    walk_scoped(expr, bound, |expr, bound| {
        if let PseudoExpr::IndexAccess { collection, index } = expr
            && let PseudoExpr::FieldAccess {
                record, selector, ..
            } = collection.as_ref()
            && selector.as_pretty_name() == "fields"
            && let PseudoExpr::Var { id, .. } = record.as_ref()
            && *id == Some(subject_id)
            && !bound.contains(&subject_id)
        {
            out.insert(*index);
        }
    });
}
