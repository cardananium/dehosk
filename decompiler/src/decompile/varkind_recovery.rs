//! Shared infrastructure for VarKind-based orphan-ref recovery.
//!
//! Three recovery passes need the same "typed-affirmative or legacy"
//! selector:
//!
//! `late/normalize/option/payload_binder_recovery::is_orphan_payload_ref`
//! `late/normalize/validator/helpers::is_orphan_generated_payload_ref`
//! `dangling_field_alias/payload_repair::is_dangling_synthetic_payload_ref`
//!
//! [`is_orphan_payload_ref_typed_or_legacy`] owns that dispatch — the
//! [`is_auto_generated_kind`] lookup, the
//! `DEHOSK_VARKIND_RECOVERY_DEBUG` instrumentation, and the
//! short-circuit on `use_varkind_recovery=false`. Each pass supplies
//! only its own legacy name predicate and debug label, so the typed
//! VarKind set is defined in one place rather than three.

use std::collections::HashMap;

use crate::pseudo::OptionVarIdGet;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;

/// Returns true iff `(name, id)` should be treated as an orphan
/// payload reference for recovery purposes.
///
/// With `use_varkind_recovery` off, this is exactly
/// `legacy_predicate(name)`. With it on, the orphan set is the
/// union of that predicate and a VarKind annotation for `id`
/// that [`is_auto_generated_kind`] accepts — a strict superset,
/// so the flag never drops a candidate the legacy path catches.
///
/// `DEHOSK_VARKIND_RECOVERY_DEBUG=1` logs every typed-only
/// delta, tagged with `debug_label` to identify the call site.
pub(crate) fn is_orphan_payload_ref_typed_or_legacy(
    name: &str,
    id: VarId,
    kind_annotations: &HashMap<VarId, VarKind>,
    use_varkind_recovery: bool,
    legacy_predicate: impl Fn(&str) -> bool,
    debug_label: &str,
) -> bool {
    if !use_varkind_recovery {
        return legacy_predicate(name);
    }

    let typed_match = kind_annotations
        .get(&id)
        .is_some_and(is_auto_generated_kind);
    let legacy_match = legacy_predicate(name);

    if typed_match && !legacy_match && crate::debug_env::varkind_recovery() {
        let kind = kind_annotations
            .get(&id)
            .map(|k| format!("{:?}", k))
            .unwrap_or_else(|| "<missing>".to_string());
        eprintln!(
            "[varkind-recovery delta {}] typed-only orphan: id={} name={:?} kind={}",
            debug_label, id, name, kind,
        );
    }

    // Inverse instrumentation — refs the legacy path catches and
    // the typed path misses, quantifying the typed-coverage gap.
    // Gated by its own `DEHOSK_VARKIND_RECOVERY_GAP_DEBUG=1`,
    // separate from the typed-only flag.
    if !typed_match && legacy_match && crate::debug_env::varkind_recovery_gaps() {
        let kind = kind_annotations
            .get(&id)
            .map(|k| format!("{:?}", k))
            .unwrap_or_else(|| "<missing>".to_string());
        eprintln!(
            "[varkind-recovery gap {}] legacy-only orphan: id={} name={:?} kind={}",
            debug_label, id, name, kind,
        );
    }

    typed_match || legacy_match
}

/// Variant of [`is_orphan_payload_ref_typed_or_legacy`] that adds a
/// name-resolution fallback for refs whose VarId doesn't appear in
/// `kind_annotations`.
///
/// Renames and clones after minting leave refs whose VarId has
/// diverged from the binder's, and the annotation is keyed on the
/// binder's id — so this helper looks the binder up by name in
/// `name_to_binder_id` (built once per recovery-pass invocation).
///
/// The map is name → ANY binder with that name, so it is not
/// scope-aware; since `VarKind` is a per-binder property and these
/// passes hunt synthetic-looking names, a same-name binder with an
/// auto-gen kind anywhere in the AST is strong evidence this ref is
/// a same-kind orphan.
pub(crate) fn is_orphan_payload_ref_typed_or_legacy_with_name_resolution(
    name: &str,
    id: VarId,
    kind_annotations: &HashMap<VarId, VarKind>,
    name_to_binder_id: &HashMap<String, VarId>,
    use_varkind_recovery: bool,
    legacy_predicate: impl Fn(&str) -> bool,
    debug_label: &str,
) -> bool {
    if !use_varkind_recovery {
        return legacy_predicate(name);
    }

    let direct_typed = kind_annotations
        .get(&id)
        .is_some_and(is_auto_generated_kind);
    let resolved_typed = !direct_typed
        && name_to_binder_id
            .get(name)
            .and_then(|binder_id| kind_annotations.get(binder_id))
            .is_some_and(is_auto_generated_kind);
    let typed_match = direct_typed || resolved_typed;
    let legacy_match = legacy_predicate(name);

    if resolved_typed && !legacy_match && crate::debug_env::varkind_recovery() {
        let binder = name_to_binder_id.get(name);
        let kind = binder
            .and_then(|bid| kind_annotations.get(bid))
            .map(|k| format!("{:?}", k))
            .unwrap_or_else(|| "<missing>".to_string());
        eprintln!(
            "[varkind-recovery delta {} name-resolved] typed-only orphan: id={} name={:?} binder={:?} kind={}",
            debug_label, id, name, binder, kind,
        );
    }
    if !typed_match && legacy_match && crate::debug_env::varkind_recovery_gaps() {
        // Also report whether the ref's own id is annotated (annotated
        // but `User`, so `direct_typed` bailed) or absent entirely (no
        // binder for this id), separating a true orphan from a
        // misannotated binder.
        let id_in_annotations = kind_annotations.contains_key(&id);
        let id_kind = kind_annotations
            .get(&id)
            .map(|k| format!("{:?}", k))
            .unwrap_or_else(|| "<not-annotated>".to_string());
        eprintln!(
            "[varkind-recovery gap {} name-resolved] legacy-only orphan: id={} name={:?} id_annotated={} id_kind={} (no binder with that name found)",
            debug_label, id, name, id_in_annotations, id_kind,
        );
    }

    typed_match || legacy_match
}

/// Map every binder's render-name to its VarId, for
/// [`is_orphan_payload_ref_typed_or_legacy_with_name_resolution`] to
/// resolve refs whose id has diverged from the binder's.
///
/// **Ambiguity handling:** a name held by two different binders is
/// dropped from the map, so the recovery passes fall through to the
/// legacy name path for it — safer than picking an arbitrary first
/// occurrence that could be an unrelated auto-generated binder.
pub(crate) fn build_name_to_binder_id_map(
    expr: &crate::pseudo::ast::PseudoExpr,
) -> HashMap<String, VarId> {
    use crate::pseudo::ast::PseudoExpr;

    enum Slot {
        Unique(VarId),
        Ambiguous,
    }
    fn insert_slot(slots: &mut HashMap<String, Slot>, name: String, id: VarId) {
        slots
            .entry(name)
            .and_modify(|slot| {
                if let Slot::Unique(existing) = *slot
                    && existing != id
                {
                    *slot = Slot::Ambiguous;
                }
            })
            .or_insert(Slot::Unique(id));
    }
    let mut slots: HashMap<String, Slot> = HashMap::new();
    walk(expr, &mut slots);
    let mut out: HashMap<String, VarId> = HashMap::with_capacity(slots.len());
    for (name, slot) in slots {
        if let Slot::Unique(id) = slot {
            out.insert(name, id);
        }
    }
    return out;

    enum Pending<'a> {
        Expr(&'a PseudoExpr),
        Pattern(&'a crate::pseudo::ast::WhenPattern),
        Insert(&'a str, VarId),
    }
    fn walk(expr: &PseudoExpr, out: &mut HashMap<String, Slot>) {
        let mut pending = vec![Pending::Expr(expr)];
        while let Some(item) = pending.pop() {
            let expr = match item {
                Pending::Insert(name, id) => {
                    insert_slot(out, name.to_string(), id);
                    continue;
                }
                Pending::Pattern(pattern) => {
                    pattern_binders(pattern, out);
                    continue;
                }
                Pending::Expr(expr) => expr,
            };
            match expr {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    if let Some(real_id) = id.get() {
                        insert_slot(out, name.clone(), real_id);
                    }
                    pending.push(Pending::Expr(body));
                    pending.push(Pending::Expr(value));
                }
                PseudoExpr::Lambda { params, body } => {
                    for binder in params {
                        insert_slot(out, binder.name.clone(), binder.id);
                    }
                    pending.push(Pending::Expr(body));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    insert_slot(out, name.name.clone(), name.id);
                    for binder in params {
                        insert_slot(out, binder.name.clone(), binder.id);
                    }
                    pending.push(Pending::Expr(body));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    for clause in clauses.iter().rev() {
                        pending.push(Pending::Expr(&clause.body));
                        if let Some(g) = &clause.guard {
                            pending.push(Pending::Expr(g));
                        }
                        pending.push(Pending::Pattern(&clause.pattern));
                    }
                    if let Some(s) = subject_name {
                        pending.push(Pending::Insert(&s.name, s.id));
                    }
                    pending.push(Pending::Expr(subject));
                }
                PseudoExpr::Apply { function, args } => {
                    for a in args.iter().rev() {
                        pending.push(Pending::Expr(a));
                    }
                    pending.push(Pending::Expr(function));
                }
                PseudoExpr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(Pending::Expr(else_branch));
                    pending.push(Pending::Expr(then_branch));
                    pending.push(Pending::Expr(condition));
                }
                PseudoExpr::List { elements, tail } => {
                    if let Some(t) = tail {
                        pending.push(Pending::Expr(t));
                    }
                    for e in elements.iter().rev() {
                        pending.push(Pending::Expr(e));
                    }
                }
                PseudoExpr::Tuple(items) => {
                    for i in items.iter().rev() {
                        pending.push(Pending::Expr(i));
                    }
                }
                PseudoExpr::Pair(a, b) => {
                    pending.push(Pending::Expr(b));
                    pending.push(Pending::Expr(a));
                }
                PseudoExpr::Constr { fields, .. } => {
                    for f in fields.iter().rev() {
                        pending.push(Pending::Expr(f));
                    }
                }
                PseudoExpr::FieldAccess { record, .. } => pending.push(Pending::Expr(record)),
                PseudoExpr::IndexAccess { collection, .. } => {
                    pending.push(Pending::Expr(collection))
                }
                PseudoExpr::BinOp { left, right, .. } => {
                    pending.push(Pending::Expr(right));
                    pending.push(Pending::Expr(left));
                }
                PseudoExpr::UnOp { operand, .. } => pending.push(Pending::Expr(operand)),
                PseudoExpr::BuiltinCall { args, .. } => {
                    for a in args.iter().rev() {
                        pending.push(Pending::Expr(a));
                    }
                }
                PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                    pending.push(Pending::Expr(inner))
                }
                PseudoExpr::Trace { message, value } => {
                    pending.push(Pending::Expr(value));
                    pending.push(Pending::Expr(message));
                }
                _ => {}
            }
        }
    }

    fn pattern_binders(pattern: &crate::pseudo::ast::WhenPattern, out: &mut HashMap<String, Slot>) {
        use crate::pseudo::ast::WhenPattern;
        match pattern {
            WhenPattern::Var(b) => {
                insert_slot(out, b.name.clone(), b.id);
            }
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                for b in fields {
                    insert_slot(out, b.name.clone(), b.id);
                }
            }
            WhenPattern::List { elements, tail } => {
                for b in elements {
                    insert_slot(out, b.name.clone(), b.id);
                }
                if let Some(t) = tail {
                    insert_slot(out, t.name.clone(), t.id);
                }
            }
            WhenPattern::Pair(a, b) => {
                insert_slot(out, a.name.clone(), a.id);
                insert_slot(out, b.name.clone(), b.id);
            }
            WhenPattern::Wildcard | WhenPattern::Literal(_) => {}
        }
    }
}

/// Returns true iff `kind` is an auto-generated binder kind — every
/// variant except `User`.
///
/// Orphan candidacy is broader than "is this a payload kind": the
/// legacy `(contains('_') && any digit)` predicate really asks "is
/// this an auto-generated name". Every non-`User` VarKind is minted
/// by the pipeline, so this is its typed equivalent, decoupled from
/// the narrower payload-kind set used by
/// `assign_names::candidate_name`. Excluding `User` is load-bearing:
/// a User binder with a user-meaningful name is not an orphan
/// candidate.
pub(crate) fn is_auto_generated_kind(kind: &VarKind) -> bool {
    !matches!(kind, VarKind::User)
}

#[cfg(test)]
mod tests;
