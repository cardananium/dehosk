//! List-element provenance for the schema-position descent.
//!
//! A list-typed context field (`tx_info.outputs : List<TxOut>`) reaches
//! its element consumers through an iteration chain the direct
//! binder/projection linkage cannot see. Both answers are VarId-keyed
//! and fail-closed.
//!
//! [`ListIterationIndex::element_binders_of`]: given a list-root binder,
//! which binders hold its elements? Fixpoint over rec-fn iteration,
//! generalizing the `schema_param_provenance` cert-list discipline: a
//! rec fn's param joins the member set when the fn is enumerable
//! (never used as a value, including 0-arg applies) and every call
//! site's slot-0 is a member form — bare `Var(l)`, `un_list_data(Var(l))`,
//! the fn's own cons-tail binder, or `List.tail(param)` — with at least
//! one non-recursive site. Let-aliases (`let xs = un_list_data(outputs)`)
//! join too. Elements are the cons-head binders of member iterations
//! plus let-bound `Var(l).head` projections.
//!
//! [`ListIterationIndex::params_with_agreed_claims`]: which helper
//! params receive only such elements? A param qualifies when its fn is
//! enumerable, has at least one call site, and every site's arg in that
//! slot resolves to a claimed element (or the `.head` of a claimed
//! member) — all agreeing on one element type. One disagreeing or
//! unproven site disqualifies the slot (all-call-sites discipline): a
//! polymorphic helper fed an element at one site and something else at
//! another never types.
//!
//! The stub-ADT descent seeds the returned binders with the field's
//! element `ContextType` and lets its existing single-variant /
//! version-by-arity gates decide whether the override actually fires —
//! this module only proves the dataflow link.

use std::collections::{BTreeMap, BTreeSet};

use crate::BuiltinId;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

/// Pre-scanned iteration/call structure of one expression tree.
pub(super) struct ListIterationIndex {
    /// Canonical fn id -> (slot-0 param id, cons-tail binder ids,
    /// cons-head binder ids) for `let f = rec fn|Lambda` definitions
    /// whose first param is cons-matched in the body.
    rec_meta: BTreeMap<VarId, RecMeta>,
    /// Canonical fn id -> every call site's args, each classified into
    /// an `ArgForm`.
    calls: BTreeMap<VarId, Vec<Vec<ArgForm>>>,
    /// Fn ids referenced OUTSIDE call-head position (value uses,
    /// including 0-arg applies) — non-enumerable, never trusted.
    value_used: BTreeSet<VarId>,
    /// Canonical fn id -> ordered param binder ids (all slots).
    params: BTreeMap<VarId, Vec<VarId>>,
    /// `let X = <list>.head` / `let X = un_list_data(<list>)` aliases:
    /// X -> (source id, AliasKind).
    let_aliases: BTreeMap<VarId, (VarId, AliasKind)>,
    /// RecFn self-name id -> canonical (enclosing let) id.
    self_aliases: BTreeMap<VarId, VarId>,
}

struct RecMeta {
    param0: VarId,
    cons_tails: BTreeSet<VarId>,
    cons_heads: BTreeSet<VarId>,
}

#[derive(Clone, Copy, PartialEq)]
enum AliasKind {
    /// `let X = builtin.un_list_data(Var(src))` — same list, unwrapped.
    UnListData,
    /// `let X = Var(src).head` — an ELEMENT of src.
    ListHead,
}

/// One classified call argument.
#[derive(Clone)]
enum ArgForm {
    /// Bare `Var(id)` (canonical).
    Var(VarId),
    /// `builtin.un_list_data(Var(id))`.
    UnListData(VarId),
    /// `List.tail(Var(id))`-shaped tail step on `id`.
    ListTail(VarId),
    /// `Var(id).head` element projection.
    Head(VarId),
    /// Anything else — never a member/element witness.
    Opaque,
}

impl ListIterationIndex {
    pub(super) fn build(expr: &PseudoExpr) -> Self {
        let mut ix = ListIterationIndex {
            rec_meta: BTreeMap::new(),
            calls: BTreeMap::new(),
            value_used: BTreeSet::new(),
            params: BTreeMap::new(),
            let_aliases: BTreeMap::new(),
            self_aliases: BTreeMap::new(),
        };
        scan(expr, &mut ix);
        // Re-key self-name call records onto their canonical ids so the
        // enumerability/all-sites checks see one unified call list.
        let alias_keys: Vec<(VarId, VarId)> =
            ix.self_aliases.iter().map(|(a, c)| (*a, *c)).collect();
        for (alias, canonical) in alias_keys {
            if let Some(mut sites) = ix.calls.remove(&alias) {
                ix.calls.entry(canonical).or_default().append(&mut sites);
            }
            if ix.value_used.contains(&alias) {
                ix.value_used.insert(canonical);
            }
        }
        ix
    }

    pub(super) fn element_binders_of(&self, list_roots: &BTreeSet<VarId>) -> BTreeSet<VarId> {
        let members = self.members_of(list_roots);
        // Elements: cons-heads of member iterations + head-projection lets.
        let mut elements: BTreeSet<VarId> = BTreeSet::new();
        for meta in self.rec_meta.values() {
            if members.contains(&meta.param0) {
                for h in &meta.cons_heads {
                    elements.insert(*h);
                }
            }
        }
        for (x, (src, kind)) in &self.let_aliases {
            if *kind == AliasKind::ListHead && members.contains(src) {
                elements.insert(*x);
            }
        }
        elements
    }

    /// UNION-claim param typing: a helper param qualifies when its fn
    /// is enumerable, has >= 1 call site, and EVERY site's slot arg
    /// resolves to a CLAIMED element/typed binder (`element_claims`) or
    /// a `.head` of a claimed member (`member_claims`) — and all the
    /// resolved claims AGREE on one element type. A helper fed TxOut at
    /// one site and TxInInfo at another never types (fail-closed).
    pub(super) fn params_with_agreed_claims(
        &self,
        element_claims: &BTreeMap<VarId, crate::decompile::simplify::postprocess::ContextType>,
        member_claims: &BTreeMap<VarId, crate::decompile::simplify::postprocess::ContextType>,
    ) -> Vec<(VarId, crate::decompile::simplify::postprocess::ContextType)> {
        let mut out = Vec::new();
        for (fid, params) in &self.params {
            if self.value_used.contains(fid) {
                continue;
            }
            let Some(sites) = self.calls.get(fid) else {
                continue;
            };
            if sites.is_empty() {
                continue;
            }
            for (slot, pid) in params.iter().enumerate() {
                let mut agreed: Option<crate::decompile::simplify::postprocess::ContextType> = None;
                let mut ok = true;
                for args in sites {
                    let claim = match args.get(slot) {
                        Some(ArgForm::Var(v)) => element_claims.get(v).copied(),
                        Some(ArgForm::Head(l)) => member_claims.get(l).copied(),
                        _ => None,
                    };
                    match (claim, agreed) {
                        (Some(ct), None) => agreed = Some(ct),
                        (Some(ct), Some(prev)) if ct == prev => {}
                        _ => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok && let Some(ct) = agreed {
                    out.push((*pid, ct));
                }
            }
        }
        out
    }

    /// The member set for `list_roots` (exposed for the Head-arg
    /// check). Multi-root on purpose: sibling co-typed list fields
    /// (`inputs` + `reference_inputs`, both `List<TxInInfo>`) often
    /// share one iteration helper whose call sites split across the
    /// roots — the all-sites member gate only passes with the union
    /// member set.
    pub(super) fn members_of(&self, list_roots: &BTreeSet<VarId>) -> BTreeSet<VarId> {
        let mut members: BTreeSet<VarId> = list_roots.clone();
        loop {
            let mut grew = false;
            for (x, (src, kind)) in &self.let_aliases {
                if *kind == AliasKind::UnListData && members.contains(src) && members.insert(*x) {
                    grew = true;
                }
            }
            for (fid, meta) in &self.rec_meta {
                if members.contains(&meta.param0) || self.value_used.contains(fid) {
                    continue;
                }
                let Some(sites) = self.calls.get(fid) else {
                    continue;
                };
                let mut external = 0usize;
                let all_member = !sites.is_empty()
                    && sites.iter().all(|args| match args.first() {
                        Some(ArgForm::Var(v)) | Some(ArgForm::UnListData(v)) => {
                            if meta.cons_tails.contains(v) {
                                true
                            } else if members.contains(v) {
                                external += 1;
                                true
                            } else {
                                false
                            }
                        }
                        Some(ArgForm::ListTail(v)) => *v == meta.param0,
                        _ => false,
                    });
                if all_member && external >= 1 && members.insert(meta.param0) {
                    grew = true;
                    for t in &meta.cons_tails {
                        members.insert(*t);
                    }
                }
            }
            if !grew {
                break;
            }
        }
        members
    }
}

fn classify_arg(e: &PseudoExpr) -> ArgForm {
    match e {
        PseudoExpr::Var { id: Some(v), .. } => ArgForm::Var(*v),
        PseudoExpr::BuiltinCall { name, args }
            if *name == BuiltinId::DataUnList && args.len() == 1 =>
        {
            match &args[0] {
                PseudoExpr::Var { id: Some(v), .. } => ArgForm::UnListData(*v),
                _ => ArgForm::Opaque,
            }
        }
        PseudoExpr::Apply { function, args }
            if args.len() == 1
                && matches!(
                    function.as_ref(),
                    PseudoExpr::BuiltinCall { name, args: ba }
                        if *name == BuiltinId::DataUnList && ba.is_empty()
                ) =>
        {
            match &args[0] {
                PseudoExpr::Var { id: Some(v), .. } => ArgForm::UnListData(*v),
                _ => ArgForm::Opaque,
            }
        }
        PseudoExpr::BuiltinCall { name, args }
            if *name == BuiltinId::ListTail && args.len() == 1 =>
        {
            match &args[0] {
                PseudoExpr::Var { id: Some(v), .. } => ArgForm::ListTail(*v),
                _ => ArgForm::Opaque,
            }
        }
        PseudoExpr::FieldAccess { record, selector }
            if matches!(selector, FieldSelector::ListHead) =>
        {
            match record.as_ref() {
                PseudoExpr::Var { id: Some(v), .. } => ArgForm::Head(*v),
                _ => ArgForm::Opaque,
            }
        }
        _ => ArgForm::Opaque,
    }
}

/// Find `when Var(param) is { [head, ..tail] -> … }` cons iterations
/// inside a fn body; collect head/tail binder ids.
fn collect_cons_bindings(
    body: &PseudoExpr,
    param0: VarId,
    heads: &mut BTreeSet<VarId>,
    tails: &mut BTreeSet<VarId>,
) {
    let mut pending = vec![body];
    while let Some(body) = pending.pop() {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = body
        {
            if matches!(
                subject.as_ref(),
                PseudoExpr::Var { id: Some(v), .. } if *v == param0
            ) {
                for clause in clauses {
                    if let WhenPattern::List { elements, tail } = &clause.pattern {
                        if let [head] = elements.as_slice() {
                            heads.insert(head.var_id());
                        }
                        if let Some(t) = tail {
                            tails.insert(t.var_id());
                        }
                    }
                }
            }
        }
        pending.extend(super::scope_recurse::children(body).into_iter().rev());
    }
}

fn record_fn_def(
    name_id: VarId,
    params: &[Binder],
    body: &PseudoExpr,
    ix: &mut ListIterationIndex,
) {
    let param_ids: Vec<VarId> = params.iter().map(|b| b.var_id()).collect();
    if let Some(p0) = param_ids.first() {
        let mut heads = BTreeSet::new();
        let mut tails = BTreeSet::new();
        collect_cons_bindings(body, *p0, &mut heads, &mut tails);
        if !heads.is_empty() || !tails.is_empty() {
            ix.rec_meta.insert(
                name_id,
                RecMeta {
                    param0: *p0,
                    cons_tails: tails,
                    cons_heads: heads,
                },
            );
        }
    }
    ix.params.insert(name_id, param_ids);
}

fn scan(expr: &PseudoExpr, ix: &mut ListIterationIndex) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            PseudoExpr::Let {
                id: Some(let_id),
                value,
                body,
                ..
            } => {
                match value.as_ref() {
                    PseudoExpr::Lambda { params, body: fb } => {
                        record_fn_def(*let_id, params, fb, ix);
                    }
                    PseudoExpr::RecFn {
                        name,
                        params,
                        body: fb,
                    } => {
                        record_fn_def(*let_id, params, fb, ix);
                        ix.self_aliases.insert(name.var_id(), *let_id);
                    }
                    other => match classify_arg(other) {
                        ArgForm::UnListData(src) => {
                            ix.let_aliases.insert(*let_id, (src, AliasKind::UnListData));
                        }
                        ArgForm::Head(src) => {
                            ix.let_aliases.insert(*let_id, (src, AliasKind::ListHead));
                        }
                        _ => {}
                    },
                }
                // Original: scan(value, ix) then scan(body, ix).
                pending.push(body);
                pending.push(value);
            }
            PseudoExpr::RecFn { name, params, body } => {
                // Bare RecFn (not let-bound): canonical id = the self name.
                record_fn_def(name.var_id(), params, body, ix);
                pending.push(body);
            }
            PseudoExpr::Apply { function, args } => {
                let visit_function = match function.as_ref() {
                    PseudoExpr::Var { id: Some(fid), .. } => {
                        if args.is_empty() {
                            // 0-arg apply — fail-closed value use.
                            ix.value_used.insert(*fid);
                        } else {
                            ix.calls
                                .entry(*fid)
                                .or_default()
                                .push(args.iter().map(classify_arg).collect());
                        }
                        None
                    }
                    other => Some(other),
                };
                // Original: (scan(function) iff not a call-head Var) then,
                // for each arg in order, scan(arg).
                pending.extend(args.iter().rev());
                if let Some(f) = visit_function {
                    pending.push(f);
                }
            }
            PseudoExpr::Var { id: Some(vid), .. } => {
                // A bare Var outside call-head position — value use.
                ix.value_used.insert(*vid);
            }
            other => {
                pending.extend(super::scope_recurse::children(other).into_iter().rev());
            }
        }
    }
}

#[cfg(test)]
mod tests;
