//! Resolve positional `tx_info.fields[N]` accessors to the schema-named
//! TxInfo field (`tx_info.inputs`, `tx_info.outputs`, …).
//!
//! The let-form companion to [`rename_tx_info_binders`], which handles
//! the `when tx_info is { Unknown_S_X(field_0, …) }` destructure form.
//! `cardano_context_naming` resolves names before render, whereas the
//! `tx_info` alias and these `field_N` lets are materialized later, here
//! in render_prep, so that resolver never sees the let-alias shape.
//!
//! A pure presentational relabel: `tx_info.fields[0]` and `tx_info.inputs`
//! decode the identical underlying Data list element, the field name being
//! the schema label for that position. No runtime check is introduced
//! (unlike an `expect Ctor(..) = x` destructure), so it can never turn a
//! passing script into a failing one. The rewrite fires only when:
//! - the record is provably TxInfo — a binder bound (by `VarId`) to
//!   `<entry>.tx_info`, `<entry>` being the validator entry param
//!   `script_context`. The inline, un-aliased
//!   `script_context.tx_info.fields[N]` form is deliberately left
//!   positional (`leaves_inline_script_context_tx_info_positional`);
//! - the index is within the version's TxInfo arity — an out-of-range
//!   index stays positional `.fields[N]`.
//!
//! The field layout differs by version (V1: 10 fields, no
//! `reference_inputs`; V2: 12; V3: 16), so the rewrite needs the concrete
//! [`ScriptVersion`], read off the [`RenderCtx`] the pipeline builds and
//! `prepare_for_render` threads in. With no version set the pass is a no-op
//! and positional `.fields[N]` is preserved.

use std::collections::{HashMap, HashSet};

use crate::builtins::BuiltinId;
use crate::decompile::ScriptVersion;
use crate::pseudo::ast::{PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

use super::ctx::RenderCtx;
use super::rename_hygiene::{apply_renames, collect_used_names, commit_binder_renames};
use super::rename_synthetic_field_let_binders::is_synthetic_field_name;
use super::rename_tx_info_binders::canonical_names_for_tx_info_arity;
use super::scope_recurse::{children, rewrite_bottom_up};

/// Pre-order walk: visit the node, then its children in source order.
fn preorder<'a>(root: &'a PseudoExpr, mut visit: impl FnMut(&'a PseudoExpr)) {
    let mut stack: Vec<&'a PseudoExpr> = vec![root];
    while let Some(expr) = stack.pop() {
        visit(expr);
        for child in children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// The canonical TxInfo field-name list for a version; the shared table is
/// keyed by arity.
fn tx_info_field_names(version: ScriptVersion) -> Option<&'static [&'static str]> {
    let arity = match version {
        ScriptVersion::PlutusV1 => 10,
        ScriptVersion::PlutusV2 => 12,
        ScriptVersion::PlutusV3 => 16,
    };
    canonical_names_for_tx_info_arity(arity)
}

/// Canonical ScriptContext field names by version — must agree with
/// `ContextField::display_name` / the typed schema. The `script_context`
/// counterpart of `tx_info_field_names`.
fn script_context_field_names(version: ScriptVersion) -> &'static [&'static str] {
    match version {
        ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => &["tx_info", "purpose"],
        ScriptVersion::PlutusV3 => &["tx_info", "redeemer", "script_info"],
    }
}

pub(super) fn resolve_tx_info_field_indices(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    // Two channels with different soundness contracts: strict
    // (`RenderCtx::version`) is `None` under V1/V2 ambiguity and gates ALL
    // TxInfo `.fields[N]` naming; sc (`RenderCtx::sc_version`) is the plan
    // version and gates only the band-invariant ScriptContext top level.
    let strict_version = ctx.version();
    let names = strict_version.and_then(tx_info_field_names);
    let Some(sc_version) = ctx.sc_version() else {
        return expr;
    };
    if strict_version.is_some() && names.is_none() {
        // Pinned version with no TxInfo layout table — nothing to relabel.
        return expr;
    }
    // The validator entry param (the `decompiled` lambda's `script_context`
    // binder). Both the tx_info-alias collection and the ScriptContext
    // field-access arm are VarId-gated on it: a name-only anchor would also
    // rewrite a helper param coincidentally named `script_context` that holds
    // arbitrary data. Empty set ⇒ neither fires (fail closed).
    let entry_sc_ids = super::collapse_script_context_when::collect_script_context_param_ids(&expr);
    // VarIds are globally unique, so a flat set (no scope tracking) is correct.
    let mut tx_info_ids = HashSet::new();
    collect_tx_info_binders(&expr, &mut tx_info_ids, &entry_sc_ids);
    // `names` is None under V1/V2 ambiguity → the TxInfo arm is skipped and
    // only the ScriptContext arm runs, on the band-invariant `sc_names`.
    let sc_names = script_context_field_names(sc_version);
    let expr = rewrite(expr, &tx_info_ids, names, sc_names, &entry_sc_ids);
    // The remaining TxInfo-field renames are strictly version-pinned.
    let Some(names) = names else {
        return expr;
    };
    // `let field_0_159 = tx_info.inputs` →
    // `let tx_inputs_0 = tx_info.inputs`.
    let expr = rename_field_aliases(expr, &tx_info_ids, names);
    // Second-order decode aliases:
    // `let fields_0_2_list = builtin.un_list_data(tx_inputs_0)` →
    // `let inputs_list = …` (and `un_map_data` → `<field>_map`).
    let expr = rename_derived_decode_aliases(expr, &tx_info_ids, names);
    // Element naming: `expect Some(item) = get_at(inputs_list, _)` →
    // `Some(input)`.
    rename_list_element_binders(expr, &tx_info_ids, names)
}

/// Rename a synthetic `field_N` binder whose value is `tx_info.<field>` to
/// `tx_<field>_<idx>`, `<idx>` being the field's TxInfo schema position.
/// The binder and every `VarId`-matched reference are renamed together;
/// collisions are dropped conservatively by [`commit_renames`].
fn rename_field_aliases(
    expr: PseudoExpr,
    ids: &HashSet<VarId>,
    names: &[&'static str],
) -> PseudoExpr {
    let mut candidates: Vec<(VarId, String)> = Vec::new();
    collect_alias_rename_candidates(&expr, ids, names, &mut candidates);
    commit_binder_renames(expr, candidates)
}

/// Rename a synthetic `field(s)_N…_list` / `…_map` binder whose value is
/// `un_list_data(<src>)` / `un_map_data(<src>)`, `<src>` a provably-TxInfo
/// field, to `<field>_list` / `<field>_map` (`inputs_list`, `mint_map`).
/// `<field>` is the schema stem, never re-parsed from a `tx_<field>_<idx>`
/// binder — which would yield `tx_inputs_0_list`.
fn rename_derived_decode_aliases(
    expr: PseudoExpr,
    ids: &HashSet<VarId>,
    names: &[&'static str],
) -> PseudoExpr {
    // VarId of each binder bound to `<tx_info>.<field>` → that field's stem.
    let mut field_alias_stems: HashMap<VarId, &'static str> = HashMap::new();
    collect_field_alias_stems(&expr, ids, names, &mut field_alias_stems);
    let mut candidates: Vec<(VarId, String)> = Vec::new();
    collect_derived_decode_candidates(&expr, ids, names, &field_alias_stems, &mut candidates);
    commit_binder_renames(expr, candidates)
}

/// Map every binder bound to `<tx_info-tracked>.<schema_field>` to that field's
/// stem (`tx_inputs_0`'s VarId → `"inputs"`). Keyed by `VarId`, so it is
/// robust to the field-alias rename having renamed the binder.
fn collect_field_alias_stems(
    expr: &PseudoExpr,
    ids: &HashSet<VarId>,
    names: &[&'static str],
    out: &mut HashMap<VarId, &'static str>,
) {
    preorder(expr, |expr| {
        if let PseudoExpr::Let {
            id: Some(bid),
            value,
            ..
        } = expr
            && let Some(stem) = tx_info_field_of(value, ids, names)
        {
            out.insert(*bid, stem);
        }
    });
}

/// If `value` is `<tx_info-tracked>.<schema_field>`, return the schema stem.
fn tx_info_field_of(
    value: &PseudoExpr,
    ids: &HashSet<VarId>,
    names: &[&'static str],
) -> Option<&'static str> {
    let PseudoExpr::FieldAccess { record, selector } = value else {
        return None;
    };
    let PseudoExpr::Var { id: Some(rid), .. } = record.as_ref() else {
        return None;
    };
    if !ids.contains(rid) {
        return None;
    }
    names
        .iter()
        .copied()
        .find(|n| *n == selector.as_pretty_name())
}

/// Collect `(decode-binder VarId, "<field>_<kind>")` for each
/// `let <synthetic-decode-alias> = un_list_data/un_map_data(<src>)` where
/// `<src>` resolves to a TxInfo field.
fn collect_derived_decode_candidates(
    expr: &PseudoExpr,
    ids: &HashSet<VarId>,
    names: &[&'static str],
    field_alias_stems: &HashMap<VarId, &'static str>,
    out: &mut Vec<(VarId, String)>,
) {
    preorder(expr, |expr| {
        if let PseudoExpr::Let {
            name,
            id: Some(bid),
            value,
            ..
        } = expr
            && is_synthetic_decode_alias_name(name)
            && let Some((kind, arg)) = un_data_decode(value)
            && let Some(field) = decode_arg_field(arg, ids, names, field_alias_stems)
        {
            out.push((*bid, format!("{field}_{kind}")));
        }
    });
}

/// The TxInfo field stem behind a `un_*_data` argument, if any: either a
/// reference to a tracked field-alias binder (`tx_inputs_0`), or the inline
/// `tx_info.<field>` access.
fn decode_arg_field(
    arg: &PseudoExpr,
    ids: &HashSet<VarId>,
    names: &[&'static str],
    field_alias_stems: &HashMap<VarId, &'static str>,
) -> Option<&'static str> {
    match arg {
        PseudoExpr::Var { id: Some(v), .. } => field_alias_stems.get(v).copied(),
        _ => tx_info_field_of(arg, ids, names),
    }
}

/// `un_list_data(x)` / `un_map_data(x)` in either the direct `BuiltinCall` form
/// or the partial-application `Apply(BuiltinCall(_, []), [x])` form. Returns the
/// decode kind (`"list"` / `"map"`) and the single argument.
fn un_data_decode(value: &PseudoExpr) -> Option<(&'static str, &PseudoExpr)> {
    let kind = |name: &BuiltinId| match name {
        BuiltinId::DataUnList => Some("list"),
        BuiltinId::DataUnMap => Some("map"),
        _ => None,
    };
    match value {
        PseudoExpr::BuiltinCall { name, args } if args.len() == 1 => {
            kind(name).map(|k| (k, &args[0]))
        }
        PseudoExpr::Apply { function, args } if args.len() == 1 => {
            if let PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } = function.as_ref()
                && builtin_args.is_empty()
            {
                kind(name).map(|k| (k, &args[0]))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Match the synthetic second-order decode-alias binder shape
/// `^fields?_\d+(_\d+)?_(list|map)$` — deliberately distinct from
/// `is_synthetic_field_name`, which rejects that suffix and the plural `fields_`.
fn is_synthetic_decode_alias_name(name: &str) -> bool {
    let Some(stem) = name
        .strip_suffix("_list")
        .or_else(|| name.strip_suffix("_map"))
    else {
        return false;
    };
    let Some(rest) = stem
        .strip_prefix("fields_")
        .or_else(|| stem.strip_prefix("field_"))
    else {
        return false;
    };
    if rest.is_empty() {
        return false;
    }
    let mut parts = rest.split('_');
    let Some(first) = parts.next() else {
        return false;
    };
    if first.is_empty() || !first.bytes().all(|b| b.is_ascii_digit()) {
        return false;
    }
    if let Some(second) = parts.next() {
        if second.is_empty() || !second.bytes().all(|b| b.is_ascii_digit()) {
            return false;
        }
    }
    parts.next().is_none()
}

/// Collect `(binder VarId, "tx_<field>_<idx>")` for each
/// `let field_N = tx_info.<field>` on a tracked TxInfo record.
fn collect_alias_rename_candidates(
    expr: &PseudoExpr,
    ids: &HashSet<VarId>,
    names: &[&'static str],
    out: &mut Vec<(VarId, String)>,
) {
    preorder(expr, |expr| {
        if let PseudoExpr::Let {
            name,
            id: Some(bid),
            value,
            ..
        } = expr
            && is_synthetic_field_name(name)
            && let PseudoExpr::FieldAccess { record, selector } = value.as_ref()
            && let PseudoExpr::Var { id: Some(rid), .. } = record.as_ref()
            && ids.contains(rid)
            && let Some(idx) = names.iter().position(|n| *n == selector.as_pretty_name())
        {
            out.push((*bid, format!("tx_{}_{}", names[idx], idx)));
        }
    });
}

/// The element (singular) name for a genuinely LIST-typed TxInfo field, or
/// `None`. An exhaustive table, NOT an English stemmer: `signatories` →
/// `signatory`, not `signatorie`.
///
/// Only the `List<_>` fields qualify. The `Pairs<_,_>` fields — `mint`,
/// `withdrawals`, `redeemers`, `datums`, `votes` — are excluded because
/// their elements are key-value pairs (a `get_at` over `datums` yields a
/// `(hash, datum)`, not a `datum`), and the scalars (`fee`, `id`,
/// `valid_range`, treasury fields) have no element at all.
fn list_field_singular(field: &str) -> Option<&'static str> {
    Some(match field {
        "inputs" => "input",
        "reference_inputs" => "reference_input",
        "outputs" => "output",
        "certificates" => "certificate",
        "signatories" => "signatory",
        "proposal_procedures" => "proposal_procedure",
        _ => return None,
    })
}

/// Name the `Some(_)` payload of a shape-verified `get_at(<list>, _)`
/// after the list field's singular, when `<list>` is provably a TxInfo
/// list-field source.
fn rename_list_element_binders(
    expr: PseudoExpr,
    ids: &HashSet<VarId>,
    names: &[&'static str],
) -> PseudoExpr {
    let source_map = build_list_source_map(&expr, ids, names);
    if source_map.is_empty() {
        return expr;
    }
    let mut candidates: Vec<(VarId, &'static str)> = Vec::new();
    let mut conflicts: HashSet<VarId> = HashSet::new();
    let mut ancestors: Vec<(VarId, &'static str)> = Vec::new();
    collect_element_candidates(
        &expr,
        &source_map,
        &mut ancestors,
        &mut candidates,
        &mut conflicts,
    );
    let owned: Vec<(VarId, String)> = candidates
        .into_iter()
        .map(|(id, target)| (id, target.to_string()))
        .collect();
    commit_element_renames(expr, owned, &conflicts)
}

/// Apply element renames. Unlike `commit_renames`, the SAME singular target
/// on MULTIPLE distinct binders is allowed and correct (two
/// `get_at(inputs_list)` results in disjoint scopes are both an `input`).
/// Capture is prevented twice over: `conflicts` holds binders NESTED under
/// a same-target element binder, and a target already bound elsewhere in
/// the tree (`used_names`) is dropped. All references are `VarId`-matched,
/// so semantics never change.
fn commit_element_renames(
    expr: PseudoExpr,
    candidates: Vec<(VarId, String)>,
    conflicts: &HashSet<VarId>,
) -> PseudoExpr {
    if candidates.is_empty() {
        return expr;
    }
    let mut used_names: HashSet<String> = HashSet::new();
    collect_used_names(&expr, &mut used_names);
    let renames: HashMap<VarId, String> = candidates
        .into_iter()
        .filter(|(id, target)| !conflicts.contains(id) && !used_names.contains(target))
        .collect();
    if renames.is_empty() {
        return expr;
    }
    apply_renames(expr, &renames)
}

/// VarId → plural list-field stem for both the field alias (`tx_inputs_0`) and
/// the decoded-list alias (`inputs_list`). Restricted to list-typed fields.
fn build_list_source_map(
    expr: &PseudoExpr,
    ids: &HashSet<VarId>,
    names: &[&'static str],
) -> HashMap<VarId, &'static str> {
    let mut field_alias_stems: HashMap<VarId, &'static str> = HashMap::new();
    collect_field_alias_stems(expr, ids, names, &mut field_alias_stems);
    // Class A: field-alias binders, restricted to list-typed fields.
    let mut map: HashMap<VarId, &'static str> = field_alias_stems
        .iter()
        .filter(|(_, stem)| list_field_singular(stem).is_some())
        .map(|(id, stem)| (*id, *stem))
        .collect();
    // Class B: `let X = un_list_data(<list-field source>)` decode aliases.
    collect_list_decode_stems(expr, ids, names, &field_alias_stems, &mut map);
    map
}

/// Add VarIds of `let X = builtin.un_list_data(<src>)` binders whose `<src>`
/// resolves to a list-typed TxInfo field, mapped to that field's stem.
fn collect_list_decode_stems(
    expr: &PseudoExpr,
    ids: &HashSet<VarId>,
    names: &[&'static str],
    field_alias_stems: &HashMap<VarId, &'static str>,
    out: &mut HashMap<VarId, &'static str>,
) {
    preorder(expr, |expr| {
        if let PseudoExpr::Let {
            id: Some(bid),
            value,
            ..
        } = expr
            && let Some(("list", arg)) = un_data_decode(value)
            && let Some(stem) = decode_arg_field(arg, ids, names, field_alias_stems)
            && list_field_singular(stem).is_some()
        {
            out.insert(*bid, stem);
        }
    });
}

/// Collect `(Some-payload binder VarId, "<singular>")` for each
/// `when get_at(<list-source>, _) is { Some(x) -> … }` (including the
/// `expect` surface, a `When` in the AST). `ancestors` tracks the element
/// binders whose Some-arm body the walk is inside; a candidate sharing a
/// target with an enclosing one goes into `conflicts` together with that
/// ancestor, so the commit step drops the pair instead of capturing.
fn collect_element_candidates(
    expr: &PseudoExpr,
    source_map: &HashMap<VarId, &'static str>,
    ancestors: &mut Vec<(VarId, &'static str)>,
    out: &mut Vec<(VarId, &'static str)>,
    conflicts: &mut HashSet<VarId>,
) {
    let mut steps: Vec<ElemStep<'_>> = vec![ElemStep::Visit(expr)];

    while let Some(step) = steps.pop() {
        match step {
            ElemStep::PopAncestor => {
                ancestors.pop();
            }
            ElemStep::Visit(expr) => {
                let PseudoExpr::When {
                    subject, clauses, ..
                } = expr
                else {
                    for child in children(expr).into_iter().rev() {
                        steps.push(ElemStep::Visit(child));
                    }
                    continue;
                };
                let element = get_at_list_source(subject, source_map).and_then(list_field_singular);
                // Reversed so they pop in source order: the subject — which
                // is evaluated in the enclosing scope (no new binder) —
                // then the clauses.
                for clause in clauses.iter().rev() {
                    steps.push(ElemStep::Clause { clause, element });
                }
                steps.push(ElemStep::Visit(subject.as_ref()));
            }
            ElemStep::Clause { clause, element } => {
                let candidate = element.and_then(|singular| match &clause.pattern {
                    WhenPattern::Constructor { shape, fields, .. }
                        if matches!(shape, ConstructorShape::Known(KnownConstructor::Some))
                            && fields.len() == 1 =>
                    {
                        Some((fields[0].var_id(), singular))
                    }
                    _ => None,
                });
                if let Some((vid, singular)) = candidate {
                    // Nesting capture guard: a same-target element binder is in scope.
                    if ancestors.iter().any(|(_, t)| *t == singular) {
                        conflicts.insert(vid);
                        for (aid, t) in ancestors.iter() {
                            if *t == singular {
                                conflicts.insert(*aid);
                            }
                        }
                    }
                    out.push((vid, singular));
                    ancestors.push((vid, singular));
                    // Reversed: guard, then body, then the `ancestors.pop()`.
                    steps.push(ElemStep::PopAncestor);
                    steps.push(ElemStep::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        steps.push(ElemStep::Visit(guard));
                    }
                } else {
                    steps.push(ElemStep::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        steps.push(ElemStep::Visit(guard));
                    }
                }
            }
        }
    }
}

/// A job on the stack of [`collect_element_candidates`] and
/// [`collect_cons_head_candidates`]. `Clause` and `PopAncestor` are the points run
/// between two child walks; they must stay separate steps.
enum ElemStep<'a> {
    Visit(&'a PseudoExpr),
    Clause {
        clause: &'a WhenClause,
        /// The singular element name the enclosing `when`'s subject
        /// licenses, computed once per `when`.
        element: Option<&'static str>,
    },
    PopAncestor,
}

/// If `subject` is `get_at(<L>, …)` where `<L>` is a proven list-field
/// source, return that field's stem. Matching `get_at` by exact name is
/// sound: only the verified list-index recursion shape is named `get_at`,
/// so the call provably yields a list element.
///
/// `<L>` is either a bare list-source `Var` or an inline
/// `un_list_data(<list-source Var>)` over one.
fn get_at_list_source<'a>(
    subject: &PseudoExpr,
    source_map: &HashMap<VarId, &'a str>,
) -> Option<&'a str> {
    let PseudoExpr::Apply { function, args } = subject else {
        return None;
    };
    let PseudoExpr::Var { name, .. } = function.as_ref() else {
        return None;
    };
    if name != "get_at" {
        return None;
    }
    let arg = args.first()?;
    // Bare `Var` list source, or `un_list_data(<Var>)` over one.
    let list_id = match arg {
        PseudoExpr::Var { id: Some(v), .. } => *v,
        _ => match un_data_decode(arg) {
            Some(("list", PseudoExpr::Var { id: Some(v), .. })) => *v,
            _ => return None,
        },
    };
    source_map.get(&list_id).copied()
}

// ===== cons-head + interproc rec-fn list-param naming =====
// Runs after `bind_list_cons_head_tail` so the `[head, ..tail]` binders
// already exist. Names a list source's cons-head after the field SINGULAR,
// and a rec-fn param provably ALWAYS fed that source after the PLURAL.

pub(super) fn rename_list_element_binders_late(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    let Some(version) = ctx.version() else {
        return expr;
    };
    let Some(names) = tx_info_field_names(version) else {
        return expr;
    };
    let entry_sc_ids = super::collapse_script_context_when::collect_script_context_param_ids(&expr);
    let mut tx_info_ids = HashSet::new();
    collect_tx_info_binders(&expr, &mut tx_info_ids, &entry_sc_ids);
    let mut source_map = build_list_source_map(&expr, &tx_info_ids, names);
    if source_map.is_empty() {
        return expr;
    }
    let mut renames: Vec<(VarId, String)> = Vec::new();
    // Interproc: augments `source_map` with each qualifying param (→ plural
    // stem) and emits its rename; the collector below names its cons-head.
    qualify_interproc_list_params(&expr, &mut source_map, &mut renames);
    // Cons-head: name `[head, ..tail]` head of a list source
    // (direct or a just-qualified param) → SINGULAR.
    let mut conflicts: HashSet<VarId> = HashSet::new();
    let mut ancestors: Vec<(VarId, &'static str)> = Vec::new();
    collect_cons_head_candidates(
        &expr,
        &source_map,
        &mut ancestors,
        &mut renames,
        &mut conflicts,
    );
    commit_element_renames(expr, renames, &conflicts)
}

/// Collect `(cons-head binder VarId, "<singular>")` for each
/// `when <list-source Var> is { [head, ..tail] -> … }`. Same scope-tracked
/// nesting/capture guard as [`collect_element_candidates`].
fn collect_cons_head_candidates(
    expr: &PseudoExpr,
    source_map: &HashMap<VarId, &'static str>,
    ancestors: &mut Vec<(VarId, &'static str)>,
    out: &mut Vec<(VarId, String)>,
    conflicts: &mut HashSet<VarId>,
) {
    let mut steps: Vec<ElemStep<'_>> = vec![ElemStep::Visit(expr)];

    while let Some(step) = steps.pop() {
        match step {
            ElemStep::PopAncestor => {
                ancestors.pop();
            }
            ElemStep::Visit(expr) => {
                let PseudoExpr::When {
                    subject, clauses, ..
                } = expr
                else {
                    for child in children(expr).into_iter().rev() {
                        steps.push(ElemStep::Visit(child));
                    }
                    continue;
                };
                let element = match subject.as_ref() {
                    PseudoExpr::Var { id: Some(v), .. } => {
                        source_map.get(v).and_then(|stem| list_field_singular(stem))
                    }
                    _ => None,
                };
                // Reversed so they pop in source order: subject, then clauses.
                for clause in clauses.iter().rev() {
                    steps.push(ElemStep::Clause { clause, element });
                }
                steps.push(ElemStep::Visit(subject.as_ref()));
            }
            ElemStep::Clause { clause, element } => {
                let candidate = element.and_then(|singular| match &clause.pattern {
                    WhenPattern::List {
                        elements,
                        tail: Some(_),
                    }
                        // Unused-binder marking ran earlier, so renaming a `_`-prefixed
                        // `_head` → `output` would strip the intentional-unused marker.
                        if elements.len() == 1 && !elements[0].as_str().starts_with('_') =>
                    {
                        Some((elements[0].var_id(), singular))
                    }
                    _ => None,
                });
                if let Some((vid, singular)) = candidate {
                    if ancestors.iter().any(|(_, t)| *t == singular) {
                        conflicts.insert(vid);
                        for (aid, t) in ancestors.iter() {
                            if *t == singular {
                                conflicts.insert(*aid);
                            }
                        }
                    }
                    out.push((vid, singular.to_string()));
                    ancestors.push((vid, singular));
                    // Reversed: guard, then body, then the `ancestors.pop()`.
                    steps.push(ElemStep::PopAncestor);
                    steps.push(ElemStep::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        steps.push(ElemStep::Visit(guard));
                    }
                } else {
                    steps.push(ElemStep::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        steps.push(ElemStep::Visit(guard));
                    }
                }
            }
        }
    }
}

/// A rec fn whose first param is cons-iterated: `param0` + the `tail` binder of
/// its `when param0 is { [_, ..tail] }` match (the recursive-call witness).
/// `opaque` gates the param rename to mechanically-named helpers. `rec_ancestors`
/// are the canonical ids of the rec fns this one is lexically nested inside —
/// used to drop a nested same-target param rename (capture guard).
struct RecListIter {
    param0: VarId,
    cons_tail: VarId,
    opaque: bool,
    rec_ancestors: Vec<VarId>,
}

/// True for the decompiler's MECHANICAL rec-fn names (`rec_fn_12`, `helper_7`).
/// Only these get the list-param rename: a RECOGNIZED generic combinator
/// (`get_at`, `find`, `any`, `filter`, …) keeps its generic `list` param, since
/// specializing it to `inputs` would misrepresent the helper as input-specific.
fn is_opaque_rec_name(name: &str) -> bool {
    let strip_digits = |s: &str| -> bool {
        !s.is_empty()
            && s.split('_')
                .all(|seg| !seg.is_empty() && seg.bytes().all(|b| b.is_ascii_digit()))
    };
    name.strip_prefix("rec_fn_").is_some_and(strip_digits)
        || name.strip_prefix("helper_").is_some_and(strip_digits)
}

#[derive(Default)]
struct RecScan {
    /// CANONICAL rec-fn id → its cons-iterated first param. The canonical id is
    /// the enclosing `let` binder when the rec fn is `let f = rec fn …` (the id
    /// EXTERNAL callers use), else the bare `RecFn` self-name.
    recs: HashMap<VarId, RecListIter>,
    /// RecFn self-name id → canonical id. A `let f = rec fn g(…)` has external
    /// calls under `f` and recursive calls under `g`; this maps `g → f` so both
    /// call sets are gathered for one function.
    aliases: HashMap<VarId, VarId>,
    /// Identifiers that appear at least once as a VALUE (not an `Apply` head) —
    /// fail-closed: such a function's call set is not fully enumerable.
    value_used: HashSet<VarId>,
    /// id → the slot-0 argument at each call site (cloned), keyed by the raw
    /// call-head id (canonical OR alias).
    slot0: HashMap<VarId, Vec<PseudoExpr>>,
    /// Canonical ids of the rec fns currently being descended into (lexical
    /// nesting stack), used to populate `RecListIter::rec_ancestors`.
    rec_stack: Vec<VarId>,
}

/// Name a rec-fn first param after a TxInfo list field when EVERY
/// call site proves the param is that list (or a recursive sub-list of it).
///
/// Sound gate (fail-closed): the rec-fn name must (a) be ENUMERABLE — never used
/// as a value, only as an `Apply` head, so every call is visible; (b) cons-iterate
/// its first param (`when param0 is { [_, ..tail] }`); and (c) every call's slot-0
/// be EITHER the same external list source `S` (≥1 such) OR the recursive
/// `tail` of that match. Then `param0` IS an `S` list across the whole iteration
/// → rename it to the plural and register it as a list source (its cons-head is
/// named SINGULAR by [`collect_cons_head_candidates`]).
fn qualify_interproc_list_params(
    expr: &PseudoExpr,
    source_map: &mut HashMap<VarId, &'static str>,
    renames: &mut Vec<(VarId, String)>,
) {
    let mut scan = RecScan::default();
    scan_rec_calls(expr, &mut scan);
    // (param0, plural stem, canonical id) for each qualifying rec fn.
    let mut quals: Vec<(VarId, &'static str, VarId)> = Vec::new();
    for (canonical, meta) in &scan.recs {
        if !meta.opaque {
            continue; // recognized generic combinator → keep its generic param
        }
        // The function's id set: the canonical id + any self-name aliases.
        let alias_ids: Vec<VarId> = scan
            .aliases
            .iter()
            .filter(|(_, c)| *c == canonical)
            .map(|(r, _)| *r)
            .collect();
        // Enumerable: NONE of the ids may be used as a value.
        if scan.value_used.contains(canonical)
            || alias_ids.iter().any(|r| scan.value_used.contains(r))
        {
            continue; // not enumerable → fail-closed
        }
        // Gather slot-0 args across all of the function's call ids.
        let mut slots: Vec<&PseudoExpr> = Vec::new();
        if let Some(s) = scan.slot0.get(canonical) {
            slots.extend(s.iter());
        }
        for r in &alias_ids {
            if let Some(s) = scan.slot0.get(r) {
                slots.extend(s.iter());
            }
        }
        if slots.is_empty() {
            continue; // no call sites
        }
        let mut stem: Option<&'static str> = None;
        let mut has_external = false;
        let mut ok = true;
        for arg in slots {
            match classify_list_arg(arg, source_map, meta.cons_tail) {
                ArgClass::Source(s) => {
                    has_external = true;
                    if let Some(prev) = stem {
                        if prev != s {
                            ok = false;
                            break;
                        }
                    } else {
                        stem = Some(s);
                    }
                }
                ArgClass::RecursiveTail => {}
                ArgClass::Other => {
                    ok = false;
                    break;
                }
            }
        }
        if ok
            && has_external
            && let Some(s) = stem
        {
            quals.push((meta.param0, s, *canonical));
        }
    }
    // Capture guard: two qualifying params with the SAME plural target whose rec
    // fns are lexically NESTED would, after both rename to e.g. `inputs`, let an
    // outer-param reference in the inner body be captured by the inner param.
    // Drop both (conservative): the commit step's `used_names` guard covers
    // only names already in the tree, so intra-batch nesting must be caught
    // here. Sibling (disjoint) same-target params are kept.
    let nested = |a: VarId, b: VarId| -> bool {
        scan.recs
            .get(&a)
            .is_some_and(|m| m.rec_ancestors.contains(&b))
            || scan
                .recs
                .get(&b)
                .is_some_and(|m| m.rec_ancestors.contains(&a))
    };
    let mut dropped: HashSet<VarId> = HashSet::new();
    for i in 0..quals.len() {
        for j in (i + 1)..quals.len() {
            if quals[i].1 == quals[j].1 && nested(quals[i].2, quals[j].2) {
                dropped.insert(quals[i].0);
                dropped.insert(quals[j].0);
            }
        }
    }
    for (param0, stem, _) in quals {
        if dropped.contains(&param0) {
            continue;
        }
        source_map.insert(param0, stem);
        renames.push((param0, stem.to_string()));
    }
}

enum ArgClass {
    /// A proven list-field source (the external entry argument).
    Source(&'static str),
    /// The recursive sub-list (the cons-`tail` of the param's match).
    RecursiveTail,
    /// Anything else — disqualifies the function.
    Other,
}

/// Classify a rec-fn slot-0 argument for the interproc gate.
fn classify_list_arg(
    arg: &PseudoExpr,
    source_map: &HashMap<VarId, &'static str>,
    cons_tail: VarId,
) -> ArgClass {
    if let PseudoExpr::Var { id: Some(v), .. } = arg {
        if *v == cons_tail {
            return ArgClass::RecursiveTail;
        }
        if let Some(stem) = source_map.get(v) {
            return ArgClass::Source(stem);
        }
    }
    if let Some(("list", PseudoExpr::Var { id: Some(v), .. })) = un_data_decode(arg)
        && let Some(stem) = source_map.get(v)
    {
        return ArgClass::Source(stem);
    }
    ArgClass::Other
}

/// One-pass scan: record cons-iterating rec fns, value-used identifiers, and
/// each rec-fn call's slot-0 argument. A `Var` reached as anything other than an
/// `Apply` head is a value-use (fail-closed enumerability).
fn scan_rec_calls(expr: &PseudoExpr, scan: &mut RecScan) {
    let mut steps: Vec<ScanStep<'_>> = vec![ScanStep::Visit(expr)];

    while let Some(step) = steps.pop() {
        let expr = match step {
            ScanStep::Visit(expr) => expr,
            ScanStep::PopRec => {
                scan.rec_stack.pop();
                continue;
            }
        };
        match expr {
            // `let f = rec fn g(p0, …) { … }` — external callers use `f`, recursive
            // calls use `g`. Canonical id = `f`; record `g → f` alias.
            PseudoExpr::Let {
                name: let_name,
                id: Some(let_id),
                value,
                body,
            } if matches!(value.as_ref(), PseudoExpr::RecFn { .. }) => {
                let PseudoExpr::RecFn {
                    name,
                    params,
                    body: fbody,
                } = value.as_ref()
                else {
                    unreachable!("guarded by the match arm");
                };
                let recorded = if let Some(p0) = params.first()
                    && let Some((_, cons_tail)) = find_param_cons_match(fbody, p0.var_id())
                {
                    scan.recs.insert(
                        *let_id,
                        RecListIter {
                            param0: p0.var_id(),
                            cons_tail,
                            opaque: is_opaque_rec_name(let_name),
                            rec_ancestors: scan.rec_stack.clone(),
                        },
                    );
                    scan.aliases.insert(name.var_id(), *let_id);
                    true
                } else {
                    false
                };
                // Descend into the rec-fn body with this canonical id on the nesting
                // stack so any inner rec fn records it as an ancestor.
                if recorded {
                    scan.rec_stack.push(*let_id);
                }
                // Reversed: the rec-fn body, then the `rec_stack` pop, then
                // the `let` body — which is NOT inside the rec fn, so it is
                // scanned un-nested.
                steps.push(ScanStep::Visit(body.as_ref()));
                if recorded {
                    steps.push(ScanStep::PopRec);
                }
                steps.push(ScanStep::Visit(fbody.as_ref()));
            }
            PseudoExpr::RecFn { name, params, body } => {
                let recorded = if let Some(p0) = params.first()
                    && let Some((_, cons_tail)) = find_param_cons_match(body, p0.var_id())
                    && !scan.aliases.contains_key(&name.var_id())
                {
                    // Bare RecFn (not the value of a `let`): canonical = self-name.
                    scan.recs.insert(
                        name.var_id(),
                        RecListIter {
                            param0: p0.var_id(),
                            cons_tail,
                            opaque: is_opaque_rec_name(name.as_str()),
                            rec_ancestors: scan.rec_stack.clone(),
                        },
                    );
                    true
                } else {
                    false
                };
                if recorded {
                    scan.rec_stack.push(name.var_id());
                }
                if recorded {
                    steps.push(ScanStep::PopRec);
                }
                steps.push(ScanStep::Visit(body.as_ref()));
            }
            PseudoExpr::Apply { function, args } => {
                let scan_function = if let PseudoExpr::Var { id: Some(fid), .. } = function.as_ref()
                {
                    if let Some(a0) = args.first() {
                        scan.slot0.entry(*fid).or_default().push(a0.clone());
                    }
                    // The function head is a CALL, not a value-use — do not scan it.
                    false
                } else {
                    true
                };
                // Reversed: the function head (when it is scanned at all),
                // then the args in source order.
                for a in args.iter().rev() {
                    steps.push(ScanStep::Visit(a));
                }
                if scan_function {
                    steps.push(ScanStep::Visit(function.as_ref()));
                }
            }
            PseudoExpr::Var { id: Some(vid), .. } => {
                scan.value_used.insert(*vid);
            }
            other => {
                for child in children(other).into_iter().rev() {
                    steps.push(ScanStep::Visit(child));
                }
            }
        }
    }
}

/// A job on [`scan_rec_calls`]'s stack. `PopRec` is the point run between two child
/// walks — unwinding the lexical rec-fn nesting stack — so it must stay a separate
/// step.
enum ScanStep<'a> {
    Visit(&'a PseudoExpr),
    PopRec,
}

/// Find a `when <Var(param0)> is { [head, ..tail] -> … }` anywhere in `body`;
/// return `(head id, tail id)` of the first cons clause matched on `param0`.
fn find_param_cons_match(body: &PseudoExpr, param0: VarId) -> Option<(VarId, VarId)> {
    let mut stack: Vec<&PseudoExpr> = vec![body];
    while let Some(body) = stack.pop() {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = body
            && matches!(subject.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == param0)
        {
            for c in clauses {
                if let WhenPattern::List {
                    elements,
                    tail: Some(tail),
                } = &c.pattern
                    && elements.len() == 1
                {
                    return Some((elements[0].var_id(), tail.var_id()));
                }
            }
        }
        for child in children(body).into_iter().rev() {
            stack.push(child);
        }
    }
    None
}

/// `value` is exactly `<entry script_context>.tx_info`, where the record is the
/// validator entry param (its `VarId` ∈ `entry_sc_ids`).
///
/// VarId-gated, NOT name-gated: a name-only match would accept a helper param
/// named `script_context` that holds arbitrary `Data` and mislabel its
/// `.fields[N]` as TxInfo fields. Empty `entry_sc_ids` ⇒ no match (fail closed).
fn is_script_context_tx_info(value: &PseudoExpr, entry_sc_ids: &HashSet<VarId>) -> bool {
    matches!(
        value,
        PseudoExpr::FieldAccess { record, selector }
            if selector.as_pretty_name() == "tx_info"
                && matches!(
                    record.as_ref(),
                    PseudoExpr::Var { id: Some(v), .. } if entry_sc_ids.contains(v)
                )
    )
}

fn collect_tx_info_binders(
    expr: &PseudoExpr,
    out: &mut HashSet<VarId>,
    entry_sc_ids: &HashSet<VarId>,
) {
    preorder(expr, |expr| {
        if let PseudoExpr::Let {
            id: Some(binder_id),
            value,
            ..
        } = expr
            && is_script_context_tx_info(value, entry_sc_ids)
        {
            out.insert(*binder_id);
        }
    });
}

/// True when `record` is a provably-TxInfo value: a binder bound by `VarId`
/// to `script_context.tx_info`.
///
/// A bare inline `script_context.tx_info` access is deliberately NOT matched:
/// that anchor is name-only, so a binder coincidentally named `script_context`
/// would be a false positive. Only the let-alias form (`let tx_info =
/// script_context.tx_info; … tx_info.fields[N]`) is tracked, by `VarId`.
fn is_tx_info_record(record: &PseudoExpr, ids: &HashSet<VarId>) -> bool {
    matches!(record, PseudoExpr::Var { id: Some(id), .. } if ids.contains(id))
}

fn rewrite(
    expr: PseudoExpr,
    ids: &HashSet<VarId>,
    names: Option<&[&'static str]>,
    sc_names: &[&'static str],
    entry_sc_ids: &HashSet<VarId>,
) -> PseudoExpr {
    rewrite_bottom_up(expr, |expr| {
        if let PseudoExpr::IndexAccess { collection, index } = &expr
            && let PseudoExpr::FieldAccess { record, selector } = collection.as_ref()
            && selector.as_pretty_name() == "fields"
        {
            // TxInfo: <tx_info_alias>.fields[N] -> <alias>.<tx_field>.
            // `names` is None under V1/V2 ambiguity (layouts diverge at
            // index 1) — the arm is skipped and positional access survives.
            if let Some(names) = names
                && is_tx_info_record(record, ids)
                && *index < names.len()
            {
                return PseudoExpr::field_access((**record).clone(), names[*index]);
            }
            // ScriptContext: script_context.fields[N] -> script_context.<sc_field>.
            // VarId-gated on the validator ENTRY param (NOT name), so a helper
            // param coincidentally named `script_context`, which can hold arbitrary
            // data, is never mis-labeled. Pure positional→schema relabel; no
            // runtime check; out-of-range index stays positional.
            if matches!(record.as_ref(), PseudoExpr::Var { id: Some(v), .. } if entry_sc_ids.contains(v))
                && *index < sc_names.len()
            {
                return PseudoExpr::field_access((**record).clone(), sc_names[*index]);
            }
        }
        // ScriptContext slot 0 via the head form: `script_context.fields.head`
        // is FieldAccess+ListHead (NEVER IndexAccess), so the arm above can't
        // see it. Slot 0 is `tx_info` in V1, V2 AND V3 — version-agnostic by
        // layout identity. Same entry-param VarId gate.
        if let PseudoExpr::FieldAccess { record, selector } = &expr
            && matches!(selector, FieldSelector::ListHead)
            && let PseudoExpr::FieldAccess {
                record: sc,
                selector: fields_sel,
            } = record.as_ref()
            && fields_sel.as_pretty_name() == "fields"
            && matches!(sc.as_ref(), PseudoExpr::Var { id: Some(v), .. } if entry_sc_ids.contains(v))
            && !sc_names.is_empty()
        {
            return PseudoExpr::field_access((**sc).clone(), sc_names[0]);
        }
        expr
    })
}

#[cfg(test)]
mod tests;
