//! `assign_names` pass.
//!
//! Walks a [`VarTable`] and computes a canonical display name for
//! each `VarId` from its [`VarKind`], so the simplifier never has
//! to synthesize name strings (`field_N`, `data_literal_N`): it
//! mints binders with whatever temporary names it likes and
//! attaches the kind to the VarId.
//!
//! Runs at the end of the nameless post-pipeline, after mint-site
//! annotations are merged into the VarTable and the verifier
//! checks shape-derived expectations, just before raising to
//! `PseudoExpr`.

use crate::decompile::simplify::is_protected_validator_param_name;
use crate::pseudo::nameless::{VarKind, VarMetadata, VarOrigin, VarTable};
use crate::pseudo::var_id::VarId;
use std::collections::{HashMap, HashSet};

/// Walk `table` and assign canonical `display_name_hint`s based on each
/// entry's [`VarKind`]. Render names are deduplicated within the table
/// by appending `_N` suffixes.
///
/// Returns the number of entries whose name was rewritten.
///
/// This unfiltered form considers EVERY table entry; production goes
/// through [`assign_names_live`]. The table accumulates entries for ids
/// long dead in the AST, and letting those through `fresh_name`'s global
/// `used` set inflates live binder names to `field_0_74`.
pub(crate) fn assign_names(table: &mut VarTable) -> usize {
    assign_names_filtered(table, None)
}

/// Live-filtered [`assign_names`]: only ids in `live` (those actually
/// OCCURRING in the final nameless AST) participate — as allocation
/// candidates, as `used`-set seeds, and in the `max_cardano_id` /
/// entry-param-role maps, so the descending-VarId "live binder wins"
/// heuristics are exact. Dead entries keep their hints; they can't render.
///
/// Fail-closed: an EMPTY `live` set falls back to the unfiltered
/// full-table behavior.
pub(crate) fn assign_names_live(
    table: &mut VarTable,
    live: &std::collections::HashSet<VarId>,
) -> usize {
    if live.is_empty() {
        return assign_names(table);
    }
    assign_names_filtered(table, Some(live))
}

fn assign_names_filtered(
    table: &mut VarTable,
    live: Option<&std::collections::HashSet<VarId>>,
) -> usize {
    // First pass: gather a candidate name per VarId from its
    // kind, without committing any of them yet.
    let ids: Vec<VarId> = table
        .iter()
        .map(|(id, _)| *id)
        .filter(|id| live.is_none_or(|l| l.contains(id)))
        .collect();

    // Highest VarId among `CardanoContext` binders per context_type.
    // The protected-name guard in `candidate_name` keeps the canonical
    // validator-param name only for that binder; a lower-VarId
    // same-context_type binder (e.g. a non-entry helper lambda the
    // early rename mis-named `script_context`) is a stale duplicate
    // and gets reassigned/suffixed, matching the descending-VarId
    // "live binder wins" allocation below.
    let mut max_cardano_id: HashMap<String, VarId> = HashMap::new();
    for id in &ids {
        if let Some(meta) = table.get(*id)
            && let VarKind::CardanoContext { context_type } = &meta.kind
        {
            max_cardano_id
                .entry(context_type.clone())
                .and_modify(|cur| {
                    if *id > *cur {
                        *cur = *id;
                    }
                })
                .or_insert(*id);
        }
    }

    // Role names claimed by the TRUE validator entry's params — those
    // stamped `ValidatorEntryParam { authoritative: true }`. A
    // NON-authoritative marker carrying one of these role names (a
    // helper the early rename also named `redeemer`) becomes a
    // reassignable candidate, allocated after the entry-marker bucket
    // below, so the marked entry claims the bare role name regardless
    // of VarId — VarId ordering is not a sound discriminator here.
    let entry_param_names: HashSet<String> = ids
        .iter()
        .filter_map(|id| match table.get(*id).map(|m| &m.kind) {
            Some(VarKind::ValidatorEntryParam {
                param_name,
                authoritative: true,
            }) => Some(param_name.clone()),
            _ => None,
        })
        .collect();

    let mut candidates: HashMap<VarId, String> = HashMap::new();
    for id in &ids {
        if let Some(meta) = table.get(*id)
            && let Some(name) =
                candidate_name(meta, table, *id, &max_cardano_id, &entry_param_names)
        {
            candidates.insert(*id, name);
        }
    }

    // Deduplicate: track seen names and suffix collisions.
    let mut used: HashSet<String> = HashSet::new();
    // Seed `used` with the render names of entries that will
    // not be rewritten (User / Synthetic with an existing
    // hint), so reassignments cannot collide with them.
    for id in &ids {
        if let Some(meta) = table.get(*id)
            && !candidates.contains_key(id)
            && let Some(name) = meta.render_name_hint()
        {
            used.insert(name.to_string());
        }
    }

    let mut rewritten = 0usize;
    // Three buckets, allocated in this order:
    //   1. AUTHORITATIVE `ValidatorEntryParam` — the TRUE entry's
    //      datum/redeemer. Claiming the bare role name FIRST suffixes any
    //      same-named competitor (a non-authoritative marker, which lands
    //      in `other`), regardless of VarId.
    //   2. `CardanoContext` (descending VarId) — live binder wins. Dead
    //      simplifier aliases can share a `context_type`; the highest-VarId
    //      (AST-live) one claims the canonical slot, the dead ones suffix.
    //   3. everything else (ascending VarId), including non-authoritative
    //      `ValidatorEntryParam` competitors.
    let mut entry_marker_ids: Vec<VarId> = Vec::new();
    let mut cardano_ids: Vec<VarId> = Vec::new();
    let mut other_ids: Vec<VarId> = Vec::new();
    for id in candidates.keys().copied() {
        match table.get(id).map(|m| &m.kind) {
            Some(VarKind::ValidatorEntryParam {
                authoritative: true,
                ..
            }) => entry_marker_ids.push(id),
            Some(VarKind::CardanoContext { .. }) => cardano_ids.push(id),
            _ => other_ids.push(id),
        }
    }
    entry_marker_ids.sort_by(|a, b| b.cmp(a)); // descending (≤1 per role in practice)
    cardano_ids.sort_by(|a, b| b.cmp(a)); // descending — live binder wins
    other_ids.sort(); // ascending — preserves prior dedup behavior
    let allocation_order: Vec<VarId> = entry_marker_ids
        .into_iter()
        .chain(cardano_ids)
        .chain(other_ids)
        .collect();

    #[cfg(debug_assertions)]
    let mut allocated_names: HashSet<String> = HashSet::new();
    for id in allocation_order {
        let base = candidates.get(&id).expect("candidate for id").clone();
        let unique = fresh_name(&base, &mut used);
        // Pairwise distinctness of allocated live names is structural
        // (fresh_name + the used-set seeding) — assert it stays that way.
        #[cfg(debug_assertions)]
        debug_assert!(
            allocated_names.insert(unique.clone()),
            "assign_names allocated a duplicate live name: {unique}"
        );
        if let Some(meta) = table.get(id) {
            let old = meta.render_name_hint().map(str::to_string);
            let new_meta = VarMetadata {
                origin: meta.origin.clone(),
                name_hint: meta.name_hint.clone(),
                display_name_hint: Some(unique),
                kind: meta.kind.clone(),
            };
            table.insert(id, new_meta);
            if old.as_deref() != table.get(id).and_then(|m| m.render_name_hint()) {
                rewritten += 1;
            }
        }
    }
    rewritten
}

/// Compute the raw (pre-dedup) canonical name for a VarId from
/// its kind. `None` leaves the existing name as-is (User /
/// Synthetic, or an entry that cannot be resolved).
fn candidate_name(
    meta: &VarMetadata,
    table: &VarTable,
    id: VarId,
    max_cardano_id: &HashMap<String, VarId>,
    entry_param_names: &HashSet<String>,
) -> Option<String> {
    match &meta.kind {
        VarKind::ValidatorEntryParam {
            param_name,
            authoritative,
        } => {
            if *authoritative {
                // The TRUE entry's role param — claim the bare role name.
                // The entry-marker allocation bucket runs first, so this
                // wins over any same-named competitor regardless of VarId.
                Some(param_name.clone())
            } else if entry_param_names.contains(param_name) {
                // Non-authoritative role param — a helper the early rename
                // gave the role the TRUE entry owns. Becoming a candidate
                // suffixes it: it allocates after the entry-marker bucket.
                Some(param_name.clone())
            } else {
                // No authoritative entry claims this role (the late rename
                // found no entry) — keep this param's name as a fallback.
                None
            }
        }
        VarKind::User
        | VarKind::Synthetic
        | VarKind::SliceTailAlias { .. }
        | VarKind::ValidatorEntry => None,
        VarKind::FieldIndexAlias { index, .. } => Some(format!("field_{}", index)),
        VarKind::DataLiteralHoist => Some("data_literal".to_string()),
        VarKind::CardanoContext { context_type } => {
            // Preserve existing validator-entry param names
            // (datum, redeemer, script_context).
            // `cardano_context_naming` tags a body-used binder
            // `CardanoContext` because the body projects
            // `.tx_info` on it; when that binder IS the entry's
            // `redeemer` (or `datum`) slot, renaming it to
            // `script_context` here would lose the semantic slot.
            // `is_protected_validator_param_name` is the same
            // protected set the validator renamer uses.
            let existing = meta.render_name_hint();
            // Only Lambda-param origins represent validator-entry
            // slots, so the guard must not shadow a user-level
            // `let datum = ...`: `VarOrigin::LetBinder` is a let
            // binding, while UserBinder (original UPLC lambda
            // binder), LambdaParam (simplifier-introduced lambda)
            // and Synthetic are binders worth protecting.
            let is_lambda_param_origin = !matches!(meta.origin, VarOrigin::LetBinder);
            if is_lambda_param_origin
                && let Some(hint) = existing
                && is_protected_validator_param_name(hint)
            {
                // Keep this protected validator-param name UNLESS a
                // strictly-higher-VarId `CardanoContext` binder has
                // `context_type == hint` — that binder is the live owner
                // and claims the name through the descending-VarId
                // allocation, so a lower-VarId helper the early rename
                // mis-named `script_context` yields here. `max_cardano_id`
                // keys on raw context_type, so the rival counts even if
                // its own candidate was suppressed. A binder whose hint
                // matches no context_type — e.g. a `redeemer` slot tagged
                // CardanoContext for projecting context fields — has no
                // such rival and is preserved.
                let yields_to_higher = max_cardano_id.get(hint).is_some_and(|&m| m > id);
                if !yields_to_higher {
                    return None;
                }
            }
            Some(context_type.clone())
        }
        VarKind::CallResult { callee } => {
            // Resolve the callee's current render name from the table. If
            // the callee also has a candidate this pass, knowing its final
            // display name would need a fixed point, so read the current
            // hint and fall back to a raw-id placeholder.
            //
            // The callee may be dead (inlined out while the result binder
            // keeps the kind). Reading the dead entry's hint is deliberate:
            // the result keeps a meaningful base name (`lookup_result` after
            // `lookup` was inlined) and the live result binder still dedups
            // through `fresh_name`.
            let callee_name = table
                .get(*callee)
                .and_then(|m| m.render_name_hint().map(str::to_string))
                .unwrap_or_else(|| format!("v_{}", callee.as_u32()));
            Some(format!("{}_result", sanitize(&callee_name)))
        }
        VarKind::UserAdtField { field_name, .. } => {
            // Blueprint-sourced user-ADT field name. Blueprint authors
            // may use camelCase or other forms that aren't valid surface syntax
            // identifiers, so sanitize; `fresh_name` then resolves any
            // collision with names already in scope.
            let sanitized = sanitize(field_name);
            // Skip rename if the binder already has a meaningful hint
            // matching the blueprint name (avoid redundant rewrites).
            let has_meaningful_hint = meta
                .display_name_hint
                .as_deref()
                .is_some_and(|n| !n.is_empty())
                || meta.name_hint.as_deref().is_some_and(|n| !n.is_empty());
            if has_meaningful_hint && meta.render_name_hint() == Some(sanitized.as_str()) {
                None
            } else {
                Some(sanitized)
            }
        }
        VarKind::ConstrPayload { index, .. } => {
            // Only canonicalise to `item_{index}` when the binder has no
            // existing hint. Overwriting a rename already in place (Cardano
            // context naming, validator params) risks render-time orphans:
            // body refs would no longer match the new name.
            // Already-named means EITHER hint is a non-empty string; `.or()`
            // chaining short-circuits on `display_name_hint = Some("")` and
            // ignores a meaningful `name_hint`.
            let has_meaningful_hint = meta
                .display_name_hint
                .as_deref()
                .is_some_and(|n| !n.is_empty())
                || meta.name_hint.as_deref().is_some_and(|n| !n.is_empty());
            if has_meaningful_hint {
                None
            } else {
                Some(format!("item_{}", index))
            }
        }
    }
}

/// Return a name not yet in `used`, appending `_N` suffixes
/// as necessary. On success inserts the returned name into `used`.
///
/// Suffixes start at `_2` (the second `field_1` becomes `field_1_2`),
/// matching the render_prep disambiguator's `make_unique_name`.
fn fresh_name(base: &str, used: &mut HashSet<String>) -> String {
    if !used.contains(base) {
        used.insert(base.to_string());
        return base.to_string();
    }
    let mut n = 2;
    loop {
        let candidate = format!("{}_{}", base, n);
        if !used.contains(&candidate) {
            used.insert(candidate.clone());
            return candidate;
        }
        n += 1;
    }
}

fn sanitize(name: &str) -> String {
    let mut out = String::new();
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
        } else if ch == '_' && !out.ends_with('_') {
            out.push('_');
        }
    }
    let trimmed = out.trim_matches('_').to_string();
    if trimmed.is_empty() {
        "x".to_string()
    } else if trimmed
        .chars()
        .next()
        .map(|c| c.is_ascii_digit())
        .unwrap_or(false)
    {
        format!("c{}", trimmed)
    } else {
        trimmed
    }
}

#[cfg(test)]
mod tests;
