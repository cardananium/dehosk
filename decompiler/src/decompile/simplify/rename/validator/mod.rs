use crate::decompile::ScriptVersion;
use crate::decompile::validator_meta::ValidatorPurpose;
use crate::decompile::validator_shape::runtime_arity_for;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::nameless::VarKind;
use crate::pseudo::var_id::VarId;
use std::collections::{HashMap, HashSet};

use super::Simplifier;

/// Returns true if `params` shows "script-context shape evidence" in
/// `body` — i.e. one of the params is observably the `script_context`
/// validator slot. Three independent signals are accepted:
///
/// 1. **Tagged** — a param's VarId is in `kind_annotations` with
///    `VarKind::CardanoContext`, established by an earlier pass or the
///    blueprint integration.
/// 2. **Named** — a param's display name is the literal string
///    `script_context`.
/// 3. **Projected** — `body` projects out of a `Var` whose `id` is one
///    of the params:
///    - `FieldAccess { selector: ContextField(_) | Named("tx_info" |
///      "purpose" | "transaction" | "datum") }`: post-rename evidence.
///    - `IndexAccess { collection: Var{id ∈ params} }`: pre-rename
///      structural evidence (`script_context.fields[i]` after Constr
///      decode, or `script_context[i]` before).
///
/// No signal fires when the candidate is structurally
/// indistinguishable from a generic helper. Only tests call this; the
/// note in `rename_lambda_in_last_matching_prefix` says why the entry
/// picker does not use it.
#[allow(dead_code)]
pub(crate) fn has_script_context_evidence(
    params: &[Binder],
    body: &PseudoExpr,
    kind_annotations: Option<&HashMap<VarId, VarKind>>,
) -> bool {
    // Signal 1: tagged param.
    if let Some(kinds) = kind_annotations
        && params
            .iter()
            .any(|p| matches!(kinds.get(&p.var_id()), Some(VarKind::CardanoContext { .. })))
    {
        return true;
    }
    // Signal 2: named param.
    if params.iter().any(|p| p.as_str() == "script_context") {
        return true;
    }
    // Signal 3: projected — manual recursive walk (the trait
    // `ExprVisitor` has no hooks for FieldAccess / IndexAccess).
    let param_ids: HashSet<VarId> = params.iter().map(|p| p.var_id()).collect();
    body_has_sc_projection(body, &param_ids)
}

#[allow(dead_code)]
fn body_has_sc_projection(expr: &PseudoExpr, param_ids: &HashSet<VarId>) -> bool {
    let var_in_params = |e: &PseudoExpr| matches!(e, PseudoExpr::Var { id: Some(vid), .. } if param_ids.contains(vid));
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        match current {
            PseudoExpr::FieldAccess { record, selector } => {
                if var_in_params(record) {
                    let hit = match selector {
                        FieldSelector::ContextField(_) => true,
                        FieldSelector::NamedField(name) => matches!(
                            name.as_str(),
                            "tx_info" | "purpose" | "transaction" | "datum"
                        ),
                        _ => false,
                    };
                    if hit {
                        return true;
                    }
                }
                pending.push(record);
            }
            PseudoExpr::IndexAccess { collection, .. } => {
                if var_in_params(collection) {
                    return true;
                }
                pending.push(collection);
            }
            PseudoExpr::Lambda { body, .. } | PseudoExpr::RecFn { body, .. } => {
                pending.push(body);
            }
            PseudoExpr::Let { value, body, .. } => {
                pending.push(value);
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
                subject, clauses, ..
            } => {
                pending.push(subject);
                for c in clauses {
                    if let Some(g) = c.guard.as_ref() {
                        pending.push(g);
                    }
                    pending.push(&c.body);
                    if let WhenPattern::Literal(lit) = &c.pattern {
                        pending.push(lit);
                    }
                }
            }
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
            PseudoExpr::List { elements, tail } => {
                pending.extend(elements.iter());
                if let Some(t) = tail.as_ref() {
                    pending.push(t);
                }
            }
            PseudoExpr::Tuple(items) => pending.extend(items.iter()),
            PseudoExpr::Pair(first, second) => {
                pending.push(first);
                pending.push(second);
            }
            PseudoExpr::Constr { fields, .. } => pending.extend(fields.iter()),
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

enum Prefix {
    Let {
        name: String,
        id: Option<VarId>,
        value: PBox,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
}

/// Rename validator parameters (datum, redeemer, script_context) by script version.
///
/// The standard roles occupy the *trailing* params of the entry lambda:
/// V1/V2 spend (last 3): datum, redeemer, script_context
/// V1/V2 mint/withdraw (last 2): redeemer, script_context
/// V3 (last 1): script_context
///
/// Leading params are user-level parameters not yet resolved by
/// `applyParamsToScript`, or ones a curried-lambda-flatten pass collapsed into
/// the entry lambda (leaving no Let prologue to strip); they keep whatever name
/// the simplifier chose. A `None` `script_version` returns `expr` unchanged.
///
/// Test-only convenience that omits VarKind annotations; production calls
/// `rename_validator_params_with_var_kinds` directly.
#[cfg(test)]
pub(crate) fn rename_validator_params(
    expr: PseudoExpr,
    script_version: Option<ScriptVersion>,
) -> PseudoExpr {
    match script_version {
        Some(version) => find_and_rename_validator(expr, version, None, None, None, false),
        None => expr,
    }
}

#[cfg(test)]
pub(crate) fn rename_validator_params_with_blueprint(
    expr: PseudoExpr,
    script_version: Option<ScriptVersion>,
    blueprint_param_names: Option<&[String]>,
) -> PseudoExpr {
    match script_version {
        Some(version) => {
            find_and_rename_validator(expr, version, None, blueprint_param_names, None, false)
        }
        None => expr,
    }
}

/// Early (pre-uncurry) validator-param rename. Stamps datum/redeemer role
/// params with NON-authoritative `ValidatorEntryParam` markers
/// (`authoritative: false`): on the not-yet-flattened tree the selected
/// callable can be a non-entry helper, so these only YIELD their role name
/// in `assign_names` (they never claim it over the true entry).
pub(crate) fn rename_validator_params_with_var_kinds(
    expr: PseudoExpr,
    script_version: Option<ScriptVersion>,
    kind_annotations: &mut HashMap<VarId, VarKind>,
    blueprint_param_names: Option<&[String]>,
    purpose: Option<ValidatorPurpose>,
) -> PseudoExpr {
    rename_validator_params_impl(
        expr,
        script_version,
        kind_annotations,
        blueprint_param_names,
        purpose,
        false,
    )
}

/// Authoritative late (post-uncurry) validator-param rename. The
/// reverse-walk selector picks the TRUE entry here, so its datum/redeemer
/// params are stamped `VarKind::ValidatorEntryParam` — letting
/// `assign_names` give them the bare role name over any unmarked
/// same-named binder (e.g. a helper the early rename also named).
pub(crate) fn rename_validator_params_with_var_kinds_authoritative(
    expr: PseudoExpr,
    script_version: Option<ScriptVersion>,
    kind_annotations: &mut HashMap<VarId, VarKind>,
    blueprint_param_names: Option<&[String]>,
    purpose: Option<ValidatorPurpose>,
) -> PseudoExpr {
    rename_validator_params_impl(
        expr,
        script_version,
        kind_annotations,
        blueprint_param_names,
        purpose,
        true,
    )
}

fn rename_validator_params_impl(
    expr: PseudoExpr,
    script_version: Option<ScriptVersion>,
    kind_annotations: &mut HashMap<VarId, VarKind>,
    blueprint_param_names: Option<&[String]>,
    purpose: Option<ValidatorPurpose>,
    authoritative: bool,
) -> PseudoExpr {
    match script_version {
        Some(version) => find_and_rename_validator(
            expr,
            version,
            Some(kind_annotations),
            blueprint_param_names,
            purpose,
            authoritative,
        ),
        None => expr,
    }
}

/// Returns `(plan, trailing_count)` for `arity` entry-lambda parameters. In
/// `plan`, `None` means "leave this param untouched" and `Some(name)` means
/// "rename to `name`". The standard validator roles always occupy the
/// *trailing* positions so leading user-level params survive;
/// `trailing_count` is how many trailing slots are roles, so a caller
/// stamping role markers never mistakes a leading blueprint param that
/// happens to be named `datum`/`redeemer` for a role.
///
/// V3 accepts any arity `>= 1` — the deepest param is always
/// `script_context` however many user-level params the author declared,
/// because the V3 UPLC emit wraps the body exactly once in
/// `Lambda __context__. body` before cast-adding user-param lambdas.
///
/// For V1/V2 the two standard arities (2 = mint/withdraw, 3 = spend) are
/// ambiguous once extra user params are present: an arity-4 script could
/// equally be spend+1-user or mint+2-user. Without blueprint hints the
/// match stays strict — arity 2 or 3 only — so a user param is never
/// mis-labelled `datum` or `redeemer`. With blueprint param names,
/// `param_names.len() + trailing.len() == arity` picks the purpose uniquely
/// and the trailing slots rename safely; the leading slots then take the
/// blueprint names, with `Some("_")` mapped to `None` so anonymous slots
/// stay untouched.
fn expected_validator_params(
    version: ScriptVersion,
    arity: usize,
    blueprint_param_names: Option<&[String]>,
    purpose: Option<ValidatorPurpose>,
) -> Option<(Vec<Option<String>>, usize)> {
    let trailing: &[&str] = match version {
        ScriptVersion::PlutusV3 if arity >= 1 => &["script_context"],
        ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 if arity >= 2 => {
            // Priority 1 — blueprint hints fully determine the layout
            // (user-param slot count + trailing standard names).
            //
            // A hint and an explicit `--purpose` can disagree — hint
            // length 1 with arity 4 implies spend where `--purpose mint`
            // asks for mint — and the hint wins silently: there is no
            // diagnostic channel at this point in the rename.
            if let Some(hint_len) = blueprint_param_names.map(<[String]>::len) {
                if hint_len + 3 == arity {
                    &["datum", "redeemer", "script_context"][..]
                } else if hint_len + 2 == arity {
                    &["redeemer", "script_context"][..]
                } else {
                    return None;
                }
            } else if let Some(p) = purpose {
                // Priority 2 — explicit purpose: the runtime
                // trailing layout is unambiguous once the role is
                // declared. Leading params beyond `runtime` are user
                // compile-time params, left untouched. This
                // OVERRIDES the exact-2/exact-3 heuristic below, so
                // `--purpose mint` at arity 3 gives `(user_a,
                // redeemer, script_context)`, not `(datum, redeemer,
                // script_context)`.
                let runtime = runtime_arity_for(Some(version), Some(p));
                if arity >= runtime {
                    match (p, runtime) {
                        (ValidatorPurpose::Spend, 3) => {
                            &["datum", "redeemer", "script_context"][..]
                        }
                        (_, 2) => &["redeemer", "script_context"][..],
                        _ => return None,
                    }
                } else {
                    return None;
                }
            } else {
                // Priority 3 — no blueprint and no declared purpose:
                // rename only at the two standard V1/V2 arities
                // (mint/withdraw = 2, spend = 3). Anything else stays
                // untouched, to avoid mislabelling user params.
                match arity {
                    2 => &["redeemer", "script_context"][..],
                    3 => &["datum", "redeemer", "script_context"][..],
                    _ => return None,
                }
            }
        }
        _ => return None,
    };

    let leading = arity - trailing.len();
    let mut plan: Vec<Option<String>> = Vec::with_capacity(arity);
    match blueprint_param_names {
        Some(names) if names.len() == leading => {
            // Blueprint hints fully determine the user-param slots; a `"_"`
            // hint stays anonymous.
            plan.extend(
                names
                    .iter()
                    .map(|n| if n == "_" { None } else { Some(n.clone()) }),
            );
        }
        _ => {
            plan.extend(std::iter::repeat_n(None, leading));
        }
    }
    plan.extend(trailing.iter().map(|name| Some(name.to_string())));
    Some((plan, trailing.len()))
}

/// Returns true if `name` is a semantic validator-entrypoint parameter name
/// assigned by [`rename_validator_params`]. Downstream simplifier passes keep
/// such a param even when unused rather than demoting it to `_`, so the
/// rendered entrypoint signature stays readable.
pub(crate) fn is_protected_validator_param_name(name: &str) -> bool {
    matches!(name, "script_context" | "datum" | "redeemer")
}

fn rename_callable_params(
    params: Vec<Binder>,
    body: PseudoExpr,
    version: ScriptVersion,
    kind_annotations: Option<&mut HashMap<VarId, VarKind>>,
    blueprint_param_names: Option<&[String]>,
    purpose: Option<ValidatorPurpose>,
    authoritative: bool,
) -> Option<(Vec<Binder>, PseudoExpr)> {
    let (plan, trailing_len) =
        expected_validator_params(version, params.len(), blueprint_param_names, purpose)?;
    // First index of the trailing standard-role region. A datum/redeemer at
    // a LEADING (user/blueprint) position is never a role marker.
    let trailing_start = params.len().saturating_sub(trailing_len);

    let already_matches = params
        .iter()
        .zip(plan.iter())
        .all(|(old, target)| match target {
            Some(new_name) => old.as_str() == new_name,
            None => true,
        });

    let mut renamed_body = body;
    for (old, target) in params.iter().zip(plan.iter()) {
        if let Some(new_name) = target
            && old.as_str() != new_name
        {
            renamed_body = Simplifier::rename_var_binding(
                &renamed_body,
                old.as_str(),
                Some(old.var_id()),
                new_name,
            );
        }
    }

    // Demote any leading (plan = `None`) param that still carries a
    // protected validator name. The early pre-uncurry rename
    // (`pipeline::RenameValidatorParams`) names a trailing param
    // `script_context`/`datum`/`redeemer`, but on the not-yet-uncurried
    // tree that binder can be one that ends up leading, leaving a stale
    // protected name on a user param. Leading params are never
    // legitimately one of these reserved names, so reset to the `v_<id>`
    // MIR form (id-targeted, so a same-named trailing param is untouched)
    // and drop the `CardanoContext` kind below. This frees the canonical
    // slot for the genuine trailing context param and stops `assign_names`
    // from picking the wrong binder — which would render
    // `validator(script_context, script_context_1)` with the leading param
    // holding the canonical name.
    let mut demoted: Vec<(VarId, String)> = Vec::new();
    for (old, target) in params.iter().zip(plan.iter()) {
        if target.is_none() && is_protected_validator_param_name(old.as_str()) {
            let generic = format!("v_{}", old.var_id().as_u32());
            renamed_body = Simplifier::rename_var_binding(
                &renamed_body,
                old.as_str(),
                Some(old.var_id()),
                &generic,
            );
            demoted.push((old.var_id(), generic));
        }
    }

    let mut script_context_ids = Vec::new();
    // (id, role_name) for the non-CardanoContext role params (datum /
    // redeemer) at TRAILING positions of THIS callable. Stamped as
    // `ValidatorEntryParam` below; a LEADING blueprint param coincidentally
    // named datum/redeemer is excluded by the `trailing_start` check.
    let mut entry_role_ids: Vec<(VarId, String)> = Vec::new();
    let mut renamed_params = Vec::with_capacity(params.len());
    for (index, (old, target)) in params.into_iter().zip(plan).enumerate() {
        match target {
            Some(new_name) => {
                let renamed = if old.as_str() == new_name {
                    old
                } else {
                    old.renamed(new_name.clone())
                };
                if index >= trailing_start {
                    if new_name == "script_context" {
                        script_context_ids.push(renamed.var_id());
                    } else if new_name == "datum" || new_name == "redeemer" {
                        entry_role_ids.push((renamed.var_id(), new_name.clone()));
                    }
                }
                renamed_params.push(renamed);
            }
            None => {
                if let Some((_, generic)) = demoted.iter().find(|(id, _)| *id == old.var_id()) {
                    renamed_params.push(old.renamed(generic.clone()));
                } else {
                    renamed_params.push(old);
                }
            }
        }
    }

    if let Some(kind_annotations) = kind_annotations {
        for id in script_context_ids {
            kind_annotations
                .entry(id)
                .or_insert_with(|| VarKind::CardanoContext {
                    context_type: "script_context".to_string(),
                });
        }
        // Mark this callable's trailing datum/redeemer role params with
        // `ValidatorEntryParam`. `authoritative` separates the late
        // rename (the TRUE entry, claiming the bare role name) from the
        // early pre-uncurry one (possibly a helper, so it yields its role
        // name in `assign_names`). `script_context` is excluded: it keeps
        // `CardanoContext`, resolved by the live-binder path.
        for (id, role_name) in &entry_role_ids {
            kind_annotations.insert(
                *id,
                VarKind::ValidatorEntryParam {
                    param_name: role_name.clone(),
                    authoritative,
                },
            );
        }
        // Strip the stale `CardanoContext` kind the early rename stamped on
        // a now-demoted leading param so it no longer competes for the
        // `script_context` name in `assign_names`.
        for (id, _) in &demoted {
            if matches!(
                kind_annotations.get(id),
                Some(VarKind::CardanoContext { .. })
            ) {
                kind_annotations.remove(id);
            }
        }
    }

    if already_matches {
        return Some((renamed_params, renamed_body));
    }

    Some((renamed_params, renamed_body))
}

/// Greedy curried-Lambda peeler.
///
/// Flattens `Lambda(p1){ let_chain; Lambda(p2){ let_chain;
/// Lambda(p3){ body } } }` into one `(params=[p1,p2,p3], body)` pair,
/// keeping the intermediate `let` chains inside the fused body: the
/// lets bound variables outside the inner Lambda's scope, so they can
/// equally be bound outside the fused body.
///
/// **Hygiene guard.** If a later-peeled lambda's param name matches
/// an earlier-peeled let's binder name, fusing would reverse the
/// shadowing (`let x = … in λx.body`: the inner λx shadows the let;
/// after fusion `λ(…,x){ let x = … in body }` the let shadows the
/// param). Such collisions are rejected outright.
///
/// **Truncation guard.** If the body after `target_arity` params
/// still starts with a `Lambda` (possibly past let chains), fusing
/// would classify an N-param curried entry as (N-1)-arity by
/// truncating the last param into the body. Rejected — picking a
/// different target arity is the caller's job.
///
/// Returns `None` if `body` doesn't reach `target_arity`, if hygiene
/// fails, or if a Lambda remains in the fused body.
fn try_uncurry_to_arity(
    initial_params: Vec<Binder>,
    initial_body: PseudoExpr,
    target_arity: usize,
) -> Option<(Vec<Binder>, PseudoExpr)> {
    use std::collections::HashSet;
    if initial_params.len() >= target_arity {
        // Already at or beyond — only accept if no further Lambda
        // hides past the lets (otherwise direct caller can decide).
        return if has_lambda_past_lets(&initial_body) {
            None
        } else {
            Some((initial_params, initial_body))
        };
    }
    // Peeled-let binder names visible at the fused body's top; a
    // later-peeled param colliding with one of them is rejected.
    let mut visible_let_names: HashSet<String> = HashSet::new();
    let mut all_params = initial_params;
    let mut current_body = initial_body;
    while all_params.len() < target_arity {
        let mut peeled_lets: Vec<(String, Option<VarId>, PBox)> = Vec::new();
        let mut walker = current_body;
        loop {
            match walker {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    peeled_lets.push((name, id, value));
                    walker = body.into_inner();
                }
                PseudoExpr::Lambda { params, body } => {
                    // Hygiene gate: any peeled-let binder name (from
                    // this peel pass or earlier ones) that collides
                    // with a not-yet-fused param name would reverse
                    // shadowing post-fusion.
                    for p in &params {
                        let pn = p.as_str();
                        if visible_let_names.contains(pn) {
                            return None;
                        }
                        for (let_name, _, _) in &peeled_lets {
                            if let_name == pn {
                                return None;
                            }
                        }
                    }
                    // Also: any peeled-let binder name colliding with
                    // an earlier `all_params` param would re-shadow.
                    for (let_name, _, _) in &peeled_lets {
                        if all_params.iter().any(|p| p.as_str() == let_name.as_str()) {
                            return None;
                        }
                        visible_let_names.insert(let_name.clone());
                    }
                    all_params.extend(params);
                    let mut rebuilt = body.into_inner();
                    for (name, id, value) in peeled_lets.into_iter().rev() {
                        rebuilt = PseudoExpr::Let {
                            name,
                            id,
                            value,
                            body: PBox::new(rebuilt),
                        };
                    }
                    current_body = rebuilt;
                    break;
                }
                _ => return None,
            }
        }
    }
    // Truncation gate: the fused body must not start with another
    // Lambda hiding past a trailing let chain — that would claim
    // arity N for a curried form of N+1 or more.
    if has_lambda_past_lets(&current_body) {
        return None;
    }
    Some((all_params, current_body))
}

/// Returns true if `expr` starts with a `Lambda` after stripping any
/// leading `Let` chain. Used by [`try_uncurry_to_arity`] to detect
/// "still has more lambdas to peel" after a candidate-arity match.
fn has_lambda_past_lets(expr: &PseudoExpr) -> bool {
    let mut walker = expr;
    loop {
        match walker {
            PseudoExpr::Let { body, .. } => walker = body,
            PseudoExpr::Lambda { .. } => return true,
            _ => return false,
        }
    }
}

/// Returns true iff `expr` is a `Let` chain of length ≥ 1 that terminates in
/// a `Lambda` (i.e. `let … ; λ…`) — the truncated-entry-spine signature: a
/// retained strict-failpoint let sits BETWEEN two curried entry lambdas,
/// stopping the upstream lambda-merge short. Unlike
/// [`has_lambda_past_lets`], a body that is DIRECTLY a `Lambda` (zero
/// interposed lets) returns false, preserving the V3 arity-preempt rule
/// for genuine single-arg entries whose body is a lambda value.
fn has_let_then_lambda(expr: &PseudoExpr) -> bool {
    let mut walker = expr;
    let mut saw_let = false;
    loop {
        match walker {
            PseudoExpr::Let { body, .. } => {
                saw_let = true;
                walker = body;
            }
            PseudoExpr::Lambda { .. } => return saw_let,
            _ => return false,
        }
    }
}

/// Returns the validator-callable arities the version can accept,
/// in descending order (longer match wins, matching
/// `expected_validator_params`).
///
/// With an explicit `purpose`, the V1/V2 set extends above the
/// strict standard arities to cover curried chains carrying user
/// compile-time params (`λa.λr.λsc.body` under `--purpose mint`
/// with 1 user param needs uncurry to arity 3, not 2), capped at
/// `runtime + MAX_PURPOSE_USER_PARAMS` to bound the search.
fn candidate_validator_arities(
    version: ScriptVersion,
    purpose: Option<ValidatorPurpose>,
) -> Vec<usize> {
    const MAX_PURPOSE_USER_PARAMS: usize = 5;
    match version {
        ScriptVersion::PlutusV1 | ScriptVersion::PlutusV2 => {
            if let Some(p) = purpose {
                let runtime = runtime_arity_for(Some(version), Some(p));
                // Descending: runtime + MAX, ..., runtime.
                (runtime..=runtime + MAX_PURPOSE_USER_PARAMS)
                    .rev()
                    .collect()
            } else {
                vec![3, 2]
            }
        }
        ScriptVersion::PlutusV3 => vec![3, 2, 1],
    }
}

/// Try direct arity first; if it doesn't match an expected validator
/// shape, try uncurrying the curried chain to the nearest valid arity.
/// Returns the rename plan applied to either the direct or uncurried
/// `(params, body)` pair, or `None` if neither shape matches.
fn select_validator_callable(
    params: Vec<Binder>,
    body: PseudoExpr,
    version: ScriptVersion,
    kind_annotations: Option<&mut HashMap<VarId, VarKind>>,
    blueprint_param_names: Option<&[String]>,
    purpose: Option<ValidatorPurpose>,
    authoritative: bool,
) -> Option<(Vec<Binder>, PseudoExpr)> {
    let direct_ok =
        expected_validator_params(version, params.len(), blueprint_param_names, purpose).is_some();
    // Accept the DIRECT arity unless the curried chain is INTERRUPTED BY A LET
    // before continuing into another Lambda (`λa.λb. let _ = <…>; λc. body`).
    // That let-then-lambda shape means a retained strict-failpoint let in the
    // entry spine truncated the upstream lambda-merge, so the entry would
    // otherwise be classified at the SHORTER direct arity with the real
    // trailing param stranded in an unapplied `fn(x_N)` body. Prefer the
    // longest uncurry there, falling back to the direct match if no longer
    // shape validates. A body that is DIRECTLY another Lambda (no interposed
    // let) is left to the direct match — the deliberate V3 arity-preempt rule:
    // a single-arg entry whose body returns a lambda value must NOT be
    // uncurried without deeper script-context evidence.
    if direct_ok && !has_let_then_lambda(&body) {
        return rename_callable_params(
            params,
            body,
            version,
            kind_annotations,
            blueprint_param_names,
            purpose,
            authoritative,
        );
    }
    // Try uncurry to each candidate arity, largest first: the longest
    // trailing form `expected_validator_params` accepts wins.
    for target in candidate_validator_arities(version, purpose) {
        if target <= params.len() {
            continue;
        }
        let trial_params = params.clone();
        let trial_body = body.clone();
        if let Some((uparams, ubody)) = try_uncurry_to_arity(trial_params, trial_body, target)
            && uparams.len() == target
            && expected_validator_params(version, uparams.len(), blueprint_param_names, purpose)
                .is_some()
        {
            return rename_callable_params(
                uparams,
                ubody,
                version,
                kind_annotations,
                blueprint_param_names,
                purpose,
                authoritative,
            );
        }
    }
    // Fallback: the chain continued but no longer uncurry shape validated
    // (hygiene or truncation rejected it) — accept the direct match.
    if direct_ok {
        return rename_callable_params(
            params,
            body,
            version,
            kind_annotations,
            blueprint_param_names,
            purpose,
            authoritative,
        );
    }
    None
}

fn find_and_rename_validator(
    expr: PseudoExpr,
    version: ScriptVersion,
    mut kind_annotations: Option<&mut HashMap<VarId, VarKind>>,
    blueprint_param_names: Option<&[String]>,
    purpose: Option<ValidatorPurpose>,
    authoritative: bool,
) -> PseudoExpr {
    let mut prefixes = Vec::new();
    let mut current = expr;

    loop {
        match current {
            PseudoExpr::Let {
                name,
                id,
                value,
                body,
            } => {
                prefixes.push(Prefix::Let { name, id, value });
                current = body.into_inner();
            }
            PseudoExpr::RecFn { name, params, body } => {
                prefixes.push(Prefix::RecFn { name, params });
                current = body.into_inner();
            }
            _ => break,
        }
    }

    let renamed = match current {
        PseudoExpr::Lambda { params, body } => {
            let fallback = PseudoExpr::Lambda {
                params: params.clone(),
                body: body.clone(),
            };
            let Some((params, body)) = select_validator_callable(
                params,
                body.into_inner(),
                version,
                kind_annotations.as_deref_mut(),
                blueprint_param_names,
                purpose,
                authoritative,
            ) else {
                return rewrap_prefixes(fallback, prefixes);
            };
            PseudoExpr::Lambda {
                params,
                body: PBox::new(body),
            }
        }
        PseudoExpr::RecFn { name, params, body } => {
            let fallback = PseudoExpr::RecFn {
                name: name.clone(),
                params: params.clone(),
                body: body.clone(),
            };
            let Some((params, body)) = select_validator_callable(
                params,
                body.into_inner(),
                version,
                kind_annotations.as_deref_mut(),
                blueprint_param_names,
                purpose,
                authoritative,
            ) else {
                return rewrap_prefixes(fallback, prefixes);
            };
            PseudoExpr::RecFn {
                name,
                params,
                body: PBox::new(body),
            }
        }
        // Compilers sometimes emit a validator into `let v = λ sc. body in v(args)`
        // instead of a bare top-level lambda. When the tail after stripping
        // Let/RecFn prefixes is just a `Var` naming one of those Lets, the entry
        // lambda lives in that Let's value — rename there.
        PseudoExpr::Var { ref name, id } => {
            let var = PseudoExpr::Var {
                name: name.clone(),
                id,
            };
            rename_lambda_inside_matching_let_prefix(
                &mut prefixes,
                name,
                id,
                version,
                kind_annotations,
                blueprint_param_names,
                purpose,
                authoritative,
            );
            return rewrap_prefixes(var, prefixes);
        }
        // The hoisted-helpers shape ends with `let helper_1 = …;
        // …; let decompiled = λ params. Body; Unit` — the validator
        // entry lives in the VALUE of the last Let, not at the tail.
        // Walk the collected prefixes backwards and rename the FIRST
        // Let whose value is a Lambda/RecFn of a renamable arity.
        other => {
            rename_lambda_in_last_matching_prefix(
                &mut prefixes,
                version,
                kind_annotations,
                blueprint_param_names,
                purpose,
                authoritative,
            );
            return rewrap_prefixes(other, prefixes);
        }
    };

    rewrap_prefixes(renamed, prefixes)
}

/// For a terminal non-Lambda/Var tail (typically Unit from the
/// hoisted-helpers shape), scan the prefix stack for the last
/// `Let { value: Lambda }` (or `RecFn`) whose params can be
/// renamed. Renames in place.
///
/// **Dispatch invariant**: this and
/// [`rename_lambda_inside_matching_let_prefix`] serve
/// non-overlapping arms of `find_and_rename_validator` (`_ =>` vs
/// `Var =>`). Callers MUST dispatch exclusively — invoking both on
/// one walk double-mutates the prefix stack.
fn rename_lambda_in_last_matching_prefix(
    prefixes: &mut [Prefix],
    version: ScriptVersion,
    mut kind_annotations: Option<&mut HashMap<VarId, VarKind>>,
    blueprint_param_names: Option<&[String]>,
    purpose: Option<ValidatorPurpose>,
    authoritative: bool,
) {
    // SC-evidence scoring is deliberately not wired in here. Helpers
    // commonly project ScriptContext fields while the entry only
    // forwards `sc` to a helper:
    //
    //   let helper = fn(a, sc) { sc.tx_info }      // SC projection
    //   let entry  = fn(r, sc) { helper(sc) }      // no direct projection
    //   Unit
    //
    // so "promote the unique SC candidate" picks the wrong let-binder.
    // Disambiguating needs a reachability check — follow Var refs from
    // the top-level tail, not from let-binder local content — which a
    // Unit tail cannot supply. The reverse-walk below stands;
    // `has_script_context_evidence` remains for callers that already
    // know which binder is the entry and only want to confirm it.
    for prefix in prefixes.iter_mut().rev() {
        let Prefix::Let { value, .. } = prefix else {
            continue;
        };
        let replaced = match std::mem::replace(value.as_mut(), PseudoExpr::Unit) {
            PseudoExpr::Lambda { params, body } => {
                let fallback = PseudoExpr::Lambda {
                    params: params.clone(),
                    body: body.clone(),
                };
                // Route through `select_validator_callable` so that
                // let-bound curried entries benefit from the
                // purpose-gated uncurry attempts.
                match select_validator_callable(
                    params,
                    body.into_inner(),
                    version,
                    kind_annotations.as_deref_mut(),
                    blueprint_param_names,
                    purpose,
                    authoritative,
                ) {
                    Some((params, body)) => Some(PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    }),
                    None => Some(fallback),
                }
            }
            PseudoExpr::RecFn { name, params, body } => {
                let fallback = PseudoExpr::RecFn {
                    name: name.clone(),
                    params: params.clone(),
                    body: body.clone(),
                };
                match select_validator_callable(
                    params,
                    body.into_inner(),
                    version,
                    kind_annotations.as_deref_mut(),
                    blueprint_param_names,
                    purpose,
                    authoritative,
                ) {
                    Some((params, body)) => Some(PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(body),
                    }),
                    None => Some(fallback),
                }
            }
            other => {
                // Not a Lambda/RecFn — put back as-is, try previous prefix.
                let _ = std::mem::replace(value.as_mut(), other);
                None
            }
        };
        if let Some(new_value) = replaced {
            **value = new_value;
            return; // renamed (or fallback-restored) — stop scanning.
        }
    }
}

/// When the outer structure is `let name = λ params. body in name`, locate
/// the matching Let prefix and rename its Lambda value's params. No-op if
/// no prefix matches or the bound value isn't a Lambda/RecFn of the right
/// arity.
fn rename_lambda_inside_matching_let_prefix(
    prefixes: &mut [Prefix],
    var_name: &str,
    var_id: Option<VarId>,
    version: ScriptVersion,
    mut kind_annotations: Option<&mut HashMap<VarId, VarKind>>,
    blueprint_param_names: Option<&[String]>,
    purpose: Option<ValidatorPurpose>,
    authoritative: bool,
) {
    for prefix in prefixes.iter_mut().rev() {
        let Prefix::Let {
            name: let_name,
            id: let_id,
            value,
        } = prefix
        else {
            continue;
        };
        if let_name != var_name || *let_id != var_id {
            continue;
        }
        let replaced = match std::mem::replace(value.as_mut(), PseudoExpr::Unit) {
            PseudoExpr::Lambda { params, body } => {
                let fallback = PseudoExpr::Lambda {
                    params: params.clone(),
                    body: body.clone(),
                };
                // Route through `select_validator_callable` so that
                // let-bound curried entries benefit from the
                // purpose-gated uncurry attempts.
                match select_validator_callable(
                    params,
                    body.into_inner(),
                    version,
                    kind_annotations.as_deref_mut(),
                    blueprint_param_names,
                    purpose,
                    authoritative,
                ) {
                    Some((new_params, new_body)) => PseudoExpr::Lambda {
                        params: new_params,
                        body: PBox::new(new_body),
                    },
                    None => fallback,
                }
            }
            PseudoExpr::RecFn { name, params, body } => {
                let fallback = PseudoExpr::RecFn {
                    name: name.clone(),
                    params: params.clone(),
                    body: body.clone(),
                };
                match select_validator_callable(
                    params,
                    body.into_inner(),
                    version,
                    kind_annotations.as_deref_mut(),
                    blueprint_param_names,
                    purpose,
                    authoritative,
                ) {
                    Some((new_params, new_body)) => PseudoExpr::RecFn {
                        name,
                        params: new_params,
                        body: PBox::new(new_body),
                    },
                    None => fallback,
                }
            }
            other => other,
        };
        *value.as_mut() = replaced;
        return;
    }
}

fn rewrap_prefixes(mut expr: PseudoExpr, prefixes: Vec<Prefix>) -> PseudoExpr {
    for prefix in prefixes.into_iter().rev() {
        expr = match prefix {
            Prefix::Let { name, id, value } => PseudoExpr::Let {
                name,
                id,
                value,
                body: PBox::new(expr),
            },
            Prefix::RecFn { name, params } => PseudoExpr::RecFn {
                name,
                params,
                body: PBox::new(expr),
            },
        };
    }

    expr
}

#[cfg(test)]
mod tests;
