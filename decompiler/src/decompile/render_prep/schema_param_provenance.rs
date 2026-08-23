//! Schema-param provenance bridge — propagate a named TxInfo list field's
//! element Cardano type to a helper-fn parameter that is provably fed only
//! that element type at every call site.
//!
//! `name_cardano_sum_arms` names a `when <subject> is { … }` dispatch's
//! constructor arms only when `<subject>` is a named Cardano binder
//! (`certificate`, `purpose`, …). A helper that destructures a TxInfo-list
//! element carries an opaque mechanical param name, so the subject
//! resolves to nothing and the arms stay `Unknown_S_*`. When every call
//! site of a helper feeds slot-0 a value provably the element of
//! `tx_info.certificates` (a `DCert`), the param is renamed to
//! `certificate` and its body `Var` references rewired by `VarId`, so
//! `name_cardano_sum_arms` then resolves the subject to
//! [`SumTypeId::Certificate`].
//!
//! Only `certificates → DCert` is bridged; [`is_cert_element`] is the
//! extension point for the other V1-ledger inner types.
//!
//! A param is bridged only when its function's call set is fully
//! enumerable (the identifier appears only as an `Apply` head — never as
//! a value: passed/returned/`when`-subject) and every call site's slot-0
//! arg is a proven `DCert` element. A single non-provable arg at any
//! site drops the whole function; a function with no call sites, or used
//! as a value anywhere, is left alone. A wrong bridge renders as
//! plausible-looking wrong output, so every gate errs toward not
//! renaming.
//!
//! Version gate: the certificate layout is version-dependent, so the
//! bridge only fires under an explicit V1/V2 render version, never the
//! `None`→V2 default. V3 `TxCert` is out of scope — the `Never`
//! deposit/refund makes its arities ambiguous, and `known_ctor_arity`
//! already refuses it.

use std::collections::{HashMap, HashSet};

use crate::builtins::BuiltinId;
use crate::decompile::ScriptVersion;
use crate::decompile::blueprint_registry::TypeHintId;
use crate::decompile::simplify::postprocess::SumTypeId;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

use super::ctx::RenderCtx;
use super::rename_hygiene::{apply_renames, find_param_cons_tail};
use super::scope_recurse::children;

/// The Purpose constructor tag that carries a single `DCert` payload in
/// V1/V2 (`Certifying(DCert)`), and that constructor's arity.
const PURPOSE_CERTIFYING_TAG: usize = 3;
const PURPOSE_CERTIFYING_ARITY: usize = 1;

pub(super) fn schema_param_provenance(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    // Certificate layout is version-dependent; the ambiguous `None`→V2
    // default is not enough evidence to name one.
    match ctx.version() {
        Some(ScriptVersion::PlutusV1) | Some(ScriptVersion::PlutusV2) => {}
        _ => return expr,
    }

    let mut sources = CertSources::default();
    collect_purpose_cert_payloads(&expr, &mut sources, &mut Vec::new());
    collect_certificates_list_sources(&expr, &mut sources);

    let mut scan = FnScan::default();
    scan_fn_calls(&expr, &mut scan);
    let renames = bridged_param_renames(&scan, &sources);
    if renames.is_empty() {
        return expr;
    }
    // Fail-closed freshness guard: the renames are VarId-keyed, so there is
    // no capture hazard, but a second binder already showing `certificate`
    // would render confusingly — skip the bridge then.
    if name_bound_outside(&expr, "certificate", &renames) {
        return expr;
    }
    apply_renames(expr, &renames)
}

/// True if a binder whose `VarId` is not in `exclude` (the params being
/// renamed) already displays `name`.
fn name_bound_outside(expr: &PseudoExpr, name: &str, exclude: &HashMap<VarId, String>) -> bool {
    fn binder_hits(b: &Binder, name: &str, exclude: &HashMap<VarId, String>) -> bool {
        b.as_str() == name && !exclude.contains_key(&b.var_id())
    }
    /// A literal pattern stores a full `PseudoExpr` that can itself
    /// introduce binders. Rather than recursing into it, hand it to the
    /// walk as another root (`extra`): the whole predicate is an OR over
    /// every reachable node, so both spellings give the same answer.
    fn pattern_binds<'a>(
        p: &'a WhenPattern,
        name: &str,
        exclude: &HashMap<VarId, String>,
        extra: &mut Vec<&'a PseudoExpr>,
    ) -> bool {
        match p {
            WhenPattern::Constructor { fields, .. } | WhenPattern::Tuple(fields) => {
                fields.iter().any(|f| binder_hits(f, name, exclude))
            }
            WhenPattern::List { elements, tail } => elements
                .iter()
                .chain(tail.iter())
                .any(|f| binder_hits(f, name, exclude)),
            WhenPattern::Pair(a, b) => {
                binder_hits(a, name, exclude) || binder_hits(b, name, exclude)
            }
            WhenPattern::Var(b) => binder_hits(b, name, exclude),
            WhenPattern::Literal(e) => {
                extra.push(e);
                false
            }
            WhenPattern::Wildcard => false,
        }
    }
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        let here = match expr {
            PseudoExpr::Lambda { params, .. } => {
                params.iter().any(|p| binder_hits(p, name, exclude))
            }
            PseudoExpr::RecFn {
                name: self_name,
                params,
                ..
            } => {
                binder_hits(self_name, name, exclude)
                    || params.iter().any(|p| binder_hits(p, name, exclude))
            }
            // A compat-placeholder `id: None` still renders the name, so it is
            // a binder too.
            PseudoExpr::Let { name: n, id, .. } => {
                n.as_str() == name
                    && match id {
                        Some(vid) => !exclude.contains_key(vid),
                        None => true,
                    }
            }
            PseudoExpr::When {
                subject_name,
                clauses,
                ..
            } => {
                subject_name
                    .as_ref()
                    .is_some_and(|b| binder_hits(b, name, exclude))
                    || clauses
                        .iter()
                        .any(|c| pattern_binds(&c.pattern, name, exclude, &mut stack))
            }
            _ => false,
        };
        if here {
            return true;
        }
        for child in children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
    false
}

// ===== certificate-element sources =====

/// Sets of `VarId`s with proven Cardano provenance.
#[derive(Default)]
struct CertSources {
    /// Binders that hold a single `DCert` value (the `Certifying` purpose
    /// payload). A bare `Var` of one of these is a DCert element.
    cert_values: HashSet<VarId>,
    /// Binders that hold the `certificates` LIST (`List<DCert>`): the TxInfo
    /// `certificates` field binder, plus rec-fn params proven to iterate it.
    /// A `<Var>.head` (ListHead) over one of these is a DCert element.
    cert_lists: HashSet<VarId>,
}

/// Collect the payload binder of a `Certifying` arm (`when <purpose> is {
/// Constr<3>(p) -> … }`) where `<purpose>` resolves to [`SumTypeId::Purpose`].
/// The proof is the subject name plus the exact Certifying tag/arity, both
/// minted only by the canonical ScriptContext destructure chain.
fn collect_purpose_cert_payloads(
    expr: &PseudoExpr,
    out: &mut CertSources,
    _stack: &mut Vec<VarId>,
) {
    let mut work: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = work.pop() {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = expr
            && subject_is_purpose(subject)
        {
            for c in clauses {
                if let WhenPattern::Constructor {
                    type_hint,
                    tag,
                    fields,
                    ..
                } = &c.pattern
                    && *tag == PURPOSE_CERTIFYING_TAG
                    && fields.len() == PURPOSE_CERTIFYING_ARITY
                    && arm_hint_is_purpose_compatible(type_hint.as_ref())
                {
                    out.cert_values.insert(fields[0].var_id());
                }
            }
        }
        for child in children(expr).into_iter().rev() {
            work.push(child);
        }
    }
}

/// True when a Certifying-arm `type_hint` does not contradict the Purpose
/// classification: absent, a synthetic stub (`Unknown_S_*`/`Unknown_E_*`), or
/// the Cardano `purpose`/`script_purpose` name. A real hint naming a different
/// type is contrary evidence — `name_cardano_sum_arms` would leave that arm
/// alone, so its payload must not be treated as a Certifying `DCert`.
fn arm_hint_is_purpose_compatible(hint: Option<&TypeHintId>) -> bool {
    match hint {
        None => true,
        Some(h) => {
            let s = h.as_str();
            s.starts_with("Unknown_S_")
                || s.starts_with("Unknown_E_")
                || s == "purpose"
                || s == "script_purpose"
        }
    }
}

/// `subject` is the canonical `purpose` Cardano binder (a named `Var` whose
/// legacy name resolves to [`SumTypeId::Purpose`]).
fn subject_is_purpose(subject: &PseudoExpr) -> bool {
    matches!(
        subject,
        PseudoExpr::Var { name, id: Some(_) }
            if SumTypeId::from_display_name(name) == Some(SumTypeId::Purpose)
    )
}

/// Collect the `certificates`-LIST sources: the TxInfo `certificates` field
/// binder(s), plus any rec-fn first param proven to be that list (or its
/// recursive sub-list) at every call site. Iterates to a fixpoint so a param
/// qualified by one rec fn can anchor a deeper one.
fn collect_certificates_list_sources(expr: &PseudoExpr, out: &mut CertSources) {
    // (a) the `certificates` TxInfo field binder(s).
    collect_certificates_field_binders(expr, &mut out.cert_lists);

    // (b) rec-fn first params proven to iterate a `certificates` source.
    let mut scan = FnScan::default();
    scan_fn_calls(expr, &mut scan);
    loop {
        let added = qualify_certificates_list_params(&scan, &mut out.cert_lists);
        if !added {
            break;
        }
    }
}

/// Collect the binder VarId of the `certificates` field of the canonical TxInfo
/// destructure: `when <tx_info-named Var> is { Constr<0>(…) }` with a pattern
/// field binder named `certificates`. That name is minted only by
/// `rename_tx_info_binders` over the schema-positioned TxInfo ctor, so such a
/// binder is the genuine field.
fn collect_certificates_field_binders(expr: &PseudoExpr, out: &mut HashSet<VarId>) {
    let mut work: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = work.pop() {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = expr
            && matches!(subject.as_ref(), PseudoExpr::Var { name, id: Some(_) } if name == "tx_info")
        {
            for c in clauses {
                // Defensive arity gate: trust a `certificates` binder only
                // under a Constr pattern whose field count is a canonical V1/V2
                // TxInfo arity (10 / 12). `rename_tx_info_binders` is already
                // arity-gated; this guards only against a malformed
                // `when tx_info is { Constr(…certificates…) }`.
                if let WhenPattern::Constructor { tag, fields, .. } = &c.pattern
                    && *tag == 0
                    && matches!(fields.len(), 10 | 12)
                {
                    for f in fields {
                        if f.as_str() == "certificates" {
                            out.insert(f.var_id());
                        }
                    }
                }
            }
        }
        for child in children(expr).into_iter().rev() {
            work.push(child);
        }
    }
}

/// Add rec-fn first params that are provably the `certificates` list at every
/// call site (each slot-0 is either an existing `cert_lists` source, an
/// `un_list_data(<cert_lists source>)`, or the recursive `tail` of the param's
/// own cons-iteration). Returns whether any param was newly added.
fn qualify_certificates_list_params(scan: &FnScan, cert_lists: &mut HashSet<VarId>) -> bool {
    let mut added = false;
    for (canonical, meta) in &scan.recs {
        if cert_lists.contains(&meta.param0) {
            continue; // already qualified
        }
        // Enumerable: the function (canonical + self-name aliases) is never
        // used as a value.
        let alias_ids: Vec<VarId> = scan
            .aliases
            .iter()
            .filter(|(_, c)| *c == canonical)
            .map(|(r, _)| *r)
            .collect();
        if scan.value_used.contains(canonical)
            || alias_ids.iter().any(|r| scan.value_used.contains(r))
        {
            continue; // not enumerable → fail-closed
        }
        // Gather every call site's slot-0.
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
            continue;
        }
        let recursive_tails = meta.recursive_tails();
        let mut has_external = false;
        let mut ok = true;
        for arg in &slots {
            match classify_cert_list_arg(arg, cert_lists, &recursive_tails) {
                CertListArg::Source => has_external = true,
                CertListArg::RecursiveTail => {}
                CertListArg::Other => {
                    ok = false;
                    break;
                }
            }
        }
        if ok && has_external {
            cert_lists.insert(meta.param0);
            added = true;
        }
    }
    added
}

enum CertListArg {
    /// A proven `certificates` list source (or `un_list_data` of one).
    Source,
    /// The recursive sub-list (the cons-`tail` / `ListTail(param0)`).
    RecursiveTail,
    /// Anything else — disqualifies the function.
    Other,
}

/// Classify a rec-fn slot-0 argument for the certificates-list gate.
fn classify_cert_list_arg(
    arg: &PseudoExpr,
    cert_lists: &HashSet<VarId>,
    recursive_tail_ids: &HashSet<VarId>,
) -> CertListArg {
    // The recursive sub-list witness: a bare `tail` var, or `ListTail(param0)`.
    if let PseudoExpr::Var { id: Some(v), .. } = arg
        && recursive_tail_ids.contains(v)
    {
        return CertListArg::RecursiveTail;
    }
    if let Some((BuiltinId::ListTail, PseudoExpr::Var { id: Some(v), .. })) = un_builtin1(arg)
        && recursive_tail_ids.contains(v)
    {
        return CertListArg::RecursiveTail;
    }
    // A proven source (bare var, or `un_list_data(<source var>)`).
    if let PseudoExpr::Var { id: Some(v), .. } = arg
        && cert_lists.contains(v)
    {
        return CertListArg::Source;
    }
    if let Some((BuiltinId::DataUnList, PseudoExpr::Var { id: Some(v), .. })) = un_builtin1(arg)
        && cert_lists.contains(v)
    {
        return CertListArg::Source;
    }
    CertListArg::Other
}

// ===== enumerable per-function slot-0 verdict =====

/// First-param metadata for a helper fn (`fn f(param0, …)`): `param0` is
/// the param fed at slot 0; the recursion witnesses are the binders that
/// hold a recursive sub-list of it.
struct RecMeta {
    param0: VarId,
    /// The cons-`tail` binder of `when param0 is { [_, ..tail] }`, if any.
    cons_tail: Option<VarId>,
}

impl RecMeta {
    /// The set of VarIds that, fed back as slot-0, count as the recursive
    /// sub-list: the param itself (consumed via `ListTail(param0)`) and the
    /// cons-tail binder.
    fn recursive_tails(&self) -> HashSet<VarId> {
        let mut s = HashSet::new();
        s.insert(self.param0);
        if let Some(t) = self.cons_tail {
            s.insert(t);
        }
        s
    }
}

#[derive(Default)]
struct FnScan {
    /// Canonical fn id → its first param + recursion metadata. Canonical id is
    /// the enclosing `let` binder for `let f = rec fn g(…)`, else a bare
    /// `RecFn`'s self-name. Captures both rec and non-rec helpers (a non-rec
    /// helper has no `cons_tail`).
    recs: HashMap<VarId, RecMeta>,
    /// RecFn self-name id → canonical id (`let f = rec fn g`: `g → f`), so both
    /// call sets are gathered for one function.
    aliases: HashMap<VarId, VarId>,
    /// Identifiers used at least once as a VALUE (not an `Apply` head) →
    /// fail-closed enumerability.
    value_used: HashSet<VarId>,
    /// fn id → slot-0 arg at each call site (cloned), keyed by the raw call-head
    /// id (canonical OR alias).
    slot0: HashMap<VarId, Vec<PseudoExpr>>,
}

/// One-pass scan: record every named helper (its first param + any cons-tail),
/// value-used identifiers, and each call's slot-0 argument.
fn scan_fn_calls(expr: &PseudoExpr, scan: &mut FnScan) {
    let mut work: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = work.pop() {
        let mut next: Vec<&PseudoExpr> = Vec::new();
        match expr {
            // `let f = rec fn g(p0, …) { … }` — external callers use `f`, recursive
            // calls use `g`.
            PseudoExpr::Let {
                id: Some(let_id),
                value,
                body,
                ..
            } if matches!(value.as_ref(), PseudoExpr::RecFn { .. }) => {
                let PseudoExpr::RecFn {
                    name,
                    params,
                    body: fbody,
                } = value.as_ref()
                else {
                    unreachable!("guarded by the match arm");
                };
                if let Some(p0) = params.first() {
                    let cons_tail = find_param_cons_tail(fbody, p0.var_id());
                    scan.recs.insert(
                        *let_id,
                        RecMeta {
                            param0: p0.var_id(),
                            cons_tail,
                        },
                    );
                    scan.aliases.insert(name.var_id(), *let_id);
                }
                next.push(fbody.as_ref());
                next.push(body.as_ref());
            }
            // `let f = fn(p0, …) { … }` — a non-rec helper.
            PseudoExpr::Let {
                id: Some(let_id),
                value,
                body,
                ..
            } if matches!(value.as_ref(), PseudoExpr::Lambda { .. }) => {
                let PseudoExpr::Lambda {
                    params,
                    body: fbody,
                } = value.as_ref()
                else {
                    unreachable!("guarded by the match arm");
                };
                if let Some(p0) = params.first() {
                    scan.recs.entry(*let_id).or_insert(RecMeta {
                        param0: p0.var_id(),
                        cons_tail: None,
                    });
                }
                next.push(fbody.as_ref());
                next.push(body.as_ref());
            }
            PseudoExpr::RecFn { name, params, body } => {
                if let Some(p0) = params.first()
                    && !scan.aliases.contains_key(&name.var_id())
                {
                    let cons_tail = find_param_cons_tail(body, p0.var_id());
                    scan.recs.entry(name.var_id()).or_insert(RecMeta {
                        param0: p0.var_id(),
                        cons_tail,
                    });
                }
                next.push(body.as_ref());
            }
            PseudoExpr::Apply { function, args } => {
                if let PseudoExpr::Var { id: Some(fid), .. } = function.as_ref() {
                    if let Some(a0) = args.first() {
                        scan.slot0.entry(*fid).or_default().push(a0.clone());
                    } else {
                        // A 0-arg `Apply(helper, [])` hides slot-0, so record it as a
                        // value-use: the function is then not enumerable and never
                        // bridged.
                        scan.value_used.insert(*fid);
                    }
                    // A non-empty function head is a CALL, not a value-use.
                } else {
                    next.push(function.as_ref());
                }
                for a in args.iter() {
                    next.push(a);
                }
            }
            PseudoExpr::Var { id: Some(vid), .. } => {
                scan.value_used.insert(*vid);
            }
            other => {
                for child in children(other) {
                    next.push(child);
                }
            }
        }
        for child in next.into_iter().rev() {
            work.push(child);
        }
    }
}

/// Compute the `param0 → "certificate"` renames for every helper whose call set
/// is enumerable and whose slot-0 is a proven `DCert` element at every call
/// site (≥1 site).
fn bridged_param_renames(scan: &FnScan, sources: &CertSources) -> HashMap<VarId, String> {
    let mut renames: HashMap<VarId, String> = HashMap::new();
    for (canonical, meta) in &scan.recs {
        // Enumerable: neither the canonical id nor any self-name alias may be
        // used as a value.
        let alias_ids: Vec<VarId> = scan
            .aliases
            .iter()
            .filter(|(_, c)| *c == canonical)
            .map(|(r, _)| *r)
            .collect();
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
        let all_cert = slots.iter().all(|arg| is_cert_element(arg, sources));
        if all_cert {
            renames.insert(meta.param0, "certificate".to_string());
        }
    }
    renames
}

/// Whether `arg` is provably a single `DCert` element:
///   - a bare `Var` whose binder is a `Certifying` purpose payload, OR
///   - `<L>.head` (ListHead) where `<L>` is a proven `certificates` list source.
fn is_cert_element(arg: &PseudoExpr, sources: &CertSources) -> bool {
    match arg {
        PseudoExpr::Var { id: Some(v), .. } => sources.cert_values.contains(v),
        PseudoExpr::FieldAccess {
            record,
            selector: FieldSelector::ListHead,
        } => matches!(
            record.as_ref(),
            PseudoExpr::Var { id: Some(v), .. } if sources.cert_lists.contains(v)
        ),
        _ => false,
    }
}

// ===== shared helpers =====

/// A one-argument builtin call in either the direct `BuiltinCall` form or the
/// partial-application `Apply(BuiltinCall(_, []), [x])` form. Returns the
/// builtin id and that argument.
fn un_builtin1(value: &PseudoExpr) -> Option<(BuiltinId, &PseudoExpr)> {
    match value {
        PseudoExpr::BuiltinCall { name, args } if args.len() == 1 => Some((*name, &args[0])),
        PseudoExpr::Apply { function, args } if args.len() == 1 => {
            if let PseudoExpr::BuiltinCall {
                name,
                args: builtin_args,
            } = function.as_ref()
                && builtin_args.is_empty()
            {
                Some((*name, &args[0]))
            } else {
                None
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests;
