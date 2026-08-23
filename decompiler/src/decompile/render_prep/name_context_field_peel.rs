//! Name a Cardano record that is taken apart by list peeling instead of
//! by field index.
//!
//! Every Cardano naming path in the decompiler keys on an INDEX form —
//! `script_context[N]`, `tx_info.fields[N]`. PlutusTx does not emit one.
//! It converts each `Constr` payload to its own list type and walks it
//! head/tail, one hoisted function per record:
//!
//! ```text
//! when o(script_context.fields) is {
//!   [] -> fail
//!   [v_225, ..variant] ->
//!     let r = extract_fields_4(v_225)
//!     expect [variant_0, ..variant_20] = variant
//!     …
//! }
//! fn extract_fields_4(x_30) {
//!   expect [v_236, ..variant] = o(x_30.fields)
//!   expect [v_238, ..variant_12] = variant
//!   …
//! }
//! ```
//!
//! so a PlutusTx-compiled validator reaches the reader with the whole
//! context anonymous — down to the transaction's own inputs, mint and
//! validity range, each a `v_NNN`.
//!
//! The pass carries a type from the one binder whose meaning the calling
//! convention fixes — the entry `script_context` — and lets the schema
//! do the rest: position `i` of a record of type `T` is `T`'s field `i`,
//! and that field's own type seeds the next peel. It crosses into a
//! helper when every call site passes the same known type at that
//! position, which is how `extract_fields_4` learns it holds a `TxInfo`.
//!
//! Two things license reading position `i` as field `i`:
//!
//!   * The subject is `<v>.fields` for a `v` whose record type is
//!     already established — from the entry param, or from a schema
//!     position named in an earlier round.
//!   * Any conversion call wrapping it is a PROVEN order- and
//!     element-preserving list rebuild: a one-parameter recursive
//!     function emitting `Cons(<head>, self(<tail>))` with the head
//!     passed through untouched. Without that, a `map` or a `swap`
//!     returns a list of the same length whose slots are not the
//!     record's fields.
//!
//! Renaming only. No binder is introduced, no expression rewritten, and
//! a name already taken elsewhere in the tree is left alone.

use std::collections::HashMap;

use crate::decompile::ScriptVersion;
use crate::decompile::simplify::postprocess::{
    CardanoTypeRef, ContextType, context_field_at, context_field_type_full,
};
use crate::pseudo::ast::{Binder, PseudoExpr, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

use super::ctx::RenderCtx;
use super::scope_recurse::{children, rewrite_bottom_up};

/// Bound on the type-propagation fixpoint. Each round can only ADD
/// bindings to a `VarId`-keyed map, so it converges on its own; the cap
/// only bounds a pathological tree.
const MAX_ROUNDS: usize = 16;

/// Stops a malformed cons chain. `context_field_at` returning
/// `None` past the record's last field ends the walk first.
const MAX_FIELDS: usize = 64;

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

/// The Cardano types a PlutusTx-shaped context settles, without touching
/// the tree.
///
/// Split out because the two halves belong at different points. The
/// forward type env the sum-arm naming consults never sees such a
/// context — it resolves a `when` subject from an INDEXED access or a
/// reserved binder name, and a peeled context has neither — so those
/// passes need these types while they still own the blueprint registry.
/// The renaming half has to wait until every other naming pass has had
/// its say.
pub(super) fn infer_context_types(
    expr: &PseudoExpr,
    ctx: &RenderCtx,
) -> HashMap<VarId, CardanoTypeRef> {
    if ctx.version().is_none() {
        return HashMap::new();
    }
    let entry_ids = super::collapse_script_context_when::collect_script_context_param_ids(expr);
    if entry_ids.is_empty() {
        return HashMap::new();
    }
    let mut defs: HashMap<VarId, &PseudoExpr> = HashMap::new();
    collect_let_values(expr, &mut defs);
    let mut types: HashMap<VarId, CardanoTypeRef> = entry_ids
        .iter()
        .map(|id| (*id, CardanoTypeRef::Record(ContextType::ScriptContext)))
        .collect();
    let mut renames = HashMap::new();
    settle(expr, ctx, &defs, &mut types, &mut renames);
    types
}

pub(super) fn name_context_field_peel(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    if ctx.version().is_none() {
        return expr;
    }
    let entry_ids = super::collapse_script_context_when::collect_script_context_param_ids(&expr);
    if entry_ids.is_empty() {
        return expr;
    }

    let mut defs: HashMap<VarId, &PseudoExpr> = HashMap::new();
    collect_let_values(&expr, &mut defs);

    let mut types: HashMap<VarId, CardanoTypeRef> = entry_ids
        .iter()
        .map(|id| (*id, CardanoTypeRef::Record(ContextType::ScriptContext)))
        .collect();
    let mut renames: HashMap<VarId, String> = HashMap::new();
    settle(&expr, ctx, &defs, &mut types, &mut renames);

    // With the types settled, the `let`-bound payload lists can name
    // what they index.
    let expr = resolve_payload_indices(expr, ctx, &types);

    if renames.is_empty() {
        return expr;
    }
    let mut candidates: Vec<(VarId, String)> = renames.into_iter().collect();
    // `commit_binder_renames` drops duplicate targets, so what it sees
    // must not depend on `HashMap` iteration order.
    candidates.sort();
    super::rename_hygiene::commit_binder_renames(expr, candidates)
}

/// Run the type/name fixpoint to convergence.
fn settle(
    expr: &PseudoExpr,
    ctx: &RenderCtx,
    defs: &HashMap<VarId, &PseudoExpr>,
    types: &mut HashMap<VarId, CardanoTypeRef>,
    renames: &mut HashMap<VarId, String>,
) {
    for _ in 0..MAX_ROUNDS {
        let before = types.len();
        name_peels(expr, ctx, defs, types, renames);
        propagate_through_calls(expr, defs, types);
        propagate_through_maps(expr, defs, types);
        if types.len() == before {
            return;
        }
    }
}

/// Every `Let`-bound value in the tree, keyed by its binder. Both the
/// conversion call's definition and a helper's body are looked up here.
fn collect_let_values<'a>(expr: &'a PseudoExpr, out: &mut HashMap<VarId, &'a PseudoExpr>) {
    preorder(expr, |expr| {
        if let PseudoExpr::Let {
            id: Some(vid),
            value,
            ..
        } = expr
        {
            out.insert(*vid, value.as_ref());
        }
    })
}

// Peel naming

fn name_peels(
    expr: &PseudoExpr,
    ctx: &RenderCtx,
    defs: &HashMap<VarId, &PseudoExpr>,
    types: &mut HashMap<VarId, CardanoTypeRef>,
    renames: &mut HashMap<VarId, String>,
) {
    preorder(expr, |expr| {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = expr
        {
            if let Some(record) = subject_record_type(subject, types, defs) {
                name_chain(expr, record, ctx, types, renames);
            }
            // The same schema, reached the other way: a record whose
            // type is known and that is destructured by a constructor
            // pattern rather than peeled. PlutusTx emits both — the
            // outer records as peels, the inner ones as `expect`.
            if let PseudoExpr::Var { id: Some(v), .. } = subject.as_ref()
                && let Some(CardanoTypeRef::Record(record)) = types.get(v).copied()
            {
                for clause in clauses {
                    name_record_pattern(&clause.pattern, record, ctx, types, renames);
                }
            }
        }
    })
}

/// Walk the cons chain, naming head `i` after field `i` of `record`.
///
/// Stops at the first index the schema does not declare: a script that
/// peels past the record's last field is not one this schema describes,
/// and the heads before that point are still its fields.
fn name_chain(
    start: &PseudoExpr,
    record: ContextType,
    ctx: &RenderCtx,
    types: &mut HashMap<VarId, CardanoTypeRef>,
    renames: &mut HashMap<VarId, String>,
) {
    let mut node = start;
    for index in 0..MAX_FIELDS {
        let PseudoExpr::When { clauses, .. } = node else {
            return;
        };
        let Some((head, tail, body)) = clauses
            .iter()
            .find_map(|c| cons_binders(&c.pattern).map(|(h, t)| (h, t, &c.body)))
        else {
            return;
        };
        let Some(field) = field_at(record, index, ctx) else {
            return;
        };
        if is_synthetic(head.as_str()) {
            // A binder the body never reads came in as `_`; keep that
            // marker so the name says WHICH field is skipped without
            // reading as a live binding.
            let unused = head.as_str().starts_with('_');
            let name = field.display_name();
            renames.insert(
                head.var_id(),
                if unused {
                    format!("_{name}")
                } else {
                    name.to_string()
                },
            );
        }
        // The field's own record type seeds the next peel — this is how
        // slot 0 of the context makes the transaction a `TxInfo`.
        if let Some(child) = context_field_type_full(field, ctx.version_or_v2()) {
            types.insert(head.var_id(), child);
        }
        let Some(next) = follow_tail(body, tail.var_id()) else {
            return;
        };
        node = next;
    }
}

/// The schema field at `index`, held back where the version is a guess
/// and the two candidate layouts disagree.
///
/// V1 and V2 share the `(1, 0)` UPLC header, so with no builtin evidence
/// the render runs V2-coerced. Their `ScriptContext` is `[tx_info,
/// purpose]` either way and `TxInfo` agrees at index 0, but past that
/// the layouts diverge — V2 inserts `reference_inputs`, which V1 does
/// not have at all. Naming a divergent position under the guess would
/// call a real V1 script's `valid_range` its `withdrawals`, and the
/// binder it replaces (`variant_3`) at least claims nothing.
fn field_at(
    record: ContextType,
    index: usize,
    ctx: &RenderCtx,
) -> Option<crate::decompile::simplify::postprocess::ContextField> {
    let field = context_field_at(record, index, ctx.version_or_v2())?;
    if !ctx.version_is_guessed() {
        return Some(field);
    }
    let v1 = context_field_at(record, index, ScriptVersion::PlutusV1);
    let v2 = context_field_at(record, index, ScriptVersion::PlutusV2);
    (v1 == v2).then_some(field)
}

/// Name a record's constructor-pattern binders after its schema fields.
///
/// A record is single-constructor, so only tag 0 qualifies. The walk
/// stops at the first index the schema does not declare: a stub ADT's
/// declared arity is widened by merging, so a pattern can carry more
/// binders than the record has fields.
fn name_record_pattern(
    pattern: &WhenPattern,
    record: ContextType,
    ctx: &RenderCtx,
    types: &mut HashMap<VarId, CardanoTypeRef>,
    renames: &mut HashMap<VarId, String>,
) {
    let WhenPattern::Constructor { tag: 0, fields, .. } = pattern else {
        return;
    };
    for (index, binder) in fields.iter().enumerate() {
        let Some(field) = field_at(record, index, ctx) else {
            return;
        };
        if is_synthetic(binder.as_str()) {
            let unused = binder.as_str().starts_with('_');
            let name = field.display_name();
            renames.insert(
                binder.var_id(),
                if unused {
                    format!("_{name}")
                } else {
                    name.to_string()
                },
            );
        }
        if let Some(child) = context_field_type_full(field, ctx.version_or_v2()) {
            types.insert(binder.var_id(), child);
        }
    }
}

/// Follow the tail binder to the next `when`/`expect` that destructures
/// it, skipping the `let`s the body binds along the way.
fn follow_tail(body: &PseudoExpr, tail_id: VarId) -> Option<&PseudoExpr> {
    let mut body = body;
    loop {
        match body {
            PseudoExpr::Let { body: inner, .. } => body = inner.as_ref(),
            PseudoExpr::When { subject, .. } => {
                return matches!(subject.as_ref(), PseudoExpr::Var { id: Some(v), .. } if *v == tail_id)
                    .then_some(body);
            }
            _ => return None,
        }
    }
}

/// `<v>.fields` for a `v` whose record type is known, possibly behind a
/// proven identity list rebuild. Only one child (`args[0]`) is ever
/// descended into, so this is a pointer loop.
fn subject_record_type(
    subject: &PseudoExpr,
    types: &HashMap<VarId, CardanoTypeRef>,
    defs: &HashMap<VarId, &PseudoExpr>,
) -> Option<ContextType> {
    let mut current = subject;
    loop {
        match current {
            PseudoExpr::FieldAccess { record, selector } => {
                if selector.as_pretty_name() != "fields" {
                    return None;
                }
                let PseudoExpr::Var { id: Some(v), .. } = record.as_ref() else {
                    return None;
                };
                return match types.get(v) {
                    Some(CardanoTypeRef::Record(t)) => Some(*t),
                    _ => None,
                };
            }
            PseudoExpr::Apply { function, args } if args.len() == 1 => {
                let PseudoExpr::Var { id: Some(fid), .. } = function.as_ref() else {
                    return None;
                };
                if !is_identity_list_rebuild(*fid, defs) {
                    return None;
                }
                current = &args[0];
            }
            _ => return None,
        }
    }
}

// Interprocedural propagation

/// Give a helper's parameter the record type its callers pass, when they
/// all agree.
///
/// PlutusTx hoists each record's destructuring into its own function, so
/// without this the schema stops at the call boundary and everything
/// below `extract_fields_4(tx_info)` stays anonymous. Disagreement — two
/// call sites passing different record types, or one passing something
/// untyped — leaves the parameter alone rather than picking a winner.
fn propagate_through_calls(
    expr: &PseudoExpr,
    defs: &HashMap<VarId, &PseudoExpr>,
    types: &mut HashMap<VarId, CardanoTypeRef>,
) {
    let mut survey = CallSurvey::default();
    survey_calls(expr, types, &mut survey);

    let mut callees: Vec<VarId> = survey.positions.keys().copied().collect();
    callees.sort();
    for callee in callees {
        // A callee whose name is used as a VALUE — passed to something,
        // returned, aliased — can be called from a site this survey
        // never sees, so its parameters are not pinned down here.
        if survey.escaped.contains_key(&callee) {
            continue;
        }
        let Some(params) = defs.get(&callee).and_then(|v| callable_params(v)) else {
            continue;
        };
        for (index, seen) in survey.positions[&callee].iter().enumerate() {
            let (Observed::Agreed(record), Some(param)) = (seen, params.get(index)) else {
                continue;
            };
            types.entry(param.var_id()).or_insert(*record);
        }
    }
}

/// What every call site of one callee passes at one position.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Observed {
    /// No call site seen yet.
    Unseen,
    /// Every site so far passed this record type.
    Agreed(CardanoTypeRef),
    /// Sites disagree, or one passed something with no known type —
    /// either way the parameter is not pinned down.
    Conflict,
}

impl Observed {
    /// `None` for the incoming observation means "a call passed
    /// something untyped", which conflicts just as a different record
    /// would: it is a call whose argument is not known to be `T`.
    fn merge(self, incoming: Option<CardanoTypeRef>) -> Self {
        match (self, incoming) {
            (Self::Conflict, _) | (_, None) => Self::Conflict,
            (Self::Unseen, Some(t)) => Self::Agreed(t),
            (Self::Agreed(a), Some(b)) if a == b => Self::Agreed(a),
            _ => Self::Conflict,
        }
    }
}

#[derive(Default)]
struct CallSurvey {
    positions: HashMap<VarId, Vec<Observed>>,
    /// How many times each name is used as a VALUE rather than called.
    /// A count rather than a flag: the map hop below accounts for the
    /// uses that are a combinator's callback slot, and a name is only
    /// pinned down when every one of its value-uses is accounted for.
    escaped: HashMap<VarId, usize>,
}

/// Record what each call site passes, and which callees escape.
fn survey_calls(expr: &PseudoExpr, types: &HashMap<VarId, CardanoTypeRef>, out: &mut CallSurvey) {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        if let PseudoExpr::Apply { function, args } = expr
            && let PseudoExpr::Var {
                id: Some(callee), ..
            } = function.as_ref()
        {
            let slots = out.positions.entry(*callee).or_default();
            if slots.len() < args.len() {
                slots.resize(args.len(), Observed::Unseen);
            }
            // A call that passes fewer args than a previous one saw
            // leaves the surplus positions unaccounted for.
            for slot in slots.iter_mut().skip(args.len()) {
                *slot = Observed::Conflict;
            }
            for (index, arg) in args.iter().enumerate() {
                let seen = match arg {
                    PseudoExpr::Var { id: Some(v), .. } => types.get(v).copied(),
                    _ => None,
                };
                slots[index] = slots[index].merge(seen);
            }
            // The callee `Var` in function position is a call, not an
            // escape; its arguments are surveyed as ordinary children.
            for arg in args.iter().rev() {
                stack.push(arg);
            }
            continue;
        }
        // Any other `Var` occurrence is the name used as a value.
        if let PseudoExpr::Var { id: Some(v), .. } = expr {
            *out.escaped.entry(*v).or_insert(0) += 1;
        }
        for child in children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
}

/// Give a list-mapper's callback the element type of the list it runs
/// over.
///
/// PlutusTx compiles `map` into a combinator — `rec_fn_7(f)` returns a
/// function that walks a list rebuilding it as `Cons(f(head),
/// self(tail))` — so the schema stops at `inputs` unless the element
/// type crosses that application. With it, the callback's parameter is a
/// `TxInInfo` and its own destructuring gets named in the next round.
///
/// A callback named rather than written inline is only typed when EVERY
/// one of its value-uses is a combinator callback slot this pass typed:
/// a name also handed somewhere else could be run over a different list.
fn propagate_through_maps(
    expr: &PseudoExpr,
    defs: &HashMap<VarId, &PseudoExpr>,
    types: &mut HashMap<VarId, CardanoTypeRef>,
) {
    let mut survey = CallSurvey::default();
    survey_calls(expr, types, &mut survey);

    let mut inline: HashMap<VarId, Observed> = HashMap::new();
    let mut named: HashMap<VarId, (Observed, usize)> = HashMap::new();
    collect_map_uses(expr, defs, types, &mut inline, &mut named);

    // A lambda written inline is still reachable from several
    // applications once the partial application is `let`-bound, so its
    // parameter is only typed when every one of them agrees.
    let mut inline_params: Vec<VarId> = inline.keys().copied().collect();
    inline_params.sort();
    for param in inline_params {
        if let Observed::Agreed(elem) = inline[&param] {
            types.entry(param).or_insert(elem);
        }
    }
    let mut names: Vec<VarId> = named.keys().copied().collect();
    names.sort();
    for cb in names {
        let (seen, slots) = named[&cb];
        // Every value-use has to be one of the slots we just typed.
        if survey.escaped.get(&cb).copied().unwrap_or(0) != slots {
            continue;
        }
        // A callback is often called directly as well — the same
        // decoder run over a list and over one value. Those calls are
        // evidence about the SAME parameter, so merge them in rather
        // than either ignoring them or refusing outright: they agree
        // when it is the same record, and conflict when it is not.
        let seen = match survey.positions.get(&cb).and_then(|p| p.first()) {
            Some(direct) => match direct {
                Observed::Unseen => seen,
                Observed::Conflict => Observed::Conflict,
                Observed::Agreed(t) => seen.merge(Some(*t)),
            },
            None => seen,
        };
        let Observed::Agreed(elem) = seen else {
            continue;
        };
        let Some(params) = defs.get(&cb).and_then(|v| callable_params(v)) else {
            continue;
        };
        let Some(param) = params.first() else {
            continue;
        };
        types.entry(param.var_id()).or_insert(elem);
    }
}

/// Walk every `<mapper>(<list>)` application, recording what element type
/// its callback runs over.
fn collect_map_uses(
    expr: &PseudoExpr,
    defs: &HashMap<VarId, &PseudoExpr>,
    types: &HashMap<VarId, CardanoTypeRef>,
    inline: &mut HashMap<VarId, Observed>,
    named: &mut HashMap<VarId, (Observed, usize)>,
) {
    preorder(expr, |expr| {
        if let PseudoExpr::Apply { function, args } = expr
            && args.len() == 1
            && let Some(callback) = map_callback(function, defs)
        {
            let elem = match &args[0] {
                PseudoExpr::Var { id: Some(v), .. } => match types.get(v) {
                    Some(CardanoTypeRef::ListOfRecords(t)) => Some(CardanoTypeRef::Record(*t)),
                    _ => None,
                },
                _ => None,
            };
            match callback {
                // Written inline: this application is its only use.
                PseudoExpr::Lambda { params, .. } | PseudoExpr::RecFn { params, .. } => {
                    if let Some(param) = params.first() {
                        let entry = inline.entry(param.var_id()).or_insert(Observed::Unseen);
                        *entry = entry.merge(elem);
                    }
                }
                PseudoExpr::Var { id: Some(cb), .. } => {
                    let entry = named.entry(*cb).or_insert((Observed::Unseen, 0));
                    entry.0 = entry.0.merge(elem);
                    entry.1 += 1;
                }
                _ => {}
            }
        }
    })
}

/// The callback of `<combinator>(<callback>)`, through a `let` if the
/// partial application was bound to a name.
fn map_callback<'a>(
    function: &'a PseudoExpr,
    defs: &HashMap<VarId, &'a PseudoExpr>,
) -> Option<&'a PseudoExpr> {
    let applied = match function {
        PseudoExpr::Apply { .. } => function,
        PseudoExpr::Var { id: Some(v), .. } => defs.get(v).copied()?,
        _ => return None,
    };
    let PseudoExpr::Apply { function, args } = applied else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let PseudoExpr::Var { id: Some(mid), .. } = function.as_ref() else {
        return None;
    };
    is_element_map_combinator(*mid, defs).then(|| &args[0])
}

/// Whether `mid` names a list mapper: a one-parameter function whose
/// every cons cell is `Cons(<param>(head), <self>(tail))`.
///
/// The same "all cells agree" discipline the identity rebuild uses. One
/// mapping cell among others would leave the result's slots unrelated to
/// the input's, and a fold that reorders or drops would not put the
/// element function on every head.
fn is_element_map_combinator(mid: VarId, defs: &HashMap<VarId, &PseudoExpr>) -> bool {
    let Some(def) = defs.get(&mid).copied() else {
        return false;
    };
    let (params, body) = match def {
        PseudoExpr::Lambda { params, body } => (params, body.as_ref()),
        PseudoExpr::RecFn { params, body, .. } => (params, body.as_ref()),
        _ => return false,
    };
    if params.len() != 1 {
        return false;
    }
    let elem_fn = params[0].var_id();
    // The rebuild lives in an inner `rec fn`; hand the walker that body
    // so the self it checks against is the walker's own name.
    let Some(rebuild) = inner_rebuild(body) else {
        return false;
    };
    cons_cells_all_agree(rebuild.0, rebuild.1, |head, arm_head| {
        // The head is THIS arm's head, put through the element function.
        let PseudoExpr::Apply { function, args } = head else {
            return false;
        };
        args.len() == 1
            && matches!(strip_force(function), PseudoExpr::Var { id: Some(f), .. } if *f == elem_fn)
            && matches!(&args[0], PseudoExpr::Var { id: Some(h), .. } if *h == arm_head)
    }) && emits_nil(rebuild.1)
}

/// The `rec fn` inside a combinator that does the rebuilding, with its
/// body. `None` when the combinator has no recursive walker at all.
fn inner_rebuild(body: &PseudoExpr) -> Option<(&PseudoExpr, &PseudoExpr)> {
    let mut stack: Vec<&PseudoExpr> = vec![body];
    while let Some(body) = stack.pop() {
        if let PseudoExpr::RecFn { body: inner, .. } = body {
            return Some((body, inner.as_ref()));
        }
        for child in children(body).into_iter().rev() {
            stack.push(child);
        }
    }
    None
}

// Payload-list indexing

/// Rewrite `<payload>.head` / `<payload>[i]` to the schema field, where
/// `<payload>` is a `let` bound to a typed record's `.fields`.
///
/// PlutusTx hoists the payload list before indexing it:
///
/// ```text
/// let fields_7: List<Data> = lower_bound.fields
/// … helper_4(builtin.un_i_data, fields_7.head) … f_4(fields_7[1]) …
/// ```
///
/// The sibling `resolve_cardano_field_indices` handles the inline
/// `<record>.fields[N]` form but not this one, because the `let` hides
/// the record from a purely local match. With the record's type known,
/// `<record>.fields[i]` and `<record>.<field_i>` decode the identical
/// `Data` element, so this introduces no runtime check — the same
/// presentational relabel, one hop further.
fn resolve_payload_indices(
    expr: PseudoExpr,
    ctx: &RenderCtx,
    types: &HashMap<VarId, CardanoTypeRef>,
) -> PseudoExpr {
    let mut payloads: HashMap<VarId, (VarId, String, ContextType)> = HashMap::new();
    collect_payload_lets(&expr, types, &mut payloads);
    if payloads.is_empty() {
        return expr;
    }
    let expr = rewrite_payload_uses(expr, ctx, &payloads);
    // The rewrite reaches past the `let`, so the payload binding is
    // usually left holding nothing. It is a pure field access on a var,
    // so an unread one just goes; the dead-let sweeps have already run
    // by the time this pass does.
    drop_unread_payload_lets(expr, &payloads)
}

/// Drop a payload `let` nothing reads any more.
fn drop_unread_payload_lets(
    expr: PseudoExpr,
    payloads: &HashMap<VarId, (VarId, String, ContextType)>,
) -> PseudoExpr {
    let mut ids: HashMap<VarId, usize> = HashMap::new();
    let mut names: HashMap<String, usize> = HashMap::new();
    count_var_uses(&expr, &mut ids, &mut names);
    prune_payload_lets(expr, payloads, &ids, &names)
}

/// Count every `Var` occurrence by id AND by name — the AST allows an
/// id-less reference resolved by name, and dropping a binding one of
/// those reads would leave a free variable behind.
fn count_var_uses(
    expr: &PseudoExpr,
    ids: &mut HashMap<VarId, usize>,
    names: &mut HashMap<String, usize>,
) {
    preorder(expr, |expr| {
        if let PseudoExpr::Var { name, id } = expr {
            if let Some(v) = id {
                *ids.entry(*v).or_insert(0) += 1;
            }
            *names.entry(name.clone()).or_insert(0) += 1;
        }
    })
}

fn prune_payload_lets(
    expr: PseudoExpr,
    payloads: &HashMap<VarId, (VarId, String, ContextType)>,
    ids: &HashMap<VarId, usize>,
    names: &HashMap<String, usize>,
) -> PseudoExpr {
    rewrite_bottom_up(expr, |expr| {
        if let PseudoExpr::Let {
            name,
            id: Some(bid),
            body,
            ..
        } = &expr
            && payloads.contains_key(bid)
            && ids.get(bid).copied().unwrap_or(0) == 0
            && names.get(name).copied().unwrap_or(0) == 0
        {
            return (**body).clone();
        }
        expr
    })
}

/// `let f = <v>.fields` where `v` is a record we have a type for.
fn collect_payload_lets(
    expr: &PseudoExpr,
    types: &HashMap<VarId, CardanoTypeRef>,
    out: &mut HashMap<VarId, (VarId, String, ContextType)>,
) {
    preorder(expr, |expr| {
        if let PseudoExpr::Let {
            id: Some(bid),
            value,
            ..
        } = expr
            && let PseudoExpr::FieldAccess { record, selector } = value.as_ref()
            && selector.as_pretty_name() == "fields"
            && let PseudoExpr::Var { id: Some(v), name } = record.as_ref()
            && let Some(CardanoTypeRef::Record(t)) = types.get(v)
        {
            out.insert(*bid, (*v, name.clone(), *t));
        }
    })
}

fn rewrite_payload_uses(
    expr: PseudoExpr,
    ctx: &RenderCtx,
    payloads: &HashMap<VarId, (VarId, String, ContextType)>,
) -> PseudoExpr {
    rewrite_bottom_up(expr, |expr| {
        let (payload, index) = match &expr {
            // `<payload>.head` is element 0.
            PseudoExpr::FieldAccess { record, selector } if selector.as_pretty_name() == "head" => {
                match record.as_ref() {
                    PseudoExpr::Var { id: Some(v), .. } => (*v, 0usize),
                    _ => return expr,
                }
            }
            PseudoExpr::IndexAccess { collection, index } => match collection.as_ref() {
                PseudoExpr::Var { id: Some(v), .. } => (*v, *index),
                _ => return expr,
            },
            _ => return expr,
        };
        let Some((record_id, record_name, record_type)) = payloads.get(&payload) else {
            return expr;
        };
        let Some(field) = field_at(*record_type, index, ctx) else {
            return expr;
        };
        PseudoExpr::field_access(
            PseudoExpr::var_with_id(record_name, *record_id),
            field.display_name(),
        )
    })
}

/// The parameter list of a `Let`-bound callable.
fn callable_params(value: &PseudoExpr) -> Option<&[Binder]> {
    match value {
        PseudoExpr::Lambda { params, .. } | PseudoExpr::RecFn { params, .. } => Some(params),
        _ => None,
    }
}

// Shape recognisers

/// Whether `fid` names a one-parameter recursive list rebuild that
/// passes each head through untouched: somewhere in its body it emits
/// `Cons(<head binder>, <self>(<tail binder>))`, and it has a nil
/// branch.
///
/// That rules out the wrappers position alone would let through. `map`
/// wraps the head (`Cons(g(h), self(t))`); `reverse` needs an
/// accumulator, so it is not one-parameter; `swap` does not recurse.
/// What is left copies the spine, which is what makes position `i` of
/// the result position `i` of the input.
fn is_identity_list_rebuild(fid: VarId, defs: &HashMap<VarId, &PseudoExpr>) -> bool {
    let Some(def) = defs.get(&fid).copied() else {
        return false;
    };
    let (params, body) = match def {
        PseudoExpr::Lambda { params, body } => (params, body.as_ref()),
        PseudoExpr::RecFn { params, body, .. } => (params, body.as_ref()),
        _ => return false,
    };
    if params.len() != 1 {
        return false;
    }
    // The head is the arm's own head, untouched.
    cons_cells_all_agree(
        def,
        body,
        |head, arm_head| matches!(head, PseudoExpr::Var { id: Some(h), .. } if *h == arm_head),
    ) && emits_nil(body)
}

/// Whether every cons cell the function builds rebuilds the list from
/// the arm that produced it — and there is at least one.
///
/// The three things a cell has to show, which a free structural scan
/// does not:
///
///   * its head comes from THIS arm's head binder (`head_ok` decides
///     whether it may be wrapped),
///   * its tail is the recursive call on THIS arm's tail binder,
///   * that call goes to the enclosing `rec fn` itself.
///
/// Without all three, `Cons(f(tail), self(head))` or a cell borrowed
/// from an unrelated nested lambda would pass, and the result's slots
/// would not be the input's elements.
fn cons_cells_all_agree(
    def: &PseudoExpr,
    body: &PseudoExpr,
    head_ok: impl Fn(&PseudoExpr, VarId) -> bool,
) -> bool {
    let mut cells = 0usize;
    let self_id = match def {
        PseudoExpr::RecFn { name, .. } => Some(name.var_id()),
        _ => None,
    };
    if !walk_cells(body, self_id, None, &head_ok, &mut cells) {
        return false;
    }
    cells > 0
}

/// `scope` is the innermost `(head, tail)` binder pair in scope — a cons
/// `when` arm, or the two-parameter continuation a list eliminator takes.
fn walk_cells(
    expr: &PseudoExpr,
    self_id: Option<VarId>,
    scope: Option<(VarId, VarId)>,
    head_ok: &impl Fn(&PseudoExpr, VarId) -> bool,
    cells: &mut usize,
) -> bool {
    let mut stack: Vec<(&PseudoExpr, Option<VarId>, Option<(VarId, VarId)>)> =
        vec![(expr, self_id, scope)];

    while let Some((expr, self_id, scope)) = stack.pop() {
        if let Some((head, tail)) = cons_cell_parts(expr) {
            *cells += 1;
            let (Some((arm_head, arm_tail)), Some(self_id)) = (scope, self_id) else {
                return false;
            };
            if !head_ok(head, arm_head) || !is_self_call_on(tail, self_id, arm_tail) {
                return false;
            }
        }
        // Descend, refreshing the binder pair where a new one comes into
        // scope. A nested `rec fn` brings its own self.
        match expr {
            PseudoExpr::RecFn { name, params, body } => {
                let inner_scope = two_binders(params).or(scope);
                stack.push((body, Some(name.var_id()), inner_scope));
            }
            PseudoExpr::Lambda { params, body } => {
                let inner_scope = two_binders(params).or(scope);
                stack.push((body, self_id, inner_scope));
            }
            PseudoExpr::When {
                subject, clauses, ..
            } => {
                for c in clauses.iter().rev() {
                    let arm_scope = cons_binders(&c.pattern)
                        .map(|(h, t)| (h.var_id(), t.var_id()))
                        .or(scope);
                    stack.push((&c.body, self_id, arm_scope));
                }
                stack.push((subject, self_id, scope));
            }
            other => {
                for c in children(other).into_iter().rev() {
                    stack.push((c, self_id, scope));
                }
            }
        }
    }
    true
}

/// Exactly two parameters — the shape a cons continuation takes.
fn two_binders(params: &[Binder]) -> Option<(VarId, VarId)> {
    match params {
        [head, tail] => Some((head.var_id(), tail.var_id())),
        _ => None,
    }
}

/// `<self>(Var(arm_tail))`, through the `force` the lowering leaves on a
/// recursive callee.
fn is_self_call_on(tail: &PseudoExpr, self_id: VarId, arm_tail: VarId) -> bool {
    let PseudoExpr::Apply { function, args } = tail else {
        return false;
    };
    args.len() == 1
        && matches!(strip_force(function), PseudoExpr::Var { id: Some(f), .. } if *f == self_id)
        && matches!(&args[0], PseudoExpr::Var { id: Some(t), .. } if *t == arm_tail)
}

/// The `(head, tail)` of a single-element cons cell, in either spelling.
fn cons_cell_parts(expr: &PseudoExpr) -> Option<(&PseudoExpr, &PseudoExpr)> {
    match expr {
        PseudoExpr::Constr { tag: 1, fields, .. } if fields.len() == 2 => {
            Some((&fields[0], &fields[1]))
        }
        PseudoExpr::List {
            elements,
            tail: Some(tail),
        } if elements.len() == 1 => Some((&elements[0], tail.as_ref())),
        _ => None,
    }
}

/// Look through the `force` wrapper the lowering leaves on a recursive
/// callee.
fn strip_force(expr: &PseudoExpr) -> &PseudoExpr {
    let mut current = expr;
    while let PseudoExpr::Force(inner) = current {
        current = inner.as_ref();
    }
    current
}

/// The rebuild's empty-list result: a nullary tag-0 constructor, or the
/// `[]` literal the recovery folds it into.
fn emits_nil(expr: &PseudoExpr) -> bool {
    let mut stack: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr {
            PseudoExpr::Constr { tag: 0, fields, .. } if fields.is_empty() => return true,
            PseudoExpr::List { elements, tail } if elements.is_empty() && tail.is_none() => {
                return true;
            }
            _ => {}
        }
        for child in children(expr).into_iter().rev() {
            stack.push(child);
        }
    }
    false
}

/// The `(head, tail)` binders of a cons pattern.
///
/// Two spellings reach render-prep: the surface `[x, ..rest]` list
/// pattern, and the constructor form the Scott/Data list recogniser
/// leaves behind — tag 1, arity 2, `ConstructorShape::Known(Cons)`.
fn cons_binders(pattern: &WhenPattern) -> Option<(Binder, Binder)> {
    match pattern {
        WhenPattern::List { elements, tail } if elements.len() == 1 => {
            Some((elements[0].clone(), tail.clone()?))
        }
        WhenPattern::Constructor { fields, shape, .. }
            if matches!(shape, ConstructorShape::Known(KnownConstructor::Cons))
                && fields.len() == 2 =>
        {
            Some((fields[0].clone(), fields[1].clone()))
        }
        _ => None,
    }
}

/// Only decompiler-minted placeholders are renamed; anything a naming
/// pass already chose deliberately is left as it is.
fn is_synthetic(name: &str) -> bool {
    let stem = name.trim_start_matches('_');
    for prefix in ["v_", "variant_", "field_", "x_", "item_", "head_", "arg_"] {
        if let Some(rest) = stem.strip_prefix(prefix)
            && rest.chars().all(|c| c.is_ascii_digit() || c == '_')
        {
            return true;
        }
    }
    stem == "variant" || stem == "head" || stem.is_empty()
}

#[cfg(test)]
mod tests;
