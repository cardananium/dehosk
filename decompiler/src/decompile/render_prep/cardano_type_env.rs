//! Forward, fail-closed Cardano type-env for render-prep: the type-based
//! alternative to re-deriving a `when` subject's Cardano type from its
//! binder name at each naming site.
//!
//! The early forward propagator (`cardano_context_naming`) runs before
//! render-prep materializes several Cardano shapes — notably the
//! `let w = (when … is { Proposing(_, proposal_procedure) ->
//! proposal_procedure; _ -> fail }).fields[2]` chain that
//! `bind_cardano_sum_when_payload` synthesizes. Without a type-env the
//! late namer [`when_subject_cardano_sum`](super::name_cardano_sum_arms::when_subject_cardano_sum)
//! has to re-derive the subject type from the binder name, so a bare
//! `let w = <GovernanceAction>` (no recognized name) stays `Unknown_E_*`.
//!
//! The env is keyed by `VarId`, not name — `VarId`s are program-unique
//! and survive renaming, so aliasing / shadowing can never conflate two
//! binders. Consumers query it type-first and keep the name shapes as a
//! fallback. A [`CardanoTypeRef`] (the record∪sum∪list-element union of
//! the context schema) is built once over the
//! post-`bind_cardano_sum_when_payload` AST and threaded read-only.
//!
//! Every transfer returns `None` on the slightest uncertainty (unknown
//! parent, a `None` field type-ref, disagreeing `when` arms, an escaping
//! value). It is stricter than the early engine's `infer_type`: the
//! `FieldAccess` rule requires a `Record` parent and verifies the field
//! belongs to that record at this version, omitting the early engine's
//! by-name-in-isolation fallthroughs (`x.value` / `x.datum` / `x.index`
//! with an unknown parent). The single seed is the validator-entry
//! `script_context` param → `Record(ScriptContext)`; no entry / no render
//! version → empty env → fully inert.

use std::collections::{HashMap, HashSet};

use crate::decompile::ScriptVersion;
use crate::decompile::simplify::postprocess::{
    CardanoTypeRef, ContextField, ContextType, SumTypeId, builtin_cardano_return, context_field_at,
    context_field_type_full, sum_type_constructor_fields,
};
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

use super::ctx::RenderCtx;
use super::rename_hygiene::find_param_cons_tail;
use super::scope_recurse::rewrite_bottom_up;

// [`walk`] threads a type ENVIRONMENT as it goes, and the moment an entry enters that
// env is load-bearing: a `let`'s value type is bound after the value's subtree and
// before the body, and a `when` arm's payload types are bound after the subject's
// subtree and before THAT arm's guard and body. Each of those points is its own step on
// the stack. Collapsing them into "process all children, then run the node's logic"
// costs a binder its type, which surfaces as a `.fields[N]` where a field name belongs.

/// A render-prep-stage Cardano type environment: the statically-known
/// [`CardanoTypeRef`] of each resolved binder, keyed by [`VarId`].
#[derive(Default)]
pub(super) struct CardanoTypeEnv {
    types: HashMap<VarId, CardanoTypeRef>,
}

impl CardanoTypeEnv {
    /// The Cardano type bound to `vid`, if known.
    pub(super) fn get(&self, vid: VarId) -> Option<CardanoTypeRef> {
        self.types.get(&vid).copied()
    }

    fn bind(&mut self, vid: VarId, ty: CardanoTypeRef) {
        // VarIds are program-unique, so the flat map doubles as both the
        // inference scratch scope and the output: a payload binder bound
        // inside one `when` arm never collides with anything else.
        self.types.insert(vid, ty);
    }

    /// Read-only: the sum type a subject EXPRESSION infers to, if any. Used by
    /// `when_subject_cardano_sum` to resolve subjects that are not bare binders
    /// (e.g. `entry.1st` — the key of a sum-keyed map iteration).
    pub(super) fn infer_sum(&self, expr: &PseudoExpr, version: ScriptVersion) -> Option<SumTypeId> {
        infer(expr, version, self).and_then(CardanoTypeRef::sum)
    }

    /// Fold in types another pass settled, WITHOUT overwriting.
    /// `name_context_field_peel` carries the schema through a
    /// PlutusTx-shaped context, which this env's own walk cannot reach —
    /// nothing there indexes a record, so there is no `<X>.fields[N]`
    /// for it to key off.
    ///
    /// Where both have an opinion this one keeps its own. The peel
    /// reasons from POSITION in the context schema and so types a binder
    /// by where it was peeled from; the walk reasons from how the value
    /// is USED, which is the stronger evidence when it exists —
    /// overwriting it costs `NoDatum` its name.
    pub(super) fn fill_gaps(&mut self, types: impl IntoIterator<Item = (VarId, CardanoTypeRef)>) {
        for (vid, ty) in types {
            self.types.entry(vid).or_insert(ty);
        }
    }

    /// Test-only: inject a typed binder directly (to exercise consumers that
    /// query the env without running the full propagator).
    #[cfg(test)]
    pub(crate) fn debug_insert(&mut self, vid: VarId, ty: CardanoTypeRef) {
        self.bind(vid, ty);
    }
}

/// Build the forward Cardano type-env over `expr`. Version comes from the
/// [`RenderCtx`]; `None` (versionless tests / debug bundles) defaults to V2,
/// under which the V3-only schema chains self-gate to `None`, leaving the env
/// inert for them.
pub(super) fn build_cardano_type_env(expr: &PseudoExpr, ctx: &RenderCtx) -> CardanoTypeEnv {
    build_env_at(expr, ctx.version_or_v2())
}

/// The one env construction, shared by every consumer so none of them can drift
/// into seeing a smaller env than the others.
///
/// Two phases: the forward `walk`, then the interproc param seed — a rec-fn
/// first param fed only a typed value at every call site (or its own recursive
/// cons-tail) IS that type. Seeding pre-binds it and the re-walk then types the
/// param's own body (`[entry, ..]` cons-head, `entry.1st` key, `entry.fields[N]`).
fn build_env_at(expr: &PseudoExpr, version: ScriptVersion) -> CardanoTypeEnv {
    let mut env = CardanoTypeEnv::default();
    walk(expr, version, &mut env, false);
    if seed_interproc_params(expr, &mut env, version) {
        walk(expr, version, &mut env, false);
    }
    env
}

/// Resolve positional `<record>.fields[N]` accessors to the schema-named field
/// (`proposal_procedure.fields[2]` → `proposal_procedure.governance_action`)
/// for ANY record the forward type-env can infer — the type-driven counterpart
/// to `resolve_tx_info_field_indices`, which only handles the name-anchored
/// `tx_info`/`script_context` records.
///
/// Pure presentational relabel: `<X>.fields[N]` and `<X>.<field>` decode the
/// identical Data list element, so no runtime check is introduced. Fail-closed:
///   - requires an EXPLICIT render version (no-op at `None`, like
///     `resolve_tx_info_field_indices`, so versionless renders are untouched);
///   - fires only when the record provably infers to `Record(T)` AND `N` is a
///     valid field index of `T` at this version (out-of-range stays positional).
pub(super) fn resolve_cardano_field_indices(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    let Some(version) = ctx.version() else {
        return expr;
    };
    let env = build_env_at(&expr, version);
    rewrite_field_indices(expr, version, &env)
}

fn rewrite_field_indices(
    expr: PseudoExpr,
    version: ScriptVersion,
    env: &CardanoTypeEnv,
) -> PseudoExpr {
    // Children first: an inner `.fields[N]` is resolved before the outer one
    // examines it. VarIds are stable across the rewrite, and the resolved
    // `.<field>` form infers to the same type as `.fields[N]`, so re-inferring
    // a partially-rewritten record is consistent.
    rewrite_bottom_up(expr, |expr| {
        if let PseudoExpr::IndexAccess { collection, index } = &expr
            && let PseudoExpr::FieldAccess { record, selector } = collection.as_ref()
            && is_fields_selector(selector)
            && let Some(CardanoTypeRef::Record(ct)) = infer(record, version, env)
            && let Some(field) = context_field_at(ct, *index, version)
        {
            return PseudoExpr::FieldAccess {
                record: record.clone(),
                selector: FieldSelector::NamedField(field.display_name().to_string()),
            };
        }
        expr
    })
}

/// Pre-order walk that records every resolvable binder's type into `env`: the
/// entry `script_context` param, `let` values, and `when` constructor-arm
/// payloads.
///
/// `in_lambda` is `true` once inside a lambda/rec-fn BODY, and the
/// `script_context` seed fires ONLY at the top level (`!in_lambda`): the
/// validator entry is a top-level lambda (or a top-level `let`-bound one),
/// never one nested inside another lambda's body, so a coincidentally
/// `script_context`-named param on a NESTED lambda is not mis-seeded.
fn walk(expr: &PseudoExpr, version: ScriptVersion, env: &mut CardanoTypeEnv, in_lambda: bool) {
    let mut steps: Vec<WalkStep> = vec![WalkStep::Enter(expr, in_lambda)];

    while let Some(step) = steps.pop() {
        match step {
            WalkStep::Enter(expr, in_lambda) => match expr {
                PseudoExpr::Lambda { params, body } => {
                    if !in_lambda {
                        seed_params(params, env);
                    }
                    steps.push(WalkStep::Enter(body.as_ref(), true));
                }
                PseudoExpr::RecFn { params, body, .. } => {
                    if !in_lambda {
                        seed_params(params, env);
                    }
                    steps.push(WalkStep::Enter(body.as_ref(), true));
                }
                PseudoExpr::Let {
                    id, value, body, ..
                } => {
                    // Descend the value FIRST (binds any nested `when` payloads /
                    // sub-`let`s), THEN infer it read-only and bind this binder.
                    steps.push(WalkStep::Enter(body.as_ref(), in_lambda));
                    steps.push(WalkStep::BindLet(value.as_ref(), *id));
                    steps.push(WalkStep::Enter(value.as_ref(), in_lambda));
                }
                PseudoExpr::When {
                    subject, clauses, ..
                } => {
                    // Descend the subject FIRST (binds its nested payloads), THEN infer
                    // it read-only for the per-arm payload binding.
                    steps.push(WalkStep::WhenArms(subject.as_ref(), clauses, in_lambda));
                    steps.push(WalkStep::Enter(subject.as_ref(), in_lambda));
                }
                other => {
                    for child in super::scope_recurse::children(other).into_iter().rev() {
                        steps.push(WalkStep::Enter(child, in_lambda));
                    }
                }
            },
            WalkStep::BindLet(value, id) => {
                if let (Some(vid), Some(ty)) = (id, infer(value, version, env)) {
                    env.bind(vid, ty);
                }
            }
            WalkStep::WhenArms(subject, clauses, in_lambda) => {
                // Inferred ONCE, right after the subject's subtree and before any
                // arm is entered — here, so no
                // arm's own bindings can feed back into the subject's type.
                let subject_ty = infer(subject, version, env);
                for c in clauses.iter().rev() {
                    steps.push(WalkStep::Enter(&c.body, in_lambda));
                    if let Some(g) = &c.guard {
                        steps.push(WalkStep::Enter(g, in_lambda));
                    }
                    steps.push(WalkStep::BindArm(subject_ty, &c.pattern));
                }
            }
            WalkStep::BindArm(subject_ty, pattern) => {
                bind_arm_payload(subject_ty, pattern, version, env);
            }
        }
    }
}

/// One pending step of [`walk`]'s explicit stack.
enum WalkStep<'a> {
    /// A node still to be visited, with the `in_lambda` flag for that edge.
    Enter(&'a PseudoExpr, bool),
    /// Between a `let`'s value and its body: infer the value read-only and
    /// bind the `let` binder.
    BindLet(&'a PseudoExpr, Option<VarId>),
    /// Between a `when`'s subject and its arms: infer the subject once, then
    /// queue each arm's payload binding + guard + body, in clause order.
    WhenArms(&'a PseudoExpr, &'a [WhenClause], bool),
    /// One arm's payload binding, sitting between the subject and THAT arm's
    /// guard and body.
    BindArm(Option<CardanoTypeRef>, &'a WhenPattern),
}

/// Seed the validator-entry `script_context` param with `Record(ScriptContext)`.
/// Name-gated to the reserved, decompiler-minted entry-param name, and (via the
/// caller's `!in_lambda` gate) to the top-level entry lambda.
fn seed_params(params: &[Binder], env: &mut CardanoTypeEnv) {
    for p in params {
        if p.as_str() == "script_context" {
            env.bind(
                p.var_id(),
                CardanoTypeRef::Record(ContextType::ScriptContext),
            );
        }
    }
}

/// Bind a `when` arm's payload binders to their schema types, for the
/// chainable subject shapes:
///
///   * `Sum(T)` — a Cardano sum: bind each payload binder from
///     `sum_type_constructor_fields`, EXACT-arity gated.
///   * `Option<T>` — the `Some(x)` arm (`Some` = Constr 0, one field)
///     binds `x` to the unwrapped inner type; `None` (tag 1) is nullary. This
///     lets `when address.stake_credential is { Some(c) -> when c is { Inline …
///     } }` type `c : StakeCredential`.
///   * a LIST cons `[head, ..tail]` over a list-like subject (`List<T>` or a
///     key-sum map) binds each head element to the element type and `tail` to
///     the list type. For a `MapKeyedBySum`, `head : SumKeyedPair`, so a later
///     `head.1st` types the (chainable) key sum of a `withdrawals`/`votes`
///     iteration.
///
/// Fields whose schema type-ref is `None` are left unbound (fail-closed).
fn bind_arm_payload(
    subject_ty: Option<CardanoTypeRef>,
    pattern: &WhenPattern,
    version: ScriptVersion,
    env: &mut CardanoTypeEnv,
) {
    // List cons-pattern over a list-like subject.
    if let WhenPattern::List { elements, tail } = pattern {
        if let Some(subj) = subject_ty
            && let Some(elem) = subj.element_type()
        {
            for head in elements {
                env.bind(head.var_id(), elem);
            }
            if let Some(t) = tail {
                env.bind(t.var_id(), subj);
            }
        }
        return;
    }
    let WhenPattern::Constructor { tag, fields, .. } = pattern else {
        return;
    };
    match subject_ty {
        // `Option<T>`: the `Some(x)` arm (tag 0, arity 1) binds `x : T`.
        Some(opt @ (CardanoTypeRef::OptionOfRecord(_) | CardanoTypeRef::OptionOfSum(_))) => {
            if *tag == 0
                && fields.len() == 1
                && let Some(inner) = opt.option_inner()
            {
                env.bind(fields[0].var_id(), inner);
            }
        }
        Some(CardanoTypeRef::Sum(sum_id)) => {
            let Some(defs) = sum_type_constructor_fields(sum_id, *tag, version) else {
                return;
            };
            // EXACT-arity gate (fail-closed): an arm whose field count disagrees
            // with the ABI is NOT this constructor (a coincidental tag), so binding
            // even a prefix mis-types a binder and leaks a wrong sum type downstream,
            // where the inner-`when` arity gate would not catch it.
            if fields.len() != defs.len() {
                return;
            }
            for (binder, (_cf, ftr)) in fields.iter().zip(defs.iter()) {
                if let Some(ftr) = ftr {
                    env.bind(binder.var_id(), CardanoTypeRef::from_field_type_ref(*ftr));
                }
            }
        }
        _ => {}
    }
}

/// Infer the Cardano type of a value expression. Fail-closed: `None` on any
/// uncertainty. READ-ONLY — `walk` binds every `let`-value and `when`-payload
/// BEFORE calling `infer` on the enclosing expression, so `infer` may also run
/// after the env is fully built (as `resolve_cardano_field_indices` does)
/// without a `&mut`.
///
/// Every operand is typed before the rule runs. `infer` is read-only over
/// `env`, so that extra work cannot change an answer.
fn infer(
    expr: &PseudoExpr,
    version: ScriptVersion,
    env: &CardanoTypeEnv,
) -> Option<CardanoTypeRef> {
    let mut steps: Vec<InferStep> = vec![InferStep::Eval(expr)];
    let mut vals: Vec<Option<CardanoTypeRef>> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            InferStep::Eval(expr) => match expr {
                PseudoExpr::Var { id: Some(vid), .. } => vals.push(env.get(*vid)),

                // `<record>.<field>` — only a `Record` parent resolves, and the
                // field must actually belong to that record at this version.
                PseudoExpr::FieldAccess { record, selector } => {
                    steps.push(InferStep::Field(selector));
                    steps.push(InferStep::Eval(record.as_ref()));
                }

                PseudoExpr::IndexAccess { collection, index } => {
                    // `<record>.fields[i]` — positional projection off a Record value.
                    if let PseudoExpr::FieldAccess { record, selector } = collection.as_ref()
                        && is_fields_selector(selector)
                    {
                        steps.push(InferStep::FieldsIndex(*index));
                        steps.push(InferStep::Eval(record.as_ref()));
                    } else {
                        // `xs[i]` on a list-of-T → element type T.
                        steps.push(InferStep::ElementOf);
                        steps.push(InferStep::Eval(collection.as_ref()));
                    }
                }

                PseudoExpr::When { clauses, .. } => {
                    let arms: Vec<&PseudoExpr> = clauses
                        .iter()
                        .filter(|c| !(is_diverging_arm(&c.body) || is_option_none(&c.body)))
                        .map(|c| &c.body)
                        .collect();
                    steps.push(InferStep::WhenJoin(arms.len()));
                    for body in arms.into_iter().rev() {
                        steps.push(InferStep::Eval(body));
                    }
                }

                // `Some(x)` → `Option<T>`. This is what an inlined `list.head` leaves
                // behind: `when xs is { [] -> None; [x, ..] -> Some(x) }`, whose value
                // an `expect Some(p) = …` then unwraps. Typing the construction lets
                // `bind_arm_payload`'s existing Option rule bind `p : T`, which is
                // otherwise unreachable — nothing else in the chain names the type.
                //
                // `Known(Some)` is name+tag+arity checked by `ConstructorShape`, so a
                // user ADT cannot drift in here. Only the two flat Option refs exist,
                // so an `Option<List<…>>` / `Option<Option<…>>` inner fails closed.
                PseudoExpr::Constr {
                    shape: ConstructorShape::Known(KnownConstructor::Some),
                    fields,
                    ..
                } => match fields.first() {
                    Some(inner) => {
                        steps.push(InferStep::SomeOf);
                        steps.push(InferStep::Eval(inner));
                    }
                    None => vals.push(None),
                },

                PseudoExpr::BuiltinCall { name, args } => {
                    steps.push(InferStep::Builtin(*name, args.len()));
                    for a in args.iter().rev() {
                        steps.push(InferStep::Eval(a));
                    }
                }

                // A `let … in` used as a value: its type is its body's; `walk` has
                // already bound the let binder.
                PseudoExpr::Let { body, .. } => steps.push(InferStep::Eval(body.as_ref())),

                _ => vals.push(None),
            },
            InferStep::Field(selector) => {
                let parent = vals.pop().expect("field access parent");
                vals.push(field_access_type(parent, selector, version));
            }
            InferStep::FieldsIndex(index) => {
                let parent = vals.pop().expect("fields index parent");
                vals.push(fields_index_type(parent, index, version));
            }
            InferStep::ElementOf => {
                let collection = vals.pop().expect("index access collection");
                vals.push(collection.and_then(|t| t.element_type()));
            }
            InferStep::SomeOf => {
                let inner = vals.pop().expect("Some payload");
                vals.push(match inner {
                    Some(CardanoTypeRef::Record(ct)) => Some(CardanoTypeRef::OptionOfRecord(ct)),
                    Some(CardanoTypeRef::Sum(st)) => Some(CardanoTypeRef::OptionOfSum(st)),
                    _ => None,
                });
            }
            InferStep::Builtin(name, argc) => {
                let at = vals.len() - argc;
                let arg_types: Vec<Option<CardanoTypeRef>> = vals.split_off(at);
                vals.push(builtin_cardano_return(name, &arg_types));
            }
            InferStep::WhenJoin(arms) => {
                let at = vals.len() - arms;
                let arm_types = vals.split_off(at);
                vals.push(join_when_arms(arm_types));
            }
        }
    }

    vals.pop().expect("infer leaves exactly one result")
}

/// One pending step of [`infer`]'s explicit stack: either a sub-expression
/// still to be typed, or the node-level rule that combines the results its
/// operands left on the value stack.
enum InferStep<'a> {
    Eval(&'a PseudoExpr),
    /// `<parent>.<selector>`.
    Field(&'a FieldSelector),
    /// `<parent>.fields[i]`.
    FieldsIndex(usize),
    /// `<collection>[i]` on a list.
    ElementOf,
    /// `Some(<inner>)`.
    SomeOf,
    Builtin(crate::BuiltinId, usize),
    /// The type-join over this many already-typed `when` arms.
    WhenJoin(usize),
}

/// The `<record>.<field>` rule, split out so [`infer`]'s stack machine can
/// keep the `?`-chain verbatim.
fn field_access_type(
    parent: Option<CardanoTypeRef>,
    selector: &FieldSelector,
    version: ScriptVersion,
) -> Option<CardanoTypeRef> {
    let parent = parent?;
    // `entry.1st` on a key-sum map ENTRY → the key sum (the chainable
    // key of a `withdrawals`/`votes`/… map). `.2nd` (the value) is not
    // tracked.
    if selector.is_pair_fst() {
        return parent.pair_first_sum().map(CardanoTypeRef::Sum);
    }
    if selector.is_pair_snd() {
        return None;
    }
    let ct = parent.record()?;
    let name = selector_field_name(selector)?;
    let field = ContextField::from_display_name(name)?;
    if !field_belongs_to(ct, field, version) {
        return None;
    }
    context_field_type_full(field, version)
}

/// The `<record>.fields[i]` positional-projection rule.
fn fields_index_type(
    parent: Option<CardanoTypeRef>,
    index: usize,
    version: ScriptVersion,
) -> Option<CardanoTypeRef> {
    let ct = parent?.record()?;
    let field = context_field_at(ct, index, version)?;
    context_field_type_full(field, version)
}

/// The type-join for a `when` used as a value, over the arm types [`infer`]
/// already computed. A provably-diverging arm (`-> fail`) is bottom and was
/// excluded before it got here; every remaining (value-producing) arm must
/// infer the SAME `Some(ty)` — any `None` or disagreement yields `None`.
/// READ-ONLY: `walk` has already bound every clause's payload binders, so the
/// arm bodies resolve their names from the env directly.
fn join_when_arms(arm_types: Vec<Option<CardanoTypeRef>>) -> Option<CardanoTypeRef> {
    let mut joined: Option<CardanoTypeRef> = None;
    let mut value_arms = 0usize;
    for arm_ty in arm_types {
        let arm_ty = arm_ty?;
        match joined {
            None if value_arms == 0 => joined = Some(arm_ty),
            Some(prev) if prev == arm_ty => {}
            _ => return None,
        }
        value_arms += 1;
    }
    if value_arms == 0 { None } else { joined }
}

/// Whether an arm body is the bare `None` constructor. `None : Option<T>` for
/// every `T`, so like a diverging arm it constrains the join not at all — the
/// `Some(x)` arm alone decides the inner type. Without this the `[] -> None`
/// arm of an inlined `list.head` would infer `None` and sink the whole join.
fn is_option_none(body: &PseudoExpr) -> bool {
    matches!(
        body,
        PseudoExpr::Constr {
            shape: ConstructorShape::Known(KnownConstructor::None),
            ..
        }
    )
}

/// Whether an arm body provably diverges (`fail`) and so contributes no value
/// to the `when`-value type join. Both shapes count: the bare `Error` node
/// `collapse_trace_fail_let` produces, and `BuiltinCall(Error)`.
fn is_diverging_arm(body: &PseudoExpr) -> bool {
    matches!(body, PseudoExpr::Error { .. })
        || matches!(body, PseudoExpr::BuiltinCall { name, .. } if *name == crate::BuiltinId::Error)
}

/// Whether `field` is a positional field of record `ct` at `version` — the
/// membership check that keeps the `FieldAccess` rule from typing a
/// coincidentally-named selector on the wrong record.
fn field_belongs_to(ct: ContextType, field: ContextField, version: ScriptVersion) -> bool {
    (0..)
        .map_while(|i| context_field_at(ct, i, version))
        .any(|f| f == field)
}

/// The legacy field name carried by a named/context selector, or `None` for
/// the structural accessors (`fst`/`snd`/`head`) which carry no field name.
fn selector_field_name(sel: &FieldSelector) -> Option<&str> {
    match sel {
        FieldSelector::NamedField(n) | FieldSelector::ContextField(n) => Some(n.as_str()),
        _ => None,
    }
}

/// Whether `sel` is the structural `.fields` accessor (the `Constr` payload
/// list), the parent of a `<record>.fields[i]` positional projection.
fn is_fields_selector(sel: &FieldSelector) -> bool {
    matches!(sel, FieldSelector::NamedField(n) if n == "fields")
}

// ===== Interproc rec-fn first-param typing =====
// Mirrors the enumerable / all-call-sites-same / recursive-tail gate of
// `resolve_tx_info_field_indices::qualify_interproc_list_params`, but TYPES the
// param into the env instead of renaming it: a helper like
// `any(un_map_data(tx_info.withdrawals))` then types its `list` param, its
// body's `[entry, ..]` cons-head, and its `entry.1st` key.

#[derive(Default)]
struct InterScan {
    /// canonical rec-fn id → (first-param VarId, the cons-`tail` VarId of its
    /// `when param0 is { [_, ..tail] }` recursion witness).
    recs: HashMap<VarId, (VarId, VarId)>,
    /// rec-fn self-name id → canonical id (`let f = rec fn g(..)` ⇒ g → f).
    aliases: HashMap<VarId, VarId>,
    /// ids reached as a VALUE (not an `Apply` head) — not enumerable.
    value_used: HashSet<VarId>,
    /// call-head id → each call's slot-0 argument (cloned).
    slot0: HashMap<VarId, Vec<PseudoExpr>>,
}

/// Returns `true` if it pre-bound at least one param (so the caller re-walks).
fn seed_interproc_params(
    expr: &PseudoExpr,
    env: &mut CardanoTypeEnv,
    version: ScriptVersion,
) -> bool {
    let mut scan = InterScan::default();
    scan_calls(expr, &mut scan);
    let mut bound_any = false;
    for (canon, (param0, cons_tail)) in &scan.recs {
        let alias_ids: Vec<VarId> = scan
            .aliases
            .iter()
            .filter(|(_, c)| *c == canon)
            .map(|(r, _)| *r)
            .collect();
        // Enumerable: none of the function's ids may be used as a value.
        if scan.value_used.contains(canon) || alias_ids.iter().any(|r| scan.value_used.contains(r))
        {
            continue;
        }
        let mut args: Vec<&PseudoExpr> = Vec::new();
        if let Some(s) = scan.slot0.get(canon) {
            args.extend(s.iter());
        }
        for r in &alias_ids {
            if let Some(s) = scan.slot0.get(r) {
                args.extend(s.iter());
            }
        }
        if args.is_empty() {
            continue;
        }
        // All slot-0 args must be EITHER the same external type `T` (≥1) OR the
        // recursive cons-tail. Any other arg disqualifies (fail-closed).
        let mut ty: Option<CardanoTypeRef> = None;
        let mut has_external = false;
        let mut ok = true;
        for arg in args {
            if matches!(arg, PseudoExpr::Var { id: Some(v), .. } if *v == *cons_tail) {
                continue; // recursive sub-list
            }
            match infer(arg, version, env) {
                Some(t) => {
                    has_external = true;
                    match ty {
                        Some(prev) if prev != t => {
                            ok = false;
                            break;
                        }
                        None => ty = Some(t),
                        _ => {}
                    }
                }
                None => {
                    ok = false;
                    break;
                }
            }
        }
        // The param is structurally a LIST — it is cons-matched `[_, ..tail]`, the
        // recursion witness `find_param_cons_tail` requires. So the agreed call-site
        // type MUST be list-like (`element_type().is_some()`: `MapKeyedBySum` and the
        // `ListOf*` refs pass, `Record`/`Sum`/`Option` do not): a non-list inference
        // (e.g. `f(script_context)` typing the param `Record(ScriptContext)`)
        // contradicts the cons witness and would leak a wrong type into env-aware
        // payload binding.
        if ok
            && has_external
            && let Some(t) = ty
            && t.element_type().is_some()
        {
            env.bind(*param0, t);
            bound_any = true;
        }
    }
    bound_any
}

fn scan_calls(expr: &PseudoExpr, scan: &mut InterScan) {
    let mut work: Vec<&PseudoExpr> = vec![expr];
    while let Some(expr) = work.pop() {
        let mut next: Vec<&PseudoExpr> = Vec::new();
        match expr {
            // `let f = rec fn g(p0, …) { … }` — external callers use `f`, recursive
            // calls use `g`. Canonical = `f`; alias g → f.
            PseudoExpr::Let {
                id: Some(let_id),
                value,
                body,
                ..
            } if matches!(value.as_ref(), PseudoExpr::RecFn { .. }) => {
                if let PseudoExpr::RecFn {
                    name,
                    params,
                    body: fbody,
                } = value.as_ref()
                    && let Some(p0) = params.first()
                    && let Some(cons_tail) = find_param_cons_tail(fbody, p0.var_id())
                {
                    scan.recs.insert(*let_id, (p0.var_id(), cons_tail));
                    scan.aliases.insert(name.var_id(), *let_id);
                }
                next.push(value.as_ref());
                next.push(body.as_ref());
            }
            PseudoExpr::RecFn { name, params, body } => {
                if let Some(p0) = params.first()
                    && let Some(cons_tail) = find_param_cons_tail(body, p0.var_id())
                    && !scan.aliases.contains_key(&name.var_id())
                {
                    scan.recs.insert(name.var_id(), (p0.var_id(), cons_tail));
                }
                next.push(body.as_ref());
            }
            PseudoExpr::Apply { function, args } => {
                if let PseudoExpr::Var { id: Some(fid), .. } = function.as_ref() {
                    if let Some(a0) = args.first() {
                        scan.slot0.entry(*fid).or_default().push(a0.clone());
                    }
                    // function head is a CALL, not a value-use.
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
                for child in super::scope_recurse::children(other) {
                    next.push(child);
                }
            }
        }
        for child in next.into_iter().rev() {
            work.push(child);
        }
    }
}

#[cfg(test)]
mod tests;
