//! Type-directed naming of `when <cardano-subject> is { Constr<tag>(…) }`
//! arms, the late counterpart to the early `cardano_context_naming` pass.
//!
//! The early pass names a `when` subject's `Constr<tag>` constructors
//! only when it can infer the subject's type then; a subject that is a
//! bare binder destructured from a pattern is still `field_N`, so its
//! arms stay `Constr<tag>`. `rename_tx_info_binders` later gives those
//! binders their canonical names (`bound_type`, `purpose`, `upper_bound`)
//! but never touches their constructors. This pass runs after it. For a
//! `when` whose subject resolves through the context schema to a known
//! [`SumTypeId`] it stamps the pattern's `type_hint` (when absent) so
//! the renderer resolves the constructor name (`Finite`,
//! `VerificationKey`, …) from the registry, and renames per-constructor
//! payload binders from the schema (`Minting(field_0)` →
//! `Minting(policy_id)`), rewiring body uses by `VarId`.
//!
//! The subject must be a real binder (`Var { id: Some(_) }`) whose
//! canonical name resolves to a `SumTypeId`, and the arm's `tag` must
//! be a valid constructor index whose schema arity matches the arm's
//! field count. Arity is the strong check — a coincidentally same-named
//! subject, or a sum whose field table is unfilled, stays `Constr<tag>`.
//! All-or-nothing per `when`: naming only some arms would mix named
//! ctors with `Constr<tag>` in one match. Names and tags come from the
//! Plutus ledger ABI (`sum_type_constructor_names` /
//! `sum_type_constructor_fields`).

use crate::decompile::ScriptVersion;
use crate::decompile::blueprint_registry::TypeHintId;
use crate::decompile::simplify::postprocess::{
    CardanoTypeRef, ContextField, SumTypeId, context_field_type_full, sum_type_constructor_fields,
};
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::var_id::VarId;

use super::cardano_type_env::CardanoTypeEnv;
use super::ctx::RenderCtx;
use super::field_kind_inference::{ScalarKind, ScalarKindTable, infer_arm_field_scalars};
use super::rename_synthetic_field_let_binders::{is_synthetic_field_name, rename_var_in};
use super::scope_recurse::{PlainPost, plain_children, rebuild_plain, take};

pub(super) fn name_cardano_sum_arms(
    expr: PseudoExpr,
    env: &CardanoTypeEnv,
    ctx: &RenderCtx,
) -> PseudoExpr {
    // The per-`(TypeHintId, tag, field_idx)` ELIMINATION-site scalar-decode
    // table, computed ONCE over the whole program and threaded read-only
    // into the walk; it gates the `Credential` naming in
    // `clauses_all_nameable`.
    let scalars = infer_arm_field_scalars(&expr);
    walk(expr, ctx, &scalars, env)
}

/// One pending step of [`walk`]'s explicit job stack.
enum Step {
    Enter(PseudoExpr),
    /// The `when` SUBJECT has been walked; resolve the sum type from it and
    /// schedule the clause work. This is a step of its own because it is
    /// the work between the subject descent and
    /// the clause descents — the naming decision reads the walked subject.
    WhenClauses {
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
    },
    Post(PostKind),
}

/// Everything about a node that is NOT one of its child expressions, held
/// while those children are being walked.
enum PostKind {
    Let {
        name: String,
        id: Option<VarId>,
    },
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    When {
        subject_name: Option<Binder>,
        clause_meta: Vec<ClauseMeta>,
    },
    Plain(PlainPost),
}

/// A `when` clause's non-expression parts, plus the order its two child
/// expressions were pushed in.
struct ClauseMeta {
    pattern: WhenPattern,
    has_guard: bool,
    /// `true` when the walk visits the guard before the body — every
    /// path but the successfully-named one, which renames and walks the
    /// body first.
    guard_first: bool,
}

/// A clause with its pattern already stamped and its payload binders
/// already rewired, but its guard/body not yet walked.
struct PreparedClause {
    pattern: WhenPattern,
    guard: Option<PseudoExpr>,
    body: PseudoExpr,
    guard_first: bool,
}

/// Children are pushed in REVERSE so they pop in source order, and are
/// popped off `done` in that same order when the node is rebuilt.
fn walk(
    expr: PseudoExpr,
    ctx: &RenderCtx,
    scalars: &ScalarKindTable,
    env: &CardanoTypeEnv,
) -> PseudoExpr {
    let mut steps: Vec<Step> = vec![Step::Enter(expr)];
    let mut done: Vec<PseudoExpr> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            Step::Enter(expr) => match expr {
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    steps.push(Step::WhenClauses {
                        subject_name,
                        clauses,
                    });
                    steps.push(Step::Enter(subject.into_inner()));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(Step::Post(PostKind::Let { name, id }));
                    steps.push(Step::Enter(body.into_inner()));
                    steps.push(Step::Enter(value.into_inner()));
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(Step::Post(PostKind::Lambda { params }));
                    steps.push(Step::Enter(body.into_inner()));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(Step::Post(PostKind::RecFn { name, params }));
                    steps.push(Step::Enter(body.into_inner()));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(Step::Post(PostKind::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(Step::Enter(c));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            Step::WhenClauses {
                subject_name,
                clauses,
            } => {
                let subject = done.last().expect("when subject");
                // All-or-nothing: name this `when`'s arms only if EVERY
                // constructor arm maps cleanly onto the sum type (valid tag +
                // exact ABI arity). Naming only some would mix named ctors with
                // raw `Unknown_S_*` / `Constr<tag>` in one `when`, which is
                // invalid — a `when` matches a single type. Mismatches arise
                // e.g. when stub-ADT arity unification pads a nullary ctor
                // sharing a merged stub with a wider sibling type.
                let sum_id = when_subject_cardano_sum(subject, ctx.version_or_v2(), env)
                    .filter(|id| clauses_all_nameable(&clauses, *id, ctx, scalars));
                let mut clause_meta = Vec::with_capacity(clauses.len());
                let mut clause_children = Vec::new();
                for c in clauses {
                    let prepared = match sum_id {
                        Some(id) => prepare_clause(c, id, ctx, scalars),
                        None => PreparedClause {
                            pattern: c.pattern,
                            guard: c.guard,
                            body: c.body,
                            guard_first: true,
                        },
                    };
                    clause_meta.push(ClauseMeta {
                        pattern: prepared.pattern,
                        has_guard: prepared.guard.is_some(),
                        guard_first: prepared.guard_first,
                    });
                    match (prepared.guard, prepared.guard_first) {
                        (Some(g), true) => {
                            clause_children.push(g);
                            clause_children.push(prepared.body);
                        }
                        (Some(g), false) => {
                            clause_children.push(prepared.body);
                            clause_children.push(g);
                        }
                        (None, _) => clause_children.push(prepared.body),
                    }
                }
                steps.push(Step::Post(PostKind::When {
                    subject_name,
                    clause_meta,
                }));
                for c in clause_children.into_iter().rev() {
                    steps.push(Step::Enter(c));
                }
            }
            Step::Post(post) => {
                let rebuilt = match post {
                    PostKind::Let { name, id } => {
                        let body = done.pop().expect("let body");
                        let value = done.pop().expect("let value");
                        PseudoExpr::Let {
                            name,
                            id,
                            value: PBox::new(value),
                            body: PBox::new(body),
                        }
                    }
                    PostKind::Lambda { params } => PseudoExpr::Lambda {
                        params,
                        body: PBox::new(done.pop().expect("lambda body")),
                    },
                    PostKind::RecFn { name, params } => PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(done.pop().expect("recfn body")),
                    },
                    PostKind::When {
                        subject_name,
                        clause_meta,
                    } => {
                        let total = 1 + clause_meta
                            .iter()
                            .map(|m| usize::from(m.has_guard) + 1)
                            .sum::<usize>();
                        let mut parts = take(&mut done, total).into_iter();
                        let subject = parts.next().expect("when subject");
                        let clauses = clause_meta
                            .into_iter()
                            .map(|m| {
                                let (guard, body) = if !m.has_guard {
                                    (None, parts.next().expect("when clause body"))
                                } else if m.guard_first {
                                    let g = parts.next().expect("when guard");
                                    (Some(g), parts.next().expect("when clause body"))
                                } else {
                                    let b = parts.next().expect("when clause body");
                                    (Some(parts.next().expect("when guard")), b)
                                };
                                WhenClause {
                                    pattern: m.pattern,
                                    guard,
                                    body,
                                }
                            })
                            .collect();
                        PseudoExpr::When {
                            subject: PBox::new(subject),
                            subject_name,
                            clauses,
                        }
                    }
                    PostKind::Plain(kind) => rebuild_plain(kind, &mut done),
                };
                done.push(rebuilt);
            }
        }
    }

    done.pop().expect("walk leaves exactly one result")
}

/// Resolve a `when` subject expression to a known [`SumTypeId`], when it is
/// a Cardano-context subject. Two subject SHAPES are typed:
///
///   1. A named Cardano BINDER — a bare `Var { id: Some(_) }` whose name
///      resolves to a sum type either directly
///      ([`SumTypeId::from_display_name`]: `purpose`, `credential`,
///      `interval_bound_type`, …) or via its static field type
///      ([`ContextField`] → [`context_field_type_full`]: `bound_type` →
///      `IntervalBoundType`, `payment_credential` → `Credential`, …).
///
///   2. A Cardano-sum FIELD ACCESS — `<record>.<field>` where `<field>` is a
///      [`ContextField`] whose static type is a sum type
///      (`<ctx>.script_info` → `ScriptInfo`, `<bound>.bound_type` →
///      `IntervalBoundType`). The V3 `ScriptContext` exposes `script_info`
///      directly and `when <ctx>.script_info is { … }` is the idiomatic V3
///      dispatch, so this shape MUST be typed for any V3 ScriptInfo naming
///      to fire. The selector may be [`FieldSelector::NamedField`] or
///      [`FieldSelector::ContextField`]; both carry the legacy name. The
///      record sub-expression is NOT itself re-typed — the field NAME alone
///      pins the sum type.
///
/// Why a name match is trustworthy: UPLC is nameless (de Bruijn), so EVERY
/// rendered identifier is synthesized, and the legacy names matched here are
/// minted only by the Cardano-context naming machinery
/// (`cardano_context_naming`, `simplify/control_flow/naming`,
/// `kind_inference`, `rename_tx_info_binders`), never by a generic
/// variable-naming heuristic — a subject binder, or a field SELECTOR,
/// carrying one came from the canonical ScriptContext destructure chain and
/// genuinely IS that sum type. A blueprint-typed subject instead carries a
/// real `type_hint`, which the caller's all-or-nothing gate respects rather
/// than overriding. With [`known_ctor_arity`] pinning exact ABI arity per
/// arm, no VarKind provenance lookup is threaded here.
///
/// `pub(crate)` so the validator-dispatch typing and the arm collector reuse
/// the same subject→`SumTypeId` resolver.
pub(crate) fn when_subject_cardano_sum(
    subject: &PseudoExpr,
    version: ScriptVersion,
    env: &CardanoTypeEnv,
) -> Option<SumTypeId> {
    // (0) TYPE-first: a resolved binder whose forward Cardano type-env entry
    //     is a sum type. Dataflow-based, so it types subjects (e.g. a bare
    //     `let w = <GovernanceAction>`) that no name shape below recognizes;
    //     with no env entry it falls through, making this a strict superset of
    //     the name path.
    if let PseudoExpr::Var { id: Some(vid), .. } = subject
        && let Some(sum) = env.get(*vid).and_then(CardanoTypeRef::sum)
    {
        return Some(sum);
    }
    // (0b) Key-sum map ENTRY projection: `when entry.1st is { … }` where `entry`
    //      is a `withdrawals`/`votes`/… map element — the env types the `.1st`
    //      (Pair.first) projection to the key sum. Only the structural `.1st`
    //      selector, which the name path below never handles.
    if let PseudoExpr::FieldAccess { selector, .. } = subject
        && selector.is_pair_fst()
        && let Some(sum) = env.infer_sum(subject, version)
    {
        return Some(sum);
    }
    match subject {
        // (1) Named Cardano binder.
        PseudoExpr::Var { name, id: Some(_) } => sum_type_for_cardano_name(name, version),
        // (2) Cardano-sum field access: the SELECTOR's legacy name pins the
        //     sum type. A structural selector (`fst`/`snd`/`head`) carries
        //     no legacy field name and falls through to `None`.
        PseudoExpr::FieldAccess { selector, .. } => match selector {
            FieldSelector::NamedField(name) | FieldSelector::ContextField(name) => {
                let field = ContextField::from_display_name(name)?;
                context_field_type_full(field, version)?.sum()
            }
            _ => None,
        },
        _ => None,
    }
}

/// Resolve a Cardano legacy NAME to a [`SumTypeId`]: directly via
/// [`SumTypeId::from_display_name`], else via its static field type
/// ([`ContextField`] → [`context_field_type_full`] → sum).
fn sum_type_for_cardano_name(name: &str, version: ScriptVersion) -> Option<SumTypeId> {
    // Direct sum-type name (`purpose`, `credential`, `interval_bound_type`…).
    if let Some(id) = SumTypeId::from_display_name(name) {
        return Some(id);
    }
    // Field name whose static type is a sum type (`bound_type` →
    // IntervalBoundType, `script_info` → ScriptInfo, `governance_action` →
    // GovernanceAction…).
    let field = ContextField::from_display_name(name)?;
    context_field_type_full(field, version)?.sum()
}

/// Whether EVERY constructor arm of a `when` maps cleanly onto `sum_id`
/// (valid tag + exact ABI arity), with at least one constructor arm;
/// `_`/literal/catch-all-binder arms are ignored. Naming only some arms
/// would mix types in one `when`, which is invalid surface syntax.
fn clauses_all_nameable(
    clauses: &[WhenClause],
    sum_id: SumTypeId,
    ctx: &RenderCtx,
    scalars: &ScalarKindTable,
) -> bool {
    let mut saw_constructor = false;
    for c in clauses {
        if let WhenPattern::Constructor {
            type_hint,
            tag,
            fields,
            ..
        } = &c.pattern
        {
            saw_constructor = true;
            if known_ctor_arity(sum_id, *tag, ctx) != Some(fields.len()) {
                return false;
            }
            // A real (non-stub) hint naming a DIFFERENT type means a
            // user/blueprint ADT is already attached to this arm (e.g. by
            // `adt_disambiguation`), so it is NOT the Cardano sum — leave
            // the whole `when` alone rather than imposing Cardano names
            // over the user typing. A stub hint, or the matching Cardano
            // legacy name, proceeds.
            if let Some(h) = type_hint
                && !is_stub_type_hint(h)
                && h.as_str() != sum_id.display_name()
            {
                return false;
            }
            // Credential field-decode GATE. `Credential` is the merged
            // 2-variant stub `Unknown_S_*` that `merge_isomorphic_stub_adts`
            // collapses with ANY other {(0,1),(1,1)} stub regardless of its
            // per-field decode, so a subject typing to `SumTypeId::Credential`
            // is NECESSARY but not SUFFICIENT: name the arms only when every
            // arm's field-0 PROVABLY decodes as `ByteArray` (a genuine
            // `Credential` is `Constr<0|1>(ByteArray)`). The ScalarKind key is
            // the merged stub `TypeHintId` + tag + field_idx, so a stub used
            // as `ByteArray` at one site and `Int`/other at another yields
            // `Conflict` and fail-closes the WHOLE merged stub to the honest
            // `Unknown_S_*`.
            if sum_id == SumTypeId::Credential
                && !arm_field0_is_bytearray(type_hint.as_ref(), *tag, scalars)
            {
                return false;
            }
        }
    }
    saw_constructor
}

/// Whether the field-0 of a stub-hinted constructor arm PROVABLY decodes as a
/// `ByteArray`, per the elimination-site ScalarKind table (keyed by the stub
/// `TypeHintId` + tag + field_idx 0). Fail-closed: a missing key, a non-stub
/// or absent hint, or any other verdict
/// (`Int`/`OtherData`/`Opaque`/`Conflict`/`Unknown`) returns `false`. This is
/// the soundness lever for `Credential`, whose genuine arms are
/// `Constr<0|1>(ByteArray)`.
fn arm_field0_is_bytearray(
    type_hint: Option<&TypeHintId>,
    tag: usize,
    scalars: &ScalarKindTable,
) -> bool {
    let Some(h) = type_hint.filter(|h| is_stub_type_hint(h)) else {
        return false;
    };
    matches!(
        scalars.get(&(h.clone(), tag, 0)),
        Some(ScalarKind::ByteArray)
    )
}

/// The KNOWN ABI arity of `sum_id`'s `tag`-th constructor, but ONLY for the
/// sum types whose per-constructor field layout this pass fully trusts.
/// `Some(n)` = the constructor takes exactly `n` fields (`Some(0)` for a
/// genuine nullary constructor); `None` = "do not touch" — either an
/// invalid tag or a sum whose field table is untrusted here, where a `None`
/// field list would be indistinguishable from a true nullary arm and could
/// mis-stamp a name. Version-DEPENDENT sums are additionally gated on an
/// EXPLICIT render version so they are never activated by the `None`→V2
/// default.
pub(crate) fn known_ctor_arity(sum_id: SumTypeId, tag: usize, ctx: &RenderCtx) -> Option<usize> {
    // `None` ⇒ V1-vs-V2 ambiguous; V2 is safe for the version-INDEPENDENT
    // sums below. The version-dependent ones re-read `ctx.version()` and
    // require an EXPLICIT match, so the default never activates them.
    let version = ctx.version_or_v2();
    match sum_id {
        // Fully-tabled sums: the field table returns `Some(_)` — incl.
        // `Some(vec![])` for genuine nullary ctors — for every valid tag,
        // and `None` for invalid tags / untrusted versions. These are
        // version-independent (StakeCredential's Inline/Pointer shape is
        // the same in V1/V2/V3) or only ever subjected under their own
        // version, so the `None`→V2 default is harmless for them.
        SumTypeId::Purpose
        | SumTypeId::ScriptInfo
        | SumTypeId::Credential
        | SumTypeId::StakeCredential => {
            sum_type_constructor_fields(sum_id, tag, version).map(|d| d.len())
        }
        // Certificate is version-DEPENDENT (V1/V2 names ≠ V3 under one key),
        // so require an EXPLICIT V1/V2 render version: under the `None`→V2
        // default a versionless render of a V3 cert AST whose arity overlaps
        // V1/V2 (e.g. tag 2) would get V1/V2 payload names. V3 is excluded
        // entirely — the `Never` deposit/refund makes tags 0/1 unnameable.
        SumTypeId::Certificate => match ctx.version() {
            Some(ScriptVersion::PlutusV1) | Some(ScriptVersion::PlutusV2) => {
                sum_type_constructor_fields(sum_id, tag, version).map(|d| d.len())
            }
            _ => None,
        },
        // GovernanceAction is V3-ONLY (the field table returns `Some(_)` for
        // every tag 0-6 only under PlutusV3, `None` otherwise), so require an
        // EXPLICIT V3 render version — never the `None`→V2 default. With no
        // surface/Data arity skew, every tabled arity is certain.
        SumTypeId::GovernanceAction => match ctx.version() {
            Some(ScriptVersion::PlutusV3) => {
                sum_type_constructor_fields(sum_id, tag, version).map(|d| d.len())
            }
            _ => None,
        },
        // Voter is V3-ONLY (tags 0/1 carry a Credential, tag 2 a pool hash).
        // Gate on EXPLICIT V3 like GovernanceAction — never the V2 default.
        SumTypeId::Voter => match ctx.version() {
            Some(ScriptVersion::PlutusV3) => {
                sum_type_constructor_fields(sum_id, tag, version).map(|d| d.len())
            }
            _ => None,
        },
        // OutputDatum is V2/V3-ONLY (V1 carries a plain `Option<DatumHash>`
        // instead). Accept an EXPLICIT V2 or V3; reject V1 and the `None`→V2
        // default-without-version. tag 0 (NoDatum) is a genuine nullary
        // (`Some(vec![])` ⇒ arity 0).
        SumTypeId::OutputDatum => match ctx.version() {
            Some(ScriptVersion::PlutusV2) | Some(ScriptVersion::PlutusV3) => {
                sum_type_constructor_fields(sum_id, tag, version).map(|d| d.len())
            }
            _ => None,
        },
        // Has nullary constructors (NegativeInfinity / PositiveInfinity)
        // that the field table reports as `None`; spell the arities out.
        SumTypeId::IntervalBoundType => match tag {
            0 | 2 => Some(0),
            1 => Some(1),
            _ => None,
        },
        // Field tables not yet trustworthy — do not name.
        _ => None,
    }
}

/// A synthetic stub type hint minted by `stub_adt` (`Unknown_S_<ord>` /
/// `Unknown_E_<arity>`) — an unresolved-type placeholder that the ABI
/// schema may override.
pub(super) fn is_stub_type_hint(hint: &TypeHintId) -> bool {
    let s = hint.as_str();
    s.starts_with("Unknown_S_") || s.starts_with("Unknown_E_")
}

/// Stamp a clause's constructor pattern with the sum-type hint, rename its
/// payload binders and rewire the body/guard references — everything
/// `name_clause` did except the two child descents, which the caller
/// schedules on its job stack.
fn prepare_clause(
    clause: WhenClause,
    sum_id: SumTypeId,
    ctx: &RenderCtx,
    scalars: &ScalarKindTable,
) -> PreparedClause {
    let WhenClause {
        pattern,
        guard,
        body,
    } = clause;

    let WhenPattern::Constructor {
        type_hint,
        tag,
        fields,
        shape,
    } = pattern
    else {
        // Not a constructor arm (`_`, literal, …) — just recurse.
        return PreparedClause {
            pattern,
            guard,
            body,
            guard_first: true,
        };
    };

    // Soundness gate: the constructor's ABI arity must be KNOWN for this sum
    // type AND match the arm's field count — `known_ctor_arity` returns
    // `Some(0)` for a true nullary but `None` for an unimplemented/untrusted
    // field table, so an arm of a sum whose layout is not fully trusted is
    // never stamped. The caller `clauses_all_nameable` already guarantees
    // this and the Credential field-decode gate for every arm; re-checking
    // keeps `prepare_clause` correct in isolation.
    let credential_gate_ok = sum_id != SumTypeId::Credential
        || arm_field0_is_bytearray(type_hint.as_ref(), tag, scalars);
    if known_ctor_arity(sum_id, tag, ctx) != Some(fields.len()) || !credential_gate_ok {
        return PreparedClause {
            pattern: WhenPattern::Constructor {
                type_hint,
                tag,
                fields,
                shape,
            },
            guard,
            body,
            guard_first: true,
        };
    }
    let field_defs = sum_type_constructor_fields(sum_id, tag, ctx.version_or_v2());

    // (B) Stamp the sum-type hint so the renderer resolves the
    // constructor name. Override `None` AND synthetic stub hints
    // (`Unknown_S_*` / `Unknown_E_*`) — the ABI schema is authoritative
    // over an unresolved placeholder — but keep a real/user hint. A stub
    // left unreferenced by such an override is dropped by the stub-ADT
    // DCE, which runs on the post-`prepare_for_render` AST.
    let new_type_hint = match type_hint {
        Some(h) if !is_stub_type_hint(&h) => Some(h),
        _ => Some(TypeHintId::new(sum_id.display_name())),
    };

    // (A) Rename synthetic payload binders to their schema field names,
    // collecting the VarId rewires for the body/guard.
    let mut renames: Vec<(VarId, &'static str)> = Vec::new();
    let new_fields: Vec<Binder> = match field_defs {
        Some(defs) => fields
            .into_iter()
            .zip(defs)
            .map(|(old, (cf, _))| {
                let new_name = cf.display_name();
                if is_synthetic_field_name(old.as_str()) && old.as_str() != new_name {
                    renames.push((old.var_id(), new_name));
                    Binder::new(new_name, old.var_id())
                } else {
                    old
                }
            })
            .collect(),
        None => fields,
    };

    // Rewire references to each renamed binder (literal-pattern aware via
    // `rename_var_in`); the caller walks the results.
    let mut body = body;
    for (vid, name) in &renames {
        body = rename_var_in(body, *vid, name);
    }
    let guard = guard.map(|g| {
        let mut g = g;
        for (vid, name) in &renames {
            g = rename_var_in(g, *vid, name);
        }
        g
    });

    PreparedClause {
        pattern: WhenPattern::Constructor {
            type_hint: new_type_hint,
            tag,
            fields: new_fields,
            shape,
        },
        guard,
        body,
        // The named path walked the body BEFORE the guard.
        guard_first: false,
    }
}

#[cfg(test)]
mod tests;
