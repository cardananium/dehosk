//! Validator PURPOSE dispatch: recognising it, splitting on it, and
//! rendering one handler body per purpose.
//!
//! A multi-purpose validator discriminates on `script_context.script_info`
//! (V3) or `.purpose` (V1/V2) and then runs one arm. The render wants
//! that as one `validator { spend(..) {..} mint(..) {..} }` block rather
//! than the raw dispatch, so these passes find the dispatch, specialize
//! the body to each arm, and render each specialization separately.
//!
//! Split out of `decompile/mod.rs`, which had grown to hold the crate's
//! public API, the render orchestration, and ~2 000 lines of passes that
//! never got their own file — while the sibling `render_prep/` keeps one
//! pass per module.

use super::*;
use crate::pseudo::ast::PBox;

/// Resolve a when-clause to the script purpose its pattern asserts, or
/// `None` for non-purpose arms. Shared by the multi-purpose splitter and
/// the single-purpose detector.
pub(super) fn purpose_of_arm(clause: &crate::pseudo::ast::WhenClause) -> Option<ValidatorPurpose> {
    use crate::decompile::validator_shape::detect_dispatch::{
        is_cardano_purpose_type_hint, purpose_from_known, purpose_from_unknown_tag,
    };
    use crate::pseudo::constructor::ConstructorShape;
    let crate::pseudo::ast::WhenPattern::Constructor {
        shape, type_hint, ..
    } = &clause.pattern
    else {
        return None;
    };
    match shape {
        ConstructorShape::Known(kc) => purpose_from_known(kc),
        // V3 ScriptInfo / V1-V2 ScriptPurpose arms whose constructor
        // stayed Unknown but whose type_hint pins the Cardano domain —
        // same anchoring rule as `detect_dispatch`.
        ConstructorShape::Unknown { tag, .. }
            if is_cardano_purpose_type_hint(type_hint.as_ref()) =>
        {
            purpose_from_unknown_tag(*tag)
        }
        _ => None,
    }
}

pub(super) fn build_purpose_handler_bodies(
    prepared: &PseudoExpr,
    show_types: bool,
    registry: &std::rc::Rc<BlueprintHintRegistry>,
    final_types: &std::rc::Rc<final_type_table::FinalTypeTable>,
    render_ctx: &RenderCtx,
) -> Vec<(ValidatorPurpose, String)> {
    // Promoted shape: the `decompiled` entry Let leads the chain.
    let PseudoExpr::Let { name, value, .. } = prepared else {
        return Vec::new();
    };
    if name != "decompiled" {
        return Vec::new();
    }
    let PseudoExpr::Lambda { body, .. } = value.as_ref() else {
        return Vec::new();
    };

    fn arm_purpose(clause: &crate::pseudo::ast::WhenClause) -> Option<ValidatorPurpose> {
        purpose_of_arm(clause)
    }
    fn is_purpose_dispatch(clauses: &[crate::pseudo::ast::WhenClause]) -> bool {
        let purposes = clauses.iter().filter_map(arm_purpose).count();
        let non_purpose = clauses
            .iter()
            .filter(|c| {
                arm_purpose(c).is_none()
                    && !matches!(c.pattern, crate::pseudo::ast::WhenPattern::Wildcard)
            })
            .count();
        purposes >= 2 && non_purpose == 0
    }

    /// Replace the spine's purpose dispatch with the single arm for
    /// `purpose`. Returns `None` when no dispatch (or no arm) was found.
    /// Spine = Let bodies; the dispatch itself may be bare or wrapped in
    /// the display-layer `expect!(dispatch, V)` — the wrapper is pushed
    /// INTO the selected arm (`expect!(arm_body, V)`), preserving the
    /// assertion while letting the single-arm `when` render as the
    /// `expect <Ctor>(..) = <subject>` destructure sugar.
    fn replace_dispatch(expr: PseudoExpr, purpose: ValidatorPurpose) -> Option<PseudoExpr> {
        let mut lets = Vec::new();
        let mut cur = expr;
        let base = loop {
            match cur {
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    lets.push((name, id, value));
                    cur = body.into_inner();
                }
                other => break other,
            }
        };
        let mut result = match base {
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } if is_purpose_dispatch(&clauses) => {
                let arm = clauses
                    .into_iter()
                    .find(|c| arm_purpose(c) == Some(purpose))?;
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses: vec![arm],
                }
            }
            PseudoExpr::Apply { function, args }
                if matches!(
                    function.as_ref(),
                    PseudoExpr::Var { name, .. } if name == "expect!"
                ) && (args.len() == 2 || args.len() == 3) =>
            {
                let mut args = args;
                let PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } = args.remove(0)
                else {
                    return None;
                };
                if !is_purpose_dispatch(&clauses) {
                    return None;
                }
                let mut arm = clauses
                    .into_iter()
                    .find(|c| arm_purpose(c) == Some(purpose))?;
                let mut wrapped_args = vec![arm.body];
                wrapped_args.extend(args);
                arm.body = PseudoExpr::Apply {
                    function,
                    args: wrapped_args.into(),
                };
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses: vec![arm],
                }
            }
            _ => return None,
        };
        for (name, id, value) in lets.into_iter().rev() {
            result = PseudoExpr::Let {
                name,
                id,
                value,
                body: PBox::new(result),
            };
        }
        Some(result)
    }

    fn dispatch_purposes(expr: &PseudoExpr) -> Vec<ValidatorPurpose> {
        let mut cur = expr;
        loop {
            match cur {
                PseudoExpr::Let { body, .. } => cur = body,
                PseudoExpr::When { clauses, .. } if is_purpose_dispatch(clauses) => {
                    return clauses.iter().filter_map(arm_purpose).collect();
                }
                PseudoExpr::Apply { function, args }
                    if matches!(
                        function.as_ref(),
                        PseudoExpr::Var { name, .. } if name == "expect!"
                    ) && !args.is_empty() =>
                {
                    return match &args[0] {
                        PseudoExpr::When { clauses, .. } if is_purpose_dispatch(clauses) => {
                            clauses.iter().filter_map(arm_purpose).collect()
                        }
                        _ => Vec::new(),
                    };
                }
                _ => return Vec::new(),
            }
        }
    }

    // Render one specialized fragment, sharing the fail-closed shadow
    // gate between the two selection strategies below.
    let render_fragment = |fragment: PseudoExpr| -> Option<String> {
        let fragment = render_prep::drop_dead_pure_lets_unchecked(fragment);
        // Fail-closed shadow gate: the renderer re-runs prepare on the
        // fragment with fragment-local name counters, so a local binder
        // can collapse onto the display name of a FREE reference (a
        // module-level helper bound outside the fragment) and capture
        // it. Predict that naming by preparing the same fragment; bail
        // to the text-pruned path on any overlap.
        let gate_view = render_prep::prepare_for_render(&fragment, render_ctx);
        if fragment_binder_shadows_free_name(&gate_view) {
            return None;
        }
        let (text, _spans) = render_decompiled_expr_with_registry_and_final_types(
            &fragment,
            show_types,
            registry,
            final_types,
            render_ctx,
        );
        Some(text)
    };

    let purposes = dispatch_purposes(body);
    if purposes.len() >= 2 {
        return purposes
            .into_iter()
            .filter_map(|purpose| {
                let fragment = replace_dispatch((**body).clone(), purpose)?;
                render_fragment(fragment).map(|text| (purpose, text))
            })
            .collect();
    }

    // No single `when` carries the dispatch. A PlutusTx-compiled
    // validator discriminates by ScriptInfo FIELD COUNT first and tag
    // second, so its purpose arms end up scattered across nested
    // `when`s and hoisted helpers, one purpose each:
    //
    // ```text
    // when script_info.fields is {
    //   [bytes, ..rest] ->
    //     fn spend_branch(_) { … when script_info is { Spending(..) -> … } }
    //     when rest is {
    //       []      -> when script_info is { Minting(..) -> …; _ -> spend_branch(Void) }
    //       [_, ..] -> spend_branch(Void)
    //     }
    // }
    // ```
    //
    // There is no arm to select, so specialize instead: under purpose P
    // the script is invoked with a `ScriptInfo` of P's tag, which makes
    // every arm naming a DIFFERENT purpose unreachable. Dropping those
    // leaves each handler with its own logic and a body that fails on
    // the shapes that purpose cannot receive — the same meaning
    // `replace_dispatch` gives the single-`when` form, reached the only
    // way this shape allows.
    let scattered = scattered_purposes(body);
    if scattered.len() < 2 {
        return Vec::new();
    }
    scattered
        .into_iter()
        .filter_map(|purpose| {
            // Specialize and render the WHOLE entry, then cut the body
            // out of the result — not the body alone. The fragment path
            // above can afford to render a sub-tree because it selects a
            // dispatch ARM, a self-contained piece; here the fragment
            // would be the entire body, whose every module-level helper
            // reference is free, and re-preparing that with
            // fragment-local name counters is exactly what the shadow
            // gate refuses. Rendering the entry keeps those binders in
            // scope, so the text comes out in the same shape (and with
            // the same names) as the flat render it replaces.
            let full = specialize_to_purpose(prepared.clone(), purpose);
            let (text, _spans) = render_decompiled_expr_with_registry_and_final_types(
                &full,
                show_types,
                registry,
                final_types,
                render_ctx,
            );
            let entry = crate::decompile::validator_meta::split_validator_entry_block(&text)?;
            Some((purpose, entry.body.to_string()))
        })
        .collect()
}

/// Is this `when` subject the script's OWN purpose value?
///
/// A `ScriptPurpose` is not only what the script was invoked for — it is
/// also ordinary DATA inside the transaction. `tx_info.redeemers` is a
/// map KEYED by `ScriptPurpose`, so a validator that walks it matches
/// `Minting(..)` / `Spending(..)` against other scripts' purposes. Those
/// arms resolve through `purpose_of_arm` exactly like the real dispatch
/// does, and specializing them would delete live logic: under `mint` the
/// `Spending` arm of a redeemer scan is perfectly reachable.
///
/// The discriminator is the schema NAME, not the type — both subjects
/// type to the same sum. `script_info` (V3 ScriptContext field 2) and
/// `purpose` (V1/V2 field 1) are the names the context-schema naming
/// gives that ONE position; a redeemer-map key reaches its `when` as a
/// `.1st` projection or a loop binder, and never under these.
///
/// A field access must additionally come off the CONTEXT binder. The
/// selector alone would accept `redeemer.script_info` — a user record
/// whose own field happens to carry that name — and dropping arms over
/// it would delete logic the handler really can reach. Anything not
/// matched here is left alone, which costs at most a split that does
/// not happen.
pub(super) fn is_own_purpose_subject(subject: &PseudoExpr) -> bool {
    /// The schema names for the ScriptContext's own purpose field.
    const OWN: &[&str] = &["script_info", "script_purpose", "purpose"];
    /// The binders the render gives the whole ScriptContext.
    const CONTEXT: &[&str] = &["script_context", "context", "ctx"];
    match subject {
        PseudoExpr::Var { name, .. } => OWN.contains(&name.as_str()),
        PseudoExpr::FieldAccess { record, selector } => {
            let named = match selector {
                crate::pseudo::field_selector::FieldSelector::NamedField(n)
                | crate::pseudo::field_selector::FieldSelector::ContextField(n) => {
                    OWN.contains(&n.as_str())
                }
                _ => false,
            };
            named
                && matches!(
                    record.as_ref(),
                    PseudoExpr::Var { name, .. } if CONTEXT.contains(&name.as_str())
                )
        }
        _ => false,
    }
}

/// Every purpose named by a `when` on the script's OWN purpose value,
/// anywhere in `body`, in first-seen order.
///
/// Weaker than `dispatch_purposes`, which requires ONE `when` to carry
/// them all with no foreign arm beside them. Here they may be spread
/// over separate `when`s. Two things keep that honest: `purpose_of_arm`
/// resolves only a prelude purpose constructor or an arm whose
/// `type_hint` pins it to the Cardano domain, and
/// [`is_own_purpose_subject`] requires the SUBJECT to be the script's
/// own purpose rather than any other `ScriptPurpose` value in reach.
pub(crate) fn scattered_purposes(body: &PseudoExpr) -> Vec<ValidatorPurpose> {
    use crate::pseudo::fold::ExprVisitor;

    struct Collect {
        found: Vec<ValidatorPurpose>,
    }
    impl ExprVisitor for Collect {
        fn visit_when(
            &mut self,
            subject: &PseudoExpr,
            _subject_name: Option<&crate::pseudo::ast::Binder>,
            clauses: &[crate::pseudo::ast::WhenClause],
        ) {
            if !is_own_purpose_subject(subject) {
                return;
            }
            for p in clauses.iter().filter_map(purpose_of_arm) {
                if !self.found.contains(&p) {
                    self.found.push(p);
                }
            }
        }
    }
    let mut c = Collect { found: Vec::new() };
    c.walk(body);
    c.found
}

/// Specialize `expr` to a single `purpose` by dropping the arms that
/// name a different one.
///
/// Sound because a handler runs only for its own purpose: the
/// `ScriptInfo` it is handed carries that tag, so an arm matching
/// another tag can never be taken. That argument holds only for the
/// script's OWN purpose value, so [`is_own_purpose_subject`] gates every
/// rewrite — a `when` over a `ScriptPurpose` that came out of the
/// transaction (a `tx_info.redeemers` key) keeps all its arms. Of the
/// rest, only arms `purpose_of_arm` RESOLVES are touched: a wildcard, a
/// literal, or any arm outside the Cardano purpose domain is carried
/// through untouched, and a `when` with no purpose arm at all is left
/// exactly as it was.
///
/// When dropping leaves a lone wildcard, the `when` collapses to that
/// arm's body, and when it leaves NOTHING the `when` becomes a `fail` —
/// the tag it demanded cannot arrive under this purpose.
pub(crate) fn specialize_to_purpose(expr: PseudoExpr, purpose: ValidatorPurpose) -> PseudoExpr {
    use crate::pseudo::ast::WhenPattern;
    use crate::pseudo::fold::ExprFolder;

    struct Specializer {
        purpose: ValidatorPurpose,
    }
    impl ExprFolder for Specializer {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<crate::pseudo::ast::Binder>,
            clauses: Vec<crate::pseudo::ast::WhenClause>,
        ) -> PseudoExpr {
            if !is_own_purpose_subject(&subject)
                || !clauses.iter().any(|c| purpose_of_arm(c).is_some())
            {
                return PseudoExpr::When {
                    subject: PBox::new(subject),
                    subject_name,
                    clauses,
                };
            }
            let kept: Vec<_> = clauses
                .into_iter()
                .filter(|c| purpose_of_arm(c).is_none_or(|p| p == self.purpose))
                .collect();
            // Nothing left to match. The original `when` had no arm for
            // this tag, so under this purpose it always fails — say so.
            // An empty clause list would be worse than wrong:
            // `collapse_empty_when` rewrites `when X is {}` to `X`, so a
            // single-arm `expect Spending(..) = script_info` would
            // silently become the VALUE `script_info` in the mint
            // handler, turning a failing assertion into a success.
            if kept.is_empty() {
                return PseudoExpr::Error { message: None };
            }
            // A lone wildcard means the `when` decides nothing, so the
            // arm body can stand on its own. Nothing is skipped by
            // dropping the `when`: `is_own_purpose_subject` already
            // admits only a binder or one field off the context binder,
            // both of which merely READ. The one remaining condition is
            // that the subject is unnamed — `when script_info as si is
            // { _ -> use(si) }` binds `si` in that body, and collapsing
            // would free it.
            if subject_name.is_none()
                && kept.len() == 1
                && matches!(kept[0].pattern, WhenPattern::Wildcard)
                && kept[0].guard.is_none()
            {
                let mut kept = kept;
                return kept.remove(0).body;
            }
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses: kept,
            }
        }
    }
    Specializer { purpose }.fold(expr)
}

/// Prove a V3 single-purpose validator from the PREPARED entry spine.
///
/// A V3 single-purpose script asserts its purpose with a `script_info`
/// match that every success path must pass:
///
/// ```text
/// expect Spending(out_ref, _) = script_context.script_info   (direct)
/// let script_info = script_context.script_info
/// expect Spending(_, _) = script_info                        (via an alias)
/// let g = when script_context.script_info is {
///   Proposing(_i, pp) -> pp    _ -> fail
/// }.governance_action                                        (in a let value)
/// ```
///
/// ### Dominance discipline (the load-bearing gate)
///
/// The walk descends ONLY positions evaluated on EVERY success path of
/// the entry body — `Let` value + body, `When` SUBJECT, `If` CONDITION,
/// `FieldAccess` record, `IndexAccess` collection, and the `expect!`
/// display wrapper's args. It NEVER enters `Lambda`/`RecFn` bodies,
/// `Delay`, When ARM bodies, or If BRANCHES: a purpose match reachable
/// only inside a sibling-bypassable region — a `Minting` arm of a
/// redeemer dispatch — must not promote.
///
/// ### Qualification
///
/// A reached `When` qualifies when its subject is the render-prep-named
/// `script_info` oracle — `FieldAccess{_, NamedField("script_info")}`
/// directly, or a `Var` whose SPINE `let` binding (one VarId-keyed hop)
/// holds that access — and EXACTLY ONE arm resolves to a purpose
/// (`purpose_of_arm`: Known ctor, or Unknown tag 0-5 with the
/// script_info/script_purpose type_hint) with a non-failing body, while
/// every other arm fails. A single-clause When (the expect-destructure
/// form) trivially satisfies the all-others-fail half.
///
/// Version-gated at the call site to DEFINITIVE V3 — an explicit
/// `--script-version v3` or the `(1, 1, _)` UPLC header, which V1/V2
/// cannot carry (tag 5 = Propose is V3-only). Returns `None` anywhere
/// short of full proof — fail-closed.
/// Purposes the body actually discriminates on, read off the tags it
/// matches against the `script_info` value.
///
/// [`detect_single_purpose_v3`] proves a SINGLE purpose from one
/// dominating assertion. This is the weaker, wider observation: which
/// `ScriptInfo` constructors the script tests at all. A PlutusTx-compiled
/// validator discriminates by field count first and tag second, spread
/// across nested `when`s, so no dominating assertion exists and the
/// stronger detector abstains — while the tags themselves are right
/// there. Without this the tool reports "purpose name not recoverable
/// from bytecode" about a script whose bytecode names two of them.
///
/// Diagnostic only: it never selects a wrap. Arity is deliberately not
/// checked — the subject is already known to be the `script_info`, so
/// the tag alone fixes the purpose, and a merged stub ADT can widen a
/// constructor's declared arity.
///
/// The anchor is the reserved `script_info` name, which only Cardano
/// naming mints (either the schema field access or the binder
/// `name_context_field_peel` named). A helper param that somehow
/// carried that name would widen the reported set — which costs a
/// comment's accuracy and nothing else, since no wrap reads this.
pub(crate) fn observe_script_info_purposes(prepared: &PseudoExpr) -> Vec<ValidatorPurpose> {
    use crate::pseudo::ast::WhenPattern;
    use crate::pseudo::constructor::ConstructorShape;
    use crate::pseudo::fold::ExprVisitor;

    fn is_script_info(subject: &PseudoExpr) -> bool {
        match subject {
            // `ctx.script_info`, or the binder the context peel named.
            PseudoExpr::FieldAccess { selector, .. } => selector.as_pretty_name() == "script_info",
            PseudoExpr::Var { name, .. } => name.as_str() == "script_info",
            _ => false,
        }
    }

    struct Observer {
        purposes: Vec<ValidatorPurpose>,
    }
    impl ExprVisitor for Observer {
        fn visit_when(
            &mut self,
            subject: &PseudoExpr,
            _subject_name: Option<&crate::pseudo::ast::Binder>,
            clauses: &[crate::pseudo::ast::WhenClause],
        ) {
            if !is_script_info(subject) {
                return;
            }
            for clause in clauses {
                let WhenPattern::Constructor { tag, shape, .. } = &clause.pattern else {
                    continue;
                };
                // A `Known` constructor here would be a prelude type, not
                // a ScriptInfo tag.
                if !matches!(shape, ConstructorShape::Unknown { .. }) {
                    continue;
                }
                let Some(p) = validator_shape::purpose_from_unknown_tag(*tag) else {
                    continue;
                };
                if !self.purposes.contains(&p) {
                    self.purposes.push(p);
                }
            }
        }
    }
    let mut o = Observer {
        purposes: Vec::new(),
    };
    o.walk(prepared);
    o.purposes
}

pub(super) fn detect_single_purpose_v3(prepared: &PseudoExpr) -> Option<ValidatorPurpose> {
    use std::collections::HashMap;

    let PseudoExpr::Let { name, value, .. } = prepared else {
        return None;
    };
    if name != "decompiled" {
        return None;
    }
    let PseudoExpr::Lambda { body, .. } = value.as_ref() else {
        return None;
    };

    fn is_script_info_access(e: &PseudoExpr) -> bool {
        matches!(
            e,
            PseudoExpr::FieldAccess { selector, .. }
                if selector.as_pretty_name() == "script_info"
        )
    }

    fn failing_body(e: &PseudoExpr) -> bool {
        let mut current = e;
        loop {
            match current {
                PseudoExpr::Error { .. } => return true,
                PseudoExpr::Trace { value, .. } => current = value,
                _ => return false,
            }
        }
    }

    fn qualifies(
        subject: &PseudoExpr,
        clauses: &[crate::pseudo::ast::WhenClause],
        spine_lets: &HashMap<crate::pseudo::var_id::VarId, &PseudoExpr>,
    ) -> Option<ValidatorPurpose> {
        let subject_ok = is_script_info_access(subject)
            || matches!(
                subject,
                PseudoExpr::Var { id: Some(vid), .. }
                    if spine_lets
                        .get(vid)
                        .is_some_and(|v| is_script_info_access(v))
            );
        if !subject_ok {
            return None;
        }
        let mut live_purpose: Option<ValidatorPurpose> = None;
        for clause in clauses {
            match purpose_of_arm(clause) {
                Some(p) if !failing_body(&clause.body) => {
                    if live_purpose.is_some() {
                        // Two live purpose arms — multi-purpose, not ours.
                        return None;
                    }
                    live_purpose = Some(p);
                }
                Some(_) => {
                    // A failing purpose arm counts as a fail arm.
                }
                None => {
                    // Every non-purpose arm must fail.
                    if !failing_body(&clause.body) {
                        return None;
                    }
                }
            }
        }
        live_purpose
    }

    fn walk<'a>(
        expr: &'a PseudoExpr,
        spine_lets: &mut HashMap<crate::pseudo::var_id::VarId, &'a PseudoExpr>,
    ) -> Option<ValidatorPurpose> {
        enum Frame<'a> {
            Visit(&'a PseudoExpr),
            BindLet {
                id: Option<crate::pseudo::var_id::VarId>,
                value: &'a PseudoExpr,
                body: &'a PseudoExpr,
            },
        }

        let mut stack = vec![Frame::Visit(expr)];
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Visit(e) => match e {
                    PseudoExpr::When {
                        subject, clauses, ..
                    } => {
                        if let Some(p) = qualifies(subject, clauses, spine_lets) {
                            return Some(p);
                        }
                        // The subject is strict; the arms are NOT (do not enter).
                        stack.push(Frame::Visit(subject));
                    }
                    PseudoExpr::Let {
                        id, value, body, ..
                    } => {
                        stack.push(Frame::BindLet {
                            id: *id,
                            value,
                            body,
                        });
                        stack.push(Frame::Visit(value));
                    }
                    PseudoExpr::If { condition, .. } => stack.push(Frame::Visit(condition)),
                    PseudoExpr::FieldAccess { record, .. } => stack.push(Frame::Visit(record)),
                    PseudoExpr::IndexAccess { collection, .. } => {
                        stack.push(Frame::Visit(collection))
                    }
                    PseudoExpr::Apply { function, args }
                        if matches!(
                            function.as_ref(),
                            PseudoExpr::Var { name, .. } if name == "expect!"
                        ) =>
                    {
                        // args[0] = condition and args[1] = continuation both
                        // sit on every success path; args[2], the 3-arg form's
                        // fail MESSAGE, does not — skip it. Push reversed so
                        // args[0] is visited (and can short-circuit) first.
                        for a in args.iter().take(2).rev() {
                            stack.push(Frame::Visit(a));
                        }
                    }
                    _ => {}
                },
                Frame::BindLet { id, value, body } => {
                    if let Some(vid) = id {
                        spine_lets.insert(vid, value);
                    }
                    stack.push(Frame::Visit(body));
                }
            }
        }
        None
    }

    let mut spine_lets = HashMap::new();
    walk(body, &mut spine_lets)
}

/// Does any binder display name in `expr` equal the display name of a
/// variable that occurs FREE in `expr` (no enclosing binder of that name)?
///
/// The per-purpose-fragment shadow gate: a fragment's free names reference
/// module-level helpers bound outside it, so a same-named fragment binder
/// would capture them in the rendered output. The intersection is global,
/// not nesting-aware — a strict over-approximation, fail-closed. Names are
/// compared in printed form (`sanitize_identifier` maps keyword names like
/// `when` -> `when_`, which can collapse distinct AST names).
pub(super) fn fragment_binder_shadows_free_name(expr: &PseudoExpr) -> bool {
    use std::collections::HashSet;

    fn push_binder(name: &str, scope: &mut Vec<String>, binders: &mut HashSet<String>) {
        if name != "_" {
            binders.insert(name.to_string());
        }
        scope.push(name.to_string());
    }

    enum Step<'a> {
        Visit(&'a PseudoExpr),
        Truncate(usize),
        /// Bind `name` (visible from here on) — used for `Let`, after its
        /// value has already been visited without it in scope.
        Bind(&'a str),
        /// `When`: subject already visited; push `subject_name` (if any),
        /// then process `clauses` in order, then truncate to `depth`.
        AfterSubject {
            subject_name: Option<&'a str>,
            clauses: &'a [crate::pseudo::ast::WhenClause],
            depth: usize,
        },
        /// One `When` clause at a time, so clause N's binders are gone
        /// before clause N+1's pattern is even considered.
        NextClause {
            remaining: &'a [crate::pseudo::ast::WhenClause],
            clause_depth: usize,
            final_depth: usize,
        },
        /// A clause's literal pattern (if any) has now been visited — bind
        /// its names and walk guard/body, then move to the next clause.
        ClauseBody {
            clause: &'a crate::pseudo::ast::WhenClause,
            rest: &'a [crate::pseudo::ast::WhenClause],
            clause_depth: usize,
            final_depth: usize,
        },
    }

    fn walk(
        expr: &PseudoExpr,
        scope: &mut Vec<String>,
        binders: &mut HashSet<String>,
        free: &mut HashSet<String>,
    ) {
        let mut stack: Vec<Step> = vec![Step::Visit(expr)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Visit(e) => match e {
                    PseudoExpr::Var { name, .. } => {
                        if !scope.iter().any(|n| n == name) {
                            free.insert(name.clone());
                        }
                    }
                    PseudoExpr::Lambda { params, body } => {
                        let depth = scope.len();
                        for p in params {
                            push_binder(p.display_name(), scope, binders);
                        }
                        stack.push(Step::Truncate(depth));
                        stack.push(Step::Visit(body));
                    }
                    PseudoExpr::RecFn { name, params, body } => {
                        let depth = scope.len();
                        push_binder(name.display_name(), scope, binders);
                        for p in params {
                            push_binder(p.display_name(), scope, binders);
                        }
                        stack.push(Step::Truncate(depth));
                        stack.push(Step::Visit(body));
                    }
                    PseudoExpr::Let {
                        name, value, body, ..
                    } => {
                        let depth = scope.len();
                        stack.push(Step::Truncate(depth));
                        stack.push(Step::Visit(body));
                        stack.push(Step::Bind(name));
                        stack.push(Step::Visit(value));
                    }
                    PseudoExpr::When {
                        subject,
                        subject_name,
                        clauses,
                    } => {
                        let depth = scope.len();
                        stack.push(Step::AfterSubject {
                            subject_name: subject_name.as_ref().map(|b| b.display_name()),
                            clauses,
                            depth,
                        });
                        stack.push(Step::Visit(subject));
                    }
                    PseudoExpr::Apply { function, args } => {
                        for a in args.iter().rev() {
                            stack.push(Step::Visit(a));
                        }
                        stack.push(Step::Visit(function));
                    }
                    PseudoExpr::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        stack.push(Step::Visit(else_branch));
                        stack.push(Step::Visit(then_branch));
                        stack.push(Step::Visit(condition));
                    }
                    PseudoExpr::List { elements, tail } => {
                        if let Some(t) = tail {
                            stack.push(Step::Visit(t));
                        }
                        for e in elements.iter().rev() {
                            stack.push(Step::Visit(e));
                        }
                    }
                    PseudoExpr::Tuple(items) => {
                        for e in items.iter().rev() {
                            stack.push(Step::Visit(e));
                        }
                    }
                    PseudoExpr::Pair(a, b) => {
                        stack.push(Step::Visit(b));
                        stack.push(Step::Visit(a));
                    }
                    PseudoExpr::Constr { fields, .. } => {
                        for e in fields.iter().rev() {
                            stack.push(Step::Visit(e));
                        }
                    }
                    PseudoExpr::FieldAccess { record, .. } => stack.push(Step::Visit(record)),
                    PseudoExpr::IndexAccess { collection, .. } => {
                        stack.push(Step::Visit(collection))
                    }
                    PseudoExpr::BinOp { left, right, .. } => {
                        stack.push(Step::Visit(right));
                        stack.push(Step::Visit(left));
                    }
                    PseudoExpr::UnOp { operand, .. } => stack.push(Step::Visit(operand)),
                    PseudoExpr::BuiltinCall { args, .. } => {
                        for a in args.iter().rev() {
                            stack.push(Step::Visit(a));
                        }
                    }
                    PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                        stack.push(Step::Visit(inner))
                    }
                    PseudoExpr::Trace { message, value } => {
                        stack.push(Step::Visit(value));
                        stack.push(Step::Visit(message));
                    }
                    PseudoExpr::Int(_)
                    | PseudoExpr::ByteArray(_)
                    | PseudoExpr::String(_)
                    | PseudoExpr::Bool(_)
                    | PseudoExpr::Unit
                    | PseudoExpr::Error { .. }
                    | PseudoExpr::Raw { .. }
                    | PseudoExpr::Data(_)
                    | PseudoExpr::HelperSymbol(_) => {}
                },
                Step::Truncate(depth) => scope.truncate(depth),
                Step::Bind(name) => push_binder(name, scope, binders),
                Step::AfterSubject {
                    subject_name,
                    clauses,
                    depth,
                } => {
                    if let Some(b) = subject_name {
                        push_binder(b, scope, binders);
                    }
                    let clause_depth = scope.len();
                    stack.push(Step::NextClause {
                        remaining: clauses,
                        clause_depth,
                        final_depth: depth,
                    });
                }
                Step::NextClause {
                    remaining,
                    clause_depth,
                    final_depth,
                } => {
                    let Some((clause, rest)) = remaining.split_first() else {
                        stack.push(Step::Truncate(final_depth));
                        continue;
                    };
                    stack.push(Step::ClauseBody {
                        clause,
                        rest,
                        clause_depth,
                        final_depth,
                    });
                    if let crate::pseudo::ast::WhenPattern::Literal(lit) = &clause.pattern {
                        stack.push(Step::Visit(lit));
                    }
                }
                Step::ClauseBody {
                    clause,
                    rest,
                    clause_depth,
                    final_depth,
                } => {
                    for n in clause.pattern.bound_names() {
                        push_binder(&n, scope, binders);
                    }
                    stack.push(Step::NextClause {
                        remaining: rest,
                        clause_depth,
                        final_depth,
                    });
                    stack.push(Step::Truncate(clause_depth));
                    stack.push(Step::Visit(&clause.body));
                    if let Some(guard) = &clause.guard {
                        stack.push(Step::Visit(guard));
                    }
                }
            }
        }
    }

    let mut scope = Vec::new();
    let mut binders = HashSet::new();
    let mut free = HashSet::new();
    walk(expr, &mut scope, &mut binders, &mut free);

    let sanitized_binders: HashSet<String> = binders
        .iter()
        .map(|n| crate::decompile::render::sanitize_identifier(n))
        .collect();
    free.iter()
        .any(|n| sanitized_binders.contains(&crate::decompile::render::sanitize_identifier(n)))
}
