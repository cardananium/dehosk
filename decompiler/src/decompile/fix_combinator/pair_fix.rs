//! Recover the U-combinator church-pair fixpoint as two named
//! mutually-recursive functions.
//!
//! After `simplify_double_rec_fn` the church pair `e` is a 2-param
//! U-comb whose body feeds two injectors into `p1`, then a driver
//! `fn(d0,d1,d2){ d0(armA, armB) }`. Every live use is `e.1st(x, y)`.
//! `armB`'s `when` has fabricated arities 1/3 because UPLC over-applies
//! a 0/2 sum to a trailing values list.
//!
//! The pair components *are* the two rec-fns: `e.1st(x,y)` becomes
//! `check_param_value(x,y)`, and `armB` is eta-expanded by moving the
//! trailing application into the clauses
//! (`(when s {…})(V) ≡ when s { C0() -> b0[t0:=V]; … }`). That is
//! sound only because every continuation use is a saturated 2-arg call.
//!
//! Fail-closed — a wrong beta flips accept/reject, so any miss
//! returns the tree unchanged:
//! (a) every self-ref of `f` is the partial `f(p0)` on f's first param;
//! (b) the tail is `p1(inj0, inj1)` with literal 1-param injectors,
//!     tags 0/1, single Var payloads;
//! (c) the driver is the literal `fn(d0,d1,d2){ d0(armA, armB) }`;
//!     `d0` is unused in the arms; every `d1`/`d2` use is a saturated
//!     2-arg head;
//! (d) after rewriting first-projection uses, no reference to the pair
//!     binder remains (including any `.2nd`).
//!
//! Names stay sense-neutral so polarity is not laundered into them.

use crate::pseudo::ast::PBox;
use std::collections::{HashMap, HashSet};

use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

const FIRST_FN_NAME: &str = "check_param_value";
const SECOND_FN_NAME: &str = "check_param_list";
const VALUES_PARAM_NAME: &str = "values";

pub(crate) fn recover_pair_fixpoint(expr: PseudoExpr) -> PseudoExpr {
    // Sync this thread's binder counter ABOVE every id in the tree
    // BEFORE any fresh mint, to avoid VarId collisions.
    VarId::ensure_binding_counter_above(
        crate::decompile::render_prep::alpha_uniquify::max_fresh_range_id(&expr),
    );

    struct PairFixpointRecoverer;

    impl ExprFolder for PairFixpointRecoverer {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_let(
            &mut self,
            name: String,
            id: Option<VarId>,
            value: PseudoExpr,
            body: PseudoExpr,
        ) -> PseudoExpr {
            if let Some(rewritten) = try_recover(id, &value, &body) {
                return rewritten;
            }
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
    }

    PairFixpointRecoverer.fold(expr)
}

/// One `Force` layer is a delay-absorption residue at the partial-app
/// sites (the UPLC fn is `λp0. delay(λp1. …)`; the pseudo `RecFn`
/// absorbed the delay into its 2-param list, the call-site `Force`
/// survived). Peel AT MOST one layer; a bare node is also accepted.
fn peel_force(expr: &PseudoExpr) -> &PseudoExpr {
    match expr {
        PseudoExpr::Force(inner) => inner,
        other => other,
    }
}

fn var_id_of(expr: &PseudoExpr) -> Option<VarId> {
    match expr {
        PseudoExpr::Var { id, .. } => *id,
        _ => None,
    }
}

fn is_var(expr: &PseudoExpr, expected: VarId) -> bool {
    var_id_of(expr) == Some(expected)
}

/// Match one injector: `fn(a) { g(Constr{tag, fields: [a]}) }` with the
/// constructor tag pinned to `expected_tag` (0 = pair-first component,
/// 1 = pair-second component) and a single-`Var` payload.
fn match_injector(expr: &PseudoExpr, knot_id: VarId, expected_tag: usize) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    if params.len() != 1 {
        return false;
    }
    let PseudoExpr::Apply { function, args } = &**body else {
        return false;
    };
    if !is_var(function, knot_id) || args.len() != 1 {
        return false;
    }
    let PseudoExpr::Constr {
        type_hint,
        tag,
        fields,
        shape:
            ConstructorShape::Unknown {
                tag: shape_tag,
                arity: 1,
                ..
            },
    } = &args[0]
    else {
        return false;
    };
    type_hint.is_none()
        && *tag == expected_tag
        && *shape_tag == expected_tag
        && fields.len() == 1
        && is_var(&fields[0], params[0].var_id())
}

/// Everything the recognizer extracted from the matched template.
struct PairFixMatch<'a> {
    e_id: VarId,
    /// armA: the per-param check — its OWN params become F1's params.
    arm_a_params: &'a [Binder],
    arm_a_body: &'a PseudoExpr,
    /// armB: 1-param lambda over the spec-list sum.
    arm_b_param: &'a Binder,
    /// nil clause: pattern binds ONE fabricated trailing binder (values).
    nil_trailing: &'a Binder,
    nil_shape: ConstructorShape,
    nil_body: &'a PseudoExpr,
    /// cons clause: pattern binds head, tail + ONE fabricated trailing binder.
    cons_head: &'a Binder,
    cons_tail: &'a Binder,
    cons_trailing: &'a Binder,
    cons_shape: ConstructorShape,
    cons_body: &'a PseudoExpr,
    /// driver continuation params: d1 ↦ pair-first (F1), d2 ↦ pair-second (F2).
    d1: VarId,
    d2: VarId,
    /// every binder id consumed by the template (for distinctness +
    /// leak audits): e, f, p0, p1, g, w, d0, d1, d2.
    template_ids: Vec<VarId>,
}

/// Match the full template (module docs). Returns `None` on ANY
/// structural deviation — this is the fail-closed gate.
fn match_template<'a>(e_id: Option<VarId>, value: &'a PseudoExpr) -> Option<PairFixMatch<'a>> {
    let e_id = e_id?;

    // let f = rec fn f(p0, p1) { … } in Force(f(driver))
    let PseudoExpr::Let {
        id: Some(f_let_id),
        value: f_rec,
        body: partial,
        ..
    } = value
    else {
        return None;
    };
    let PseudoExpr::RecFn {
        name: f_name,
        params: f_params,
        body: f_body,
    } = &**f_rec
    else {
        return None;
    };
    // The `let f = rec fn f` same-id convention is what the references
    // resolve against; a mismatched pair is an unproven shape.
    if f_name.var_id() != *f_let_id || f_params.len() != 2 {
        return None;
    }
    let f_id = *f_let_id;
    let p0 = f_params[0].var_id();
    let p1 = f_params[1].var_id();

    // f body: let g = fn(w) { Force(f(p0))( Force(p0)(w) ) } in p1(inj0, inj1)
    let PseudoExpr::Let {
        id: Some(g_id),
        value: knot,
        body: tail,
        ..
    } = &**f_body
    else {
        return None;
    };
    let g_id = *g_id;
    let PseudoExpr::Lambda {
        params: knot_params,
        body: knot_body,
    } = &**knot
    else {
        return None;
    };
    if knot_params.len() != 1 {
        return None;
    }
    let w = knot_params[0].var_id();
    // knot body = (one application, one argument)
    let PseudoExpr::Apply {
        function: knot_fn,
        args: knot_args,
    } = &**knot_body
    else {
        return None;
    };
    if knot_args.len() != 1 {
        return None;
    }
    // head: Force(f(p0)) — invariant (a): the ONLY self-ref inside f's
    // body, a partial app on f's own first param.
    let PseudoExpr::Apply {
        function: self_ref,
        args: self_args,
    } = peel_force(knot_fn)
    else {
        return None;
    };
    if !is_var(self_ref, f_id) || self_args.len() != 1 || !is_var(&self_args[0], p0) {
        return None;
    }
    // argument: Force(p0)(w)
    let PseudoExpr::Apply {
        function: drv_ref,
        args: drv_args,
    } = &knot_args[0]
    else {
        return None;
    };
    if !is_var(peel_force(drv_ref), p0) || drv_args.len() != 1 || !is_var(&drv_args[0], w) {
        return None;
    }

    // tail: p1(inj0, inj1) — invariant (b).
    let PseudoExpr::Apply {
        function: tail_fn,
        args: tail_args,
    } = &**tail
    else {
        return None;
    };
    if !is_var(tail_fn, p1) || tail_args.len() != 2 {
        return None;
    }
    if !match_injector(&tail_args[0], g_id, 0) || !match_injector(&tail_args[1], g_id, 1) {
        return None;
    }

    // partial app: Force(f(driver)) — invariant (c): driver literal.
    let PseudoExpr::Apply {
        function: pa_fn,
        args: pa_args,
    } = peel_force(partial)
    else {
        return None;
    };
    if !is_var(pa_fn, f_id) || pa_args.len() != 1 {
        return None;
    }
    let PseudoExpr::Lambda {
        params: drv_params,
        body: drv_body,
    } = &pa_args[0]
    else {
        return None;
    };
    if drv_params.len() != 3 {
        return None;
    }
    let d0 = drv_params[0].var_id();
    let d1 = drv_params[1].var_id();
    let d2 = drv_params[2].var_id();
    let PseudoExpr::Apply {
        function: drv_head,
        args: arms,
    } = &**drv_body
    else {
        return None;
    };
    if !is_var(drv_head, d0) || arms.len() != 2 {
        return None;
    }

    // armA: literal 2-param lambda.
    let PseudoExpr::Lambda {
        params: arm_a_params,
        body: arm_a_body,
    } = &arms[0]
    else {
        return None;
    };
    if arm_a_params.len() != 2 {
        return None;
    }

    // armB: literal 1-param lambda; body = when over its OWN param with
    // exactly the two fabricated-arity clauses (1 and 3), no guards, no
    // subject_name, no type hints.
    let PseudoExpr::Lambda {
        params: arm_b_params,
        body: arm_b_body,
    } = &arms[1]
    else {
        return None;
    };
    if arm_b_params.len() != 1 {
        return None;
    }
    let arm_b_param = &arm_b_params[0];
    let PseudoExpr::When {
        subject,
        subject_name,
        clauses,
    } = &**arm_b_body
    else {
        return None;
    };
    if subject_name.is_some() || !is_var(subject, arm_b_param.var_id()) || clauses.len() != 2 {
        return None;
    }
    let (nil_trailing, nil_shape, nil_body) = match_arm_b_clause(&clauses[0], 0, 1)?;
    let (cons_fields, cons_shape, cons_body) = match_arm_b_clause_fields(&clauses[1], 1, 3)?;

    Some(PairFixMatch {
        e_id,
        arm_a_params,
        arm_a_body,
        arm_b_param,
        nil_trailing,
        nil_shape,
        nil_body,
        cons_head: &cons_fields[0],
        cons_tail: &cons_fields[1],
        cons_trailing: &cons_fields[2],
        cons_shape,
        cons_body,
        d1,
        d2,
        template_ids: vec![e_id, f_id, p0, p1, g_id, w, d0, d1, d2],
    })
}

/// Match one armB clause (no guard; Unknown constructor pattern with
/// pinned tag and FABRICATED arity; no type hint) and return its single
/// trailing binder + shape + body.
fn match_arm_b_clause(
    clause: &WhenClause,
    tag: usize,
    arity: usize,
) -> Option<(&Binder, ConstructorShape, &PseudoExpr)> {
    let (fields, shape, body) = match_arm_b_clause_fields(clause, tag, arity)?;
    Some((fields.last()?, shape, body))
}

fn match_arm_b_clause_fields(
    clause: &WhenClause,
    expected_tag: usize,
    expected_arity: usize,
) -> Option<(&[Binder], ConstructorShape, &PseudoExpr)> {
    if clause.guard.is_some() {
        return None;
    }
    let WhenPattern::Constructor {
        type_hint,
        tag,
        fields,
        shape:
            shape @ ConstructorShape::Unknown {
                tag: shape_tag,
                arity,
                ..
            },
    } = &clause.pattern
    else {
        return None;
    };
    if type_hint.is_some()
        || *tag != expected_tag
        || *shape_tag != expected_tag
        || *arity != expected_arity
        || fields.len() != expected_arity
    {
        return None;
    }
    Some((fields.as_slice(), *shape, &clause.body))
}

// ---------------------------------------------------------------------
// Audits
// ---------------------------------------------------------------------

/// Reference / binder / saturated-call census of one opaque region.
#[derive(Default)]
struct BodyAudit {
    /// `Var` reference counts by id.
    refs: HashMap<VarId, usize>,
    /// every binder id bound anywhere inside the region.
    binders: HashSet<VarId>,
    /// count of `Apply { function: Var(id), args: [_, _] }` heads.
    saturated_2arg_heads: HashMap<VarId, usize>,
}

impl BodyAudit {
    fn collect(expr: &PseudoExpr) -> Self {
        let mut audit = Self::default();
        walk_audit(expr, &mut audit);
        audit
    }

    fn ref_count(&self, id: VarId) -> usize {
        self.refs.get(&id).copied().unwrap_or(0)
    }

    /// True iff EVERY reference to `id` is the head of a 2-arg apply.
    fn only_saturated_2arg_calls(&self, id: VarId) -> bool {
        self.ref_count(id) == self.saturated_2arg_heads.get(&id).copied().unwrap_or(0)
    }

    fn binds_any(&self, ids: &[VarId]) -> bool {
        ids.iter().any(|id| self.binders.contains(id))
    }

    fn refs_any(&self, ids: &[VarId]) -> bool {
        ids.iter().any(|id| self.ref_count(*id) > 0)
    }
}

/// A job on [`walk_audit`]'s stack. `Bind` and `Clause` are the points run between two
/// child walks; they stay separate steps.
enum AuditStep<'a> {
    Visit(&'a PseudoExpr),
    /// The `When` subject_name binder: recorded BETWEEN the subject walk and
    /// the clause walks.
    Bind(VarId),
    /// One `When` clause: its pattern binders are recorded before its
    /// sub-expressions, and after the previous clause finished.
    Clause(&'a WhenClause),
}

/// COMPLETE walker: every `Var` ref, every binder occurrence (lambda /
/// recfn name+params / let / when subject_name / pattern fields incl.
/// pattern-`Literal` payloads), and saturated 2-arg apply heads. No
/// wildcard arm — a new `PseudoExpr` variant is a compile error here,
/// not a silent audit hole.
fn walk_audit(expr: &PseudoExpr, audit: &mut BodyAudit) {
    let mut steps: Vec<AuditStep<'_>> = vec![AuditStep::Visit(expr)];

    while let Some(step) = steps.pop() {
        let expr = match step {
            AuditStep::Visit(expr) => expr,
            AuditStep::Bind(id) => {
                audit.binders.insert(id);
                continue;
            }
            AuditStep::Clause(clause) => {
                // Reversed so they pop in source order: pattern, guard, body.
                steps.push(AuditStep::Visit(&clause.body));
                if let Some(guard) = &clause.guard {
                    steps.push(AuditStep::Visit(guard));
                }
                walk_pattern_audit(&clause.pattern, audit, &mut steps);
                continue;
            }
        };
        match expr {
            PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Bool(_)
            | PseudoExpr::Unit
            | PseudoExpr::Error { .. }
            | PseudoExpr::Raw { .. }
            | PseudoExpr::Data(_)
            | PseudoExpr::HelperSymbol(_) => {}
            PseudoExpr::Var { id, .. } => {
                if let Some(v) = id {
                    *audit.refs.entry(*v).or_insert(0) += 1;
                }
            }
            PseudoExpr::Lambda { params, body } => {
                for p in params {
                    audit.binders.insert(p.var_id());
                }
                steps.push(AuditStep::Visit(body));
            }
            PseudoExpr::RecFn { name, params, body } => {
                audit.binders.insert(name.var_id());
                for p in params {
                    audit.binders.insert(p.var_id());
                }
                steps.push(AuditStep::Visit(body));
            }
            PseudoExpr::Apply { function, args } => {
                if args.len() == 2
                    && let PseudoExpr::Var { id: Some(head), .. } = &**function
                {
                    *audit.saturated_2arg_heads.entry(*head).or_insert(0) += 1;
                }
                for a in args.iter().rev() {
                    steps.push(AuditStep::Visit(a));
                }
                steps.push(AuditStep::Visit(function));
            }
            PseudoExpr::Let {
                id, value, body, ..
            } => {
                if let Some(v) = id {
                    audit.binders.insert(*v);
                }
                steps.push(AuditStep::Visit(body));
                steps.push(AuditStep::Visit(value));
            }
            PseudoExpr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                steps.push(AuditStep::Visit(else_branch));
                steps.push(AuditStep::Visit(then_branch));
                steps.push(AuditStep::Visit(condition));
            }
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            } => {
                // Reversed: subject, then the subject_name binder, then the
                // clauses in source order.
                for clause in clauses.iter().rev() {
                    steps.push(AuditStep::Clause(clause));
                }
                if let Some(b) = subject_name {
                    steps.push(AuditStep::Bind(b.var_id()));
                }
                steps.push(AuditStep::Visit(subject));
            }
            PseudoExpr::List { elements, tail } => {
                if let Some(t) = tail {
                    steps.push(AuditStep::Visit(t));
                }
                for e in elements.iter().rev() {
                    steps.push(AuditStep::Visit(e));
                }
            }
            PseudoExpr::Tuple(elements) => {
                for e in elements.iter().rev() {
                    steps.push(AuditStep::Visit(e));
                }
            }
            PseudoExpr::Pair(first, second) => {
                steps.push(AuditStep::Visit(second));
                steps.push(AuditStep::Visit(first));
            }
            PseudoExpr::Constr { fields, .. } => {
                for f in fields.iter().rev() {
                    steps.push(AuditStep::Visit(f));
                }
            }
            PseudoExpr::FieldAccess { record, .. } => steps.push(AuditStep::Visit(record)),
            PseudoExpr::IndexAccess { collection, .. } => steps.push(AuditStep::Visit(collection)),
            PseudoExpr::BinOp { left, right, .. } => {
                steps.push(AuditStep::Visit(right));
                steps.push(AuditStep::Visit(left));
            }
            PseudoExpr::UnOp { operand, .. } => steps.push(AuditStep::Visit(operand)),
            PseudoExpr::BuiltinCall { args, .. } => {
                for a in args.iter().rev() {
                    steps.push(AuditStep::Visit(a));
                }
            }
            PseudoExpr::Delay(inner) | PseudoExpr::Force(inner) => {
                steps.push(AuditStep::Visit(inner))
            }
            PseudoExpr::Trace { message, value } => {
                steps.push(AuditStep::Visit(value));
                steps.push(AuditStep::Visit(message));
            }
        }
    }
}

/// A pattern's binder occurrences. A `Literal` payload is an EXPRESSION, so
/// it goes back onto the caller's job stack (pushed last, popping before the
/// clause's guard and body — where the walk visits it) rather than onto
/// the call stack.
fn walk_pattern_audit<'a>(
    pattern: &'a WhenPattern,
    audit: &mut BodyAudit,
    steps: &mut Vec<AuditStep<'a>>,
) {
    match pattern {
        WhenPattern::Constructor { fields, .. } => {
            for f in fields {
                audit.binders.insert(f.var_id());
            }
        }
        WhenPattern::List { elements, tail } => {
            for e in elements {
                audit.binders.insert(e.var_id());
            }
            if let Some(t) = tail {
                audit.binders.insert(t.var_id());
            }
        }
        WhenPattern::Tuple(elements) => {
            for e in elements {
                audit.binders.insert(e.var_id());
            }
        }
        WhenPattern::Pair(a, b) => {
            audit.binders.insert(a.var_id());
            audit.binders.insert(b.var_id());
        }
        WhenPattern::Var(b) => {
            audit.binders.insert(b.var_id());
        }
        WhenPattern::Wildcard => {}
        WhenPattern::Literal(expr) => steps.push(AuditStep::Visit(expr)),
    }
}

// ---------------------------------------------------------------------
// Substitution (ref-for-ref only; replacement ids are FRESH mints, and
// the audits reject any shadowing binder of a substitution target, so
// capture is impossible)
// ---------------------------------------------------------------------

struct VarSubst<'a> {
    map: &'a HashMap<VarId, (String, VarId)>,
}

impl ExprFolder for VarSubst<'_> {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
        if let Some(vid) = id
            && let Some((new_name, new_id)) = self.map.get(&vid)
        {
            return PseudoExpr::Var {
                name: new_name.clone(),
                id: Some(*new_id),
            };
        }
        PseudoExpr::Var { name, id }
    }
}

fn substitute_refs(expr: PseudoExpr, map: &HashMap<VarId, (String, VarId)>) -> PseudoExpr {
    VarSubst { map }.fold(expr)
}

// ---------------------------------------------------------------------
// Consumer rewrite
// ---------------------------------------------------------------------

/// Rewrites every recognized FIRST-projection application of the pair
/// binder to a direct `check_param_value(x, y)` call. Recognized forms:
///
/// 1. `Apply { FieldAccess { Var(e), PairFst }, [x, y] }`
///    (the projection was already classified);
/// 2. `Apply { Apply { Var(e), [fn(u, v) { u }] }, [x, y] }`
///    (the literal church selector form);
/// 3. `Apply { Var(e), [fn(u, v) { u }, x, y] }` (flattened spine).
///
/// Anything else referencing `e`, including ANY second-projection use,
/// is left in place; the caller aborts on the residual reference
/// (invariant (d)).
struct ConsumerRewriter {
    e_id: VarId,
    f1_id: VarId,
    rewrites: usize,
}

impl ConsumerRewriter {
    fn f1_call(&mut self, args: Vec<PseudoExpr>) -> PseudoExpr {
        self.rewrites += 1;
        PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::Var {
                name: FIRST_FN_NAME.to_string(),
                id: Some(self.f1_id),
            }),
            args: args.into(),
        }
    }
}

/// `fn(u, v) { u }` — the literal church pair-FIRST selector.
fn is_fst_selector(expr: &PseudoExpr) -> bool {
    let PseudoExpr::Lambda { params, body } = expr else {
        return false;
    };
    params.len() == 2
        && params[0].var_id() != params[1].var_id()
        && is_var(body, params[0].var_id())
}

impl ExprFolder for ConsumerRewriter {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        // Form 1: e.1st(x, y)
        if args.len() == 2
            && let PseudoExpr::FieldAccess { record, selector } = &function
            && *selector == FieldSelector::PairFst
            && is_var(record, self.e_id)
        {
            return self.f1_call(args);
        }
        // Form 2: (e(fst_selector))(x, y)
        if args.len() == 2
            && let PseudoExpr::Apply {
                function: inner_fn,
                args: inner_args,
            } = &function
            && is_var(inner_fn, self.e_id)
            && inner_args.len() == 1
            && is_fst_selector(&inner_args[0])
        {
            return self.f1_call(args);
        }
        // Form 3: e(fst_selector, x, y)
        if args.len() == 3 && is_var(&function, self.e_id) && is_fst_selector(&args[0]) {
            let mut args = args;
            args.remove(0);
            return self.f1_call(args);
        }
        PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        }
    }
}

// ---------------------------------------------------------------------
// The recognizer + rewriter entry
// ---------------------------------------------------------------------

fn try_recover(
    e_id: Option<VarId>,
    value: &PseudoExpr,
    consumer: &PseudoExpr,
) -> Option<PseudoExpr> {
    let m = match_template(e_id, value)?;

    // Template binders must be pairwise distinct (substitution identity).
    let mut all_ids: Vec<VarId> = m.template_ids.clone();
    all_ids.extend([
        m.arm_a_params[0].var_id(),
        m.arm_a_params[1].var_id(),
        m.arm_b_param.var_id(),
        m.nil_trailing.var_id(),
        m.cons_head.var_id(),
        m.cons_tail.var_id(),
        m.cons_trailing.var_id(),
    ]);
    {
        let mut seen = HashSet::new();
        if !all_ids.iter().all(|id| seen.insert(*id)) {
            return None;
        }
    }

    let pa0 = m.arm_a_params[0].var_id();
    let pa1 = m.arm_a_params[1].var_id();
    let pb0 = m.arm_b_param.var_id();
    let t_nil = m.nil_trailing.var_id();
    let t_cons = m.cons_trailing.var_id();
    let cons_head = m.cons_head.var_id();
    let cons_tail = m.cons_tail.var_id();

    // ---- invariant (c) audits over the three opaque arm bodies ----
    // Substitution targets (d1, d2 + the per-clause trailing binder)
    // must not be shadowed; template ids must not leak in as refs OR
    // binders; every continuation use must be a saturated 2-arg call.
    let arm_a_audit = BodyAudit::collect(m.arm_a_body);
    let nil_audit = BodyAudit::collect(m.nil_body);
    let cons_audit = BodyAudit::collect(m.cons_body);

    for audit in [&arm_a_audit, &nil_audit, &cons_audit] {
        if !audit.only_saturated_2arg_calls(m.d1) || !audit.only_saturated_2arg_calls(m.d2) {
            return None;
        }
        // No arm may reference or rebind any template id except the
        // continuations d1/d2, whose uses are checked saturated above.
        let banned_refs: Vec<VarId> = m
            .template_ids
            .iter()
            .copied()
            .filter(|id| *id != m.d1 && *id != m.d2)
            .collect();
        if audit.refs_any(&banned_refs) || audit.binds_any(&m.template_ids) {
            return None;
        }
    }
    // Cross-scope leak bans: each opaque body may only reference the
    // binders that remain in scope for it AFTER the rewrite.
    if arm_a_audit.refs_any(&[pb0, t_nil, t_cons, cons_head, cons_tail]) {
        return None;
    }
    if nil_audit.refs_any(&[pa0, pa1, t_cons, cons_head, cons_tail])
        || nil_audit.binds_any(&[t_nil, pb0])
    {
        return None;
    }
    if cons_audit.refs_any(&[pa0, pa1, t_nil]) || cons_audit.binds_any(&[t_cons, pb0]) {
        return None;
    }

    // ---- mint the new identities (counter pre-synced at pass entry) ----
    let f1_id = VarId::fresh_binding();
    let f2_id = VarId::fresh_binding();
    let values_id = VarId::fresh_binding();

    // ---- invariant (d): consumer totality ----
    let consumer_audit = BodyAudit::collect(consumer);
    if consumer_audit.binders.contains(&m.e_id) {
        return None; // a shadowing rebind of e — unproven scoping.
    }
    // The pair binder must actually be used (otherwise stay inert) and
    // nothing from the dismantled template may leak into the consumer.
    if consumer_audit.ref_count(m.e_id) == 0 {
        return None;
    }
    let banned_in_consumer: Vec<VarId> = m
        .template_ids
        .iter()
        .copied()
        .filter(|id| *id != m.e_id)
        .chain([pa0, pa1, pb0, t_nil, t_cons, cons_head, cons_tail])
        .collect();
    if consumer_audit.refs_any(&banned_in_consumer) {
        return None;
    }
    let mut rewriter = ConsumerRewriter {
        e_id: m.e_id,
        f1_id,
        rewrites: 0,
    };
    let consumer_rewritten = rewriter.fold(consumer.clone());
    if rewriter.rewrites == 0 {
        return None;
    }
    // Residual check: EVERY use must have been one of the recognized
    // first-projection applications. Any survivor (bare value use,
    // second projection, odd arities) aborts the transform.
    if BodyAudit::collect(&consumer_rewritten).ref_count(m.e_id) != 0 {
        return None;
    }

    // ---- build the two named mutually-recursive functions ----
    let f1_var = (FIRST_FN_NAME.to_string(), f1_id);
    let f2_var = (SECOND_FN_NAME.to_string(), f2_id);

    // F2 = check_param_list(spec, values): the armB body with the
    // fabricated trailing binders redirected to the honest `values`
    // param and the clause arities collapsed to the true 0 / 2.
    let mut nil_map = HashMap::new();
    nil_map.insert(t_nil, (VALUES_PARAM_NAME.to_string(), values_id));
    nil_map.insert(m.d1, f1_var.clone());
    nil_map.insert(m.d2, f2_var.clone());
    let nil_body = substitute_refs(m.nil_body.clone(), &nil_map);

    let mut cons_map = HashMap::new();
    cons_map.insert(t_cons, (VALUES_PARAM_NAME.to_string(), values_id));
    cons_map.insert(m.d1, f1_var.clone());
    cons_map.insert(m.d2, f2_var.clone());
    let cons_body = substitute_refs(m.cons_body.clone(), &cons_map);

    let f2_body = PseudoExpr::When {
        subject: PBox::new(PseudoExpr::Var {
            name: m.arm_b_param.as_str().to_string(),
            id: Some(pb0),
        }),
        subject_name: None,
        clauses: vec![
            WhenClause {
                pattern: WhenPattern::constructor(m.nil_shape.with_arity(0), vec![]),
                guard: None,
                body: nil_body,
            },
            WhenClause {
                pattern: WhenPattern::constructor(
                    m.cons_shape.with_arity(2),
                    vec![m.cons_head.clone(), m.cons_tail.clone()],
                ),
                guard: None,
                body: cons_body,
            },
        ],
    };
    let f2 = PseudoExpr::RecFn {
        name: Binder::new(SECOND_FN_NAME, f2_id),
        params: vec![
            m.arm_b_param.clone(),
            Binder::new(VALUES_PARAM_NAME, values_id),
        ],
        body: PBox::new(f2_body),
    };

    // F1 = check_param_value(<armA params>) with F2 nested inside so
    // both directions of the mutual recursion resolve by simple
    // lexical scope (F2 sees F1 via the RecFn name binder; F1's body
    // sees F2 via the inner let).
    let mut arm_a_map = HashMap::new();
    arm_a_map.insert(m.d1, f1_var);
    arm_a_map.insert(m.d2, f2_var);
    let arm_a_body = substitute_refs(m.arm_a_body.clone(), &arm_a_map);

    let f1 = PseudoExpr::RecFn {
        name: Binder::new(FIRST_FN_NAME, f1_id),
        params: m.arm_a_params.to_vec(),
        body: PBox::new(PseudoExpr::Let {
            name: SECOND_FN_NAME.to_string(),
            id: Some(f2_id),
            value: PBox::new(f2),
            body: PBox::new(arm_a_body),
        }),
    };

    Some(PseudoExpr::Let {
        name: FIRST_FN_NAME.to_string(),
        id: Some(f1_id),
        value: PBox::new(f1),
        body: PBox::new(consumer_rewritten),
    })
}
