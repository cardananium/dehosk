//! Lower multi-variant Scott-encoded eliminator applications to native `when`.
//!
//! A Scott sum is a function of one continuation per variant; applying
//! it (`v(k0, .., kN)`) selects the matching variant and passes its
//! fields. The constructor side already becomes `Constr(Unknown..)`; an
//! eliminator whose subject is an opaque `Var` (a field from decoded
//! data) stays a raw application.
//!
//! A syntactic `v(lambda,..)` rewrite is unsound — church-pair selectors
//! and higher-order calls share the shape. Two fail-closed guards:
//!
//! 1. Origin (`scott_rooted`): `v` is a field/payload binder of a value
//!    matched as a stub-ADT constructor (transitively). Plutus `Data`
//!    cannot contain functions, so a field applied as a function is a
//!    nested Scott value built in-validator — never an externally
//!    supplied HOF (those originate as function parameters).
//! 2. Resolution (`catalog`): every continuation is a lambda or a pure
//!    const, and `v`'s merged arg shape matches a declared stub's
//!    per-variant arity signature. Several stubs sharing the signature
//!    still rebuild, with no type attribution (`Constr<tag>`).
//!

use crate::pseudo::ast::PBox;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

use crate::decompile::TypeHintId;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::{PlainPost, children, plain_children, rebuild_plain, take};

/// Per-variant arity signature of a stub ADT (arity indexed by tag 0..N-1).
type Signature = Vec<usize>;

/// A resolved Scott type for a binder: which stub type it is, and the
/// per-variant arities (so literal-arg continuations get the right wildcard
/// pattern arity).
#[derive(Debug, Clone)]
struct Resolved {
    /// `None` when SEVERAL declared stub types share the signature: the
    /// rebuild is still sound (arities come from the eliminator's own lambda
    /// uses, and a declared type does exist), but naming one would be a
    /// guess, so patterns render as positional `Constr<tag>`.
    type_hint: Option<TypeHintId>,
    arities: Signature,
}

pub(crate) fn resolve_scott_eliminator(expr: PseudoExpr) -> PseudoExpr {
    // 1. Catalog declared stub types by UNIQUE per-variant arity signature.
    let catalog = build_stub_catalog(&expr);
    if catalog.is_empty() {
        return expr;
    }

    // 2. Per-binder eliminator-use arg shapes + non-eliminator uses.
    let mut shapes: HashMap<VarId, Option<Vec<Option<usize>>>> = HashMap::new();
    let mut non_elim: HashSet<VarId> = HashSet::new();
    collect_uses(&expr, false, &mut shapes, &mut non_elim);

    // 3. Resolve each pure-eliminand binder to a unique stub type.
    let mut resolved: HashMap<VarId, Resolved> = HashMap::new();
    for (id, shape) in &shapes {
        if non_elim.contains(id) {
            continue;
        }
        let Some(shape) = shape else { continue }; // inconsistent arg count
        if shape.len() < 2 {
            continue; // single-continuation handled by the existing `expect` path
        }
        if let Some(r) = resolve_shape(shape, &catalog) {
            resolved.insert(*id, r);
        }
    }
    if resolved.is_empty() {
        return expr;
    }

    // 4. Top-down rewrite, gating on `scott_rooted` origin.
    rewrite(expr, &HashSet::new(), &resolved)
}

// ----------------------------------------------------------------------------
// Stub catalog
// ----------------------------------------------------------------------------

/// Map each per-variant arity signature to its declared stub type, or to
/// `None` when SEVERAL types share it (the rebuild still fires, with
/// un-attributed positional patterns; naming one would be a guess).
/// Dropping shared signatures instead would make structural recovery
/// depend on unrelated naming passes — e.g. the opt-in Ordering naming
/// removes a 3-nullary enum from the stub population.
fn build_stub_catalog(expr: &PseudoExpr) -> HashMap<Signature, Option<TypeHintId>> {
    // type_hint -> (tag -> max arity seen)
    let mut by_type: HashMap<TypeHintId, BTreeMap<usize, usize>> = HashMap::new();
    collect_stub_shapes(expr, &mut by_type);

    // signature -> set of type_hints producing it
    let mut by_sig: HashMap<Signature, HashSet<TypeHintId>> = HashMap::new();
    for (th, tags) in &by_type {
        // Only contiguous tag sets 0..N-1 form a usable positional signature.
        let n = tags.len();
        if (0..n).any(|t| !tags.contains_key(&t)) {
            continue;
        }
        let sig: Signature = (0..n).map(|t| tags[&t]).collect();
        by_sig.entry(sig).or_default().insert(th.clone());
    }

    by_sig
        .into_iter()
        .map(|(sig, ths)| {
            if ths.len() == 1 {
                let th = ths.into_iter().next().unwrap();
                (sig, Some(th))
            } else {
                (sig, None)
            }
        })
        .collect()
}

fn collect_stub_shapes(
    expr: &PseudoExpr,
    by_type: &mut HashMap<TypeHintId, BTreeMap<usize, usize>>,
) {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match expr {
            PseudoExpr::Constr {
                tag,
                shape: ConstructorShape::Unknown { arity, .. },
                type_hint: Some(th),
                ..
            } => {
                let e = by_type.entry(th.clone()).or_default();
                let slot = e.entry(*tag).or_insert(0);
                *slot = (*slot).max(*arity);
            }
            PseudoExpr::When { clauses, .. } => {
                for c in clauses {
                    if let WhenPattern::Constructor {
                        tag,
                        shape: ConstructorShape::Unknown { arity, .. },
                        type_hint: Some(th),
                        ..
                    } = &c.pattern
                    {
                        let e = by_type.entry(th.clone()).or_default();
                        let slot = e.entry(*tag).or_insert(0);
                        *slot = (*slot).max(*arity);
                    }
                }
            }
            _ => {}
        }
        pending.extend(children(expr));
    }
}

// ----------------------------------------------------------------------------
// Use collection
// ----------------------------------------------------------------------------

/// The eliminator subject is applied through the Scott calling convention,
/// which `force`s the (delayed) value before applying it:
/// `Apply { function: Force(Var v), args }`. Strip leading `Force`s and
/// return the underlying identified `Var`.
fn scott_head(function: &PseudoExpr) -> Option<(String, VarId)> {
    let mut f = function;
    while let PseudoExpr::Force(inner) = f {
        f = inner;
    }
    if let PseudoExpr::Var { name, id: Some(v) } = f {
        Some((name.clone(), *v))
    } else {
        None
    }
}

fn is_elim_arg(e: &PseudoExpr) -> bool {
    matches!(
        e,
        PseudoExpr::Lambda { .. }
            | PseudoExpr::Bool(_)
            | PseudoExpr::Int(_)
            | PseudoExpr::ByteArray(_)
            | PseudoExpr::String(_)
            | PseudoExpr::Unit
    )
}

fn arg_arity(e: &PseudoExpr) -> Option<usize> {
    match e {
        PseudoExpr::Lambda { params, .. } => Some(params.len()),
        _ => None, // pure const — arity supplied by the resolved stub type
    }
}

/// Walk uses. An "eliminator use" is `Var(v)` applied to >=1 args that are all
/// lambdas-or-pure-consts. Records `v`'s per-position arg arities (None for a
/// const). Any other occurrence of `v` (argument, subject, over-applied head,
/// non-elim-arg call) marks it `non_elim` so the rewrite skips it.
fn collect_uses(
    expr: &PseudoExpr,
    in_apply_fn_pos: bool,
    shapes: &mut HashMap<VarId, Option<Vec<Option<usize>>>>,
    non_elim: &mut HashSet<VarId>,
) {
    let mut pending = vec![(expr, in_apply_fn_pos)];
    while let Some((expr, in_apply_fn_pos)) = pending.pop() {
        if let PseudoExpr::Apply { function, args } = expr {
            if let Some((_, v)) = scott_head(function)
                && !args.is_empty()
                && args.iter().all(is_elim_arg)
            {
                if in_apply_fn_pos {
                    // `v(..)(extra)` — over-applied, not a clean elimination.
                    non_elim.insert(v);
                } else {
                    let this: Vec<Option<usize>> = args.iter().map(arg_arity).collect();
                    merge_shape(shapes, v, this);
                }
                for a in args.iter().rev() {
                    pending.push((a, false));
                }
                continue;
            }
            for a in args.iter().rev() {
                pending.push((a, false));
            }
            pending.push((function, true));
            continue;
        }
        if let PseudoExpr::Var { id: Some(v), .. } = expr {
            non_elim.insert(*v);
            continue;
        }
        for child in children(expr).into_iter().rev() {
            pending.push((child, false));
        }
    }
}

fn merge_shape(
    shapes: &mut HashMap<VarId, Option<Vec<Option<usize>>>>,
    v: VarId,
    this: Vec<Option<usize>>,
) {
    match shapes.get_mut(&v) {
        None => {
            shapes.insert(v, Some(this));
        }
        Some(None) => {}
        Some(Some(prev)) => {
            if prev.len() != this.len() {
                shapes.insert(v, None); // inconsistent variant count
                return;
            }
            // Merge per-position arities: a Some must agree; fill None from the
            // other use. Disagreeing Somes → inconsistent.
            let mut merged = Vec::with_capacity(prev.len());
            let mut ok = true;
            for (a, b) in prev.iter().zip(this.iter()) {
                match (a, b) {
                    (Some(x), Some(y)) if x != y => {
                        ok = false;
                        break;
                    }
                    (Some(x), _) => merged.push(Some(*x)),
                    (None, Some(y)) => merged.push(Some(*y)),
                    (None, None) => merged.push(None),
                }
            }
            if ok {
                shapes.insert(v, Some(merged));
            } else {
                shapes.insert(v, None);
            }
        }
    }
}

/// Resolve a merged arg shape to its stub type by EXACT signature match.
///
/// Every variant's arity must come from at least one lambda use across `v`'s
/// uses; an all-const position would otherwise let an arity be fabricated
/// from the stub, mis-resolving e.g. `v(False, True)` to whatever single
/// 2-variant stub exists. Uses that swap continuation positions (`v(k,c)`
/// and `v(c,k)`) still merge to a fully known signature. A catalog hit
/// shared by several stub types resolves with NO type attribution — the
/// rebuild is arity-driven, only pattern naming needed the type.
fn resolve_shape(
    shape: &[Option<usize>],
    catalog: &HashMap<Signature, Option<TypeHintId>>,
) -> Option<Resolved> {
    let sig: Signature = shape.iter().copied().collect::<Option<Vec<usize>>>()?;
    let th = catalog.get(&sig)?.clone();
    Some(Resolved {
        type_hint: th,
        arities: sig,
    })
}

// ----------------------------------------------------------------------------
// Rewrite
// ----------------------------------------------------------------------------

/// One pending step of [`rewrite`]'s explicit stack: enter a subtree under
/// its `scott_rooted` set, or (once its queued children are on `done`)
/// reassemble it, carrying whatever isn't a child.
///
/// `WhenClauses` and `ScottClause` are the points run between two child walks; they
/// stay separate steps.
enum RewriteStep {
    Enter(PseudoExpr, Rc<HashSet<VarId>>),
    /// Ran after the `When` subject, before the first clause: each clause
    /// extends the outer set with its pattern binders before descending.
    WhenClauses {
        subject_name: Option<Binder>,
        clauses: Vec<WhenClause>,
        subject_is_scott: bool,
        outer: Rc<HashSet<VarId>>,
    },
    /// One continuation of a rewritten Scott eliminator (what `build_when`
    /// did per arg). Its own step because a pure-const continuation mints
    /// its wildcard field binders with `Binder::synthetic`, which hands out
    /// ids in call order: arm `n`'s binders must be minted AFTER arm
    /// `n - 1`'s body has been rewritten.
    ScottClause {
        tag: usize,
        arity: usize,
        arg: PseudoExpr,
        outer: Rc<HashSet<VarId>>,
    },
    Post(RewritePost),
}

enum RewritePost {
    Lambda {
        params: Vec<Binder>,
    },
    RecFn {
        name: Binder,
        params: Vec<Binder>,
    },
    /// The value is folded; whether it lands in the stable set for `body`
    /// depends on the FOLDED value's shape (a rewritten Scott eliminator
    /// collapses to a bare `Var`), so opening the binding is a step of its
    /// own — it can only happen after `value` comes off `done`.
    LetBody {
        name: String,
        id: Option<VarId>,
        body: PseudoExpr,
        stable: Rc<HashSet<VarId>>,
    },
    LetPost {
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
    },
    When {
        subject_name: Option<Binder>,
        /// Per clause: its pattern (never descended into) and whether it
        /// had a guard.
        clause_meta: Vec<(WhenPattern, bool)>,
    },
    /// Reassembles the `when` a Scott eliminator was rewritten into, from
    /// the continuation bodies its `ScottClause` steps left on `done`.
    ScottWhen {
        v: VarId,
        v_name: String,
        type_hint: Option<TypeHintId>,
        count: usize,
    },
    Plain(PlainPost),
}

/// One rewritten Scott continuation awaiting reassembly: everything that
/// is NOT its body expression.
struct ScottArm {
    tag: usize,
    arity: usize,
    fields: Vec<Binder>,
}

/// The scope (`scott_rooted`) rides on each job as an `Rc`, so a subtree's
/// augmented set is shared instead of saved and restored per frame.
fn rewrite(
    expr: PseudoExpr,
    scott_rooted: &HashSet<VarId>,
    resolved: &HashMap<VarId, Resolved>,
) -> PseudoExpr {
    let mut steps = vec![RewriteStep::Enter(expr, Rc::new(scott_rooted.clone()))];
    let mut done: Vec<PseudoExpr> = Vec::new();
    // Scott-arm reassembly data, pushed by `ScottClause` and drained by the
    // matching `Post::ScottWhen`. LIFO like `done`: an arm's own subtree
    // (and any nested eliminator in it) completes before the next arm's
    // step runs.
    let mut arms_done: Vec<ScottArm> = Vec::new();

    while let Some(step) = steps.pop() {
        match step {
            RewriteStep::Enter(expr, stable) => match expr {
                PseudoExpr::Apply { function, args } => {
                    if let Some((v_name, v)) = scott_head(&function)
                        && !args.is_empty()
                        && args.iter().all(is_elim_arg)
                        && stable.contains(&v)
                        && let Some(r) = resolved.get(&v)
                        && r.arities.len() == args.len()
                    {
                        // `build_when`, unrolled: one `ScottClause` step per
                        // continuation, in source order.
                        let count = args.len();
                        steps.push(RewriteStep::Post(RewritePost::ScottWhen {
                            v,
                            v_name,
                            type_hint: r.type_hint.clone(),
                            count,
                        }));
                        for (tag, arg) in args.into_vec().into_iter().enumerate().rev() {
                            steps.push(RewriteStep::ScottClause {
                                tag,
                                arity: r.arities[tag],
                                arg,
                                outer: Rc::clone(&stable),
                            });
                        }
                    } else {
                        steps.push(RewriteStep::Post(RewritePost::Plain(PlainPost::Apply {
                            argc: args.len(),
                        })));
                        for a in args.into_iter().rev() {
                            steps.push(RewriteStep::Enter(a, Rc::clone(&stable)));
                        }
                        steps.push(RewriteStep::Enter(function.into_inner(), stable));
                    }
                }
                PseudoExpr::Lambda { params, body } => {
                    steps.push(RewriteStep::Post(RewritePost::Lambda { params }));
                    steps.push(RewriteStep::Enter(body.into_inner(), stable));
                }
                PseudoExpr::RecFn { name, params, body } => {
                    steps.push(RewriteStep::Post(RewritePost::RecFn { name, params }));
                    steps.push(RewriteStep::Enter(body.into_inner(), stable));
                }
                PseudoExpr::When {
                    subject,
                    subject_name,
                    clauses,
                } => {
                    let subject_is_scott = matches!(
                        subject.as_ref(),
                        PseudoExpr::Var { id: Some(s), .. } if stable.contains(s)
                    );
                    steps.push(RewriteStep::WhenClauses {
                        subject_name,
                        clauses,
                        subject_is_scott,
                        outer: Rc::clone(&stable),
                    });
                    steps.push(RewriteStep::Enter(subject.into_inner(), stable));
                }
                PseudoExpr::Let {
                    name,
                    id,
                    value,
                    body,
                } => {
                    steps.push(RewriteStep::Post(RewritePost::LetBody {
                        name,
                        id,
                        body: body.into_inner(),
                        stable: Rc::clone(&stable),
                    }));
                    steps.push(RewriteStep::Enter(value.into_inner(), stable));
                }
                other => match plain_children(other) {
                    Ok((kind, children)) => {
                        steps.push(RewriteStep::Post(RewritePost::Plain(kind)));
                        for c in children.into_iter().rev() {
                            steps.push(RewriteStep::Enter(c, Rc::clone(&stable)));
                        }
                    }
                    Err(leaf) => done.push(leaf),
                },
            },
            RewriteStep::WhenClauses {
                subject_name,
                clauses,
                subject_is_scott,
                outer,
            } => {
                let mut clause_meta = Vec::with_capacity(clauses.len());
                // Built in source order, then drained onto `steps` in
                // reverse so the jobs pop in source order.
                let mut jobs: Vec<RewriteStep> = Vec::new();
                for c in clauses {
                    let mut inner = (*outer).clone();
                    let pat_is_stub = matches!(
                        &c.pattern,
                        WhenPattern::Constructor {
                            shape: ConstructorShape::Unknown { .. },
                            ..
                        }
                    );
                    // Fields of a stub-matched value, or of an
                    // already-Scott subject, are themselves
                    // Scott-rooted.
                    if pat_is_stub || subject_is_scott {
                        for id in c.pattern.bound_ids() {
                            inner.insert(id);
                        }
                    }
                    if subject_is_scott && let Some(sn) = &subject_name {
                        inner.insert(sn.id);
                    }
                    let inner = Rc::new(inner);
                    clause_meta.push((c.pattern, c.guard.is_some()));
                    if let Some(g) = c.guard {
                        jobs.push(RewriteStep::Enter(g, Rc::clone(&inner)));
                    }
                    jobs.push(RewriteStep::Enter(c.body, inner));
                }
                steps.push(RewriteStep::Post(RewritePost::When {
                    subject_name,
                    clause_meta,
                }));
                while let Some(job) = jobs.pop() {
                    steps.push(job);
                }
            }
            // One Scott continuation: its field binders (minted here for a
            // pure-const arm) become Scott-rooted inside its body.
            RewriteStep::ScottClause {
                tag,
                arity,
                arg,
                outer,
            } => {
                let (fields, body): (Vec<Binder>, PseudoExpr) = match arg {
                    PseudoExpr::Lambda { params, body } => (params, body.into_inner()),
                    // pure-const continuation (e.g. a `False` mismatch shortcut):
                    // ignore this variant's fields with `_` wildcards.
                    konst => ((0..arity).map(|_| Binder::synthetic("_")).collect(), konst),
                };
                // The continuation params become this variant's field binders, so
                // inside its body they are Scott-rooted (fields of a Scott value).
                let mut inner = (*outer).clone();
                for f in &fields {
                    inner.insert(f.id);
                }
                arms_done.push(ScottArm { tag, arity, fields });
                steps.push(RewriteStep::Enter(body, Rc::new(inner)));
            }
            RewriteStep::Post(post) => match post {
                RewritePost::Lambda { params } => {
                    let body = done.pop().expect("lambda body");
                    done.push(PseudoExpr::Lambda {
                        params,
                        body: PBox::new(body),
                    });
                }
                RewritePost::RecFn { name, params } => {
                    let body = done.pop().expect("recfn body");
                    done.push(PseudoExpr::RecFn {
                        name,
                        params,
                        body: PBox::new(body),
                    });
                }
                RewritePost::LetBody {
                    name,
                    id,
                    body,
                    stable,
                } => {
                    let value = done.pop().expect("let value");
                    let mut inner = (*stable).clone();
                    if let (Some(yid), PseudoExpr::Var { id: Some(xid), .. }) = (id, &value)
                        && stable.contains(xid)
                    {
                        inner.insert(yid);
                    }
                    steps.push(RewriteStep::Post(RewritePost::LetPost { name, id, value }));
                    steps.push(RewriteStep::Enter(body, Rc::new(inner)));
                }
                RewritePost::LetPost { name, id, value } => {
                    let body = done.pop().expect("let body");
                    done.push(PseudoExpr::Let {
                        name,
                        id,
                        value: PBox::new(value),
                        body: PBox::new(body),
                    });
                }
                RewritePost::When {
                    subject_name,
                    clause_meta,
                } => {
                    let total = 1 + clause_meta
                        .iter()
                        .map(|(_, has_guard)| usize::from(*has_guard) + 1)
                        .sum::<usize>();
                    let mut parts = take(&mut done, total).into_iter();
                    let new_subject = parts.next().expect("when subject");
                    let new_clauses = clause_meta
                        .into_iter()
                        .map(|(pattern, has_guard)| WhenClause {
                            pattern,
                            guard: has_guard.then(|| parts.next().expect("when guard")),
                            body: parts.next().expect("when clause body"),
                        })
                        .collect();
                    done.push(PseudoExpr::When {
                        subject: PBox::new(new_subject),
                        subject_name,
                        clauses: new_clauses,
                    });
                }
                RewritePost::ScottWhen {
                    v,
                    v_name,
                    type_hint,
                    count,
                } => {
                    let arms = arms_done.split_off(arms_done.len() - count);
                    let mut bodies = take(&mut done, count).into_iter();
                    let clauses = arms
                        .into_iter()
                        .map(|arm| WhenClause {
                            pattern: WhenPattern::Constructor {
                                type_hint: type_hint.clone(),
                                tag: arm.tag,
                                fields: arm.fields,
                                shape: ConstructorShape::scott_positional(arm.tag, arm.arity),
                            },
                            guard: None,
                            body: bodies.next().expect("scott clause body"),
                        })
                        .collect();
                    done.push(PseudoExpr::When {
                        subject: PBox::new(PseudoExpr::Var {
                            name: v_name,
                            id: Some(v),
                        }),
                        subject_name: None,
                        clauses,
                    });
                }
                RewritePost::Plain(kind) => {
                    let rebuilt = rebuild_plain(kind, &mut done);
                    done.push(rebuilt);
                }
            },
        }
    }

    debug_assert_eq!(done.len(), 1, "rewrite must leave one result");
    done.pop().expect("rewrite result")
}

#[cfg(test)]
mod tests;
