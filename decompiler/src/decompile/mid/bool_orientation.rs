//! Church-bool orientation witnesses for Scott two-branch cases.
//!
//! `try_recognize_scott_encoding` mints `Case` branch tags from argument
//! positions, not data constructor tags. For a 2-branch/0-binder Scott
//! case the True arm is not knowable from `(tag, arity)` alone: a
//! church/CPS bool (`\t f -> t` = true, the `ifThenElse` continuation
//! order) selects continuation 0 when true, while a constructor-ordered
//! Scott data Bool (`False = 0`, `True = 1`) selects continuation 1.
//!
//! Feeding position tags into the data-tag table
//! (`KnownConstructor::recognize_two_branch_adt`, `(0,0) -> False`)
//! label-inverts every church-bool `when`. This derives orientation from
//! the producer side instead: a conservative let-environment dataflow
//! from the case scrutinee to construction sites. The circular "which
//! selector is true?" question is broken by `ifThenElse` (`MidExpr::If`
//! exists only from that builtin): its then branch runs exactly when the
//! condition is builtin-true, so `If(c, <fst-selector>, <snd-selector>)`
//! proves `TrueFirst`. A two-arm case over a decoded data tag is the
//! second anchor: ledger data Bool is `True = 1`, so a tag-1 arm yielding
//! the fst-selector likewise proves `TrueFirst`.
//!
//! All resolvable producer leaves must agree (this assigns True/False
//! labels — an all-tail assertion); any unresolved or disagreeing leaf
//! leaves the case unwitnessed with honest positional
//! `Constr<0>/Constr<1>` patterns (fail closed: no Bool claim without a
//! witness).

use std::collections::{HashMap, HashSet};

use crate::pseudo::mid::expr::{CaseEncoding, MidExpr};
use crate::pseudo::mid::expr_id::MidExprId;
use crate::pseudo::var_id::VarId;

/// Resolution depth bound for the value dataflow (Var hops, selector
/// unwraps). A bound, not a tuning knob — unresolved means
/// unwitnessed, never wrong.
///
/// It is also what keeps the dataflow probes (`orient`,
/// `classify_selector`, `resolve`, `orient_datatag`, `join_datatag`,
/// `nullary_constr_tag`) safe to leave RECURSIVE while the rest of the
/// decompiler goes iterative: every one of them decrements `depth` on every
/// self-call and returns at zero, so they cost at most `MAX_DEPTH` call
/// frames — they follow value edges, not the script-controlled nesting of
/// the tree. The one walk here whose depth the script does control is
/// [`scoped_walk`], and that is already an explicit job-stack machine. If a
/// probe ever stops decrementing `depth` on some path, that path becomes
/// unbounded and has to be converted.
const MAX_DEPTH: usize = 32;

/// Which branch position a TRUE scrutinee selects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Orientation {
    /// Truth selects continuation 0 (church/`ifThenElse` convention).
    TrueFirst,
    /// Truth selects continuation 1 (constructor-ordered Scott data Bool).
    FalseFirst,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Selector {
    Fst,
    Snd,
}

/// A lexical binding visible to the orientation dataflow.
///
/// The dataflow env is a TRUE lexical environment, not a flat
/// insert-and-keep map: MIR `VarId`s are NOT globally unique at this pass
/// — precompute (Y-comb conversion, app folding, sibling cloning)
/// duplicates binder ids across DISJOINT sibling scopes, refreshing
/// `MidExprId` only. A flat env would let a Case in one sibling resolve a
/// `Var` to an unrelated sibling's binding and mint a WRONG orientation.
/// `walk` therefore inserts on scope entry and RESTORES on scope exit, so
/// the env holds exactly the bindings on the root→node path — and along a
/// single path every `VarId` is unique.
#[derive(Debug, Clone, Copy)]
enum Binding<'a> {
    /// A `let`-bound value the dataflow may resolve into.
    Value(&'a MidExpr),
    /// A binder with no static producer (lambda param / case branch
    /// binder). In scope — so it SHADOWS any stale outer same-`VarId`
    /// binding — but unresolvable: the dataflow fails closed here.
    Opaque,
}

/// Restore an env slot to its pre-scope state (the value a shadowing
/// binder displaced, or absent).
fn restore<'a>(env: &mut HashMap<VarId, Binding<'a>>, var: VarId, prev: Option<Binding<'a>>) {
    match prev {
        Some(p) => {
            env.insert(var, p);
        }
        None => {
            env.remove(&var);
        }
    }
}

/// Compute orientation witnesses for every Scott 2x0-binder case in the
/// tree. Absent key = no witness = the case must stay positionally
/// `Unknown` (the lowering's fail-closed default).
pub(crate) fn analyze_bool_orientations(root: &MidExpr) -> HashMap<MidExprId, Orientation> {
    let mut env: HashMap<VarId, Binding> = HashMap::new();
    let mut out = HashMap::new();
    walk(root, &mut env, &mut out);
    out
}

/// One pending step of [`scoped_walk`].
enum ScopeStep<'a> {
    /// Fire the visitor on this node, then queue its children.
    Visit(&'a MidExpr),
    /// A non-recursive `let`: bring `var` into scope (the VALUE was walked
    /// outside it) and walk the body under it.
    EnterLetBody {
        var: VarId,
        value: &'a MidExpr,
        body: &'a MidExpr,
    },
    /// A `case` branch: its binders are in scope for its body only.
    EnterBranch(&'a crate::pseudo::mid::expr::MidBranch),
    /// Put shadowed bindings back, innermost first.
    Restore(Vec<(VarId, Option<Binding<'a>>)>),
}

/// Pre-order walk that maintains the `VarId → Binding` scope, iteratively.
fn scoped_walk<'a, F>(root: &'a MidExpr, env: &mut HashMap<VarId, Binding<'a>>, mut visit: F)
where
    F: FnMut(&'a MidExpr, &HashMap<VarId, Binding<'a>>),
{
    let mut steps: Vec<ScopeStep<'a>> = vec![ScopeStep::Visit(root)];
    while let Some(step) = steps.pop() {
        match step {
            ScopeStep::Visit(expr) => {
                visit(expr, env);
                match expr {
                    MidExpr::Let {
                        var, value, body, ..
                    } => {
                        steps.push(ScopeStep::EnterLetBody {
                            var: *var,
                            value,
                            body,
                        });
                        steps.push(ScopeStep::Visit(value));
                    }
                    MidExpr::Closure { params, body, .. } => {
                        let saved: Vec<(VarId, Option<Binding<'a>>)> = params
                            .iter()
                            .map(|p| (*p, env.insert(*p, Binding::Opaque)))
                            .collect();
                        steps.push(ScopeStep::Restore(saved));
                        steps.push(ScopeStep::Visit(body));
                    }
                    MidExpr::Case {
                        scrutinee,
                        branches,
                        ..
                    } => {
                        for b in branches.iter().rev() {
                            steps.push(ScopeStep::EnterBranch(b));
                        }
                        steps.push(ScopeStep::Visit(scrutinee));
                    }
                    other => {
                        for child in other.children().into_iter().rev() {
                            steps.push(ScopeStep::Visit(child));
                        }
                    }
                }
            }
            ScopeStep::EnterLetBody { var, value, body } => {
                let prev = env.insert(var, Binding::Value(value));
                steps.push(ScopeStep::Restore(vec![(var, prev)]));
                steps.push(ScopeStep::Visit(body));
            }
            ScopeStep::EnterBranch(b) => {
                let saved: Vec<(VarId, Option<Binding<'a>>)> = b
                    .binders
                    .iter()
                    .map(|p| (*p, env.insert(*p, Binding::Opaque)))
                    .collect();
                steps.push(ScopeStep::Restore(saved));
                steps.push(ScopeStep::Visit(&b.body));
            }
            ScopeStep::Restore(saved) => {
                for (p, prev) in saved.into_iter().rev() {
                    restore(env, p, prev);
                }
            }
        }
    }
}

fn walk<'a>(
    expr: &'a MidExpr,
    env: &mut HashMap<VarId, Binding<'a>>,
    out: &mut HashMap<MidExprId, Orientation>,
) {
    scoped_walk(expr, env, |node, env| {
        let MidExpr::Case {
            id,
            scrutinee,
            branches,
            encoding,
        } = node
        else {
            return;
        };
        if *encoding == CaseEncoding::Scott
            && branches.len() == 2
            && branches.iter().all(|b| b.binders.is_empty())
            && let Some(o) = orient(scrutinee, env, &mut HashSet::new(), MAX_DEPTH)
        {
            out.insert(*id, o);
        }
    });
}

/// Orient a church-bool VALUE: which continuation position does it select
/// when the boolean it encodes is true? `None` = no structural witness.
fn orient<'a>(
    expr: &'a MidExpr,
    env: &HashMap<VarId, Binding<'a>>,
    visiting: &mut HashSet<VarId>,
    depth: usize,
) -> Option<Orientation> {
    if depth == 0 {
        return None;
    }
    crate::stack::grow_pass(|| match expr {
        MidExpr::Thunk { body, .. } | MidExpr::Trace { body, .. } => {
            orient(body, env, visiting, depth - 1)
        }
        MidExpr::Force {
            resolved: Some(r), ..
        } => orient(r, env, visiting, depth - 1),
        MidExpr::Force { body, .. } => orient(body, env, visiting, depth - 1),
        MidExpr::Var { var, .. } => {
            // Cycle guard, not a memo: remove after so diamond sharing still
            // resolves.
            if !visiting.insert(*var) {
                return None;
            }
            let r = match env.get(var) {
                Some(Binding::Value(bound)) => orient(bound, env, visiting, depth - 1),
                // Opaque binder (param/branch) or out of scope: no producer.
                _ => None,
            };
            visiting.remove(var);
            r
        }
        MidExpr::If {
            then_branch,
            else_branch,
            ..
        } => {
            // The anchor: MidExpr::If exists only from builtin ifThenElse,
            // so then runs exactly on builtin-true.
            let then_sel = classify_selector(then_branch, env, &mut HashSet::new(), depth - 1);
            let else_sel = classify_selector(else_branch, env, &mut HashSet::new(), depth - 1);
            // DISPLAY CONTRACT for FalseFirst: the label follows the
            // semantic condition `c` (the `then` arm runs when `c` is true),
            // NOT the church value's own fst=true convention. For
            // `If(c, snd, fst)` the church VALUE is fst (true) exactly when
            // `c` is false, so any other surface that church-DISPLAYS this
            // same subject reads `!c` while these branch labels read `c`.
            match (then_sel, else_sel) {
                (Some(Selector::Fst), Some(Selector::Snd)) => Some(Orientation::TrueFirst),
                (Some(Selector::Snd), Some(Selector::Fst)) => Some(Orientation::FalseFirst),
                // Same selector on both sides: the value is constant w.r.t.
                // the condition — no orientation info, and a downstream Bool
                // label would be a guess.
                (Some(_), Some(_)) => None,
                // Not selector leaves: both sides must be producers of the
                // SAME convention.
                _ => {
                    let t = orient(then_branch, env, visiting, depth - 1)?;
                    let e = orient(else_branch, env, visiting, depth - 1)?;
                    (t == e).then_some(t)
                }
            }
        }
        MidExpr::Case {
            branches, encoding, ..
        } => {
            // Data-tag anchor (NOT valid for Scott cases, whose tags are
            // positions): a two-arm dispatch over a real data tag where the
            // tag-1 arm yields the fst-selector is a decoded ledger data
            // Bool (True = 1) re-encoded as church — truth-selects-first.
            if *encoding != CaseEncoding::Scott
                && branches.len() == 2
                && branches.iter().all(|b| b.binders.is_empty())
            {
                let sel_of = |tag: usize| {
                    branches.iter().find(|b| b.tag == tag).and_then(|b| {
                        classify_selector(&b.body, env, &mut HashSet::new(), depth - 1)
                    })
                };
                match (sel_of(0), sel_of(1)) {
                    (Some(Selector::Snd), Some(Selector::Fst)) => {
                        return Some(Orientation::TrueFirst);
                    }
                    (Some(Selector::Fst), Some(Selector::Snd)) => {
                        return Some(Orientation::FalseFirst);
                    }
                    _ => {}
                }
            }
            // Generic join: every branch must be a producer of the same
            // convention.
            let mut acc: Option<Orientation> = None;
            for b in branches {
                let o = orient(&b.body, env, visiting, depth - 1)?;
                match acc {
                    Some(prev) if prev != o => return None,
                    _ => acc = Some(o),
                }
            }
            acc
        }
        MidExpr::Apply { function, args, .. } => {
            // The call's RESULT carries the orientation; params stay
            // unresolved (a selector flowing in through a param leaf makes
            // the body's own leaves unresolvable -> None, fail closed).
            //
            // Do NOT beta-reduce here (bind params->args, orient the body):
            // it reaches the producer behind an identity or
            // selector-passing helper `(\p.p)(ifThenElse …)`, but it also
            // mis-orients at least one integer comparator as FalseFirst
            // where the UPLC is TrueFirst, inverting the render and
            // leaving a dead branch.
            match resolve(function, env, depth - 1)? {
                MidExpr::Closure {
                    params,
                    body,
                    recursive: None,
                    ..
                } if params.len() == args.len() => orient(body, env, visiting, depth - 1),
                // Partial/over-application: the applied value is NOT the
                // closure body's value, so its orientation does not carry.
                _ => None,
            }
        }
        _ => None,
    })
}

/// Structurally classify a 2-parameter selector constant: `\a b -> a`
/// (`Fst`) or `\a b -> b` (`Snd`), through thunk/force/trace wrappers, Var
/// hops, and curried or merged param lists. Anything else (including
/// thunks BETWEEN the two lambdas, which change application arity) is
/// `None`.
fn classify_selector<'a>(
    expr: &'a MidExpr,
    env: &HashMap<VarId, Binding<'a>>,
    visiting: &mut HashSet<VarId>,
    depth: usize,
) -> Option<Selector> {
    if depth == 0 {
        return None;
    }
    crate::stack::grow_pass(|| match expr {
        MidExpr::Thunk { body, .. } | MidExpr::Trace { body, .. } => {
            classify_selector(body, env, visiting, depth - 1)
        }
        MidExpr::Force {
            resolved: Some(r), ..
        } => classify_selector(r, env, visiting, depth - 1),
        MidExpr::Force { body, .. } => classify_selector(body, env, visiting, depth - 1),
        MidExpr::Var { var, .. } => {
            if !visiting.insert(*var) {
                return None;
            }
            let r = match env.get(var) {
                Some(Binding::Value(bound)) => classify_selector(bound, env, visiting, depth - 1),
                _ => None,
            };
            visiting.remove(var);
            r
        }
        MidExpr::Closure {
            params,
            body,
            recursive: None,
            ..
        } => {
            let mut chain: Vec<VarId> = params.clone();
            let mut cur: &MidExpr = body;
            while let MidExpr::Closure {
                params,
                body,
                recursive: None,
                ..
            } = cur
            {
                chain.extend(params.iter().copied());
                cur = body;
            }
            if chain.len() != 2 {
                return None;
            }
            match cur {
                MidExpr::Var { var, .. } if *var == chain[0] => Some(Selector::Fst),
                MidExpr::Var { var, .. } if *var == chain[1] => Some(Selector::Snd),
                _ => None,
            }
        }
        _ => None,
    })
}

/// Resolve a value to its defining non-wrapper expression (for `Apply`
/// callee lookup).
fn resolve<'a>(
    expr: &'a MidExpr,
    env: &HashMap<VarId, Binding<'a>>,
    depth: usize,
) -> Option<&'a MidExpr> {
    if depth == 0 {
        return None;
    }
    match expr {
        MidExpr::Var { var, .. } => match env.get(var) {
            Some(Binding::Value(b)) => resolve(b, env, depth - 1),
            _ => None,
        },
        MidExpr::Thunk { body, .. } | MidExpr::Trace { body, .. } => resolve(body, env, depth - 1),
        MidExpr::Force {
            resolved: Some(r), ..
        } => resolve(r, env, depth - 1),
        MidExpr::Force { body, .. } => resolve(body, env, depth - 1),
        other => Some(other),
    }
}

// ---------------------------------------------------------------------------
// Data-tag church-bool conventions.
//
// The pass above models SCOTT/CPS selector church bools. Some scripts
// instead encode a church bool as a DATA TAG (`if c {Constr<a>} else
// {Constr<b>}`, a/b nullary) consumed by Native cases — a different
// encoding. This resolves, for each Native 2x0-binder case (the consumer),
// its scrutinee to a data-tag producer and reports `church_true = a` (the
// `then` arm runs when `c` holds, so its Constr tag is the bool's true).
// Fail-closed.
// ---------------------------------------------------------------------------

/// Compute data-tag church-bool conventions: for every Native 2x0-binder case
/// (the consumer) whose scrutinee resolves to a data-tag church-bool producer
/// `if c {Constr<a>} else {Constr<b>}`, map its `MidExprId` to `church_true =
/// a`. Absent key = no witness = the case keeps the program-flag fallback.
/// `DEHOSK_DATATAG_PROBE` in the env dumps each decision to stderr.
/// Fail-closed.
pub(crate) fn analyze_datatag_church_conventions(root: &MidExpr) -> HashMap<MidExprId, usize> {
    let mut env: HashMap<VarId, Binding> = HashMap::new();
    let mut out: HashMap<MidExprId, usize> = HashMap::new();
    let dump = crate::debug_env::datatag_probe();
    dt_walk(root, &mut env, &mut out, dump);
    out
}

fn dt_walk<'a>(
    expr: &'a MidExpr,
    env: &mut HashMap<VarId, Binding<'a>>,
    out: &mut HashMap<MidExprId, usize>,
    dump: bool,
) {
    scoped_walk(expr, env, |node, env| {
        let MidExpr::Case {
            id,
            scrutinee,
            branches,
            encoding,
        } = node
        else {
            return;
        };
        if *encoding != CaseEncoding::Scott
            && branches.len() == 2
            && branches.iter().all(|b| b.binders.is_empty())
            // Only reorient a GENUINE Bool collapse: every arm body must
            // be church-bool-valued (a church-bool producer, a bare nullary
            // church Constr, or fail). A sum/Option dispatch over a church
            // bool — arms yielding `None` and `if b { <work> }` — is
            // consumed as a STUB ADT, not a Bool; reorienting it would
            // invert a faithful dispatch. Fail-closed: a non-Bool arm body
            // leaves the case unwitnessed.
            && branches
                .iter()
                .all(|b| is_church_bool_valued(&b.body, env, MAX_DEPTH))
            && let Some(ct) = orient_datatag(scrutinee, env, &mut HashSet::new(), MAX_DEPTH)
        {
            out.insert(*id, ct);
            if dump {
                let tags: Vec<usize> = branches.iter().map(|b| b.tag).collect();
                eprintln!(
                    "[b21dt] case={:?} arm_tags={:?} church_true=Some({}) swap={}",
                    id,
                    tags,
                    ct,
                    ct == 0
                );
            }
        } else if dump
            && *encoding != CaseEncoding::Scott
            && branches.len() == 2
            && branches.iter().all(|b| b.binders.is_empty())
        {
            let tags: Vec<usize> = branches.iter().map(|b| b.tag).collect();
            eprintln!(
                "[b21dt] case={:?} arm_tags={:?} church_true=None swap=NO-WITNESS",
                id, tags
            );
        }
    });
}

/// Resolve a value to a data-tag church bool's `church_true` tag: an
/// `If(c, then, else)` whose `then`/`else` resolve to distinct nullary
/// `Constr<a>`/`Constr<b>` yields `Some(a)` (then runs when `c` holds).
fn orient_datatag<'a>(
    expr: &'a MidExpr,
    env: &HashMap<VarId, Binding<'a>>,
    visiting: &mut HashSet<VarId>,
    depth: usize,
) -> Option<usize> {
    if depth == 0 {
        return None;
    }
    crate::stack::grow_pass(|| match expr {
        MidExpr::Thunk { body, .. } | MidExpr::Trace { body, .. } => {
            orient_datatag(body, env, visiting, depth - 1)
        }
        MidExpr::Force {
            resolved: Some(r), ..
        } => orient_datatag(r, env, visiting, depth - 1),
        MidExpr::Force { body, .. } => orient_datatag(body, env, visiting, depth - 1),
        MidExpr::Var { var, .. } => {
            if !visiting.insert(*var) {
                return None;
            }
            let r = match env.get(var) {
                Some(Binding::Value(bound)) => orient_datatag(bound, env, visiting, depth - 1),
                _ => None,
            };
            visiting.remove(var);
            r
        }
        MidExpr::If {
            then_branch,
            else_branch,
            ..
        } => {
            // Direct data-tag producer `if c {Constr<a>} else {Constr<b>}`
            // (the unambiguous anchor: then runs when c holds, so a is
            // church_true). If the branches are not bare nullary Constrs, fall
            // back to joining them as church-bool sub-producers (e.g. nested
            // `if`/`case`).
            if let (Some(a), Some(b)) = (
                nullary_constr_tag(then_branch, env, depth - 1),
                nullary_constr_tag(else_branch, env, depth - 1),
            ) {
                // A church bool's tags are exactly {0,1}. Requiring a,b <= 1
                // (and distinct) is essential: `false_tag_for_shape` derives
                // the false tag as the {0,1} sibling, so a producer like
                // `if c {Constr<0>} else {Constr<2>}` (church_true=0, false on
                // tag 2) would be mis-decoded. Non-{0,1} tags -> fall through
                // to the join, which fails closed on the non-church leaf.
                if a != b && a <= 1 && b <= 1 {
                    return Some(a);
                }
            }
            join_datatag(
                [then_branch.as_ref(), else_branch.as_ref()].into_iter(),
                env,
                visiting,
                depth - 1,
            )
        }
        MidExpr::Case { branches, .. } => {
            // A church bool produced by a sum-type dispatch (Result/Option
            // `when variant is { Ok -> <church bool>; Error -> <church bool> }`).
            // Join the arms: every arm that DEFINITELY carries a convention
            // (an inner `if`-producer) must agree; bare nullary Constr arms
            // (church-true/false constants) carry no definite convention and
            // are skipped. At least one definite arm is required (else None,
            // fail-closed).
            join_datatag(branches.iter().map(|b| &b.body), env, visiting, depth - 1)
        }
        _ => None,
    })
}

/// Is `expr` church-bool-VALUED — i.e. a valid arm body of a genuine Bool
/// collapse? True for a church-bool producer (`if`/`case` yielding nullary
/// church Constrs), a bare nullary church Constr (a church-true/false
/// constant), or `Error`/fail. False for a sum/Option value: `None` alone
/// passes as a bare Constr, but `Some(x)` or an Option-returning `if` does
/// not. Fail-closed.
fn is_church_bool_valued<'a>(
    expr: &'a MidExpr,
    env: &HashMap<VarId, Binding<'a>>,
    depth: usize,
) -> bool {
    // A bare nullary Constr counts only for the church-bool tags {0,1} — a
    // non-{0,1} nullary constructor is a genuine sum value, not a church bool
    // constant.
    nullary_constr_tag(expr, env, depth).is_some_and(|t| t <= 1)
        || orient_datatag(expr, env, &mut HashSet::new(), depth).is_some()
        || matches!(expr, MidExpr::Error { .. })
}

/// Join the church-bool conventions of several sub-expressions: each that
/// yields a definite `church_true` (an `if`/`case` producer) must agree; bare
/// nullary-Constr leaves (no definite convention) are skipped. Returns the
/// agreed tag, or `None` if there is no definite arm or two disagree.
fn join_datatag<'a, I: Iterator<Item = &'a MidExpr>>(
    items: I,
    env: &HashMap<VarId, Binding<'a>>,
    visiting: &mut HashSet<VarId>,
    depth: usize,
) -> Option<usize> {
    if depth == 0 {
        return None;
    }
    let mut acc: Option<usize> = None;
    for item in items {
        // A DEFINITELY-non-church arm fails the join (fail-closed): a
        // constructor WITH fields (a real sum value like `Some(x)`), a nullary
        // Constr with a non-church tag (>= 2), or a non-Bool literal/list. None
        // of these can be a church bool, so this is not a Bool producer.
        if is_definitely_non_church(item, env, depth - 1) {
            return None;
        }
        // A church-bool CONSTANT (Constr<0>/Constr<1>) carries no definite
        // convention but is compatible — skip it.
        if matches!(nullary_constr_tag(item, env, depth - 1), Some(t) if t <= 1) {
            continue;
        }
        match orient_datatag(item, env, visiting, depth - 1) {
            Some(ct) => match acc {
                Some(prev) if prev != ct => return None,
                _ => acc = Some(ct),
            },
            // A church-bool-SHAPED arm (case/if/apply/let/var) that
            // `orient_datatag` cannot fully trace: skip it. SOUND for a
            // uniformly-encoded church bool (every real PlutusTx church
            // bool uses ONE convention, so the untraceable arm shares the
            // witnessed convention). A SELF-INCONSISTENT bool — different
            // conventions on different producer paths, one of them
            // untraceable — could be mis-oriented; the
            // is_definitely_non_church gate above rejects only the clearly
            // non-bool case.
            None => continue,
        }
    }
    acc
}

/// True when `expr` provably CANNOT be a church bool: a constructor carrying
/// fields (a genuine sum value), a non-church nullary Constr (tag >= 2), or a
/// non-Bool literal. Used to fail the producer join closed on a clearly
/// non-church arm (vs an untraceable but church-bool-shaped arm).
fn is_definitely_non_church<'a>(
    expr: &'a MidExpr,
    _env: &HashMap<VarId, Binding<'a>>,
    depth: usize,
) -> bool {
    let mut current = expr;
    let mut depth = depth;
    loop {
        if depth == 0 {
            return false;
        }
        match current {
            MidExpr::Thunk { body, .. } | MidExpr::Trace { body, .. } => {
                current = body;
                depth -= 1;
            }
            MidExpr::Force {
                resolved: Some(r), ..
            } => {
                current = r;
                depth -= 1;
            }
            MidExpr::Force { body, .. } => {
                current = body;
                depth -= 1;
            }
            // A constructor WITH fields is a real sum value, never a church bool.
            MidExpr::Constr { fields, tag, .. } => return !fields.is_empty() || *tag > 1,
            // Non-Bool literals are not church bools (church bools are Constrs).
            MidExpr::Lit { value, .. } => {
                return !matches!(value, crate::pseudo::mid::expr::MidLiteral::Bool(_));
            }
            _ => return false,
        }
    }
}

/// Resolve a value to a nullary `Constr` tag (a church-bool data leaf),
/// through wrapper/Var hops. `None` if it is not a nullary constructor.
fn nullary_constr_tag<'a>(
    expr: &'a MidExpr,
    env: &HashMap<VarId, Binding<'a>>,
    depth: usize,
) -> Option<usize> {
    if depth == 0 {
        return None;
    }
    match expr {
        MidExpr::Thunk { body, .. } | MidExpr::Trace { body, .. } => {
            nullary_constr_tag(body, env, depth - 1)
        }
        MidExpr::Force {
            resolved: Some(r), ..
        } => nullary_constr_tag(r, env, depth - 1),
        MidExpr::Force { body, .. } => nullary_constr_tag(body, env, depth - 1),
        MidExpr::Var { var, .. } => match env.get(var) {
            Some(Binding::Value(b)) => nullary_constr_tag(b, env, depth - 1),
            _ => None,
        },
        MidExpr::Constr { tag, fields, .. } if fields.is_empty() => Some(*tag),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
