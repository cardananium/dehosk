//! Relabel a 3-way `int.compare` producer's nullary `Constr<0|1|2>` leaves
//! to `Ordering` (`Less`/`Equal`/`Greater`) — tag-faithful, never reordered.
//!
//! [`crate::decompile::boolean_cleanup`] leaves a 3-variant sum alone, so
//! the helper still prints as `Unknown_E_0_<tag>` while a consumer `when`
//! already names `Less`/`Equal`/`Greater`. That name mismatch is not
//! compilable. The rename changes no tags: `Constr<N>` still lands in the
//! consumer arm for tag `N`.
//!
//! Fail-closed — fires only when all of these hold:
//! 1. The producer is a 2-level if-chain whose three branches are nullary
//!    `Constr`s with tag set `{0, 1, 2}`.
//! 2. Some `when <call>` consumes the result as exactly those three
//!    guardless `Known(Less/Equal/Greater)` arms. Stub `Unknown` arms do
//!    not qualify (that would be a name disagreement, not a recovery).
//! 3. No other `when` reads the same helper under a different name map.
//! 4. Each branch condition's meaning matches that tag (`==` is Equal, …).
//!    A scrambled comparator (`==`→0, `<=`→2) stays `Unknown_E_0_<tag>` —
//!    a tag-only rename would print "Less" on equal inputs.
//!
//! Needs `DecompileOptions::ordering_names` or a blueprint that pins the
//! literal constructors. A non-`when` use is not a disqualifier.

use crate::pseudo::ast::PBox;
use std::collections::HashSet;

use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::constructor::{ConstructorShape, KnownConstructor};
use crate::pseudo::var_id::VarId;

pub(super) fn recover_ordering_comparator(expr: PseudoExpr) -> PseudoExpr {
    // Pass 1: the VarIds whose result is consumed by a clean 3-way Ordering
    // `when`, minus those SOME OTHER `when` reads under a different name map
    // (e.g. a church-bool `True`/`False` dispatch). Relabeling a helper matched
    // both ways to `Less/Equal/Greater` would disagree with the non-Ordering
    // consumer's arm names (valid-looking-wrong).
    let mut ordering_consumed: HashSet<VarId> = HashSet::new();
    let mut disqualified: HashSet<VarId> = HashSet::new();
    collect_ordering_consumers(&expr, &mut ordering_consumed, &mut disqualified);
    let consumed: HashSet<VarId> = ordering_consumed
        .difference(&disqualified)
        .copied()
        .collect();
    if consumed.is_empty() {
        return expr;
    }
    // Pass 2: rewrite each producer-comparator helper bound to one of those
    // VarIds.
    rewrite(expr, &consumed)
}

/// Walk the tree, classifying each function VarId `f` by how its result is
/// consumed:
///
///   * `out` — `f` has a `when f(args) is { … }` that is a clean 3-way Ordering
///     dispatch (exactly three guardless `Known(Less/Equal/Greater)` arms
///     covering tags {0,1,2}).
///   * `disq` — `f` has SOME OTHER `when f(args) is { … }`: a church-bool
///     `True`/`False`, a different sum, a wildcard/guarded shape, …. Such a
///     consumer reads the result under a different constructor-name map, so
///     relabeling the producer to Ordering would create a NAME disagreement.
///
/// A helper that lands in BOTH sets is dropped from the rewrite (see the
/// `difference` in `recover_ordering_comparator`).
///
/// A *non-`when`* use of `f` (passed as a value, applied into a lambda body,
/// compared `f(..) == Constr<n>`) is NOT a disqualifier — the relabel changes
/// ZERO tags, so such uses stay semantically identical; at worst their render
/// mixes an `Ordering` producer with a stub consumer. Only a competing `when`
/// pins a concrete, conflicting arm-name map.
fn collect_ordering_consumers(
    expr: &PseudoExpr,
    out: &mut HashSet<VarId>,
    disq: &mut HashSet<VarId>,
) {
    let mut pending = vec![expr];
    while let Some(cur) = pending.pop() {
        if let PseudoExpr::When {
            subject, clauses, ..
        } = cur
            && let PseudoExpr::Apply { function, .. } = subject.as_ref()
            && let PseudoExpr::Var { id: Some(fid), .. } = function.as_ref()
        {
            if is_clean_ordering_when(clauses) {
                out.insert(*fid);
            } else {
                disq.insert(*fid);
            }
        }
        pending.extend(cur.provenance_children().into_iter().rev());
    }
}

/// True when `clauses` is exactly three guardless arms, each a nullary
/// `Known(Less/Equal/Greater)` constructor whose Ordering tag matches the
/// pattern tag, together covering the tag set {0, 1, 2}. Wildcard / extra /
/// guarded / non-nullary arms all disqualify (fail-closed).
///
/// Requiring `Known(Less/Equal/Greater)` arms — rather than also accepting
/// un-named `Unknown { tag }` stubs or other known nullary ctors — is the
/// soundness pivot: this pass relabels only the PRODUCER (the comparator
/// body), never the consumer arms, so it must fire only when the consumer is
/// ALREADY an established native-`Ordering` dispatch (its arms named
/// `Less/Equal/Greater` by `adt_disambiguation`). A consumer matching
/// un-named `Unknown { tag }` stubs, church-bool `True`/`False` (which reads
/// the value as a `Bool`), or any other known nullary ctor at tags 0/1 would
/// end up disagreeing with the relabeled producer's names.
fn is_clean_ordering_when(clauses: &[crate::pseudo::ast::WhenClause]) -> bool {
    use crate::pseudo::constructor::KnownConstructor;
    if clauses.len() != 3 {
        return false;
    }
    let mut tags = [false; 3];
    for clause in clauses {
        if clause.guard.is_some() {
            return false;
        }
        let crate::pseudo::ast::WhenPattern::Constructor {
            tag, fields, shape, ..
        } = &clause.pattern
        else {
            return false;
        };
        if !fields.is_empty() || *tag > 2 {
            return false;
        }
        // Each arm must be the `Known` native-`Ordering` variant whose canonical
        // tag matches this pattern tag (Less=0, Equal=1, Greater=2). `Unknown`
        // stubs, church-bool `True`/`False`, and any other known nullary ctor
        // are rejected — the consumer must already be a native Ordering
        // dispatch before the producer is touched.
        let arm_is_ordering = matches!(
            (*tag, shape.as_known()),
            (0, Some(KnownConstructor::Less))
                | (1, Some(KnownConstructor::Equal))
                | (2, Some(KnownConstructor::Greater))
        );
        if !arm_is_ordering {
            return false;
        }
        tags[*tag] = true;
    }
    tags == [true, true, true]
}

fn rewrite(expr: PseudoExpr, consumed: &HashSet<VarId>) -> PseudoExpr {
    use crate::pseudo::fold::ExprFolder;

    struct OrderingRewriter<'a> {
        consumed: &'a HashSet<VarId>,
    }

    impl ExprFolder for OrderingRewriter<'_> {
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
            // The original relabeled the value BEFORE recursing into it, but
            // that's safe to defer to here (after value and body are both
            // already folded): `relabel_comparator_fn` matches only a narrow
            // Lambda/RecFn { If { If { nullary Constr leaf } } } shape whose
            // node kinds this fold never rewrites in place (it only ever
            // changes something at a nested Let), so folding first sees the
            // identical shape the pre-order check would have. The relabel
            // only rewrites `Unknown`-shaped nullary Constrs, so this cannot
            // double-apply.
            let value = if id.is_some_and(|vid| self.consumed.contains(&vid)) {
                relabel_comparator_fn(value)
            } else {
                value
            };
            PseudoExpr::Let {
                name,
                id,
                value: PBox::new(value),
                body: PBox::new(body),
            }
        }
    }

    OrderingRewriter { consumed }.fold(expr)
}

/// If `f` is a 2-param `Lambda`/`RecFn` whose body is the 3-way comparator
/// `if`-chain WITH CANONICAL SEMANTICS, return it with the three branch
/// `Constr`s relabeled to `Ordering`. Otherwise return `f` unchanged.
fn relabel_comparator_fn(f: PseudoExpr) -> PseudoExpr {
    match f {
        PseudoExpr::Lambda { params, body } if params.len() == 2 => {
            if let Some(new_body) = relabel_three_way_if(&body, params[0].id, params[1].id) {
                PseudoExpr::Lambda {
                    params,
                    body: PBox::new(new_body),
                }
            } else {
                PseudoExpr::Lambda { params, body }
            }
        }
        PseudoExpr::RecFn { name, params, body } if params.len() == 2 => {
            if let Some(new_body) = relabel_three_way_if(&body, params[0].id, params[1].id) {
                PseudoExpr::RecFn {
                    name,
                    params,
                    body: PBox::new(new_body),
                }
            } else {
                PseudoExpr::RecFn { name, params, body }
            }
        }
        other => other,
    }
}

/// Relation bitmask over the comparator's `(p, q)` params.
const REL_LT: u8 = 1;
const REL_EQ: u8 = 2;
const REL_GT: u8 = 4;
const REL_ALL: u8 = REL_LT | REL_EQ | REL_GT;

/// The set of `(p, q)` relations under which `cond` is true, or `None` when
/// `cond` is not a direct comparison of EXACTLY the two comparator params
/// (any other shape — arithmetic, derived values, cross-multiplication —
/// fails the semantic gate; fail-closed).
fn relation_set(cond: &PseudoExpr, p: VarId, q: VarId) -> Option<u8> {
    use crate::pseudo::ast::BinaryOp;
    let PseudoExpr::BinOp { op, left, right } = cond else {
        return None;
    };
    let (l, r) = match (left.as_ref(), right.as_ref()) {
        (PseudoExpr::Var { id: Some(a), .. }, PseudoExpr::Var { id: Some(b), .. }) => (*a, *b),
        _ => return None,
    };
    let forward = if l == p && r == q {
        true
    } else if l == q && r == p {
        false
    } else {
        return None;
    };
    Some(match (op, forward) {
        (BinaryOp::Eq, _) => REL_EQ,
        (BinaryOp::Neq, _) => REL_LT | REL_GT,
        (BinaryOp::Lt, true) | (BinaryOp::Gt, false) => REL_LT,
        (BinaryOp::Lte, true) | (BinaryOp::Gte, false) => REL_LT | REL_EQ,
        (BinaryOp::Gt, true) | (BinaryOp::Lt, false) => REL_GT,
        (BinaryOp::Gte, true) | (BinaryOp::Lte, false) => REL_GT | REL_EQ,
        _ => return None,
    })
}

/// The canonical Ordering tag for a SINGLETON relation set.
fn canonical_tag(rel: u8) -> Option<usize> {
    match rel {
        REL_LT => Some(0), // Less
        REL_EQ => Some(1), // Equal
        REL_GT => Some(2), // Greater
        _ => None,
    }
}

/// Match `if c0 { Constr<t0> } else if c1 { Constr<t1> } else { Constr<t2> }`
/// with `{t0,t1,t2} == {0,1,2}` (all nullary) AND CANONICAL SEMANTICS: each
/// branch's effective relation (its condition minus the relations already
/// consumed by earlier branches) must be a singleton whose canonical
/// Ordering tag EQUALS the branch's own tag (`<`→0/Less, `==`→1/Equal,
/// `>`→2/Greater, with operand order accounted for). A scrambled-tag
/// comparator (`==`→tag 0, `<=`→tag 2, else→tag 1) FAILS the gate and keeps
/// honest stub names — prelude names that disagree with the comparison's
/// meaning would lie to the reader even though a tag-only relabel is
/// value-faithful. On match, return the same `If` with each branch
/// relabeled; conditions are preserved verbatim, branches NEVER reordered.
fn relabel_three_way_if(body: &PseudoExpr, p: VarId, q: VarId) -> Option<PseudoExpr> {
    let PseudoExpr::If {
        condition: c0,
        then_branch: t0,
        else_branch: rest,
    } = body
    else {
        return None;
    };
    let PseudoExpr::If {
        condition: c1,
        then_branch: t1,
        else_branch: t2,
    } = rest.as_ref()
    else {
        return None;
    };
    let tag0 = nullary_unknown_tag(t0)?;
    let tag1 = nullary_unknown_tag(t1)?;
    let tag2 = nullary_unknown_tag(t2)?;
    let mut seen = [false; 3];
    for tag in [tag0, tag1, tag2] {
        seen[tag] = true;
    }
    if seen != [true, true, true] {
        return None;
    }
    // Semantic gate: effective relation per branch, in chain order.
    let s0 = relation_set(c0, p, q)?;
    let s1 = relation_set(c1, p, q)?;
    let b0 = s0;
    let b1 = s1 & !s0;
    let b2 = REL_ALL & !(s0 | s1);
    if canonical_tag(b0)? != tag0 || canonical_tag(b1)? != tag1 || canonical_tag(b2)? != tag2 {
        return None;
    }
    Some(PseudoExpr::If {
        condition: c0.clone(),
        then_branch: PBox::new(ordering_constr(tag0)),
        else_branch: PBox::new(PseudoExpr::If {
            condition: c1.clone(),
            then_branch: PBox::new(ordering_constr(tag1)),
            else_branch: PBox::new(ordering_constr(tag2)),
        }),
    })
}

/// Returns the tag if `e` is a nullary `Constr` with an `Unknown` shape and a
/// tag in `{0, 1, 2}`. An already-`Known` constructor (Bool/Ordering/…) is
/// rejected — only un-recovered stub `Constr`s are relabeled.
fn nullary_unknown_tag(e: &PseudoExpr) -> Option<usize> {
    match e {
        PseudoExpr::Constr {
            tag,
            fields,
            shape: ConstructorShape::Unknown { .. },
            ..
        } if fields.is_empty() && *tag <= 2 => Some(*tag),
        _ => None,
    }
}

fn ordering_constr(tag: usize) -> PseudoExpr {
    let kc = match tag {
        0 => KnownConstructor::Less,
        1 => KnownConstructor::Equal,
        2 => KnownConstructor::Greater,
        _ => unreachable!("ordering_constr called with tag {tag} > 2"),
    };
    PseudoExpr::constr_known(kc, vec![])
}

#[cfg(test)]
mod tests;
