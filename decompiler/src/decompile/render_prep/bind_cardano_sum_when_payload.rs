//! Bind nullary `when <cardano-sum>` arms that re-project the ABI payload by hand.
//!
//! A nullary `Constr<tag>` arm that re-reads `<subject>.fields[i]` binds no
//! payload, while the real ABI constructor (e.g. `ScriptInfo::Proposing`) has
//! a non-zero arity, so arity-gated [`name_cardano_sum_arms`](super::name_cardano_sum_arms)
//! declines: a nullary `Proposing` is not valid surface syntax. When the subject
//! resolves to a [`SumTypeId`] via
//! [`when_subject_cardano_sum`](super::name_cardano_sum_arms::when_subject_cardano_sum)
//! and every non-wildcard arm is a nullary `Constr<tag>` with trusted ABI
//! arity `n` ([`known_ctor_arity`](super::name_cardano_sum_arms::known_ctor_arity)),
//! bind `n` fresh positional fields and rewrite every `<subject>.fields[i]` to
//! `field_i`. `name_cardano_sum_arms` must run after this pass; no name is attached here (worst case an honest `Constr<tag>(field_0, …)`).
//!
//! Pure alpha-rewrite: identical projected values, tag dispatch, `_ -> fail`
//! arm, failing-input set, evaluation order; no trace dropped. `n` comes from
//! the trusted Plutus-ABI table (inheriting its version gates) — the bound
//! arity is the ledger arity. The nullary `Constr<tag>` was already invalid
//! surface — invalid→valid, never valid→valid-looking-wrong. Every
//! gate is required, else the whole `when` is untouched: subject resolves
//! to a `SumTypeId`; every non-wildcard arm is a nullary `Constr<tag>` with
//! `known_ctor_arity(id, tag) == Some(n)` (unknown ⇒ bail); no
//! `<subject>.fields[i]` with `i >= n` in any arm (a wider projection would
//! prove the subject is not this `n`-field constructor — bail); at least
//! one arm binds (`n > 0`). `when_subject_cardano_sum` keys a `FieldAccess`
//! subject off its selector name (`.script_info`/`.purpose`/…); the arity
//! gate backstops that reserved-name convention. Only the downstream name
//! could be wrong on a non-Cardano record with a reserved context-field name
//! and coincident tag+arity — the residual the naming pass already carries.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::constructor::ConstructorShape;
use crate::pseudo::field_selector::FieldSelector;
use crate::pseudo::fold::{ExprFolder, FoldAction};
use crate::pseudo::var_id::VarId;

use super::cardano_type_env::CardanoTypeEnv;
use super::ctx::RenderCtx;
use super::name_cardano_sum_arms::{known_ctor_arity, when_subject_cardano_sum};
use super::scope_recurse::children;

/// Reshape nullary `when <cardano-sum>` arms into ABI-arity payload binders.
///
/// The [`CardanoTypeEnv`] resolves a `when` over a bare binder by dataflow
/// type rather than by name alone; pass [`CardanoTypeEnv::default`] for the
/// name-only first run.
pub(super) fn bind_cardano_sum_when_payload(
    expr: PseudoExpr,
    env: &CardanoTypeEnv,
    ctx: &RenderCtx,
) -> PseudoExpr {
    walk(expr, ctx, env)
}

fn walk(expr: PseudoExpr, ctx: &RenderCtx, env: &CardanoTypeEnv) -> PseudoExpr {
    struct BindWalker<'a> {
        ctx: &'a RenderCtx,
        env: &'a CardanoTypeEnv,
    }
    impl ExprFolder for BindWalker<'_> {
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
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            try_bind(
                PBox::new(subject),
                subject_name,
                clauses,
                self.ctx,
                self.env,
            )
        }
    }
    BindWalker { ctx, env }.fold(expr)
}

fn try_bind(
    subject: PBox,
    subject_name: Option<Binder>,
    clauses: Vec<WhenClause>,
    ctx: &RenderCtx,
    env: &CardanoTypeEnv,
) -> PseudoExpr {
    // Borrow `subject`/`clauses` while planning so the bail path can return
    // them untouched. `Some(n)` = bind `n` fields; `None` = leave the clause
    // as-is (wildcard / arity-0).
    let plan: Option<Vec<Option<usize>>> =
        // `None` ⇒ V1/V2-ambiguous; default to V2 (the version-gated ABI
        // tables self-restrict V3-only sums, so a V3 sum can never resolve
        // under V2).
        when_subject_cardano_sum(&subject, ctx.version_or_v2(), env).and_then(|sum_id| {
            let mut arities: Vec<Option<usize>> = Vec::with_capacity(clauses.len());
            for c in &clauses {
                match &c.pattern {
                    // Only the un-bound (nullary) form is a target.
                    WhenPattern::Constructor { tag, fields, .. } if fields.is_empty() => {
                        let n = known_ctor_arity(sum_id, *tag, ctx)?;
                        // Range-check BOTH body and guard (bind_arm rewrites
                        // both): an out-of-range projection anywhere disproves
                        // the arity, so bail (fail-closed).
                        if !arm_projections_in_range(&c.body, &subject, n)
                            || c
                                .guard
                                .as_ref()
                                .is_some_and(|g| !arm_projections_in_range(g, &subject, n))
                        {
                            return None;
                        }
                        arities.push(if n > 0 { Some(n) } else { None });
                    }
                    WhenPattern::Wildcard => arities.push(None),
                    // A non-nullary ctor (already bound) or a non-ctor
                    // pattern (Var/List/Tuple/Pair/Literal) is not the clean
                    // nullary tag-dispatch this pass targets — bail.
                    _ => return None,
                }
            }
            arities.iter().any(Option::is_some).then_some(arities)
        });

    match plan {
        Some(arities) => {
            let clauses = clauses
                .into_iter()
                .zip(arities)
                .map(|(c, arity)| match arity {
                    Some(n) => bind_arm(c, &subject, n),
                    None => c,
                })
                .collect();
            PseudoExpr::When {
                subject,
                subject_name,
                clauses,
            }
        }
        None => PseudoExpr::When {
            subject,
            subject_name,
            clauses,
        },
    }
}

/// Bind `n` fresh positional fields into the arm's `Constr<tag>` pattern and
/// rewrite `<subject>.fields[i] → field_i` in its body/guard.
fn bind_arm(c: WhenClause, subject: &PseudoExpr, n: usize) -> WhenClause {
    let WhenClause {
        pattern,
        guard,
        body,
    } = c;
    let WhenPattern::Constructor {
        type_hint,
        tag,
        shape,
        ..
    } = pattern
    else {
        // Unreachable: try_bind only schedules `Some(n)` for nullary ctors.
        return WhenClause {
            pattern,
            guard,
            body,
        };
    };
    let binders: Vec<Binder> = (0..n)
        .map(|i| Binder::new(format!("field_{i}"), VarId::fresh_binding()))
        .collect();
    let body = rewrite_projections(body, subject, &binders);
    let guard = guard.map(|g| rewrite_projections(g, subject, &binders));
    // Keep the shape's arity consistent with the now-bound field count.
    let shape = match shape {
        ConstructorShape::Unknown { tag, .. } => ConstructorShape::unknown_data(tag, n),
        other => other,
    };
    WhenClause {
        pattern: WhenPattern::Constructor {
            type_hint,
            tag,
            shape,
            fields: binders,
        },
        guard,
        body,
    }
}

/// VarId-SENSITIVE structural equality for the subject path (a `Var` or a
/// `FieldAccess`/`IndexAccess` chain rooted in one). `PseudoExpr`'s own
/// `PartialEq` compares `Var`s by NAME only and would confuse two same-named
/// binders; matching by `VarId` keeps a projection of a DIFFERENT record from
/// being rewritten or range-checked as the subject's. Unrecognized shapes
/// don't match — a missed bind, never a wrong one.
fn subject_eq(a: &PseudoExpr, b: &PseudoExpr) -> bool {
    use PseudoExpr::*;
    let (mut a, mut b) = (a, b);
    loop {
        match (a, b) {
            (Var { id: Some(x), .. }, Var { id: Some(y), .. }) => return x == y,
            (
                Var {
                    id: None, name: n1, ..
                },
                Var {
                    id: None, name: n2, ..
                },
            ) => return n1 == n2,
            (
                FieldAccess {
                    record: r1,
                    selector: s1,
                },
                FieldAccess {
                    record: r2,
                    selector: s2,
                },
            ) => {
                if s1 != s2 {
                    return false;
                }
                a = r1;
                b = r2;
            }
            (
                IndexAccess {
                    collection: c1,
                    index: i1,
                },
                IndexAccess {
                    collection: c2,
                    index: i2,
                },
            ) => {
                if i1 != i2 {
                    return false;
                }
                a = c1;
                b = c2;
            }
            _ => return false,
        }
    }
}

/// Replace `<subject>.fields[i]` (for `i < binders.len()`) with `field_i`.
fn rewrite_projections(expr: PseudoExpr, subject: &PseudoExpr, binders: &[Binder]) -> PseudoExpr {
    struct ProjectionRewriter<'a> {
        subject: &'a PseudoExpr,
        binders: &'a [Binder],
    }
    impl ExprFolder for ProjectionRewriter<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn pre_expr(&mut self, expr: &PseudoExpr) -> FoldAction {
            if let PseudoExpr::IndexAccess { collection, index } = expr
                && let PseudoExpr::FieldAccess { record, selector } = collection.as_ref()
                && matches!(selector, FieldSelector::NamedField(s) if s == "fields")
                && subject_eq(record.as_ref(), self.subject)
                && *index < self.binders.len()
            {
                let b = &self.binders[*index];
                return FoldAction::Replace(PseudoExpr::Var {
                    name: b.as_str().to_string(),
                    id: Some(b.id),
                });
            }
            FoldAction::Walk
        }
    }
    ProjectionRewriter { subject, binders }.fold(expr)
}

/// Fail-closed: `true` iff NO `<subject>.fields[i]` with `i >= n` appears
/// anywhere in `expr`. A projection past the constructor's arity would prove
/// the subject is not this `n`-field constructor, so the bind must not fire.
fn arm_projections_in_range(expr: &PseudoExpr, subject: &PseudoExpr, n: usize) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::IndexAccess { collection, index } = current
            && let PseudoExpr::FieldAccess { record, selector } = collection.as_ref()
            && matches!(selector, FieldSelector::NamedField(s) if s == "fields")
            && subject_eq(record.as_ref(), subject)
            && *index >= n
        {
            return false;
        }
        pending.extend(children(current));
    }
    true
}

#[cfg(test)]
mod tests;
