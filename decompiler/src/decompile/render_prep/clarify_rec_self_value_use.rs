//! Revert over-eager Scott-encoding decode on rec-fn-self `when`
//! subjects.
//!
//! `mid/patterns::try_recognize_scott_encoding` turns every
//! `Force(Apply(Force(X), [b0, b1, b2…]))` into a `MidExpr::Case`
//! with `CaseEncoding::Scott`, whether or not `X` is really a
//! Scott-encoded ADT rather than a regular N-arg call. When `X` is
//! a recursive function value the `Case` renders as `when self is {
//! Less -> …; Equal -> …; Greater -> … }` — invalid surface syntax
//! (a function cannot be matched as Ordering). The original UPLC
//! was a plain N-arg recursive call `self(b0, b1, b2)`.
//!
//! At a `RecFn { name, body }`, every `When { subject: Var(name.id),
//! clauses }` inside `body` whose clauses are
//! `WhenPattern::Constructor` over a complete consecutive tag
//! sequence 0, 1, 2, … with no guard and no informative binder
//! becomes `Apply(Var(name.id), [body_tag_0, body_tag_1, …])`: each
//! "branch" body becomes an argument. In UPLC `(rec_fn b0 b1 b2)`
//! evaluates each branch eagerly and applies `rec_fn` to them; with
//! `rec_fn = λv. λx y z. body` that binds `v` to b0, `x` to b1, `y`
//! to b2. Idiomatic in Plutus's Scott-encoded recursive helpers.
//!
//! Only fires when the scrutinee is exactly `Var(name.id)` of the
//! enclosing `RecFn`; Cases over genuine ADTs stay. Guards, and
//! binders other than unreferenced `_` padding, carry information
//! the Apply form would lose. A gap in the tag sequence, a start
//! above 0, or a Wildcard catch-all means the source was not a
//! plain N-arg call.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr, WhenClause, WhenPattern};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

/// Complete occurs-scan (covers `WhenPattern::Literal` payloads, unlike
/// `scope_recurse::children`).
fn body_references_id(body: &PseudoExpr, id: VarId) -> bool {
    use crate::pseudo::fold::ExprVisitor;
    struct S {
        id: VarId,
        hit: bool,
    }
    impl ExprVisitor for S {
        fn visit_var(&mut self, _name: &str, vid: &Option<VarId>) {
            if *vid == Some(self.id) {
                self.hit = true;
            }
        }
    }
    let mut s = S { id, hit: false };
    s.walk(body);
    s.hit
}

use super::scope_recurse::rewrite_bottom_up;

pub(super) fn clarify_rec_self_value_use(expr: PseudoExpr) -> PseudoExpr {
    rewrite_bottom_up(expr, try_rewrite)
}

fn try_rewrite(expr: PseudoExpr) -> PseudoExpr {
    let PseudoExpr::RecFn { name, params, body } = expr else {
        return expr;
    };
    // Narrow gate: fire only when the rec-fn is structurally a
    // FUNCTION (params, or an inner Lambda). A body that is a
    // pure value-producing expression may be a rec-fn that
    // genuinely returns an ADT, where case-on-self is legitimate.
    let is_function_shaped = !params.is_empty() || contains_lambda(&body);
    if !is_function_shaped {
        return PseudoExpr::RecFn { name, params, body };
    }
    let self_id = name.id;
    let new_body = revert_self_when_subjects(body.into_inner(), self_id, &name.name);
    PseudoExpr::RecFn {
        name,
        params,
        body: PBox::new(new_body),
    }
}

fn contains_lambda(expr: &PseudoExpr) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if matches!(
            current,
            PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. }
        ) {
            return true;
        }
        pending.extend(super::scope_recurse::children(current));
    }
    false
}

/// Walk `expr`, replacing `When { subject: Var(self_id), clauses: …
/// }` with `Apply(Var(self_id), [arm0, arm1, …])` when the clauses
/// form a complete consecutive constructor-tag sequence.
fn revert_self_when_subjects(expr: PseudoExpr, self_id: VarId, self_name: &str) -> PseudoExpr {
    struct RevertSelf<'a> {
        self_id: VarId,
        self_name: &'a str,
    }

    impl ExprFolder for RevertSelf<'_> {
        fn fold_pattern(&mut self, pattern: WhenPattern) -> WhenPattern {
            pattern
        }

        fn post_when(
            &mut self,
            subject: PseudoExpr,
            subject_name: Option<Binder>,
            clauses: Vec<WhenClause>,
        ) -> PseudoExpr {
            let is_self_subject = matches!(
                &subject,
                PseudoExpr::Var { id: Some(v), .. } if *v == self.self_id
            );
            if is_self_subject && let Some(args) = try_extract_complete_tag_args(&clauses) {
                return PseudoExpr::Apply {
                    function: PBox::new(PseudoExpr::Var {
                        name: self.self_name.to_string(),
                        id: Some(self.self_id),
                    }),
                    args: args.into(),
                };
            }
            PseudoExpr::When {
                subject: PBox::new(subject),
                subject_name,
                clauses,
            }
        }
    }

    RevertSelf { self_id, self_name }.fold(expr)
}

/// Complete consecutive tag-sequence `[0, 1, 2, …]` of no-guard
/// Constructor patterns whose fields are all unreferenced `_`
/// padding → the clause bodies in tag order.
fn try_extract_complete_tag_args(clauses: &[WhenClause]) -> Option<Vec<PseudoExpr>> {
    let n = clauses.len();
    if n < 2 {
        return None;
    }
    // Collect (tag → body) pairs; reject any guard or
    // non-Constructor pattern.
    let mut by_tag: std::collections::BTreeMap<usize, PseudoExpr> =
        std::collections::BTreeMap::new();
    for c in clauses {
        if c.guard.is_some() {
            return None;
        }
        let WhenPattern::Constructor { tag, fields, .. } = &c.pattern else {
            return None;
        };
        // Arity-PADDING binders (literal `_`, minted by
        // `unify_constructor_pattern_arity` when this when's tags share a
        // stub class with higher-arity construction sites) carry no
        // information — the mis-recognized Scott case was nullary. A NAMED
        // binder rejects; a `_` binder must also be unreferenced in the
        // body, since the `_` convention is not an enforced invariant.
        if !fields.iter().all(|b| b.name == "_") {
            return None;
        }
        if fields.iter().any(|b| body_references_id(&c.body, b.id)) {
            return None;
        }
        if by_tag.insert(*tag, c.body.clone()).is_some() {
            // Duplicate tag — abort.
            return None;
        }
    }
    // Check complete consecutive sequence starting at 0.
    let tags: Vec<usize> = by_tag.keys().copied().collect();
    if tags.first() != Some(&0) {
        return None;
    }
    for (i, &t) in tags.iter().enumerate() {
        if t != i {
            return None;
        }
    }
    Some(by_tag.into_values().collect())
}

#[cfg(test)]
mod tests;
