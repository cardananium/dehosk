//! Inline let-bound constructor helpers — Lambdas whose body is a
//! constructor of their params and nothing else. After
//! `decode_church_to_native` rewrites church-encoded helpers to native
//! shapes, the canonical forms are `Pair(a, b)`, `(a, …)`, and
//! `[h, ..t]`. The body has no computation, only packing, so every
//! call inlines. If all uses of the helper are inlined, the definition
//! is dropped.
//!
//! Body must be exactly a constructor whose every component is `Var`
//! referencing a param by `VarId`, in order, no shuffling. The strict
//! id-match rejects a helper that builds its constructor from outer
//! vars (`fn h(a, b) { Pair(c, d) }`): `c`/`d` are closure-captured,
//! not reachable by parameter substitution.
//!
//! Pure substitution; no fresh `VarId`s minted. A bare ref to the
//! helper (passed as a value, not called) keeps the let alive; its
//! call-sites are still rewritten. Only fires on those exact
//! constructor shapes.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::PseudoExpr;
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::scope_recurse::children;

pub(super) fn inline_constructor_helpers(expr: PseudoExpr) -> PseudoExpr {
    InlineConstructorHelpers.fold(expr)
}

struct InlineConstructorHelpers;

impl ExprFolder for InlineConstructorHelpers {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    // The classify-and-substitute logic only needs the already-folded
    // `value`/`body` (nothing must be pushed before `body` is folded), so
    // it slots into `post_let` unchanged from the old post-order code.
    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        let helper_template = match &id {
            Some(vid) => classify_constructor_helper(&value).map(|tpl| (*vid, tpl)),
            None => None,
        };

        if let Some((helper_id, template)) = helper_template {
            let (new_body, kept_bare_ref) = rewrite_uses(body, helper_id, &template);
            if kept_bare_ref {
                return PseudoExpr::Let {
                    name,
                    id,
                    value: PBox::new(value),
                    body: PBox::new(new_body),
                };
            }
            // No bare refs — helper unused after inlining, drop the let.
            return new_body;
        }

        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }
}

/// Template describing a constructor helper that can be inlined.
#[derive(Debug, Clone)]
enum Template {
    /// `fn(p0, p1) { Pair(Var(p0), Var(p1)) }`
    Pair,
    /// `fn(p0, p1, ..., pN-1) { (Var(p0), Var(p1), ..., Var(pN-1)) }`
    Tuple { params: Vec<VarId> },
    /// `fn(p0, p1) { [Var(p0), ..Var(p1)] }`
    ListCons,
}

/// Classify a let-value as a constructor helper. Returns the
/// substitution template if recognised.
fn classify_constructor_helper(value: &PseudoExpr) -> Option<Template> {
    let PseudoExpr::Lambda { params, body } = value else {
        return None;
    };
    match body.as_ref() {
        // `fn(a, b) { Pair(a, b) }`
        PseudoExpr::Pair(a, b) if params.len() == 2 => {
            expect_param_var(a, params[0].id)?;
            expect_param_var(b, params[1].id)?;
            Some(Template::Pair)
        }
        // `fn(a, b, c, …) { (a, b, c, …) }` (Tuple with N≥3 components)
        PseudoExpr::Tuple(items) if items.len() == params.len() && items.len() >= 3 => {
            let mut param_ids = Vec::with_capacity(items.len());
            for (item, param) in items.iter().zip(params.iter()) {
                let id = expect_param_var(item, param.id)?;
                param_ids.push(id);
            }
            Some(Template::Tuple { params: param_ids })
        }
        // `fn(h, t) { [h, ..t] }` — single-element list with tail.
        PseudoExpr::List { elements, tail } if params.len() == 2 && elements.len() == 1 => {
            let tail_expr = tail.as_deref()?;
            expect_param_var(&elements[0], params[0].id)?;
            expect_param_var(tail_expr, params[1].id)?;
            Some(Template::ListCons)
        }
        _ => None,
    }
}

/// `expr` must be a `Var { id: Some(vid) }` with `vid == expected`.
fn expect_param_var(expr: &PseudoExpr, expected: VarId) -> Option<VarId> {
    if let PseudoExpr::Var { id: Some(vid), .. } = expr
        && *vid == expected
    {
        return Some(*vid);
    }
    None
}

/// Walk `body`, inlining every `Apply { Var(helper_id), [args] }` to
/// the substituted constructor. Returns the new body and whether any
/// non-call reference to `helper_id` remained (which would keep the
/// helper let alive).
fn rewrite_uses(body: PseudoExpr, helper_id: VarId, template: &Template) -> (PseudoExpr, bool) {
    let mut substituter = SubstituteConstructorCall {
        helper_id,
        template,
    };
    let new_body = substituter.fold(body);
    let bare_ref = contains_var_id(&new_body, helper_id);
    (new_body, bare_ref)
}

struct SubstituteConstructorCall<'a> {
    helper_id: VarId,
    template: &'a Template,
}

impl ExprFolder for SubstituteConstructorCall<'_> {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn post_apply(&mut self, function: PseudoExpr, args: Vec<PseudoExpr>) -> PseudoExpr {
        if let PseudoExpr::Var { id: Some(vid), .. } = &function
            && *vid == self.helper_id
            && self.template.matches_arity(args.len())
        {
            // `args` are already folded (nested call sites included).
            return self.template.instantiate(args);
        }
        PseudoExpr::Apply {
            function: PBox::new(function),
            args: args.into(),
        }
    }
}

fn contains_var_id(expr: &PseudoExpr, target: VarId) -> bool {
    let mut pending: Vec<&PseudoExpr> = vec![expr];
    while let Some(current) = pending.pop() {
        if let PseudoExpr::Var { id: Some(vid), .. } = current
            && *vid == target
        {
            return true;
        }
        pending.extend(children(current));
    }
    false
}

impl Template {
    fn matches_arity(&self, n: usize) -> bool {
        match self {
            Template::Pair => n == 2,
            Template::Tuple { params } => n == params.len(),
            Template::ListCons => n == 2,
        }
    }

    fn instantiate(&self, args: Vec<PseudoExpr>) -> PseudoExpr {
        match self {
            Template::Pair => {
                let mut it = args.into_iter();
                PseudoExpr::Pair(PBox::new(it.next().unwrap()), PBox::new(it.next().unwrap()))
            }
            Template::Tuple { .. } => PseudoExpr::Tuple(args.into()),
            Template::ListCons => {
                let mut it = args.into_iter();
                let head = it.next().unwrap();
                let tail = it.next().unwrap();
                PseudoExpr::List {
                    elements: vec![head].into(),
                    tail: Some(PBox::new(tail)),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
