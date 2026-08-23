//! Rewrite Church-encoded values to native types (gated on
//! [`RenderCtx::decode_church`], from `DecompileOptions::decode_church_to_native`).
//!
//! Each shape requires strict `VarId` identity between the Lambda's
//! params and the inner `Var(...)`(s):
//! - `Lambda { [x], Apply { Var(x), [a, b] } }` → `Pair(a, b)`
//!   (church-pack; arity ≥ 3 becomes a Tuple instead)
//! - `Lambda { [t, _], Var(t) }` / `Lambda { [_, f], Var(f) }` →
//!   `Bool(true)` / `Bool(false)`
//! - `Lambda { [_, k], Apply { Var(k), [h, t] } }` → `[h, ..t]`
//!   (church-cons; the first param is the nil continuation)
//!
//! Runs late in render_prep, after the other church-collapse passes
//! (`church_pair_collapse`, `recover_church_list_literal`, …); what
//! survives to here sits in helper function bodies (e.g.
//! `fn pair_pack(a, b) { fn(x) { x(a, b) } }`) and in `--raw` /
//! `--safe-mode` output, where those passes were skipped.
//!
//! The rewrite is at the value level — the compiled UPLC still uses
//! the Church encoding, so `Pair(a, b)` is a readability surface, not a
//! literal compilation target. Leave the flag off for faithful UPLC.

use crate::pseudo::ast::PBox;
use std::collections::HashMap;

use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::ctx::RenderCtx;

/// What the decode attributed to each let-binding it rewrote: the
/// binding's `VarId` → its encoding tag (`church-pair`, `church-cons`,
/// `church-pack-<n>`, `church-true`/`-false`, or hints like `identity`).
///
/// An OUTPUT of the pass, consumed one phase later by the pretty-printer,
/// which emits it as a trailing `// <tag>` comment. It travels out of
/// `prepare_for_render` beside the tree it describes, because the `VarId`
/// keys are only meaningful for THAT tree — every `prepare_for_render`
/// re-mints binder ids, so a map from any other run would stamp tags on
/// unrelated bindings.
#[derive(Debug, Clone, Default)]
pub(crate) struct ChurchLetComments(HashMap<VarId, String>);

impl ChurchLetComments {
    /// The tag attributed to `vid`'s value, if the decode rewrote it.
    pub(crate) fn get(&self, vid: VarId) -> Option<&str> {
        self.0.get(&vid).map(String::as_str)
    }
}

pub(super) fn decode_church_to_native(
    expr: PseudoExpr,
    ctx: &RenderCtx,
    notes: &mut ChurchLetComments,
) -> PseudoExpr {
    if !ctx.decode_church() {
        return expr;
    }
    rewrite(expr, notes)
}

fn rewrite(expr: PseudoExpr, notes: &mut ChurchLetComments) -> PseudoExpr {
    DecodeChurchToNative { notes }.fold(expr)
}

struct DecodeChurchToNative<'a> {
    notes: &'a mut ChurchLetComments,
}

impl ExprFolder for DecodeChurchToNative<'_> {
    // `try_rewrite_self` only ever matches a `Lambda` shape, so hanging it
    // off `post_lambda` reproduces the old "rewrite self, then descend into
    // whatever children remain" behaviour: it runs after `body` is already
    // folded, but none of its patterns look past the immediate `Apply`/`Var`
    // shape of that body, so folding it first vs. after wrapping in the
    // rewritten `Pair`/`Tuple`/`List` node changes nothing.
    fn post_lambda(&mut self, params: Vec<Binder>, body: PseudoExpr) -> PseudoExpr {
        let candidate = PseudoExpr::Lambda {
            params,
            body: PBox::new(body),
        };
        match try_rewrite_self(candidate) {
            Ok((rewritten, _tag)) => rewritten,
            Err(orig) => orig,
        }
    }

    // Tag attribution happens ONLY here, from the already-folded value's
    // immediate shape: a church shape buried deep in an unrelated
    // expression (a `fn(_, f) { f }` inside a `when`) must not tag the
    // enclosing let `church-false`. Runs after both `value` and `body` are
    // folded, same as the old post-order code.
    fn post_let(
        &mut self,
        name: String,
        id: Option<VarId>,
        value: PseudoExpr,
        body: PseudoExpr,
    ) -> PseudoExpr {
        if let Some(vid) = id {
            let tag =
                detect_immediate_church_native(&value).or_else(|| try_annotate_immediate(&value));
            if let Some(tag) = tag {
                self.notes.0.insert(vid, tag);
            }
        }
        PseudoExpr::Let {
            name,
            id,
            value: PBox::new(value),
            body: PBox::new(body),
        }
    }

    // Do not walk a `when` clause's pattern (only its guard/body), so a
    // church shape sitting inside a `Literal` pattern is left untouched.
    fn fold_pattern(
        &mut self,
        pattern: crate::pseudo::ast::WhenPattern,
    ) -> crate::pseudo::ast::WhenPattern {
        pattern
    }
}

/// Tag from the let's IMMEDIATE value shape — `Pair`, `Tuple`, `List` or
/// `Bool`, either directly or at a Lambda's body root, which is what a
/// church-native rewrite leaves behind: `let pair_pack = fn(a, b) { … }`
/// whose rewritten body is `Pair` tags `church-pair`. A `Pair` nested any
/// deeper (`let x = when … { … Pair(a, b) … }`) gets no tag.
fn detect_immediate_church_native(expr: &PseudoExpr) -> Option<String> {
    let inner = match expr {
        PseudoExpr::Lambda { body, .. } => body.as_ref(),
        other => other,
    };
    match inner {
        PseudoExpr::Pair(_, _) => Some("church-pair".to_string()),
        PseudoExpr::Tuple(items) => Some(pack_tag(items.len())),
        PseudoExpr::List { .. } => Some("church-cons".to_string()),
        PseudoExpr::Bool(true) => Some("church-true".to_string()),
        PseudoExpr::Bool(false) => Some("church-false".to_string()),
        _ => None,
    }
}

/// Format a `church-pack-<n>` tag for the given arity.
fn pack_tag(n: usize) -> String {
    format!("church-pack-{}", n)
}

/// Patterns that tag the enclosing Let with a hint without
/// rewriting the AST. Called only on the immediate Let value:
/// deeper, an inline `fn(x) { x }` passed as an arg would tag
/// whatever Let happens to enclose it.
fn try_annotate_immediate(expr: &PseudoExpr) -> Option<String> {
    // `fn(x) { x }` — identity lambda.
    if let PseudoExpr::Lambda { params, body } = expr
        && params.len() == 1
        && let PseudoExpr::Var { id: Some(vid), .. } = body.as_ref()
        && *vid == params[0].id
    {
        return Some("identity".to_string());
    }
    // `fn(<any params>) { fail … }` — always-fail continuation.
    if let PseudoExpr::Lambda { params: _, body } = expr
        && matches!(body.as_ref(), PseudoExpr::Error { .. })
    {
        return Some("always-fail".to_string());
    }
    // `fn(<≥2 params>) { c }` for c a primitive literal. 1-arg
    // constant-fns are noisy — every `fn(_) { x }` projector
    // would fire — so ≥2 only.
    if let PseudoExpr::Lambda { params, body } = expr
        && params.len() >= 2
        && matches!(
            body.as_ref(),
            PseudoExpr::Int(_)
                | PseudoExpr::Bool(_)
                | PseudoExpr::ByteArray(_)
                | PseudoExpr::Unit
                | PseudoExpr::String(_)
                | PseudoExpr::HelperSymbol(_)
        )
    {
        return Some("constant".to_string());
    }
    None
}

/// Try to rewrite a church-shape Lambda to its native equivalent. Returns
/// `Ok((native, tag))` on a hit, `Err(original)` on a miss.
fn try_rewrite_self(expr: PseudoExpr) -> Result<(PseudoExpr, String), PseudoExpr> {
    // `fn(x) { x(a, b, c, ...) }` (church-N-pack):
    //   - arity 2 → `Pair(a, b)` (Pair builtin, `.fst`/`.snd`)
    //   - arity ≥ 3 → `(a, b, c, ...)` (Tuple); consumers
    //     use numeric `.<n>` access, matching Tuple semantics.
    if let PseudoExpr::Lambda { params, body } = &expr
        && params.len() == 1
        && let PseudoExpr::Apply { function, args } = body.as_ref()
        && let PseudoExpr::Var {
            id: Some(fn_id), ..
        } = function.as_ref()
        && *fn_id == params[0].id
    {
        match args.len() {
            0 => {}
            1 => {} // arity 1 is identity-ish; not a pack shape, skip
            2 => {
                return Ok((
                    PseudoExpr::Pair(PBox::new(args[0].clone()), PBox::new(args[1].clone())),
                    "church-pair".to_string(),
                ));
            }
            n => {
                return Ok((PseudoExpr::Tuple(args.clone()), pack_tag(n)));
            }
        }
    }
    if let PseudoExpr::Lambda { params, body } = &expr
        && params.len() == 2
        && let PseudoExpr::Var { id: Some(vid), .. } = body.as_ref()
    {
        if *vid == params[0].id {
            return Ok((PseudoExpr::Bool(true), "church-true".to_string()));
        }
        if *vid == params[1].id {
            return Ok((PseudoExpr::Bool(false), "church-false".to_string()));
        }
    }
    // Church-cons: `fn(_, k) { k(head, tail) }` ≡ `[head, ..tail]`; the
    // first param is the unused nil-continuation.
    if let PseudoExpr::Lambda { params, body } = &expr
        && params.len() == 2
        && let PseudoExpr::Apply { function, args } = body.as_ref()
        && let PseudoExpr::Var {
            id: Some(fn_id), ..
        } = function.as_ref()
        && *fn_id == params[1].id
        && args.len() == 2
    {
        return Ok((
            PseudoExpr::List {
                elements: vec![args[0].clone()].into(),
                tail: Some(PBox::new(args[1].clone())),
            },
            "church-cons".to_string(),
        ));
    }
    Err(expr)
}

#[cfg(test)]
mod tests;
