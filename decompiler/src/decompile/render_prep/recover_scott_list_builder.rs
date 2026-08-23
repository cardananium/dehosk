//! Recover a Scott-encoded list producer into native list cells (opt-in).
//!
//! V1 / PlutusTx builds `cons(h, t)` as a 2-field constructor and `nil` as
//! church-true `λt.λf.t`. The consumer already recovers to
//! `when xs is { [] -> …; [h, ..t] -> … }`, but the producer stays a stub
//! `Constr`. `complete_church_nil_to_empty_list` turns `[] -> church_true`
//! into `[] -> []` only once the sibling cons arm's value leaves are
//! native `List` cells — which a raw Scott cell never is. This pass
//! supplies that missing step.
//!
//! Fail-closed: inside a `rec fn f`, only
//! `Constr { arity == 2, fields: [head, Apply(Var(self), …)] }` where
//! `self` is the enclosing `RecFn`'s VarId (unique after
//! alpha-uniquify). A genuine 2-field ADT does not systematically place
//! the rec-fn self-call in its second field across a list fold.
//!
//! Opt-in behind `--decode-church-to-native`: a native-list *reading* of
//! a Scott producer. Flag off is the identity.

use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::ctx::RenderCtx;

pub(super) fn recover_scott_list_builder(expr: PseudoExpr, ctx: &RenderCtx) -> PseudoExpr {
    if !ctx.decode_church() {
        return expr;
    }
    ScottListBuilder {
        self_id: None,
        outer: Vec::new(),
    }
    .fold(expr)
}

/// `self_id` is the innermost enclosing `RecFn`'s own `VarId`, rebound on
/// entry to each `RecFn` and restored on exit via `outer` — a stack because
/// `RecFn`s can nest and the driver folds iteratively, not by real
/// recursion, so there is no call frame to hold the previous value for us.
struct ScottListBuilder {
    self_id: Option<VarId>,
    outer: Vec<Option<VarId>>,
}

impl ExprFolder for ScottListBuilder {
    // Folded flat: this implementation overrides none of
    // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
    // can reassemble a `when` itself instead of recursing through
    // the hook once per nesting level.
    fn machine_folds_when(&self) -> bool {
        true
    }
    fn enter_recfn(&mut self, name: &Binder, params: &[Binder]) -> (Binder, Vec<Binder>) {
        self.outer.push(self.self_id);
        self.self_id = Some(name.id);
        (name.clone(), params.to_vec())
    }

    fn exit_recfn(&mut self, _name: &Binder, _params: &[Binder]) {
        self.self_id = self
            .outer
            .pop()
            .expect("enter_recfn pushed a matching entry");
    }

    fn post_constr(
        &mut self,
        type_hint: Option<crate::pseudo::type_hint::TypeHintId>,
        tag: usize,
        fields: Vec<PseudoExpr>,
        shape: crate::pseudo::constructor::ConstructorShape,
    ) -> PseudoExpr {
        // A 2-field constructor whose second field is a recursive self-call
        // is a Scott cons cell → native `[head, ..self(…)]`. Fields are
        // already folded (bottom-up). The self-call shape — `Apply` whose
        // function is `Var(self_id)` — is never rewritten by this pass, so
        // checking it post-fold is enough.
        if let Some(self_id) = self.self_id {
            if fields.len() == 2 && is_self_call(&fields[1], self_id) {
                let mut it = fields.into_iter();
                let head = it.next().expect("len checked == 2");
                let tail = it.next().expect("len checked == 2");
                return PseudoExpr::List {
                    elements: vec![head].into(),
                    tail: Some(PBox::new(tail)),
                };
            }
        }
        PseudoExpr::Constr {
            type_hint,
            tag,
            fields: fields.into(),
            shape,
        }
    }
}

/// Whether `expr` is a recursive self-call — an application of `self_id`.
fn is_self_call(expr: &PseudoExpr, self_id: VarId) -> bool {
    matches!(
        expr,
        PseudoExpr::Apply { function, .. }
            if matches!(function.as_ref(), PseudoExpr::Var { id: Some(id), .. } if *id == self_id)
    )
}

#[cfg(test)]
mod tests;
