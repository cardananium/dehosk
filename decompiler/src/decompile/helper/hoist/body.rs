use crate::pseudo::OptionVarIdGet;
use crate::pseudo::ast::PBox;
use crate::pseudo::ast::{Binder, PseudoExpr};
use crate::pseudo::fold::ExprFolder;
use crate::pseudo::var_id::VarId;

use super::BindingTarget;
use super::calls::{append_helper_call_args, helper_body_binds_name, helper_is_direct_call_only};
use super::dependencies::{helper_value_free_vars_within, helper_value_is_closed};
use super::references::var_is_referenced_id_aware;

pub(super) fn canonicalize_inverted_recfn_let(
    name: String,
    id: Option<VarId>,
    value: &PseudoExpr,
    body: &PseudoExpr,
) -> Option<PseudoExpr> {
    let PseudoExpr::Apply { function, args } = value else {
        return None;
    };
    let PseudoExpr::Var {
        name: call_name,
        id: Some(call_id),
    } = function.as_ref()
    else {
        return None;
    };
    let PseudoExpr::RecFn { name: fn_name, .. } = body else {
        return None;
    };

    if call_name != &name || fn_name.as_str() != name {
        return None;
    }
    let id_concrete = id.unwrap_or_else(VarId::fresh_compat_placeholder);
    if call_id.get().is_some_and(|call_id| call_id != id_concrete) {
        return None;
    }

    Some(PseudoExpr::Let {
        name,
        id,
        value: PBox::new(body.clone()),
        body: PBox::new(PseudoExpr::Apply {
            function: PBox::new(PseudoExpr::var_with_id(call_name.clone(), id_concrete)),
            args: args.clone(),
        }),
    })
}

pub(super) fn is_helper_binding_value(expr: &PseudoExpr) -> bool {
    matches!(expr, PseudoExpr::Lambda { .. } | PseudoExpr::RecFn { .. })
}

pub(super) fn try_hoist_helper_from_body(
    outer_name: String,
    outer_id: Option<VarId>,
    outer_value: PseudoExpr,
    outer_body: PseudoExpr,
) -> Option<PseudoExpr> {
    let PseudoExpr::Let {
        name: inner_name,
        id: inner_id,
        value: inner_value,
        body: inner_body,
    } = outer_body
    else {
        return None;
    };

    // `.get()` on an `Option<VarId>` reduces a compat-placeholder id
    // to `None`, so `.get().unwrap_or_else(...)` here would mint a
    // fresh compat and perturb downstream identity comparisons. Keep
    // the incoming id.
    let inner_id_concrete = inner_id.unwrap_or_else(VarId::fresh_compat_placeholder);
    let outer_id_concrete = outer_id.unwrap_or_else(VarId::fresh_compat_placeholder);

    if !is_helper_binding_value(inner_value.as_ref())
        || var_is_referenced_id_aware(&outer_value, inner_id_concrete, &inner_name)
    {
        return None;
    }

    let outer_binder = Binder::new(outer_name.clone(), outer_id_concrete);

    if !var_is_referenced_id_aware(inner_value.as_ref(), outer_id_concrete, &outer_name) {
        if is_helper_binding_value(&outer_value) {
            return None;
        }
        if !helper_value_is_closed(inner_value.as_ref()) {
            return None;
        }
        return Some(PseudoExpr::Let {
            name: inner_name,
            id: inner_id,
            value: inner_value,
            body: PBox::new(PseudoExpr::Let {
                name: outer_binder.name.clone(),
                id: Some(outer_binder.id),
                value: PBox::new(outer_value),
                body: inner_body,
            }),
        });
    }

    let PseudoExpr::RecFn {
        name: rec_name,
        params,
        body: rec_body,
    } = inner_value.as_ref()
    else {
        return None;
    };

    if rec_name != &inner_name
        || !helper_value_free_vars_within(
            inner_value.as_ref(),
            &[BindingTarget {
                name: outer_name.clone(),
                id: outer_id_concrete,
            }],
        )
        || helper_body_binds_name(rec_body, &outer_name)
        || helper_body_binds_name(inner_body.as_ref(), &outer_name)
        || !helper_is_direct_call_only(
            inner_body.as_ref(),
            &inner_name,
            inner_id_concrete,
            params.len(),
        )
    {
        return None;
    }

    let helper_capture_param = Binder::new(outer_name.clone(), VarId::fresh_binding());
    struct RetargetCaptureVarId<'a> {
        target: &'a str,
        target_id: VarId,
        new_id: VarId,
    }
    impl ExprFolder for RetargetCaptureVarId<'_> {
        // Folded flat: this implementation overrides none of
        // `fold_when` / `fold_clause` / `fold_pattern`, so the machine
        // can reassemble a `when` itself instead of recursing through
        // the hook once per nesting level.
        fn machine_folds_when(&self) -> bool {
            true
        }
        fn post_var(&mut self, name: String, id: Option<VarId>) -> PseudoExpr {
            if crate::decompile::var_match::refs_match(
                &name,
                id.get(),
                self.target,
                self.target_id.get(),
            ) {
                PseudoExpr::Var {
                    name,
                    id: Some(self.new_id),
                }
            } else {
                PseudoExpr::Var { name, id }
            }
        }
    }
    let lifted_body = RetargetCaptureVarId {
        target: &outer_name,
        target_id: outer_id_concrete,
        new_id: helper_capture_param.id,
    }
    .fold(rec_body.as_ref().clone());
    // Self-recursive calls in the helper body reference the RecFn's
    // own self-name binder (`rec_name`), whose VarId can differ
    // from the let binder (`inner_id`). Key the in-body append on
    // `rec_name` so the capture arg threads through the recursion;
    // keyed on `inner_id` the self-call stays under-applied
    // (`rec fn any(list, u) { … any(tail) }`).
    let rec_self_id = rec_name.var_id();
    let lifted_body = append_helper_call_args(
        &lifted_body,
        rec_name.as_str(),
        rec_self_id,
        params.len(),
        &[PseudoExpr::var_with_id(
            helper_capture_param.as_str(),
            helper_capture_param.id,
        )],
    );
    let lifted_helper = PseudoExpr::RecFn {
        name: rec_name.clone(),
        params: params
            .iter()
            .cloned()
            .chain(std::iter::once(helper_capture_param))
            .collect(),
        body: PBox::new(lifted_body),
    };
    let lifted_call_body = append_helper_call_args(
        inner_body.as_ref(),
        &inner_name,
        inner_id_concrete,
        params.len(),
        &[PseudoExpr::var_with_id(
            outer_binder.as_str(),
            outer_binder.id,
        )],
    );

    Some(PseudoExpr::Let {
        name: inner_name,
        id: inner_id,
        value: PBox::new(lifted_helper),
        body: PBox::new(PseudoExpr::Let {
            name: outer_binder.name,
            id: Some(outer_binder.id),
            value: PBox::new(outer_value),
            body: PBox::new(lifted_call_body),
        }),
    })
}
